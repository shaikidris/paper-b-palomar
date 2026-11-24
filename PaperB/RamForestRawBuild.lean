module

public import PaperB.RamForestRowSchedule
public import PaperB.RamForestSweep
public import PaperB.RamForestFinishAdapter
public import PaperB.ForestPreparedBuild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
End-to-end single-run word-RAM constructor for Lemma 3.2 (v1.3):
- encodes any `LabelledQuotient` into raw input words (`rawInputOfQuotient`),
- dispatches dynamically on `n_H < 3` (`smallBuildCode`) vs `3 ≤ n_H`
  (`stage1Phase` -> `dictSortPhase` -> `sweepPhase` -> `fullPackedFinishProgram`)
  in ONE single fixed program `rawForestBuildProgram`,
- proves `O((n_H + m_H) L^2)` total RAM operations (`≤ 11662 * ((n_H + m_H) * L^2)`),
  `O(n_H + m_H)` peak live words (`inputCap + workCap + 15 ≤ 70 * (n_H + m_H)`),
  `O(n_H)` retained words (`≤ 1 + 18 * n_H ≤ 19 * n_H`), `O(L)` pair lookup, and
  `O(1)` known-node membership,
- exports the public root `PaperB.build_proper_loss_forest` (and v1.2 cubic corollary
  `PaperB.build_proper_loss_forest_v12_cubic`).
-/

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (zero ltb ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.ArcDecode
open PaperB.RamForestProgram.ArcParents
open PaperB.RamForestProgram.DictSort
open PaperB.RamForestProgram.Sweep
open PaperB.RetainedProperLoss
open PaperB.ForestDictionary (Rows)
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount)
open _root_.EX24.PreparedSweep (orderedConfig)

/-! ### 1. Raw Quotient Word Encoding & Word-Size Bounds -/

theorem rawWordBits_ge_seven (H : LabelledQuotient) :
    7 ≤ OracleContract.wordBits 5 H.vertexCount H.arcCount := by
  have hpos : 1 ≤ H.vertexCount := Fin.pos H.root
  unfold OracleContract.wordBits OracleContract.L
  have hlog : 1 ≤ Nat.log2 (H.vertexCount + H.arcCount + 1) :=
    (Nat.le_log2 (by omega)).mpr (by omega)
  omega

theorem pow_two_ge_of_wordBits (H : LabelledQuotient) :
    128 ≤ 2 ^ OracleContract.wordBits 5 H.vertexCount H.arcCount := by
  calc 128 = 2 ^ 7 := by decide
    _ ≤ 2 ^ OracleContract.wordBits 5 H.vertexCount H.arcCount :=
      Nat.pow_le_pow_right (by decide) (rawWordBits_ge_seven H)

/-- Canonical raw input word buffer `[n_H, m_H, root_H, sources..., heads...]`
for an arbitrary `H : LabelledQuotient`. -/
noncomputable def rawInputOfQuotient (H : LabelledQuotient) :
    Input (layout (OracleContract.wordBits 5 H.vertexCount H.arcCount)
      (rawInputCap H.arcCount) (rawWorkCap H.vertexCount H.arcCount)
      (rawWordBits_fit H.vertexCount H.arcCount).1
      (rawWordBits_fit H.vertexCount H.arcCount).2.1) where
  words :=
    Array.ofFn fun i : Fin (rawInputCap H.arcCount) =>
      let bits := OracleContract.wordBits 5 H.vertexCount H.arcCount
      have hfit := rawWordBits_fit H.vertexCount H.arcCount
      have hn : H.vertexCount < 2 ^ bits := by
        have : 1 + 18 * H.vertexCount < 2 ^ bits := hfit.2.2
        omega
      have hm : H.arcCount < 2 ^ bits := by
        have : rawInputCap H.arcCount ≤ 2 ^ bits := hfit.1
        unfold rawInputCap at this
        omega
      if _ : i.val = 0 then ⟨H.vertexCount, hn⟩
      else if _ : i.val = 1 then ⟨H.arcCount, hm⟩
      else if _ : i.val = 2 then ⟨H.root.val, Nat.lt_trans H.root.isLt hn⟩
      else if _ : i.val < 3 + H.arcCount then
        let e : Fin H.arcCount := ⟨i.val - 3, by omega⟩
        ⟨(rawOccurrence H e).1.val, Nat.lt_trans (rawOccurrence H e).1.isLt hn⟩
      else
        let e : Fin H.arcCount := ⟨i.val - (3 + H.arcCount), by
          have hi := i.isLt
          unfold rawInputCap at hi
          omega⟩
        ⟨(rawHead H e).val, Nat.lt_trans (rawHead H e).isLt hn⟩
  size_eq := Array.size_ofFn

theorem rawInputOfQuotient_spec (H : LabelledQuotient) :
    RawQuotientInput (rawInputOfQuotient H) H where
  cap_ge := Nat.le_refl _
  hdr_n := by
    have hlt0 : 0 < rawInputCap H.arcCount := by unfold rawInputCap; omega
    have hlt : 0 < (rawInputOfQuotient H).words.size := by
      rw [(rawInputOfQuotient H).size_eq]; exact hlt0
    rw [getElem?_pos (rawInputOfQuotient H).words 0 hlt]
    change Option.map Fin.val
      (some ((Array.ofFn _)[0]'(by simpa only [Array.size_ofFn] using hlt0))) = _
    simp
  hdr_m := by
    have hlt1 : 1 < rawInputCap H.arcCount := by unfold rawInputCap; omega
    have hlt : 1 < (rawInputOfQuotient H).words.size := by
      rw [(rawInputOfQuotient H).size_eq]; exact hlt1
    rw [getElem?_pos (rawInputOfQuotient H).words 1 hlt]
    change Option.map Fin.val
      (some ((Array.ofFn _)[1]'(by simpa only [Array.size_ofFn] using hlt1))) = _
    simp
  hdr_root := by
    have hlt2 : 2 < rawInputCap H.arcCount := by unfold rawInputCap; omega
    have hlt : 2 < (rawInputOfQuotient H).words.size := by
      rw [(rawInputOfQuotient H).size_eq]; exact hlt2
    rw [getElem?_pos (rawInputOfQuotient H).words 2 hlt]
    change Option.map Fin.val
      (some ((Array.ofFn _)[2]'(by simpa only [Array.size_ofFn] using hlt2))) = _
    simp
  sources := by
    intro e
    have he := e.isLt
    have hlte : 3 + e.val < rawInputCap H.arcCount := by unfold rawInputCap; omega
    have hlt : 3 + e.val < (rawInputOfQuotient H).words.size := by
      rw [(rawInputOfQuotient H).size_eq]; exact hlte
    rw [getElem?_pos (rawInputOfQuotient H).words (3 + e.val) hlt]
    change Option.map Fin.val
      (some ((Array.ofFn _)[3 + e.val]'(by simpa only [Array.size_ofFn] using hlte))) = _
    rw [Array.getElem_ofFn]
    have hne0 : ¬ (3 + e.val = 0) := by omega
    have hne1 : ¬ (3 + e.val = 1) := by omega
    have hne2 : ¬ (3 + e.val = 2) := by omega
    have hsrc : 3 + e.val < 3 + H.arcCount := by omega
    simp only [hne0, hne1, hne2, hsrc, ↓reduceDIte, Option.map_some]
    have hfin : (⟨3 + e.val - 3, by omega⟩ : Fin H.arcCount) = e := by
      apply Fin.ext; simp
    rw [hfin]
  heads := by
    intro e
    have he := e.isLt
    have hlte : 3 + H.arcCount + e.val < rawInputCap H.arcCount := by unfold rawInputCap; omega
    have hlt : 3 + H.arcCount + e.val < (rawInputOfQuotient H).words.size := by
      rw [(rawInputOfQuotient H).size_eq]; exact hlte
    rw [getElem?_pos (rawInputOfQuotient H).words (3 + H.arcCount + e.val) hlt]
    change Option.map Fin.val
      (some ((Array.ofFn _)[3 + H.arcCount + e.val]'(by simpa only [Array.size_ofFn] using hlte))) = _
    rw [Array.getElem_ofFn]
    have hne0 : ¬ (3 + H.arcCount + e.val = 0) := by omega
    have hne1 : ¬ (3 + H.arcCount + e.val = 1) := by omega
    have hne2 : ¬ (3 + H.arcCount + e.val = 2) := by omega
    have hnsrc : ¬ (3 + H.arcCount + e.val < 3 + H.arcCount) := by omega
    simp only [hne0, hne1, hne2, hnsrc, ↓reduceDIte, Option.map_some]
    have hfin : (⟨3 + H.arcCount + e.val - (3 + H.arcCount), by omega⟩ : Fin H.arcCount) = e := by
      apply Fin.ext; simp
    rw [hfin]

/-! ### 2. Relocated Two-Branch Runtime Dispatcher & Single-Run Build Program -/

section DispatchAndBuild

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}

private theorem step_imm_next {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {dst : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.imm dst w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State (layout bits inputCap workCap hi hw), step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ t.data = s.data ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  have hd : dst.val < s.regs.size := by simpa only [s.regs_size] using dst.isLt
  let t : State (layout bits inputCap workCap hi hw) :=
    { s with regs := s.regs.set dst.val w hd, pc := s.pc + 1,
             regs_size := by simp only [Array.size_set, s.regs_size] }
  have hs : step code input s = some (Transition.next t) := by
    unfold step; rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next t) else none) = _
    rw [ite_eq_left hn]
  refine ⟨t, hs, rfl, rfl, ?_, ?_⟩
  · change (s.regs.set dst.val w hd)[dst.val]'_ = w; simp
  · intro r hr
    have hv : r.val ≠ dst.val := fun e => hr (Fin.ext e)
    change (s.regs.set dst.val w hd)[r.val]'_ = s.regs[r.val]'_
    simp [Array.getElem_set, Ne.symm hv]

private theorem step_loadInput_next {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {dst addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput dst addr))
    (hread : input.words[(reg s addr).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    ∃ t : State (layout bits inputCap workCap hi hw), step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ t.data = s.data ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  have hd : dst.val < s.regs.size := by simpa only [s.regs_size] using dst.isLt
  let t : State (layout bits inputCap workCap hi hw) :=
    { s with regs := s.regs.set dst.val w hd, pc := s.pc + 1,
             regs_size := by simp only [Array.size_set, s.regs_size] }
  have hs : step code input s = some (Transition.next t) := by
    have h1 : step code input s =
        (input.words[(reg s addr).val]? >>= fun v =>
          if s.pc + 1 < code.size then some (Transition.next
            { s with regs := s.regs.set dst.val v hd, pc := s.pc + 1,
                     regs_size := by simp only [Array.size_set, s.regs_size] })
          else none) := by
      unfold step; rw [hf]; rfl
    rw [h1, hread]
    change (if s.pc + 1 < code.size then some (Transition.next t) else none) = _
    rw [ite_eq_left hn]
  refine ⟨t, hs, rfl, rfl, ?_, ?_⟩
  · change (s.regs.set dst.val w hd)[dst.val]'_ = w; simp
  · intro r hr
    have hv : r.val ≠ dst.val := fun e => hr (Fin.ext e)
    change (s.regs.set dst.val w hd)[r.val]'_ = s.regs[r.val]'_
    simp [Array.getElem_set, Ne.symm hv]

private def dispatchHeader (smallLen : Nat) (h3 : 3 < 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  #[Instr.imm 0 (zero bits),
    Instr.loadInput 1 0,
    Instr.imm 2 ⟨3, h3⟩,
    Instr.branchLt 1 2 4 (4 + smallLen)]

private def dispatchProgram (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  dispatchHeader (hi := hi) (hw := hw) small.size h3 ++ small.map (relocateInstr 4) ++
    large.map (relocateInstr (4 + small.size))

private theorem relocated_small (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) :
    RelocatedSlice small (dispatchProgram small large h3) 4 := by
  intro i op hop
  have hiLt : i < small.size := by
    by_cases h : i < small.size
    · exact h
    · simp [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hop
  unfold dispatchProgram
  rw [Array.getElem?_append_left (by simp [dispatchHeader, Array.size_append, Array.size_map]; omega)]
  rw [Array.getElem?_append_right (by simp [dispatchHeader])]
  have h4 : (dispatchHeader (hi := hi) (hw := hw) small.size h3).size = 4 := rfl
  rw [h4, Nat.add_sub_cancel_left, Array.getElem?_map, hop]
  rfl

private theorem relocated_large (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) :
    RelocatedSlice large (dispatchProgram small large h3) (4 + small.size) := by
  intro i op hop
  have hSize : (dispatchHeader (hi := hi) (hw := hw) small.size h3 ++
      small.map (relocateInstr 4)).size = 4 + small.size := by
    simp [dispatchHeader, Array.size_append, Array.size_map]
  unfold dispatchProgram
  rw [Array.getElem?_append_right (by omega), hSize, Nat.add_sub_cancel_left,
    Array.getElem?_map, hop]
  rfl

private theorem run_relocated_branch
    {sub code : Program (layout bits inputCap workCap hi hw)} {offset : Nat}
    (placed : RelocatedSlice sub code offset)
    {input : Input (layout bits inputCap workCap hi hw)}
    {s₀ sStart u : State (layout bits inputCap workCap hi hw)} {prefixSteps wSub : Nat}
    (hPrefix : Steps code input prefixSteps s₀ (relocateStatePC offset (Phase.initial sStart)))
    (hSub : run sub input wSub (Phase.initial sStart) = some ⟨u, wSub⟩) :
    ∃ v trace, v.data = u.data ∧
      run code input (prefixSteps + wSub) s₀ = some ⟨v, prefixSteps + wSub⟩ ∧
      SuccessfulTrace code input s₀ trace ⟨v, prefixSteps + wSub⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨k, atHalt, route, halt, cost⟩ := run_has_steps_then_halt hSub
  have routeRel := route.relocate placed
  obtain ⟨fetch, stateEq⟩ := halted_fetch_and_state halt
  have stop : step code input (relocateStatePC offset atHalt) =
      some (.halted (relocateStatePC offset u)) := by
    change u = atHalt at stateEq
    rw [stateEq]
    exact step_halt_at (s := relocateStatePC offset atHalt) (placed atHalt.pc .halt fetch)
  have exec := (hPrefix.append routeRel).halts stop
  change wSub = k + 1 at cost
  rw [Nat.add_assoc, ← cost] at exec
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  exact ⟨relocateStatePC offset u, trace, rfl, exec, ok, by simpa only [footprint] using ok.peak_eq⟩

private theorem dispatch_step_lt (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) :
    ∀ {i : Nat} {op : Instr bits 15},
      (dispatchHeader (hi := hi) (hw := hw) small.size h3)[i]? = some op →
      (dispatchProgram small large h3)[i]? = some op := by
  intro i op hop
  have hiLt : i < 4 := by
    by_cases h : i < 4
    · exact h
    · have : (dispatchHeader (hi := hi) (hw := hw) small.size h3)[i]? = none :=
        Array.getElem?_eq_none (by simp [dispatchHeader]; omega)
      rw [this] at hop; cases hop
  unfold dispatchProgram
  rw [Array.getElem?_append_left (by simp [Array.size_append, dispatchHeader]; omega),
      Array.getElem?_append_left (by simp [dispatchHeader]; exact hiLt)]
  exact hop

private theorem dispatch_hdr_steps (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits)
    (input : Input (layout bits inputCap workCap hi hw)) {n : Nat} (hn : n < 2 ^ bits)
    (hHdrN : (input.words[0]?).map Fin.val = some n)
    (s₀ : State (layout bits inputCap workCap hi hw)) :
    ∃ s3 : State (layout bits inputCap workCap hi hw),
      Steps (dispatchProgram small large h3) input 3 (Phase.initial s₀) s3 ∧
      s3.pc = 3 ∧ s3.data = s₀.data ∧
      reg s3 1 = ⟨n, hn⟩ ∧ reg s3 2 = ⟨3, h3⟩ := by
  let code := dispatchProgram small large h3
  have hsz : 4 ≤ code.size := by
    simp [code, dispatchProgram, dispatchHeader, Array.size_append]
  let p0 : State (layout bits inputCap workCap hi hw) := Phase.initial s₀
  have pc0 : p0.pc = 0 := rfl
  have f0 : code[p0.pc]? = some (.imm 0 (zero bits)) := by
    rw [pc0]; exact dispatch_step_lt small large h3 (i := 0) rfl
  obtain ⟨s1, st01, pc1, d1, r0_1, _⟩ :=
    step_imm_next (code := code) (input := input) (s := p0) f0 (by omega)
  have r0val1 : (reg s1 0).val = 0 := congrArg Fin.val r0_1
  have hread0 : input.words[(reg s1 0).val]? = some ⟨n, hn⟩ := by
    rw [r0val1]
    cases hopt : input.words[0]? with
    | none => simp [hopt] at hHdrN
    | some v =>
      rw [hopt, Option.map_some] at hHdrN
      exact congrArg some (Fin.ext (Option.some.inj hHdrN))
  have f1 : code[s1.pc]? = some (.loadInput 1 0) := by
    rw [pc1, pc0]; exact dispatch_step_lt small large h3 (i := 1) rfl
  obtain ⟨s2, st12, pc2, d2, r1_2, _⟩ :=
    step_loadInput_next (code := code) (input := input) (s := s1) f1 hread0 (by omega)
  have f2 : code[s2.pc]? = some (.imm 2 ⟨3, h3⟩) := by
    rw [pc2, pc1, pc0]; exact dispatch_step_lt small large h3 (i := 2) rfl
  obtain ⟨s3, st23, pc3, d3, r2_3, keep3⟩ :=
    step_imm_next (code := code) (input := input) (s := s2) f2 (by omega)
  have r1_3 : reg s3 1 = ⟨n, hn⟩ :=
    (keep3 1 (show (1 : Fin 15) ≠ 2 by decide)).trans r1_2
  refine ⟨s3, Steps.cons st01 (Steps.cons st12 (Steps.cons st23 (Steps.zero s3))),
    by omega, ?_, r1_3, r2_3⟩
  rw [d3, d2, d1]; rfl

private theorem dispatch_run_small (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) (hSmallPos : 0 < small.size)
    (input : Input (layout bits inputCap workCap hi hw))
    {n : Nat} (hn : n < 3) (hnBits : n < 2 ^ bits)
    (hHdrN : (input.words[0]?).map Fin.val = some n)
    (s₀ : State (layout bits inputCap workCap hi hw))
    {P : State (layout bits inputCap workCap hi hw) → Nat → Prop}
    (hSmallRun : ∀ sStart : State (layout bits inputCap workCap hi hw),
      sStart.data = s₀.data →
      ∃ u wSmall, run small input wSmall (Phase.initial sStart) = some ⟨u, wSmall⟩ ∧ P u wSmall) :
    ∃ v trace wSmall,
      run (dispatchProgram small large h3) input (4 + wSmall) (Phase.initial s₀) =
        some ⟨v, 4 + wSmall⟩ ∧
      SuccessfulTrace (dispatchProgram small large h3) input (Phase.initial s₀) trace
        ⟨v, 4 + wSmall⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      (∃ u, v.data = u.data ∧ P u wSmall) := by
  let code := dispatchProgram small large h3
  obtain ⟨s3, st03, pc3, d3, r1_3, r2_3⟩ :=
    dispatch_hdr_steps small large h3 input hnBits hHdrN s₀
  have hsz : 4 + small.size ≤ code.size := by
    simp [code, dispatchProgram, dispatchHeader, Array.size_append, Array.size_map]
  have f3 : code[s3.pc]? = some (.branchLt 1 2 4 (4 + small.size)) := by
    rw [pc3]; exact dispatch_step_lt small large h3 (i := 3) rfl
  have hltb : ltb (reg s3 1) (reg s3 2) = true :=
    (ltb_eq_true _ _).mpr (by rw [r1_3, r2_3]; exact hn)
  have st34 : step code input s3 = some (Transition.next { s3 with pc := 4 }) := by
    simpa only [hltb, ite_true] using
      step_branchLt_at (input := input) f3 (by simp only [hltb, ite_true]; omega)
  have hPrefix : Steps code input 4 (Phase.initial s₀) (relocateStatePC 4 (Phase.initial s3)) := by
    have hRel : relocateStatePC 4 (Phase.initial s3) = { s3 with pc := 4 } := by
      simp [relocateStatePC, Phase.initial]
    rw [hRel]
    exact st03.append (Steps.cons st34 (Steps.zero _))
  obtain ⟨u, wSmall, hSub, hP⟩ := hSmallRun s3 d3
  obtain ⟨v, trace, hData, hExec, hTrace, hPeak⟩ :=
    run_relocated_branch (relocated_small small large h3) hPrefix hSub
  exact ⟨v, trace, wSmall, hExec, hTrace, hPeak, u, hData, hP⟩

private theorem dispatch_run_large (small large : Program (layout bits inputCap workCap hi hw))
    (h3 : 3 < 2 ^ bits) (hLargePos : 0 < large.size)
    (input : Input (layout bits inputCap workCap hi hw))
    {n : Nat} (hn : 3 ≤ n) (hnBits : n < 2 ^ bits)
    (hHdrN : (input.words[0]?).map Fin.val = some n)
    (s₀ : State (layout bits inputCap workCap hi hw))
    {P : State (layout bits inputCap workCap hi hw) → Nat → Prop}
    (hLargeRun : ∀ sStart : State (layout bits inputCap workCap hi hw),
      sStart.data = s₀.data →
      ∃ u wLarge, run large input wLarge (Phase.initial sStart) = some ⟨u, wLarge⟩ ∧ P u wLarge) :
    ∃ v trace wLarge,
      run (dispatchProgram small large h3) input (4 + wLarge) (Phase.initial s₀) =
        some ⟨v, 4 + wLarge⟩ ∧
      SuccessfulTrace (dispatchProgram small large h3) input (Phase.initial s₀) trace
        ⟨v, 4 + wLarge⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      (∃ u, v.data = u.data ∧ P u wLarge) := by
  let code := dispatchProgram small large h3
  obtain ⟨s3, st03, pc3, d3, r1_3, r2_3⟩ :=
    dispatch_hdr_steps small large h3 input hnBits hHdrN s₀
  have hsz : 4 + small.size + large.size ≤ code.size := by
    simp [code, dispatchProgram, dispatchHeader, Array.size_append, Array.size_map]
    omega
  have f3 : code[s3.pc]? = some (.branchLt 1 2 4 (4 + small.size)) := by
    rw [pc3]; exact dispatch_step_lt small large h3 (i := 3) rfl
  have hltb : ltb (reg s3 1) (reg s3 2) = false := by
    cases h : ltb (reg s3 1) (reg s3 2) with
    | false => rfl
    | true =>
      have := (ltb_eq_true _ _).mp h
      rw [r1_3, r2_3] at this
      simp at this
      omega
  have st34 : step code input s3 = some (Transition.next { s3 with pc := 4 + small.size }) := by
    simpa only [hltb, Bool.false_eq_true, ↓reduceIte] using
      step_branchLt_at (input := input) f3 (by rw [hltb]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  have hPrefix : Steps code input 4 (Phase.initial s₀)
      (relocateStatePC (4 + small.size) (Phase.initial s3)) := by
    have hRel : relocateStatePC (4 + small.size) (Phase.initial s3) =
        { s3 with pc := 4 + small.size } := by
      simp [relocateStatePC, Phase.initial]
    rw [hRel]
    exact st03.append (Steps.cons st34 (Steps.zero _))
  obtain ⟨u, wLarge, hSub, hP⟩ := hLargeRun s3 d3
  obtain ⟨v, trace, hData, hExec, hTrace, hPeak⟩ :=
    run_relocated_branch (relocated_large small large h3) hPrefix hSub
  exact ⟨v, trace, wLarge, hExec, hTrace, hPeak, u, hData, hP⟩

private noncomputable def liftStage2Output
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

/-- Linked front phase (`stage1Phase` -> `dictSortPhase` -> `sweepPhase`) for `3 ≤ n_H`. -/
def largeFrontPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h8 : 8 ≤ 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  (stage1Phase (hi := hi) (hw := hw) (by omega)).link
    ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8))

/-- Linked large-quotient build program (`largeFrontPhase` + `fullPackedFinishProgram`). -/
def largeBuildProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h8 : 8 ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  let front := largeFrontPhase hi hw h8
  join front.code (fullPackedFinishProgram (hi := hi) (hw := hw)) front.haltPC front.haltFits

private theorem largeBuildProgram_nonempty (hi : inputCap ≤ 2 ^ bits)
    (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    0 < (largeBuildProgram hi hw h8).size := by
  unfold largeBuildProgram join
  rw [Array.size_append, Array.size_set, Array.size_map]
  have hp := fullPackedFinishProgram_nonempty (hi := hi) (hw := hw)
  omega

private theorem rawPhaseEq_link {bits c₁ d₁ c₂ d₂ : Nat}
    {h₁ : c₁ ≤ 2 ^ bits} {k₁ : d₁ ≤ 2 ^ bits}
    {h₂ : c₂ ≤ 2 ^ bits} {k₂ : d₂ ≤ 2 ^ bits}
    {p₁ q₁ : Phase (layout bits c₁ d₁ h₁ k₁)}
    {p₂ q₂ : Phase (layout bits c₂ d₂ h₂ k₂)}
    (hp : p₁.code = p₂.code ∧ p₁.haltPC = p₂.haltPC)
    (hq : q₁.code = q₂.code ∧ q₁.haltPC = q₂.haltPC) :
    (p₁.link q₁).code = (p₂.link q₂).code ∧
    (p₁.link q₁).haltPC = (p₂.link q₂).haltPC := by
  refine ⟨?_, ?_⟩
  · simp only [Phase.link, join, hp.1, hp.2, hq.1]
  · simp only [Phase.link, hp.1, hq.2]

theorem largeBuildProgram_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    largeBuildProgram (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ h8 =
      largeBuildProgram (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ h8 := by
  have hStage1 :
      (stage1Phase (bits := bits) (hi := h₁) (hw := k₁) (by omega)).code =
        (stage1Phase (bits := bits) (hi := h₂) (hw := k₂) (by omega)).code ∧
      (stage1Phase (bits := bits) (hi := h₁) (hw := k₁) (by omega)).haltPC =
        (stage1Phase (bits := bits) (hi := h₂) (hw := k₂) (by omega)).haltPC := by
    unfold stage1Phase
    exact rawPhaseEq_link
      (kahnStagePhase_cap_indep h₁ k₁ h₂ k₂ (by omega) (by omega))
      (stage1BPhase_cap_indep h₁ k₁ h₂ k₂ (by omega) (by omega))
  have hDict :
      (dictSortPhase (bits := bits) h₁ k₁ h8).code = (dictSortPhase (bits := bits) h₂ k₂ h8).code ∧
      (dictSortPhase (bits := bits) h₁ k₁ h8).haltPC = (dictSortPhase (bits := bits) h₂ k₂ h8).haltPC := by
    unfold dictSortPhase
    exact rawPhaseEq_link ⟨rfl, rfl⟩ (rawPhaseEq_link ⟨rfl, rfl⟩ ⟨rfl, rfl⟩)
  have hSweep :
      (sweepPhase (bits := bits) h₁ k₁ h8).code = (sweepPhase (bits := bits) h₂ k₂ h8).code ∧
      (sweepPhase (bits := bits) h₁ k₁ h8).haltPC = (sweepPhase (bits := bits) h₂ k₂ h8).haltPC := by
    unfold sweepPhase
    exact rawPhaseEq_link ⟨rfl, rfl⟩ (rawPhaseEq_link ⟨rfl, rfl⟩ ⟨rfl, rfl⟩)
  have hFront := rawPhaseEq_link hStage1 (rawPhaseEq_link hDict hSweep)
  have hFin := fullPackedFinishProgram_cap_indep h₁ k₁ h₂ k₂
  unfold largeBuildProgram largeFrontPhase
  dsimp only
  simp only [join, hFront.1, hFront.2, hFin]

/-- Single fixed word-RAM build program for all flat acyclic quotients,
dispatching at runtime on `n_H < 3` (`smallBuildCode`) vs `3 ≤ n_H` (`largeBuildProgram`). -/
def rawForestBuildProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h8 : 8 ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  dispatchProgram (smallBuildCode hi hw (by omega)) (largeBuildProgram hi hw h8) (by omega)

private theorem raw_combined_work_bound (n m w1 w2a w2bc w3 : Nat) (hn : 1 ≤ n)
    (h1 : w1 ≤ stage1WorkFactor * (n + m + 1))
    (h2a : w2a ≤ 120 * (n + 1) * OracleContract.L n)
    (h2bc : w2bc ≤ 5200 * ((n + m + 1) * (OracleContract.L n) ^ 2))
    (h3 : w3 ≤ 232 * n + 159) :
    4 + (w1 + (w2a + w2bc) + w3) ≤ 11662 * ((n + m) * (OracleContract.L n) ^ 2) := by
  have hL : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hL2 : 1 ≤ (OracleContract.L n) ^ 2 := Nat.pow_pos hL
  have hL_le : OracleContract.L n ≤ (OracleContract.L n) ^ 2 := by
    simpa only [Nat.pow_two] using Nat.le_mul_of_pos_right (OracleContract.L n) hL
  let LSq := (OracleContract.L n) ^ 2
  let B := (n + m + 1) * LSq
  have hB : 1 ≤ B := Nat.mul_pos (by omega) hL2
  have hw1 : w1 ≤ 275 * B :=
    Nat.le_trans h1 (Nat.mul_le_mul_left 275 (Nat.le_mul_of_pos_right _ hL2))
  have hw2a : w2a ≤ 120 * B := by
    calc w2a ≤ 120 * (n + 1) * OracleContract.L n := h2a
      _ ≤ 120 * (n + m + 1) * LSq :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 120 (by omega)) hL_le
      _ = 120 * B := Nat.mul_assoc _ _ _
  have hw2bc : w2bc ≤ 5200 * B := h2bc
  have hw3 : w3 ≤ 232 * B :=
    Nat.le_trans (by omega : w3 ≤ 232 * (n + m + 1))
      (Nat.mul_le_mul_left 232 (Nat.le_mul_of_pos_right _ hL2))
  have h4 : 4 ≤ 4 * B := Nat.le_mul_of_pos_right 4 hB
  have hsum : 4 + (w1 + (w2a + w2bc) + w3) ≤ 5831 * B := by omega
  have hnm : n + m + 1 ≤ 2 * (n + m) := by omega
  calc 4 + (w1 + (w2a + w2bc) + w3)
      ≤ 5831 * B := hsum
    _ ≤ 5831 * ((2 * (n + m)) * LSq) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnm)
    _ = 11662 * ((n + m) * LSq) := by
      rw [Nat.mul_assoc 2 (n + m) LSq, ← Nat.mul_assoc 5831 2 ((n + m) * LSq)]

/-- Execute the single fixed program `rawForestBuildProgram` from ANY raw quotient
input buffer `input` satisfying `RawQuotientInput input H`, arbitrary sufficient
work capacity `rawWorkCap n_H m_H ≤ workCap`, and arbitrary initial state `s₀`. -/
theorem run_raw_forest_build (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat) (acyc : H.IsAcyclic)
    (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s₀ : State (layout bits inputCap workCap hi hw)) :
    let code := rawForestBuildProgram hi hw h8
    let L := OracleContract.L H.vertexCount
    ∃ (w : WordColumns bits) (t : State (layout bits inputCap workCap hi hw))
      (trace : List (State (layout bits inputCap workCap hi hw))) (work : Nat),
      w.wordCount ≤ workCap ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      w.wordCount ≤ 19 * H.vertexCount ∧
      SerializedProperLossIndex H w ∧
      run code input work (Phase.initial s₀) = some ⟨t, work⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) trace ⟨t, work⟩ := by
  intro code L
  have hpos : 1 ≤ H.vertexCount := Fin.pos H.root
  have hnBits : H.vertexCount < 2 ^ bits := by omega
  by_cases hsmall : H.vertexCount < 3
  · have h4 : 4 < 2 ^ bits := by omega
    have hbitsN : 4 + H.vertexCount < 2 ^ bits := by omega
    have hworkSmall : 5 + H.vertexCount ≤ workCap := by
      unfold rawWorkCap at hWork; omega
    let h1 : 1 < 2 ^ bits := by omega
    let w := smallWordColumns H bits h1
    obtain ⟨v, trace, wSmall, hExec, hTrace, hPeak, u, hData, hwEq, hSmallOut⟩ :=
      dispatch_run_small (smallBuildCode hi hw (by omega)) (largeBuildProgram hi hw h8) (by omega)
        (by unfold smallBuildCode; simp)
        input hsmall hnBits hRaw.hdr_n s₀
        (P := fun u wSmall =>
          wSmall = 25 + 4 * H.vertexCount ∧
          u.data.extract 0 w.wordCount = packedPayload w)
        (fun sStart _ => by
          obtain ⟨u, _, wSmall, hwEq, _, hExt, _, hRun, _, _⟩ :=
            run_small_build input H hRaw hsmall h4 hbitsN hworkSmall sStart
          exact ⟨u, wSmall, hRun, hwEq, hExt⟩)
    have hWorkBound : 4 + wSmall ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
      have hLPos : 1 ≤ L := OracleContract.one_le_L H.vertexCount
      have hMulPos : 1 ≤ (H.vertexCount + H.arcCount) * L ^ 2 :=
        Nat.mul_pos (by omega) (Nat.pow_pos hLPos)
      have h37 : 4 + wSmall ≤ 37 := by omega
      have h116 : 37 ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
        calc 37 ≤ 11662 * 1 := by decide
          _ ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) :=
            Nat.mul_le_mul_left 11662 hMulPos
      omega
    have hwRet : w.wordCount ≤ 1 + 18 * H.vertexCount :=
      smallWordColumns_wordCount_le H bits h1
    have hwRet19 : w.wordCount ≤ 19 * H.vertexCount := by omega
    have hwCap : w.wordCount ≤ workCap := by
      rw [smallWordColumns_wordCount]; exact hworkSmall
    refine ⟨w, v, trace, 4 + wSmall, hwCap, ?_, hWorkBound, hPeak, hwRet, hwRet19,
      smallWordColumns_isSerializedProperLossIndex H hsmall h1, hExec, hTrace⟩
    rw [hData]; exact hSmallOut
  · have hlarge : 3 ≤ H.vertexCount := by omega
    obtain ⟨v, trace, wLarge, hExec, hTrace, hPeak, u, hData,
        ⟨w, hwCap, hExt, hWorkLarge, hwRet, hIdx⟩⟩ :=
      dispatch_run_large (smallBuildCode hi hw (by omega)) (largeBuildProgram hi hw h8) (by omega)
        (largeBuildProgram_nonempty hi hw h8) input hlarge hnBits hRaw.hdr_n s₀
        (P := fun u wLarge =>
          ∃ w : WordColumns bits,
            w.wordCount ≤ workCap ∧
            u.data.extract 0 w.wordCount = packedPayload w ∧
            wLarge ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) - 4 ∧
            w.wordCount ≤ 1 + 18 * H.vertexCount ∧
            SerializedProperLossIndex H w)
        (fun sStart _ => by
          obtain ⟨t1, _, w1, order, size_order, rank, rows, hw1, hRun1, _, _, hSt1⟩ :=
            run_stage1 input hRaw acyc hWork sStart
          have hRun1' :
              run (stage1Phase (hi := hi) (hw := hw) (by omega)).code input w1
                (Phase.initial sStart) = some ⟨t1, w1⟩ := hRun1
          obtain ⟨t2, _, w2a, hw2a, hRun2a, _, _, dso⟩ :=
            run_dict_sort h8 H input hRaw hWork t1 hSt1
          let r : PaperB.OrderedReaderResult rows order size_order rank hlarge :=
            runOrderedReaderFast rows order size_order rank hlarge
              dso.stage1.rank_increasing dso.stage1.covers dso.stage1.rank_arc flat
          obtain ⟨t3, _, w2bc, hw2bc, hRun2bc, _, _, ⟨out3⟩⟩ :=
            run_sweep h8 H input hRaw hWork rows hlarge dso r hWidth
          have hSweepPos : 0 < (sweepPhase hi hw h8).code.size := by
            have := (sweepPhase hi hw h8).haltFits; omega
          obtain ⟨t23, _, hR23, hD23, hRun23, _, _⟩ :=
            run_linked_pair (dictSortPhase hi hw h8) (sweepPhase hi hw h8).code
              hSweepPos hRun2a hRun2bc
          have hDSPos : 0 < ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).code.size := by
            have := ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).haltFits; omega
          obtain ⟨t123, _, hR123, hD123, hRun123, _, _⟩ :=
            run_linked_pair (stage1Phase (hi := hi) (hw := hw) (by omega))
              ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).code
              hDSPos hRun1' hRun23
          have hStage2 : Nonempty (Stage2Output H r hWidth t123) :=
            ⟨liftStage2Output (hR123.trans hR23) (hD123.trans hD23) out3⟩
          obtain ⟨t4, _, w3, hwCap, hExt, hw3, hwRet, hIdx, hRunAll, _, _⟩ :=
            run_linked_stage2_finish (largeFrontPhase hi hw h8) input r hWidth hRun123 hStage2
          have hComb := raw_combined_work_bound H.vertexCount H.arcCount w1 w2a w2bc w3
            hpos hw1 hw2a hw2bc hw3
          have hSub : (w1 + (w2a + w2bc)) + w3 ≤
              11662 * ((H.vertexCount + H.arcCount) * (OracleContract.L H.vertexCount) ^ 2) - 4 := by
            omega
          exact ⟨t4, (w1 + (w2a + w2bc)) + w3, hRunAll, packWordColumns r hWidth,
            hwCap, hExt, by dsimp only [L]; exact hSub, hwRet, hIdx⟩)
    have hWorkBound : 4 + wLarge ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
      have hLPos : 1 ≤ L := OracleContract.one_le_L H.vertexCount
      have hMulPos : 1 ≤ (H.vertexCount + H.arcCount) * L ^ 2 :=
        Nat.mul_pos (by omega) (Nat.pow_pos hLPos)
      have h4le : 4 ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
        calc 4 ≤ 11662 * 1 := by decide
          _ ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) :=
            Nat.mul_le_mul_left 11662 hMulPos
      omega
    have hwRet19 : w.wordCount ≤ 19 * H.vertexCount := by omega
    refine ⟨w, v, trace, 4 + wLarge, hwCap, ?_, hWorkBound, hPeak, hwRet, hwRet19,
      hIdx, hExec, hTrace⟩
    rw [hData]; exact hExt

end DispatchAndBuild

end PaperB.RamForestProgram.RawBuild

namespace PaperB

open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.RawBuild
open PaperB.RetainedProperLoss
open PaperB.ForestHead (Vertex)

/-- **Lemma 3.2 (constructing the forest, Paper B v1.3)**:
On any flat acyclic quotient `H` with `n_H` vertices and `m_H` labelled arcs,
the single fixed word-RAM program `rawForestBuildProgram` runs on
`rawInputOfQuotient H` at word width `bits := OracleContract.wordBits 5 n_H m_H`:
- halts in `O((n_H + m_H) L^2)` RAM steps (`≤ 11662 * ((n_H + m_H) * L^2)`),
- uses `O(n_H + m_H)` peak live words (`inputCap + workCap + 15 ≤ 70 * (n_H + m_H)`),
- emits exact serialized banks `t.data[0 .. w.wordCount) = packedPayload w` using
  `O(n_H)` retained words (`w.wordCount ≤ 1 + 18 * n_H ≤ 19 * n_H`),
- supports `O(L)` keyed pair lookup (including canonical unordered `CutPair H`
  lookup exact iff `H.ProperLoss q v`) and `O(1)` (`4` accesses) known-node
  proper-loss membership (`SerializedProperLossIndex H w`). -/
theorem build_proper_loss_forest (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat) (acyc : H.IsAcyclic) :
    let bits := OracleContract.wordBits 5 H.vertexCount H.arcCount
    let inCap := rawInputCap H.arcCount
    let wCap := rawWorkCap H.vertexCount H.arcCount
    have hi : inCap ≤ 2 ^ bits := (rawWordBits_fit H.vertexCount H.arcCount).1
    have hw : wCap ≤ 2 ^ bits := (rawWordBits_fit H.vertexCount H.arcCount).2.1
    have h8 : 8 ≤ 2 ^ bits := Nat.le_trans (by decide) (pow_two_ge_of_wordBits H)
    let code := rawForestBuildProgram (hi := hi) (hw := hw) h8
    let input := rawInputOfQuotient H
    let L := OracleContract.L H.vertexCount
    RawQuotientInput input H ∧
    ∀ s₀ : State (layout bits inCap wCap hi hw),
      ∃ (w : WordColumns bits) (t : State (layout bits inCap wCap hi hw))
        (trace : List (State (layout bits inCap wCap hi hw))) (work : Nat),
        w.wordCount ≤ wCap ∧
        t.data.extract 0 w.wordCount = packedPayload w ∧
        work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) ∧
        tracePeakWords input trace = inCap + wCap + 15 ∧
        tracePeakWords input trace ≤ 70 * (H.vertexCount + H.arcCount) ∧
        w.wordCount ≤ 1 + 18 * H.vertexCount ∧
        w.wordCount ≤ 19 * H.vertexCount ∧
        ∃ idx : SerializedProperLossIndex H w,
          (∀ (q : CutPair H) (v : Vertex H),
            let qc := q.canonical
            let x : Word bits := ⟨qc.fst.val, Nat.lt_of_lt_of_le qc.fst.isLt (by
              have := (rawWordBits_fit H.vertexCount H.arcCount).2.2
              change H.vertexCount ≤ 2 ^ OracleContract.wordBits 5 H.vertexCount H.arcCount
              omega)⟩
            let y : Word bits := ⟨qc.snd.val, Nat.lt_of_lt_of_le qc.snd.isLt (by
              have := (rawWordBits_fit H.vertexCount H.arcCount).2.2
              change H.vertexCount ≤ 2 ^ OracleContract.wordBits 5 H.vertexCount H.arcCount
              omega)⟩
            ∃ answer steps probes,
              w.keyedProbed idx.dict_valid
                (by omega : 1 < 2 ^ bits) (33 * L + 39) x y v.val = some (answer, steps, probes) ∧
              (answer = true ↔ H.ProperLoss q v) ∧
              steps ≤ 33 * L + 39 ∧ probes ≤ 9) ∧
          run code input work (Phase.initial s₀) = some ⟨t, work⟩ ∧
          SuccessfulTrace code input (Phase.initial s₀) trace ⟨t, work⟩ := by
  intro bits inCap wCap hi hw h8 code input L
  have hRaw := rawInputOfQuotient_spec H
  refine ⟨hRaw, ?_⟩
  intro s₀
  have hpos : 1 ≤ H.vertexCount := Fin.pos H.root
  have hWidth : 1 + 18 * H.vertexCount < 2 ^ bits :=
    (rawWordBits_fit H.vertexCount H.arcCount).2.2
  have hV : H.vertexCount ≤ 2 ^ bits := by omega
  have h1 : 1 < 2 ^ bits := by omega
  obtain ⟨w, t, trace, work, hwCap, hExt, hWork, hPeak, hwRet, hwRet19, hIdx, hExec, hTrace⟩ :=
    run_raw_forest_build h8 H flat acyc input hRaw (Nat.le_refl _) hWidth s₀
  have hPeakLinear : tracePeakWords input trace ≤ 70 * (H.vertexCount + H.arcCount) := by
    rw [hPeak]
    change rawInputCap H.arcCount + rawWorkCap H.vertexCount H.arcCount + 15 ≤
      70 * (H.vertexCount + H.arcCount)
    unfold rawInputCap rawWorkCap
    omega
  refine ⟨w, t, trace, work, hwCap, hExt, hWork, hPeak, hPeakLinear, hwRet, hwRet19, hIdx, ?_,
    hExec, hTrace⟩
  intro q v
  exact serialized_canonical_keyedProbed_iff hIdx h1 hV q v

/-- Paper B v1.2 cubic corollary of `build_proper_loss_forest`: the same
single-run program satisfies the weaker `O((n_H + m_H) L^3)` work bound. -/
theorem build_proper_loss_forest_v12_cubic (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat) (acyc : H.IsAcyclic) :
    let bits := OracleContract.wordBits 5 H.vertexCount H.arcCount
    let inCap := rawInputCap H.arcCount
    let wCap := rawWorkCap H.vertexCount H.arcCount
    have hi : inCap ≤ 2 ^ bits := (rawWordBits_fit H.vertexCount H.arcCount).1
    have hw : wCap ≤ 2 ^ bits := (rawWordBits_fit H.vertexCount H.arcCount).2.1
    have h8 : 8 ≤ 2 ^ bits := Nat.le_trans (by decide) (pow_two_ge_of_wordBits H)
    let code := rawForestBuildProgram (hi := hi) (hw := hw) h8
    let input := rawInputOfQuotient H
    let L := OracleContract.L H.vertexCount
    ∀ s₀ : State (layout bits inCap wCap hi hw),
      ∃ (w : WordColumns bits) (t : State (layout bits inCap wCap hi hw))
        (trace : List (State (layout bits inCap wCap hi hw))) (work : Nat),
        w.wordCount ≤ wCap ∧
        t.data.extract 0 w.wordCount = packedPayload w ∧
        work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 3) ∧
        tracePeakWords input trace ≤ 70 * (H.vertexCount + H.arcCount) ∧
        w.wordCount ≤ 19 * H.vertexCount ∧
        SerializedProperLossIndex H w ∧
        run code input work (Phase.initial s₀) = some ⟨t, work⟩ ∧
        SuccessfulTrace code input (Phase.initial s₀) trace ⟨t, work⟩ := by
  intro bits inCap wCap hi hw h8 code input L s₀
  obtain ⟨_, hBuild⟩ := build_proper_loss_forest H flat acyc
  obtain ⟨w, t, trace, work, hwCap, hExt, hWork, _, hPeakLinear, _, hwRet19, hIdx, _,
    hExec, hTrace⟩ := hBuild s₀
  have hL : 1 ≤ L := OracleContract.one_le_L H.vertexCount
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by decide)
  have hWork3 : work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 3) :=
    Nat.le_trans hWork (Nat.mul_le_mul_left 11662 (Nat.mul_le_mul_left _ hL23))
  exact ⟨w, t, trace, work, hwCap, hExt, hWork3, hPeakLinear, hwRet19, hIdx, hExec, hTrace⟩

end PaperB
