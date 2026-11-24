module

public import PaperB.RamDomBuild
public import PaperB.RamForestPhaseLink
public import PaperB.RamForestDegreeInit
public import PaperB.RamForestHistogram
public import PaperB.RamForestCsrOffsets
public import PaperB.RamForestScatter
public import PaperB.RamForestWriteback
public import PaperB.StaticTreeReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 Phase B2 (Part 2): Full 15-register Word-RAM pipeline (`domAndStaticTreePhase` /
`domAndStaticTreeProgram`) linking `domBuildPhase` (`RamDomBuild`), `Finish` layout &
parent-CSR (`RamForestDegreeInit`/`Histogram`/`CsrOffsets`/`Scatter`/`Writeback`),
and linear `O(Q)` post-processing passes (`denseOfEntry`, `heavy`, `head`,
`childEntries`/`childStops`).

Reads `DenseIncomingSpec` from `input.words` and populates `data[0 .. 11 * Q)` (using
scratch up to `17 * Q ≤ workCap` words, compatible with `workCap ≤ 32 * (Q + 1)`):
- `[0 .. Q)`: `domParent` (`domParent[0] = 0`, `∀ 1 ≤ v < Q, domParent[v] < v`,
  exact `Digraph.IsImmediateDominator`)
- `[Q .. 2 * Q)`: `domDepth` (`ValidDepthTree ⟨0, _⟩ domParent domDepth`)
- `[2 * Q .. 3 * Q)`: `heavy` (`Q` if leaf, else heavy child maximizing `stop - entry`)
- `[3 * Q .. 4 * Q)`: `head` (`head[0] = 0`, `head[v] = if heavy[p] = v then head[p] else v`)
- `[4 * Q .. 5 * Q)`: `entry` (preorder entry time in `0 .. Q - 1`)
- `[5 * Q .. 6 * Q)`: `stop` (exclusive subtree end in `entry[v] < stop[v] ≤ Q`)
- `[6 * Q .. 7 * Q)`: `denseOfEntry` (`denseOfEntry[entry[v]] = v`)
- `[7 * Q .. 8 * Q + 1)`: `childStart` (`childStart[0] = 0`, `childStart[Q] = Q - 1`, monotone)
- `[8 * Q + 1 .. 9 * Q)`: `childEntries` (`entry[childIds[i]]`, strictly increasing per bucket)
- `[9 * Q + 1 .. 10 * Q)`: `childStops` (`stop[childIds[i]]`)
- `[10 * Q + 1 .. 11 * Q)`: `childIds` (`Q - 1` child IDs)

Complexity: `O((Q + mReach) * L^2)` steps (`work ≤ 1050 * (Q + mReach) * (OracleContract.L Q) ^ 2`),
peak words `inputCap + workCap + 15`.
-/

namespace PaperB.RamDomAndStaticTree

open PaperB
open PaperB.Digraph
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamDomBuild
open PaperB.LabelledQuotient
open PaperB.ForestLayout

section Helpers

private theorem fin_ne_of_val {n : Nat} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun e => h (congrArg Fin.val e)

private theorem reg_eq_of_regs_eq {bits : Nat} {L : Layout bits} {s₁ s₂ : State L}
    (h : s₁.regs = s₂.regs) (r : Fin L.registerCount) : reg s₁ r = reg s₂ r := by
  change s₁.regs[r.val]'(by rw [s₁.regs_size]; exact r.isLt) =
    s₂.regs[r.val]'(by rw [s₂.regs_size]; exact r.isLt)
  simp only [h]

@[simp] private theorem phase_ofLast_code {bits : Nat} {L : Layout bits}
    (code : Program L) (hpc : Nat) (h1 h2 h3) :
    (Phase.ofLast code hpc h1 h2 h3).code = code := rfl

private theorem step_storeData_exists {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {a v : Fin L.registerCount}
    (hf : code[s.pc]? = some (.storeData a v))
    (hFit : (reg s a).val < s.data.size) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧
      t.data = s.data.set (reg s a).val (reg s v) hFit :=
  ⟨_, step_storeData_at (input := input) hf hFit hn⟩

@[simp] private theorem initial_data {bits : Nat} {L : Layout bits} (s : State L) :
    (Phase.initial s).data = s.data := rfl

@[simp] private theorem initial_reg {bits : Nat} {L : Layout bits} (s : State L)
    (r : Fin L.registerCount) : reg (Phase.initial s) r = reg s r := rfl

private theorem placed_append_left {bits : Nat} {L : Layout bits} {code : Program L}
    {base : Nat} {xs ys : List (Instr bits L.registerCount)}
    (h : Placed code base (xs ++ ys)) : Placed code base xs := by
  intro i ins hi
  rcases Nat.lt_or_ge i xs.length with hLen | hGe
  · have h1 : (xs ++ ys)[i]? = xs[i]? := List.getElem?_append_left hLen
    exact h i ins (h1.trans hi)
  · rw [List.getElem?_eq_none hGe] at hi
    cases hi

private theorem placed_append_right {bits : Nat} {L : Layout bits} {code : Program L}
    {base : Nat} {xs ys : List (Instr bits L.registerCount)}
    (h : Placed code base (xs ++ ys)) : Placed code (base + xs.length) ys := by
  intro i ins hi
  have h1 : (xs ++ ys)[xs.length + i]? = ys[i]? := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp
  have h2 := h (xs.length + i) ins (h1.trans hi)
  simpa only [Nat.add_assoc] using h2

private theorem placed_append_self_left {bits : Nat} {L : Layout bits}
    (xs ys : List (Instr bits L.registerCount)) :
    Placed (xs ++ ys).toArray 0 xs := by
  intro i op hiOp
  rcases Nat.lt_or_ge i xs.length with hLt | hGe
  · rw [Nat.zero_add, List.getElem?_toArray, List.getElem?_append_left hLt]; exact hiOp
  · rw [List.getElem?_eq_none hGe] at hiOp; cases hiOp

private theorem nonHalt_append {bits : Nat} {L : Layout bits}
    (xs ys : List (Instr bits L.registerCount))
    (hx : xs.all (nonHalt (L := L)) = true) (hy : ys.all (nonHalt (L := L)) = true) :
    (xs ++ ys).all (nonHalt (L := L)) = true := by
  rw [List.all_append, hx, hy]; rfl

private theorem nonHalt_replicate {bits : Nat} {L : Layout bits}
    (k : Nat) (ins : Instr bits L.registerCount)
    (h : nonHalt (L := L) ins = true) :
    (List.replicate k ins).all (nonHalt (L := L)) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.all_cons, h, Bool.true_and, ih]

private theorem list_take_exact_append_halt {α : Type} (xs : List α) (h : α) :
    List.take xs.length (xs ++ [h]) = xs := by
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

private theorem list_getElem?_append_last {α : Type} (xs : List α) (h : α) :
    (xs ++ [h])[xs.length]? = some h := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private def mulAddInstrs {bits : Nat} (dst countReg oneReg : Fin 15) (mul off : Nat) :
    List (Instr bits 15) :=
  [.imm dst ⟨0, Nat.one_le_two_pow⟩] ++
    List.replicate mul (.add dst dst countReg) ++
    List.replicate off (.add dst dst oneReg)

private theorem mulAddInstrs_length {bits : Nat} (dst countReg oneReg : Fin 15) (mul off : Nat) :
    (mulAddInstrs (bits := bits) dst countReg oneReg mul off).length = 1 + mul + off := by
  simp [mulAddInstrs]; omega

private theorem nonHalt_mulAddInstrs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (dst countReg oneReg : Fin 15) (mul off : Nat) :
    (mulAddInstrs (bits := bits) dst countReg oneReg mul off).all
      (nonHalt (L := layout bits inputCap workCap hi hw)) = true := by
  unfold mulAddInstrs
  apply nonHalt_append (L := layout bits inputCap workCap hi hw)
  · apply nonHalt_append (L := layout bits inputCap workCap hi hw)
    · rfl
    · exact nonHalt_replicate (L := layout bits inputCap workCap hi hw) _ _ rfl
  · exact nonHalt_replicate (L := layout bits inputCap workCap hi hw) _ _ rfl

private theorem add_rep_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (dst src : Fin 15) (hne : dst ≠ src) (stepVal : Nat) :
    ∀ (k basePc curVal : Nat) (s : State (layout bits inputCap workCap hi hw)),
      s.pc = basePc →
      basePc + k < code.size →
      Placed code basePc (List.replicate k (.add dst dst src)) →
      (reg s dst).val = curVal →
      (reg s src).val = stepVal →
      curVal + k * stepVal < 2 ^ bits →
      ∃ t : State (layout bits inputCap workCap hi hw),
        Steps code input k s t ∧
        t.pc = basePc + k ∧
        t.data = s.data ∧
        (reg t dst).val = curVal + k * stepVal ∧
        ∀ r, r ≠ dst → reg t r = reg s r := by
  intro k
  induction k with
  | zero =>
    intro basePc curVal s hpc _ _ hDst _ _
    exact ⟨s, .zero _, hpc, rfl, by rw [hDst, Nat.zero_mul, Nat.add_zero], fun _ _ => rfl⟩
  | succ k ih =>
    intro basePc curVal s hpc hSz hPl hDst hSrc hFit
    have hAt : code[s.pc]? = some (.add dst dst src) := by
      rw [hpc]
      exact hPl 0 _ (by simp [List.replicate_succ])
    have hNextFit : s.pc + 1 < code.size := by rw [hpc]; omega
    obtain ⟨s1, hs1, hpc1, hrd, hro, hd1⟩ := step_add_at (input := input) hAt hNextFit
    have hNoWrap : (reg s dst).val + (reg s src).val < 2 ^ bits := by
      rw [hDst, hSrc]
      have hMul : 1 * stepVal ≤ (k + 1) * stepVal :=
        Nat.mul_le_mul_right stepVal (Nat.succ_pos k)
      omega
    have hDst1 : (reg s1 dst).val = curVal + stepVal := by
      rw [hrd, add_no_wrap _ _ hNoWrap, hDst, hSrc]
    have hSrc1 : (reg s1 src).val = stepVal := by
      rw [hro src hne.symm, hSrc]
    have hPl1 : Placed code (basePc + 1) (List.replicate k (.add dst dst src)) := by
      intro i ins hi'
      simpa only [Nat.add_assoc] using hPl (1 + i) ins (by
        rw [← Nat.succ_eq_one_add, List.replicate_succ]
        exact hi')
    have hFit1 : (curVal + stepVal) + k * stepVal < 2 ^ bits := by
      rw [Nat.succ_mul] at hFit; omega
    obtain ⟨t, htSteps, htpc, htd, htDst, hto⟩ :=
      ih (basePc + 1) (curVal + stepVal) s1 (by rw [hpc1, hpc]) (by omega) hPl1 hDst1 hSrc1 hFit1
    refine ⟨t, Steps.cons hs1 htSteps, by omega, by rw [htd, hd1], ?_, ?_⟩
    · rw [htDst, Nat.succ_mul]; omega
    · intro r hr; rw [hto r hr, hro r hr]

private theorem run_mulAddInstrs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (dst countReg oneReg : Fin 15) (hneC : dst ≠ countReg) (hneO : dst ≠ oneReg)
    {mul off Q basePc : Nat} (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = basePc)
    (hSz : basePc + (1 + mul + off) < code.size)
    (hPl : Placed code basePc (mulAddInstrs dst countReg oneReg mul off))
    (hC : (reg s countReg).val = Q) (hO : (reg s oneReg).val = 1)
    (hFit : mul * Q + off < 2 ^ bits) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (1 + mul + off) s t ∧
      t.pc = basePc + (1 + mul + off) ∧
      t.data = s.data ∧
      (reg t dst).val = mul * Q + off ∧
      ∀ r, r ≠ dst → reg t r = reg s r := by
  have hAt0 : code[s.pc]? = some (.imm dst ⟨0, Nat.one_le_two_pow⟩) := by
    rw [hpc]
    have h0 : Placed code basePc [.imm dst ⟨0, Nat.one_le_two_pow⟩] :=
      placed_append_left (placed_append_left hPl)
    exact h0 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hrd1, hro1, hd1⟩ := step_imm_at (input := input) hAt0 (by rw [hpc]; omega)
  have hPl1 : Placed code (basePc + 1) (List.replicate mul (.add dst dst countReg)) := by
    have h12 := placed_append_left hPl
    simpa only [List.length_cons, List.length_nil] using placed_append_right h12
  have hPl2 : Placed code (basePc + 1 + mul) (List.replicate off (.add dst dst oneReg)) := by
    have h3 := placed_append_right hPl
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      Nat.zero_add] at h3
    rw [← Nat.add_assoc] at h3
    exact h3
  have hDst1 : (reg s1 dst).val = 0 := by rw [hrd1]
  have hC1 : (reg s1 countReg).val = Q := by rw [hro1 countReg hneC.symm, hC]
  have hO1 : (reg s1 oneReg).val = 1 := by rw [hro1 oneReg hneO.symm, hO]
  obtain ⟨s2, hs2, hpc2, hd2, hDst2, ho2⟩ :=
    add_rep_steps dst countReg hneC Q mul (basePc + 1) 0 s1 (by rw [hpc1, hpc]) (by omega) hPl1 hDst1 hC1
      (by omega)
  have hO2 : (reg s2 oneReg).val = 1 := by rw [ho2 oneReg hneO.symm, hO1]
  have hDst2' : (reg s2 dst).val = mul * Q := by rw [hDst2, Nat.zero_add]
  obtain ⟨t, hs3, hpc3, hd3, hDst3, ho3⟩ :=
    add_rep_steps dst oneReg hneO 1 off (basePc + 1 + mul) (mul * Q) s2 hpc2 (by omega) hPl2 hDst2' hO2
      (by simp only [Nat.mul_one]; exact hFit)
  refine ⟨t, ?_, by omega, by rw [hd3, hd2, hd1], ?_, ?_⟩
  · simpa only [Nat.add_assoc, show (mul + off).succ = 1 + mul + off by omega] using
      Steps.cons hs1 (hs2.append hs3)
  · rw [hDst3, Nat.mul_one]
  · intro r hr
    rw [ho3 r hr, ho2 r hr, hro1 r hr]

private def reloadQInstrs {bits : Nat} (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.zero ⟨0, by omega⟩
  , .imm registers.one ⟨1, by omega⟩
  , .loadInput count registers.zero
  ]

private def copySetupInstrs {bits : Nat} (srcMul srcOff dstMul dstOff lenMul lenOff lenSub : Nat) :
    List (Instr bits 15) :=
  mulAddInstrs tinBase count registers.one srcMul srcOff ++
  mulAddInstrs toutBase count registers.one dstMul dstOff ++
  mulAddInstrs registers.remain count registers.one lenMul lenOff ++
  List.replicate lenSub (.sub registers.remain registers.remain registers.one) ++
  [.imm clk ⟨0, Nat.one_le_two_pow⟩]

private theorem copySetupInstrs_length {bits : Nat}
    (srcMul srcOff dstMul dstOff lenMul lenOff lenSub : Nat) :
    (copySetupInstrs (bits := bits) srcMul srcOff dstMul dstOff lenMul lenOff lenSub).length =
      (1 + srcMul + srcOff) + (1 + dstMul + dstOff) + (1 + lenMul + lenOff) + lenSub + 1 := by
  simp [copySetupInstrs, mulAddInstrs_length, Nat.add_assoc]

private def copyLoopInstrs {bits : Nat} : List (Instr bits 15) :=
  [ .branchLt clk registers.remain 1 7
  , .add registers.tmp tinBase clk
  , .loadData registers.value registers.tmp
  , .add registers.tmp toutBase clk
  , .storeData registers.tmp registers.value
  , .add clk clk registers.one
  , .goto 0
  , .halt
  ]

private def setArenaCtrlInstrs {bits : Nat} (baseMul : Nat) : List (Instr bits 15) :=
  mulAddInstrs registers.stackBase count registers.one baseMul 0 ++
  mulAddInstrs tinBase count registers.one (baseMul + 2) 0 ++
  mulAddInstrs toutBase count registers.one (baseMul + 3) 0 ++
  mulAddInstrs offsetBase count registers.one (baseMul + 4) 0 ++
  mulAddInstrs childrenBase count registers.one (baseMul + 5) 1 ++
  [ .imm cmd ⟨0, Nat.one_le_two_pow⟩
  , .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩
  , .imm clk ⟨0, Nat.one_le_two_pow⟩
  ]

private theorem setArenaCtrlInstrs_length {bits : Nat} (baseMul : Nat) :
    (setArenaCtrlInstrs (bits := bits) baseMul).length =
      (1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)) + (1 + (baseMul + 4)) + (1 + (baseMul + 5) + 1) + 3 := by
  simp [setArenaCtrlInstrs, mulAddInstrs_length, Nat.add_assoc]

/-! ### Generic `PhasesExec` composition (no off-by-one `+1` accumulation) -/

inductive PhasesExec {bits : Nat} {L : Layout bits} (input : Input L) :
    List (Phase L) → State L → State L → Nat → Prop where
  | nil (s : State L) : PhasesExec input [] s s 0
  | cons {p : Phase L} {ps : List (Phase L)} {s t u : State L} {a b : Nat} :
      run p.code input a (Phase.initial s) = some ⟨t, a⟩ →
      PhasesExec input ps t u b →
      PhasesExec input (p :: ps) s u (a + b)

theorem PhasesExec.single {bits : Nat} {L : Layout bits} {input : Input L}
    (p : Phase L) {s t : State L} {w : Nat}
    (h : run p.code input w (Phase.initial s) = some ⟨t, w⟩) :
    PhasesExec input [p] s t w := by
  simpa only [Nat.add_zero] using PhasesExec.cons h (PhasesExec.nil t)

theorem PhasesExec.append {bits : Nat} {L : Layout bits} {input : Input L}
    {ps qs : List (Phase L)} {s t u : State L} {a b : Nat}
    (hp : PhasesExec input ps s t a) (hq : PhasesExec input qs t u b) :
    PhasesExec input (ps ++ qs) s u (a + b) := by
  induction hp with
  | nil => simpa only [Nat.zero_add, List.nil_append] using hq
  | cons hstep _ ih =>
    simpa only [List.cons_append, Nat.add_assoc] using PhasesExec.cons hstep (ih hq)

theorem PhasesExec.toPhasesRun {bits : Nat} {L : Layout bits} {input : Input L}
    {ps : List (Phase L)} {s t : State L} {w : Nat}
    (h : PhasesExec input ps s t w) :
    PhasesRun input ps s (Phase.initial t) (w + 1) := by
  induction h with
  | nil s => simpa only [Nat.zero_add] using @PhasesRun.nil bits L input s
  | cons hstep _ ih =>
    simpa only [Nat.add_assoc] using PhasesRun.cons hstep ih

end Helpers

section BasePhases

variable {bits : Nat} {inputCap : Nat} {workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

/-! ### Phase builders for `Finish` / `CSR`, `reloadQ`, `copySetup`, `copyLoop`, and `setArenaCtrl` -/

private def prepPhase : Phase DomL :=
  Phase.ofLast (prepareParentPhase hi hw) 3 rfl rfl rfl

private def clearPhase : Phase DomL :=
  Phase.ofLast (zeroDegreeProgram hi hw) 5 rfl rfl rfl

private def histogramPhase : Phase DomL :=
  Phase.ofLast (parentScanCode histogramBody) 13 rfl rfl rfl

private def offsetPhase : Phase DomL :=
  Phase.ofLast (offsetProgram hi hw) 10 rfl rfl rfl

private def scatterPhase : Phase DomL :=
  Phase.ofLast (parentScanCode scatterBody) 18 rfl rfl rfl

private def csrPhases : List (Phase DomL) :=
  [prepPhase, clearPhase, prepPhase, histogramPhase, prepPhase, offsetPhase, prepPhase, scatterPhase]

private def finishPhases : List (Phase DomL) :=
  csrPhases ++ [prepPhase, serializationPhase]

def reloadQPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) :=
    (reloadQInstrs hTen ++ [Instr.halt]).toArray
  Phase.ofLast code 3 rfl rfl rfl

theorem run_reloadQ {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    {input : Input DomL} (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    (hTen : 10 ≤ 2 ^ bits) (hQFit : Q < 2 ^ bits) (s : State DomL) :
    ∃ t : State DomL,
      run (reloadQPhase hi hw hTen).code input 4 (Phase.initial s) = some ⟨t, 4⟩ ∧
      t.data = s.data ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q := by
  let code := (reloadQPhase hi hw hTen).code
  let s0 := Phase.initial s
  have hSz : code.size = 4 := by dsimp [code, reloadQPhase, reloadQInstrs]; rfl
  have hpc0 : s0.pc = 0 := rfl
  have h0 : code[s0.pc]? = some (.imm registers.zero ⟨0, by omega⟩) := by
    rw [hpc0]; rfl
  obtain ⟨s1, hs1, hpc1, hz1, ho1, hd1⟩ :=
    step_imm_at (input := input) h0 (by rw [hSz, hpc0]; omega)
  have h1 : code[s1.pc]? = some (.imm registers.one ⟨1, by omega⟩) := by
    rw [hpc1, hpc0]; rfl
  obtain ⟨s2, hs2, hpc2, ho_val, ho2, hd2⟩ :=
    step_imm_at (input := input) h1 (by rw [hSz, hpc1, hpc0]; omega)
  have h2 : code[s2.pc]? = some (.loadInput count registers.zero) := by
    rw [hpc2, hpc1, hpc0]; rfl
  have hz2 : (reg s2 registers.zero).val = 0 := by
    rw [ho2 registers.zero (fin_ne_of_val (by decide))]; exact congrArg Fin.val hz1
  have hWord0 : input.words[(reg s2 registers.zero).val]? = some ⟨Q, hQFit⟩ := by
    rw [hz2]
    have hC := sp.word0
    cases hInp : input.words[0]? with
    | none => rw [hInp] at hC; cases hC
    | some w => rw [hInp, Option.map_some] at hC; congr 1; exact Fin.ext (Option.some.inj hC)
  obtain ⟨t, hs3, hpc3, htc, ho3, hdt⟩ :=
    step_loadInput_at (input := input) h2 (by rw [hSz, hpc2, hpc1, hpc0]; omega) hWord0
  have hHalt : step code input t = some (.halted t) := by
    apply step_halt_at; rw [hpc3, hpc2, hpc1, hpc0]; rfl
  have hSteps : Steps code input 3 s0 t := Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (.zero _)))
  refine ⟨t, hSteps.halts hHalt, by rw [hdt, hd2, hd1, initial_data], ?_, ?_, by rw [htc]⟩
  · rw [ho3 registers.zero (fin_ne_of_val (by decide))]; exact hz2
  · rw [ho3 registers.one (fin_ne_of_val (by decide)), ho_val]

/-! ### Generic range-copy setup & loop phases -/

private theorem nonHalt_copySetupInstrs (srcMul srcOff dstMul dstOff lenMul lenOff lenSub : Nat) :
    (copySetupInstrs (bits := bits) srcMul srcOff dstMul dstOff lenMul lenOff lenSub).all
      (nonHalt (L := DomL)) = true := by
  unfold copySetupInstrs
  apply nonHalt_append (L := DomL)
  · apply nonHalt_append (L := DomL)
    · apply nonHalt_append (L := DomL)
      · apply nonHalt_append (L := DomL)
        · exact nonHalt_mulAddInstrs _ _ _ _ _
        · exact nonHalt_mulAddInstrs _ _ _ _ _
      · exact nonHalt_mulAddInstrs _ _ _ _ _
    · exact nonHalt_replicate (L := DomL) _ _ rfl
  · rfl

def copySetupPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (srcMul srcOff dstMul dstOff lenMul lenOff lenSub : Nat) :
    Phase (layout bits inputCap workCap hi hw) :=
  let ins := copySetupInstrs (bits := bits) srcMul srcOff dstMul dstOff lenMul lenOff lenSub
  let code : Program (layout bits inputCap workCap hi hw) := (ins ++ [Instr.halt]).toArray
  Phase.ofLast code ins.length
    (by simp [code]) (by simp [code])
    (by
      have hTake : List.take ins.length code.toList = ins := by
        simp [code]
      rw [hTake]
      exact nonHalt_copySetupInstrs (hi := hi) (hw := hw) _ _ _ _ _ _ _)

private theorem sub_rep_steps {code : Program DomL} {input : Input DomL}
    (dst oneReg : Fin 15) (hne : dst ≠ oneReg) :
    ∀ (k basePc curVal : Nat) (s : State DomL),
      s.pc = basePc →
      basePc + k < code.size →
      Placed code basePc (List.replicate k (.sub dst dst oneReg)) →
      (reg s dst).val = curVal →
      (reg s oneReg).val = 1 →
      k ≤ curVal →
      ∃ t : State DomL,
        Steps code input k s t ∧
        t.pc = basePc + k ∧
        t.data = s.data ∧
        (reg t dst).val = curVal - k ∧
        ∀ r, r ≠ dst → reg t r = reg s r := by
  intro k
  induction k with
  | zero =>
    intro basePc curVal s hpc _ _ hDst _ _
    exact ⟨s, .zero _, hpc, rfl, by rw [hDst, Nat.sub_zero], fun _ _ => rfl⟩
  | succ k ih =>
    intro basePc curVal s hpc hSz hPl hDst hOne hLe
    have hAt : code[s.pc]? = some (.sub dst dst oneReg) := by
      rw [hpc]; exact hPl 0 _ (by simp [List.replicate_succ])
    obtain ⟨s1, hs1, hpc1, hrd, hro, hd1⟩ := step_sub_at (input := input) hAt (by rw [hpc]; omega)
    have hDst1 : (reg s1 dst).val = curVal - 1 := by
      rw [hrd, PaperB.RamDomBuild.sub_exact_word _ _ (by rw [hDst, hOne]; omega), hDst, hOne]
    have hOne1 : (reg s1 oneReg).val = 1 := by rw [hro oneReg hne.symm, hOne]
    have hPl1 : Placed code (basePc + 1) (List.replicate k (.sub dst dst oneReg)) := by
      intro i ins hi'
      simpa only [Nat.add_assoc] using hPl (1 + i) ins (by
        rw [← Nat.succ_eq_one_add, List.replicate_succ]; exact hi')
    obtain ⟨t, htSteps, htpc, htd, htDst, hto⟩ :=
      ih (basePc + 1) (curVal - 1) s1 (by rw [hpc1, hpc]) (by omega) hPl1 hDst1 hOne1 (by omega)
    refine ⟨t, Steps.cons hs1 htSteps, by omega, by rw [htd, hd1], ?_, ?_⟩
    · rw [htDst]; omega
    · intro r hr; rw [hto r hr, hro r hr]

theorem run_copySetup {input : Input DomL}
    (srcMul srcOff dstMul dstOff lenMul lenOff lenSub Q : Nat)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hSrcFit : srcMul * Q + srcOff < 2 ^ bits)
    (hDstFit : dstMul * Q + dstOff < 2 ^ bits)
    (hLenFit : lenMul * Q + lenOff < 2 ^ bits)
    (hSubLe : lenSub ≤ lenMul * Q + lenOff) :
    let p := copySetupPhase hi hw srcMul srcOff dstMul dstOff lenMul lenOff lenSub
    let w := (copySetupInstrs (bits := bits) srcMul srcOff dstMul dstOff lenMul lenOff lenSub).length + 1
    ∃ t : State DomL,
      run p.code input w (Phase.initial s) = some ⟨t, w⟩ ∧
      t.data = s.data ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (reg t tinBase).val = srcMul * Q + srcOff ∧
      (reg t toutBase).val = dstMul * Q + dstOff ∧
      (reg t registers.remain).val = (lenMul * Q + lenOff) - lenSub ∧
      (reg t clk).val = 0 := by
  intro p w
  let ins := copySetupInstrs (bits := bits) srcMul srcOff dstMul dstOff lenMul lenOff lenSub
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = ins.length + 1 := by simp [p, copySetupPhase, ins]
  have hPlAll : Placed p.code 0 ins := by
    intro i op hiOp
    simp only [p, copySetupPhase, phase_ofLast_code, Nat.zero_add]
    rcases Nat.lt_or_ge i ins.length with hiLt | hGe
    · rw [List.getElem?_toArray, List.getElem?_append_left hiLt]; exact hiOp
    · rw [List.getElem?_eq_none hGe] at hiOp; cases hiOp
  have hPl1 : Placed p.code 0 (mulAddInstrs tinBase count registers.one srcMul srcOff) :=
    placed_append_left (placed_append_left (placed_append_left (placed_append_left hPlAll)))
  have hL1 := mulAddInstrs_length (bits := bits) tinBase count registers.one srcMul srcOff
  have hPl2 : Placed p.code (1 + srcMul + srcOff)
      (mulAddInstrs toutBase count registers.one dstMul dstOff) := by
    have h := placed_append_right (placed_append_left (placed_append_left (placed_append_left hPlAll)))
    simpa only [Nat.zero_add, hL1] using h
  have hPl3 : Placed p.code ((1 + srcMul + srcOff) + (1 + dstMul + dstOff))
      (mulAddInstrs registers.remain count registers.one lenMul lenOff) := by
    have h := placed_append_right (placed_append_left (placed_append_left hPlAll))
    simp only [List.length_append, mulAddInstrs_length, Nat.zero_add] at h
    exact h
  have hPl4 : Placed p.code ((1 + srcMul + srcOff) + (1 + dstMul + dstOff) + (1 + lenMul + lenOff))
      (List.replicate lenSub (.sub registers.remain registers.remain registers.one)) := by
    have h := placed_append_right (placed_append_left hPlAll)
    simp only [List.length_append, mulAddInstrs_length, Nat.zero_add] at h
    exact h
  have hLastAt : p.code[((1 + srcMul + srcOff) + (1 + dstMul + dstOff) + (1 + lenMul + lenOff)) + lenSub]? =
      some (.imm clk ⟨0, Nat.one_le_two_pow⟩) := by
    have h := placed_append_right hPlAll
    simp only [List.length_append, mulAddInstrs_length, List.length_replicate, Nat.zero_add] at h
    exact h 0 _ rfl
  have hLenIns : ins.length = (1 + srcMul + srcOff) + (1 + dstMul + dstOff) + (1 + lenMul + lenOff) + lenSub + 1 :=
    copySetupInstrs_length _ _ _ _ _ _ _
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have ho0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, htin1, ho1⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz, hLenIns]; omega) hPl1 hc0 ho0 hSrcFit
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have ho1' : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), ho0]
  have hpc1' : s1.pc = 1 + srcMul + srcOff := by rw [hpc1, Nat.zero_add]
  obtain ⟨s2, hs2, hpc2, hd2, htout2, ho2⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 hpc1' (by rw [hSz, hLenIns]; omega) hPl2 hc1 ho1' hDstFit
  have hc2 : (reg s2 count).val = Q := by rw [ho2 count (fin_ne_of_val (by decide)), hc1]
  have ho2' : (reg s2 registers.one).val = 1 := by rw [ho2 registers.one (fin_ne_of_val (by decide)), ho1']
  have hpc2' : s2.pc = (1 + srcMul + srcOff) + (1 + dstMul + dstOff) := by rw [hpc2]
  obtain ⟨s3, hs3, hpc3, hd3, hrem3, ho3⟩ :=
    run_mulAddInstrs (input := input) registers.remain count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s2 hpc2' (by rw [hSz, hLenIns]; omega) hPl3 hc2 ho2' hLenFit
  have ho3' : (reg s3 registers.one).val = 1 := by rw [ho3 registers.one (fin_ne_of_val (by decide)), ho2']
  obtain ⟨s4, hs4, hpc4, hd4, hrem4, ho4⟩ :=
    sub_rep_steps (input := input) registers.remain registers.one (fin_ne_of_val (by decide))
      lenSub _ (lenMul * Q + lenOff) s3 hpc3 (by rw [hSz, hLenIns]; omega) hPl4 hrem3 ho3' hSubLe
  obtain ⟨t, hs5, hpc5, htclk, ho5, hdt⟩ :=
    step_imm_at (input := input) (by rw [hpc4]; exact hLastAt) (by rw [hpc4, hSz, hLenIns]; omega)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at
    rw [hpc5, hpc4]
    have hpLast := p.haltAt
    have hpPc : p.haltPC = ins.length := rfl
    rw [hpPc, hLenIns] at hpLast
    simpa only [Nat.add_assoc] using hpLast
  have hAllSteps : Steps p.code input ins.length s0 t := by
    rw [hLenIns]
    simpa only [Nat.add_assoc] using (hs1.append (hs2.append (hs3.append hs4))).append (Steps.cons hs5 (.zero _))
  refine ⟨t, by simpa only [w] using hAllSteps.halts hHalt, by rw [hdt, hd4, hd3, hd2, hd1, initial_data], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ho5 registers.zero (fin_ne_of_val (by decide)), ho4 registers.zero (fin_ne_of_val (by decide)),
        ho3 registers.zero (fin_ne_of_val (by decide)), ho2 registers.zero (fin_ne_of_val (by decide)),
        ho1 registers.zero (fin_ne_of_val (by decide)), initial_reg]; exact hz
  · rw [ho5 registers.one (fin_ne_of_val (by decide)), ho4 registers.one (fin_ne_of_val (by decide))]; exact ho3'
  · rw [ho5 count (fin_ne_of_val (by decide)), ho4 count (fin_ne_of_val (by decide)),
        ho3 count (fin_ne_of_val (by decide))]; exact hc2
  · rw [ho5 tinBase (fin_ne_of_val (by decide)), ho4 tinBase (fin_ne_of_val (by decide)),
        ho3 tinBase (fin_ne_of_val (by decide)), ho2 tinBase (fin_ne_of_val (by decide))]; exact htin1
  · rw [ho5 toutBase (fin_ne_of_val (by decide)), ho4 toutBase (fin_ne_of_val (by decide)),
        ho3 toutBase (fin_ne_of_val (by decide))]; exact htout2
  · rw [ho5 registers.remain (fin_ne_of_val (by decide))]; exact hrem4
  · rw [htclk]

def copyLoopPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) := (copyLoopInstrs (bits := bits)).toArray
  Phase.ofLast code 7 rfl rfl rfl

private theorem copyLoop_iter {input : Input DomL} {src dst len : Nat}
    (hSrcFit : src + len ≤ workCap) (hDstFit : dst + len ≤ workCap)
    (hDisj : src + len ≤ dst ∨ dst + len ≤ src) (hLenFit : len < 2 ^ bits) :
    ∀ (rem i : Nat) (s : State DomL),
      s.pc = 0 →
      len = i + rem →
      s.data.size = workCap →
      (reg s registers.zero).val = 0 →
      (reg s registers.one).val = 1 →
      (reg s tinBase).val = src →
      (reg s toutBase).val = dst →
      (reg s registers.remain).val = len →
      (reg s clk).val = i →
      ∃ t : State DomL,
        Steps (copyLoopPhase hi hw).code input (7 * rem + 1) s t ∧
        t.pc = 7 ∧
        t.data.size = workCap ∧
        (reg t registers.zero).val = 0 ∧
        (reg t registers.one).val = 1 ∧
        (∀ r, r ≠ clk → r ≠ registers.value → r ≠ registers.tmp → reg t r = reg s r) ∧
        (∀ k, i ≤ k → k < len → t.data[dst + k]? = s.data[src + k]?) ∧
        (∀ j, (j < dst + i ∨ dst + len ≤ j) → t.data[j]? = s.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro i s hpc hEq hSz hz ho hSrc hDst hRem hClk
    let code := (copyLoopPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt clk registers.remain 1 7) := by rw [hpc]; rfl
    have hFalse : ltb (reg s clk) (reg s registers.remain) = false := by
      cases hC : ltb (reg s clk) (reg s registers.remain) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hClk, hRem] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 1 else 7) < 8; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s clk) (reg s registers.remain) = true then 1 else 7 }
    refine ⟨t, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      hSz, hz, ho, fun _ _ _ _ => rfl, fun k hk1 hk2 => by omega, fun _ _ => rfl⟩
  | succ rem ih =>
    intro i s hpc hEq hSz hz ho hSrc hDst hRem hClk
    let code := (copyLoopPhase hi hw).code
    have hiLt : i < len := by omega
    have h0 : code[s.pc]? = some (.branchLt clk registers.remain 1 7) := by rw [hpc]; rfl
    have hTrue : ltb (reg s clk) (reg s registers.remain) = true :=
      (ltb_eq_true _ _).mpr (by rw [hClk, hRem]; exact hiLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 1 else 7) < 8; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s clk) (reg s registers.remain) = true then 1 else 7 }
    have hpc1 : s1.pc = 1 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp tinBase clk) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 1 + 1 < 8; omega)
    have h2tVal : (reg s2 registers.tmp).val = src + i := by
      rw [h2t, add_no_wrap _ _ (by change (reg s tinBase).val + (reg s clk).val < 2 ^ bits; rw [hSrc, hClk]; exact Nat.lt_of_lt_of_le (by omega) hw)]
      change (reg s tinBase).val + (reg s clk).val = _; rw [hSrc, hClk]
    obtain ⟨wSrc, hwSrcAt, hwSrcEq⟩ : ∃ w : Word bits, s2.data[(reg s2 registers.tmp).val]? = some w ∧
        s.data[src + i]? = some w := by
      rw [h2tVal, hd2]
      cases hC : s.data[src + i]? with
      | none => exact False.elim (by have := (Array.getElem?_eq_none_iff).mp hC; rw [hSz] at this; omega)
      | some w => exact ⟨w, rfl, rfl⟩
    have h2 : code[s2.pc]? = some (.loadData registers.value registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3v, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwSrcAt (by rw [hpc2, hpc1]; change 1 + 1 + 1 < 8; omega)
    have h3 : code[s3.pc]? = some (.add registers.tmp toutBase clk) := by rw [hpc3, hpc2, hpc1]; rfl
    obtain ⟨s4, hs4, hpc4, h4t, h4o, hd4⟩ :=
      step_add_at (input := input) h3 (by rw [hpc3, hpc2, hpc1]; change 1 + 1 + 1 + 1 < 8; omega)
    have h4tVal : (reg s4 registers.tmp).val = dst + i := by
      have h3tb : (reg s3 toutBase).val = dst := by
        rw [h3o toutBase (fin_ne_of_val (by decide)), h2o toutBase (fin_ne_of_val (by decide))]; exact hDst
      have h3c : (reg s3 clk).val = i := by
        rw [h3o clk (fin_ne_of_val (by decide)), h2o clk (fin_ne_of_val (by decide))]; exact hClk
      rw [h4t, add_no_wrap _ _ (by rw [h3tb, h3c]; exact Nat.lt_of_lt_of_le (by omega) hw), h3tb, h3c]
    have hFitDst : (reg s4 registers.tmp).val < s4.data.size := by rw [h4tVal, hd4, hd3, hd2, hSz]; omega
    have h4 : code[s4.pc]? = some (.storeData registers.tmp registers.value) := by rw [hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s5, hs5, hpc5, hr5, hd5⟩ :=
      step_storeData_exists (input := input) h4 hFitDst (by rw [hpc4, hpc3, hpc2, hpc1]; change 1 + 1 + 1 + 1 + 1 < 8; omega)
    have h5c : (reg s5 clk).val = i := by
      rw [reg_eq_of_regs_eq hr5, h4o clk (fin_ne_of_val (by decide)),
          h3o clk (fin_ne_of_val (by decide)), h2o clk (fin_ne_of_val (by decide))]; exact hClk
    have h5o : (reg s5 registers.one).val = 1 := by
      rw [reg_eq_of_regs_eq hr5, h4o registers.one (fin_ne_of_val (by decide)),
          h3o registers.one (fin_ne_of_val (by decide)), h2o registers.one (fin_ne_of_val (by decide))]; exact ho
    have h5 : code[s5.pc]? = some (.add clk clk registers.one) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s6, hs6, hpc6, h6c, h6o, hd6⟩ :=
      step_add_at (input := input) h5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; change 1 + 1 + 1 + 1 + 1 + 1 < 8; omega)
    have h6 : code[s6.pc]? = some (.goto 0) := by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    have hs67 := step_goto_at (input := input) h6 (by change 0 < 8; omega)
    let s7 : State DomL := { s6 with pc := 0 }
    have h7c : (reg s7 clk).val = i + 1 := by
      change (reg s6 clk).val = _
      rw [h6c, add_no_wrap _ _ (by rw [h5c, h5o]; omega), h5c, h5o]
    have h7reg : ∀ r, r ≠ clk → r ≠ registers.value → r ≠ registers.tmp → reg s7 r = reg s r := by
      intro r hrc hrv hrt
      change reg s6 r = reg s r
      rw [h6o r hrc, reg_eq_of_regs_eq hr5, h4o r hrt, h3o r hrv, h2o r hrt]; rfl
    have h7Sz : s7.data.size = workCap := by change s6.data.size = workCap; rw [s6.data_size]
    obtain ⟨t, htSteps, htpc, htSz, htz, hto, htReg, htCopied, htFrame⟩ :=
      ih (i + 1) s7 rfl (by omega) h7Sz
        (by rw [h7reg registers.zero (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hz)
        (by rw [h7reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h7reg tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hSrc)
        (by rw [h7reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hDst)
        (by rw [h7reg registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hRem)
        h7c
    have hStepOne : Steps code input 7 s s7 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs67 (.zero _)))))))
    have hs7data : ∀ j, j ≠ dst + i → s7.data[j]? = s.data[j]? := fun j hne => by
      change s6.data[j]? = s.data[j]?
      rw [hd6, hd5, Array.getElem?_set_ne _ (by rw [h4tVal]; exact fun e => hne e.symm), hd4, hd3, hd2]
    have hs7at : s7.data[dst + i]? = s.data[src + i]? := by
      change s6.data[dst + i]? = _
      rw [hd6, hd5]
      have he : dst + i = (reg s4 registers.tmp).val := h4tVal.symm
      simp only [he, Array.getElem?_set_self]
      have h4v : reg s4 registers.value = wSrc := by
        rw [h4o registers.value (fin_ne_of_val (by decide)), h3v]
      rw [h4v, hwSrcEq]
    refine ⟨t, by simpa only [show 7 + (7 * rem + 1) = 7 * (rem + 1) + 1 by omega] using hStepOne.append htSteps,
      htpc, htSz, htz, hto, fun r h1 h2 h3 => (htReg r h1 h2 h3).trans (h7reg r h1 h2 h3),
      ?_, ?_⟩
    · intro k hk1 hk2
      by_cases hkEq : k = i
      · subst k
        have hUntouchedTail : t.data[dst + i]? = s7.data[dst + i]? := htFrame (dst + i) (by omega)
        exact hUntouchedTail.trans hs7at
      · have hk1' : i + 1 ≤ k := by omega
        have hTail := htCopied k hk1' hk2
        have hSrcSame : s7.data[src + k]? = s.data[src + k]? := hs7data (src + k) (by omega)
        exact hTail.trans hSrcSame
    · intro j hj
      have hj' : j < dst + (i + 1) ∨ dst + len ≤ j := by omega
      have hTail := htFrame j hj'
      exact hTail.trans (hs7data j (by omega))

theorem run_copyLoop {input : Input DomL} {Q src dst len : Nat}
    (hSrcFit : src + len ≤ workCap) (hDstFit : dst + len ≤ workCap)
    (hDisj : src + len ≤ dst ∨ dst + len ≤ src) (hLenFit : len < 2 ^ bits)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hSrc : (reg s tinBase).val = src)
    (hDst : (reg s toutBase).val = dst)
    (hRem : (reg s registers.remain).val = len)
    (hClk : (reg s clk).val = 0) :
    ∃ t : State DomL,
      run (copyLoopPhase hi hw).code input (7 * len + 2) (Phase.initial s) = some ⟨t, 7 * len + 2⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (∀ k, k < len → t.data[dst + k]? = s.data[src + k]?) ∧
      (∀ j, (j < dst ∨ dst + len ≤ j) → t.data[j]? = s.data[j]?) := by
  let s0 := Phase.initial s
  obtain ⟨t, htSteps, htpc, _, htz, hto, htReg, htCopied, htFrame⟩ :=
    copyLoop_iter (input := input) hSrcFit hDstFit hDisj hLenFit len 0 s0 rfl (by omega) s0.data_size
      (by simpa [s0] using hz) (by simpa [s0] using ho) (by simpa [s0] using hSrc)
      (by simpa [s0] using hDst) (by simpa [s0] using hRem) (by simpa [s0] using hClk)
  have hHalt : step (copyLoopPhase hi hw).code input t = some (.halted t) := by
    apply step_halt_at; rw [htpc]; rfl
  refine ⟨t, ?_, htz, hto, ?_, fun k hk => ?_, fun j hj => ?_⟩
  · simpa only [Nat.add_assoc, show 7 * len + 1 + 1 = 7 * len + 2 by omega] using htSteps.halts hHalt
  · rw [htReg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
    simpa [s0] using hc
  · simpa [s0] using htCopied k (Nat.zero_le k) hk
  · simpa [s0] using htFrame j (by omega)

/-! ### Arena `Control` setup phase -/

private theorem nonHalt_setArenaCtrlInstrs (baseMul : Nat) :
    (setArenaCtrlInstrs (bits := bits) baseMul).all (nonHalt (L := DomL)) = true := by
  unfold setArenaCtrlInstrs
  apply nonHalt_append (L := DomL)
  · apply nonHalt_append (L := DomL)
    · apply nonHalt_append (L := DomL)
      · apply nonHalt_append (L := DomL)
        · apply nonHalt_append (L := DomL)
          · exact nonHalt_mulAddInstrs _ _ _ _ _
          · exact nonHalt_mulAddInstrs _ _ _ _ _
        · exact nonHalt_mulAddInstrs _ _ _ _ _
      · exact nonHalt_mulAddInstrs _ _ _ _ _
    · exact nonHalt_mulAddInstrs _ _ _ _ _
  · rfl

def setArenaCtrlPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (baseMul : Nat) :
    Phase (layout bits inputCap workCap hi hw) :=
  let ins := setArenaCtrlInstrs (bits := bits) baseMul
  let code : Program (layout bits inputCap workCap hi hw) := (ins ++ [Instr.halt]).toArray
  Phase.ofLast code ins.length
    (by simp [code]) (by simp [code])
    (by
      have hTake : List.take ins.length code.toList = ins := by
        simp [code]
      rw [hTake]
      exact nonHalt_setArenaCtrlInstrs (hi := hi) (hw := hw) _)

theorem run_setArenaCtrl {input : Input DomL} {baseMul Q : Nat} (_hQ : 1 ≤ Q)
    (a : Arena bits workCap Q) (haBase : a.base = baseMul * Q)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q) :
    let p := setArenaCtrlPhase hi hw baseMul
    let w := (setArenaCtrlInstrs (bits := bits) baseMul).length + 1
    ∃ t : State DomL,
      run p.code input w (Phase.initial s) = some ⟨t, w⟩ ∧
      t.data = s.data ∧
      Control a t ∧
      (reg t cmd).val = 0 ∧
      (reg t registers.ptr).val = 0 ∧
      (reg t clk).val = 0 := by
  intro p w
  let ins := setArenaCtrlInstrs (bits := bits) baseMul
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = ins.length + 1 := by simp [p, setArenaCtrlPhase, ins]
  have hLenIns := setArenaCtrlInstrs_length (bits := bits) baseMul
  have hFits := a.wordFits
  have haTin : a.tin = (baseMul + 2) * Q := by
    unfold Arena.tin; rw [haBase, Nat.add_mul]
  have haTout : a.tout = (baseMul + 3) * Q := by
    unfold Arena.tout; rw [haBase, Nat.add_mul]
  have haOff : a.offsets = (baseMul + 4) * Q := by
    unfold Arena.offsets; rw [haBase, Nat.add_mul]
  have haPay : a.payload = (baseMul + 5) * Q + 1 := by
    unfold Arena.payload; rw [haBase, Nat.add_mul]
  have hFits5 : (baseMul + 5) * Q + 1 < 2 ^ bits := by
    rw [← haPay]; unfold Arena.payload at *; omega
  have hFits0 : baseMul * Q + 0 < 2 ^ bits := by rw [Nat.add_zero, ← haBase]; omega
  have hFits2 : (baseMul + 2) * Q + 0 < 2 ^ bits := by rw [Nat.add_zero, ← haTin]; unfold Arena.tin; omega
  have hFits3 : (baseMul + 3) * Q + 0 < 2 ^ bits := by rw [Nat.add_zero, ← haTout]; unfold Arena.tout; omega
  have hFits4 : (baseMul + 4) * Q + 0 < 2 ^ bits := by rw [Nat.add_zero, ← haOff]; unfold Arena.offsets; omega
  have hPlAll : Placed p.code 0 ins := by
    intro i op hiOp
    simp only [p, setArenaCtrlPhase, phase_ofLast_code, Nat.zero_add]
    rcases Nat.lt_or_ge i ins.length with hiLt | hGe
    · rw [List.getElem?_toArray, List.getElem?_append_left hiLt]; exact hiOp
    · rw [List.getElem?_eq_none hGe] at hiOp; cases hiOp
  have hPl1 := placed_append_left (placed_append_left (placed_append_left (placed_append_left (placed_append_left hPlAll))))
  have hPl2 : Placed p.code (1 + baseMul) (mulAddInstrs tinBase count registers.one (baseMul + 2) 0) := by
    have h := placed_append_right (placed_append_left (placed_append_left (placed_append_left (placed_append_left hPlAll))))
    simp only [mulAddInstrs_length, Nat.add_zero, Nat.zero_add] at h; exact h
  have hPl3 : Placed p.code ((1 + baseMul) + (1 + (baseMul + 2)))
      (mulAddInstrs toutBase count registers.one (baseMul + 3) 0) := by
    have h := placed_append_right (placed_append_left (placed_append_left (placed_append_left hPlAll)))
    simp only [List.length_append, mulAddInstrs_length, Nat.add_zero, Nat.zero_add] at h; exact h
  have hPl4 : Placed p.code ((1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)))
      (mulAddInstrs offsetBase count registers.one (baseMul + 4) 0) := by
    have h := placed_append_right (placed_append_left (placed_append_left hPlAll))
    simp only [List.length_append, mulAddInstrs_length, Nat.add_zero, Nat.zero_add] at h; exact h
  have hPl5 : Placed p.code ((1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)) + (1 + (baseMul + 4)))
      (mulAddInstrs childrenBase count registers.one (baseMul + 5) 1) := by
    have h := placed_append_right (placed_append_left hPlAll)
    simp only [List.length_append, mulAddInstrs_length, Nat.add_zero, Nat.zero_add] at h; exact h
  let pc6 := (1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)) + (1 + (baseMul + 4)) + (1 + (baseMul + 5) + 1)
  have hPl6 : Placed p.code pc6
      [.imm cmd ⟨0, Nat.one_le_two_pow⟩, .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩, .imm clk ⟨0, Nat.one_le_two_pow⟩] := by
    have h := placed_append_right hPlAll
    simp only [List.length_append, mulAddInstrs_length, Nat.add_zero, Nat.zero_add] at h; exact h
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have hone0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, hsb1, ho1⟩ :=
    run_mulAddInstrs (input := input) registers.stackBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz, hLenIns]; omega) hPl1 hc0 hone0 hFits0
  have hpc1' : s1.pc = 1 + baseMul := by simp only [hpc1, Nat.zero_add, Nat.add_zero]
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have hone1 : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), hone0]
  obtain ⟨s2, hs2, hpc2, hd2, htin2, ho2⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 hpc1' (by rw [hSz, hLenIns]; omega) hPl2 hc1 hone1 hFits2
  have hpc2' : s2.pc = (1 + baseMul) + (1 + (baseMul + 2)) := by simp only [hpc2, Nat.add_zero]
  have hc2 : (reg s2 count).val = Q := by rw [ho2 count (fin_ne_of_val (by decide)), hc1]
  have hone2 : (reg s2 registers.one).val = 1 := by rw [ho2 registers.one (fin_ne_of_val (by decide)), hone1]
  obtain ⟨s3, hs3, hpc3, hd3, htout3, ho3⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s2 hpc2' (by rw [hSz, hLenIns]; omega) hPl3 hc2 hone2 hFits3
  have hpc3' : s3.pc = (1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)) := by
    simp only [hpc3, Nat.add_zero]
  have hc3 : (reg s3 count).val = Q := by rw [ho3 count (fin_ne_of_val (by decide)), hc2]
  have hone3 : (reg s3 registers.one).val = 1 := by rw [ho3 registers.one (fin_ne_of_val (by decide)), hone2]
  obtain ⟨s4, hs4, hpc4, hd4, hoff4, ho4⟩ :=
    run_mulAddInstrs (input := input) offsetBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s3 hpc3' (by rw [hSz, hLenIns]; omega) hPl4 hc3 hone3 hFits4
  have hpc4' : s4.pc = (1 + baseMul) + (1 + (baseMul + 2)) + (1 + (baseMul + 3)) + (1 + (baseMul + 4)) := by
    simp only [hpc4, Nat.add_zero]
  have hc4 : (reg s4 count).val = Q := by rw [ho4 count (fin_ne_of_val (by decide)), hc3]
  have hone4 : (reg s4 registers.one).val = 1 := by rw [ho4 registers.one (fin_ne_of_val (by decide)), hone3]
  obtain ⟨s5, hs5, hpc5, hd5, hch5, ho5⟩ :=
    run_mulAddInstrs (input := input) childrenBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s4 hpc4' (by rw [hSz, hLenIns]; omega) hPl5 hc4 hone4 hFits5
  have hpc5' : s5.pc = pc6 := by rw [hpc5]
  have h56at : p.code[s5.pc]? = some (.imm cmd ⟨0, Nat.one_le_two_pow⟩) := by
    rw [hpc5']; exact hPl6 0 _ rfl
  obtain ⟨s6, hs6, hpc6, hcmd6, ho6, hd6⟩ :=
    step_imm_at (input := input) h56at (by rw [hpc5', hSz, hLenIns]; omega)
  have h67at : p.code[s6.pc]? = some (.imm registers.ptr ⟨0, Nat.one_le_two_pow⟩) := by
    rw [hpc6, hpc5']; exact hPl6 1 _ rfl
  obtain ⟨s7, hs7, hpc7, hptr7, ho7, hd7⟩ :=
    step_imm_at (input := input) h67at (by rw [hpc6, hpc5', hSz, hLenIns]; omega)
  have h78at : p.code[s7.pc]? = some (.imm clk ⟨0, Nat.one_le_two_pow⟩) := by
    rw [hpc7, hpc6, hpc5']; exact hPl6 2 _ rfl
  obtain ⟨t, hs8, hpc8, hclk8, ho8, hdt⟩ :=
    step_imm_at (input := input) h78at (by rw [hpc7, hpc6, hpc5', hSz, hLenIns]; omega)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at
    rw [hpc8, hpc7, hpc6, hpc5']
    have hpLast := p.haltAt
    have hpPc : p.haltPC = ins.length := rfl
    rw [hpPc, hLenIns] at hpLast
    simpa only [pc6, Nat.add_assoc] using hpLast
  have hAllSteps : Steps p.code input ins.length s0 t := by
    rw [hLenIns]
    simpa only [Nat.add_assoc, Nat.add_zero] using
      (hs1.append (hs2.append (hs3.append (hs4.append hs5)))).append
        (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (.zero _))))
  have hCtrl : Control a t :=
    { count_eq := by
        rw [ho8 count (fin_ne_of_val (by decide)), ho7 count (fin_ne_of_val (by decide)),
            ho6 count (fin_ne_of_val (by decide)), ho5 count (fin_ne_of_val (by decide))]; exact hc4
      one := by
        rw [ho8 registers.one (fin_ne_of_val (by decide)), ho7 registers.one (fin_ne_of_val (by decide)),
            ho6 registers.one (fin_ne_of_val (by decide)), ho5 registers.one (fin_ne_of_val (by decide))]; exact hone4
      zero := by
        rw [ho8 registers.zero (fin_ne_of_val (by decide)), ho7 registers.zero (fin_ne_of_val (by decide)),
            ho6 registers.zero (fin_ne_of_val (by decide)), ho5 registers.zero (fin_ne_of_val (by decide)),
            ho4 registers.zero (fin_ne_of_val (by decide)), ho3 registers.zero (fin_ne_of_val (by decide)),
            ho2 registers.zero (fin_ne_of_val (by decide)), ho1 registers.zero (fin_ne_of_val (by decide)),
            initial_reg]; exact hz
      stackBase_eq := by
        rw [ho8 registers.stackBase (fin_ne_of_val (by decide)), ho7 registers.stackBase (fin_ne_of_val (by decide)),
            ho6 registers.stackBase (fin_ne_of_val (by decide)), ho5 registers.stackBase (fin_ne_of_val (by decide)),
            ho4 registers.stackBase (fin_ne_of_val (by decide)), ho3 registers.stackBase (fin_ne_of_val (by decide)),
            ho2 registers.stackBase (fin_ne_of_val (by decide)), hsb1, haBase, Nat.add_zero]
      tin_eq := by
        rw [ho8 tinBase (fin_ne_of_val (by decide)), ho7 tinBase (fin_ne_of_val (by decide)),
            ho6 tinBase (fin_ne_of_val (by decide)), ho5 tinBase (fin_ne_of_val (by decide)),
            ho4 tinBase (fin_ne_of_val (by decide)), ho3 tinBase (fin_ne_of_val (by decide)),
            htin2, haTin, Nat.add_zero]
      tout_eq := by
        rw [ho8 toutBase (fin_ne_of_val (by decide)), ho7 toutBase (fin_ne_of_val (by decide)),
            ho6 toutBase (fin_ne_of_val (by decide)), ho5 toutBase (fin_ne_of_val (by decide)),
            ho4 toutBase (fin_ne_of_val (by decide)), htout3, haTout, Nat.add_zero]
      offset_eq := by
        rw [ho8 offsetBase (fin_ne_of_val (by decide)), ho7 offsetBase (fin_ne_of_val (by decide)),
            ho6 offsetBase (fin_ne_of_val (by decide)), ho5 offsetBase (fin_ne_of_val (by decide)),
            hoff4, haOff, Nat.add_zero]
      child_eq := by
        rw [ho8 childrenBase (fin_ne_of_val (by decide)), ho7 childrenBase (fin_ne_of_val (by decide)),
            ho6 childrenBase (fin_ne_of_val (by decide)), hch5, haPay] }
  refine ⟨t, by simpa only [w] using hAllSteps.halts hHalt,
    by rw [hdt, hd7, hd6, hd5, hd4, hd3, hd2, hd1, initial_data], hCtrl, ?_, ?_, ?_⟩
  · rw [ho8 cmd (fin_ne_of_val (by decide)), ho7 cmd (fin_ne_of_val (by decide)), hcmd6]
  · rw [ho8 registers.ptr (fin_ne_of_val (by decide)), hptr7]
  · rw [hclk8]

/-! ### CSR and Finish `PhasesExec` bridges -/

private theorem sum_map_add_indicator {n : Nat} (xs : List (Fin n)) (target : Fin n)
    (f : Fin n → Nat) :
    xs.Nodup → target ∈ xs →
      (xs.map (fun p => f p + if p = target then 1 else 0)).sum = (xs.map f).sum + 1 := by
  induction xs with
  | nil => intro _ hMem; cases hMem
  | cons a as ih =>
    intro hNd hMem
    have hNd' := List.nodup_cons.mp hNd
    rcases List.mem_cons.mp hMem with ha | has
    · subst ha
      have hMapAs : as.map (fun p => f p + if p = target then 1 else 0) = as.map f := by
        apply List.map_congr_left
        intro p hp
        have hne : p ≠ target := fun e => hNd'.1 (e ▸ hp)
        simp [hne]
      simp only [List.map_cons, List.sum_cons, ↓reduceIte, hMapAs]
      omega
    · have haNe : a ≠ target := fun e => hNd'.1 (e ▸ has)
      simp only [List.map_cons, List.sum_cons, haNe, ↓reduceIte, Nat.add_zero]
      have ihR := ih hNd'.2 has
      omega

private theorem filter_len_partition {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    cases h : p a <;> simp [h] <;> omega

private theorem sum_visitedRows_add {n : Nat} (root : Fin n) (parent : Fin n → Fin n)
    (xs : List (Fin n)) (start : Fin n → List (Fin n)) :
    ((finElems n).map (fun p => (bucketPassAux root parent xs start p).length)).sum =
      ((finElems n).map (fun p => (start p).length)).sum + (xs.filter (fun x => decide (x ≠ root))).length := by
  induction xs generalizing start with
  | nil => simp [bucketPassAux]
  | cons x xs ih =>
    simp only [bucketPassAux, List.filter_cons]
    by_cases hx : x = root
    · subst hx
      simp [addChildToBuckets, ih]
    · have hxNe : decide (x ≠ root) = true := decide_eq_true hx
      simp only [hxNe]
      have hSumStep : ((finElems n).map (fun p => (addChildToBuckets root parent start x p).length)).sum =
          ((finElems n).map (fun p => (start p).length)).sum + 1 := by
        have hNodup : (finElems n).Nodup := PaperB.LabelledQuotient.nodup_finElems n
        have hMem : parent x ∈ finElems n := PaperB.LabelledQuotient.mem_finElems (parent x)
        have hEq : ∀ q : Fin n, (addChildToBuckets root parent start x q).length =
            (start q).length + if q = parent x then 1 else 0 := by
          intro q
          simp only [addChildToBuckets, hx, ↓reduceIte]
          by_cases hq : q = parent x <;> simp [hq]
        have hMap : (finElems n).map (fun p => (addChildToBuckets root parent start x p).length) =
            (finElems n).map (fun p => (start p).length + if p = parent x then 1 else 0) :=
          List.map_congr_left (fun p _ => hEq p)
        rw [hMap]
        exact sum_map_add_indicator (finElems n) (parent x) (fun p => (start p).length) hNodup hMem
      rw [ih, hSumStep]
      simp
      omega

private theorem rowPrefix_parentDegree_le {n : Nat} (hn : 1 ≤ n) (root : Fin n) (parent : Fin n → Fin n) :
    rowPrefix (parentDegree root parent) n ≤ n - 1 := by
  have hPrefixEq : ∀ k ≤ n, rowPrefix (parentDegree root parent) k =
      ((finElems n).take k |>.map (fun p => (visitedRows root parent n p).length)).sum := by
    intro k hk
    induction k with
    | zero => simp [rowPrefix]
    | succ k ih =>
      have hkLt : k < n := by omega
      have hTake : (finElems n).take (k + 1) = (finElems n).take k ++ [⟨k, hkLt⟩] := by
        have hkLen : k < (finElems n).length := by rw [length_finElems]; exact hkLt
        rw [List.take_succ_eq_append_getElem hkLen, PaperB.RamForestProgram.Finish.finElems_index n ⟨k, hkLt⟩]
      rw [rowPrefix, ih (by omega), hTake, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hDeg : parentDegree root parent k = (visitedRows root parent n ⟨k, hkLt⟩).length := by
        simp [parentDegree, hkLt]
      rw [hDeg]
  rw [hPrefixEq n (Nat.le_refl n)]
  have hTakeAll : (finElems n).take n = finElems n := by
    apply List.take_of_length_le; rw [length_finElems]; exact Nat.le_refl _
  rw [hTakeAll]
  unfold visitedRows
  rw [hTakeAll, sum_visitedRows_add]
  have hInit0 : ((finElems n).map (fun _ => ([] : List (Fin n)).length)).sum = 0 := by
    induction (finElems n) with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_nil, Nat.zero_add]; exact ih
  rw [hInit0, Nat.zero_add]
  have hRootMem : root ∈ finElems n := PaperB.LabelledQuotient.mem_finElems root
  have hPart := filter_len_partition (finElems n) (fun x => decide (x ≠ root))
  have hPos : 1 ≤ ((finElems n).filter (fun x => !decide (x ≠ root))).length := by
    have : root ∈ (finElems n).filter (fun x => !decide (x ≠ root)) :=
      List.mem_filter.mpr ⟨hRootMem, by simp⟩
    exact List.length_pos_of_mem this
  rw [length_finElems] at hPart
  omega

private theorem control_initial {n : Nat} {a : Arena bits workCap n} {s : State DomL}
    (h : Control a s) : Control a (Phase.initial s) :=
  ⟨h.count_eq, h.one, h.zero, h.stackBase_eq, h.tin_eq, h.tout_eq, h.offset_eq, h.child_eq⟩

private theorem cursor_initial {n : Nat} {a : Arena bits workCap n} {root : Fin n} {i : Nat}
    {s : State DomL} (h : ParentCursor a root i s) : ParentCursor a root i (Phase.initial s) :=
  ⟨control_initial h.ctrl, h.rootVal, h.ptrVal⟩

theorem phasesExec_csr {input : Input DomL} {n : Nat}
    {a : Arena bits workCap n} (root : Fin n) (parent : Fin n → Fin n)
    (hMass : rowPrefix (parentDegree root parent) n ≤ a.children)
    (s : State DomL) (hCtrl : Control a s) (hCmd : (reg s cmd).val = root.val)
    (hPar : ParentAt a parent s.data)
    (hPtr : (reg s registers.ptr).val = 0) :
    ∃ t w,
      w ≤ 42 * n + 27 ∧
      PhasesExec input (csrPhases (hi := hi) (hw := hw)) s t w ∧
      ChildImage a (bucketChildLists root parent) t.data ∧
      ParentCursor a root n t ∧
      ∀ j, j < a.base → t.data[j]? = s.data[j]? := by
  have hCur0 : ParentCursor a root 0 (Phase.initial s) := cursor_initial ⟨hCtrl, hCmd, hPtr⟩
  obtain ⟨s1, hr1, hc1, _, _, hd1⟩ :=
    run_prepare_parent_phase input (a := a) (root := root) (i := 0) (Phase.initial s) rfl hCur0
  obtain ⟨s2, _, hr2, hc2, hZero2, hKeep2, _, _⟩ :=
    run_zero_degrees input (a := a) (root := root) (Phase.initial s1) rfl (cursor_initial hc1)
  obtain ⟨s3, hr3, hc3, _, _, hd3⟩ :=
    run_prepare_parent_phase input (a := a) (root := root) (i := n) (Phase.initial s2) rfl (cursor_initial hc2)
  have hPar3 : ParentAt a parent s3.data := by
    rw [hd3, initial_data]
    intro v
    have hvLt : a.base + v.val < a.tin := by unfold Arena.tin; have := v.isLt; omega
    rw [hKeep2 _ (Or.inl hvLt), initial_data, hd1, initial_data]
    exact hPar v
  have hZero3 : ∀ p : Fin n, (s3.data[a.tin + p.val]?).map Fin.val = some 0 := by
    rw [hd3, initial_data]; exact hZero2
  obtain ⟨s4, _, w4, hw4, hr4, hc4, hPar4, hDeg4, hKeep4, _, _⟩ :=
    run_parent_histogram input root parent (Phase.initial s3) rfl (cursor_initial hc3) hPar3 hZero3
  obtain ⟨s5, hr5, hc5, hClk5, _, hd5⟩ :=
    run_prepare_parent_phase input (a := a) (root := root) (i := n) (Phase.initial s4) rfl (cursor_initial hc4)
  have hDeg5 : ∀ p : Fin n, (s5.data[a.tin + p.val]?).map Fin.val = some (visitedRows root parent n p).length := by
    intro p
    rw [hd5, initial_data, hDeg4 p, parentDegree_at, visitedRows_full]
  have hOffIn5 : OffsetInput a (parentDegree root parent) (Phase.initial s5) :=
    offsetInput_of_parent_degrees (Phase.initial s5) root parent rfl hc5.ptrVal hClk5 (control_initial hc5.ctrl) hDeg5 hMass
  obtain ⟨s6, _, hr6, hOff6, hKeep6, _, _, hCtrlKeep6, hPtr6⟩ :=
    run_csr_offsets_with_frame input (Phase.initial s5) hOffIn5
  have hCtrl6 : Control a s6 :=
    { count_eq := (congrArg Fin.val (hCtrlKeep6 count (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.count_eq
      one := (congrArg Fin.val (hCtrlKeep6 registers.one (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.one
      zero := (congrArg Fin.val (hCtrlKeep6 registers.zero (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.zero
      stackBase_eq := (congrArg Fin.val (hCtrlKeep6 registers.stackBase (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.stackBase_eq
      tin_eq := (congrArg Fin.val (hCtrlKeep6 tinBase (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.tin_eq
      tout_eq := (congrArg Fin.val (hCtrlKeep6 toutBase (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.tout_eq
      offset_eq := (congrArg Fin.val (hCtrlKeep6 offsetBase (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.offset_eq
      child_eq := (congrArg Fin.val (hCtrlKeep6 childrenBase (by decide) (by decide) (by decide) (by decide))).trans hc5.ctrl.child_eq }
  have hCmd6 : (reg s6 cmd).val = root.val :=
    (congrArg Fin.val (hCtrlKeep6 cmd (by decide) (by decide) (by decide) (by decide))).trans hc5.rootVal
  have hCur6 : ParentCursor a root n s6 := ⟨hCtrl6, hCmd6, hPtr6⟩
  obtain ⟨s7, hr7, hc7, _, _, hd7⟩ :=
    run_prepare_parent_phase input (a := a) (root := root) (i := n) (Phase.initial s6) rfl (cursor_initial hCur6)
  have hPar7 : ParentAt a parent s7.data := by
    intro v
    have hvLt : a.base + v.val < a.offsets := by unfold Arena.offsets; have := v.isLt; omega
    rw [hd7, initial_data, hKeep6 _ (Or.inl hvLt), initial_data, hd5, initial_data]
    exact hPar4 v
  have hOff7 : OffsetAt a root parent s7.data := by
    intro i hi'
    rw [hd7, initial_data]; exact hOff6 i hi'
  have hDeg7 : ∀ p : Fin n, (s7.data[a.tin + p.val]?).map Fin.val = some (parentDegree root parent p.val) := by
    intro p
    have hpLt : a.tin + p.val < a.offsets := by unfold Arena.tin Arena.offsets; have := p.isLt; omega
    rw [hd7, initial_data, hKeep6 _ (Or.inl hpLt), initial_data, hd5, initial_data]
    exact hDeg4 p
  obtain ⟨t, _, w8, hw8, hr8, hc8, hImg8, hKeep8, _, _⟩ :=
    run_parent_scatter input root parent (Phase.initial s7) rfl (cursor_initial hc7) hPar7 hOff7 hDeg7 hMass
  have hExec : PhasesExec input (csrPhases (hi := hi) (hw := hw)) s t
      (4 + ((5 * n + 2) + (4 + (w4 + (4 + ((8 * n + 4) + (4 + w8))))))) :=
    PhasesExec.cons hr1 (PhasesExec.cons hr2 (PhasesExec.cons hr3 (PhasesExec.cons hr4
      (PhasesExec.cons hr5 (PhasesExec.cons hr6 (PhasesExec.cons hr7 (PhasesExec.single scatterPhase hr8)))))))
  refine ⟨t, _, by omega, hExec, hImg8, hc8, fun j hj => ?_⟩
  have hBaseTin : a.base ≤ a.tin := by unfold Arena.tin; omega
  have hBaseOff : a.base ≤ a.offsets := by unfold Arena.offsets; omega
  rw [hKeep8 j hj, initial_data, hd7, initial_data, hKeep6 j (Or.inl (by omega)), initial_data, hd5, initial_data,
      hKeep4 j (Or.inl (by omega)), initial_data, hd3, initial_data,
      hKeep2 j (Or.inl (by omega)), initial_data, hd1, initial_data]

theorem phasesExec_finish {input : Input DomL} {n : Nat} (hn : 1 ≤ n)
    {a : Arena bits workCap n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth)
    (hMass : rowPrefix (parentDegree ⟨0, hn⟩ parent) n ≤ a.children)
    (hChLe : a.children ≤ n) (hBase2 : 2 * n ≤ a.base)
    (s : State DomL) (hCtrl : Control a s) (hCmd : (reg s cmd).val = 0)
    (hPar : ParentAt a parent s.data) (hPtr : (reg s registers.ptr).val = 0) :
    have dst := a.base - 2 * n
    have final := PaperB.ForestLayout.layout (bucketChildLists ⟨0, hn⟩ parent) ⟨0, hn⟩ (2 * n)
    ∃ t w,
      w ≤ 106 * n + 44 ∧
      PhasesExec input (finishPhases (hi := hi) (hw := hw)) s t w ∧
      ColumnAt (n := n) dst final.entries t.data ∧
      ColumnAt (n := n) (dst + n) final.ends t.data ∧
      ∀ j, j < dst → t.data[j]? = s.data[j]? := by
  intro dst final
  obtain ⟨s1, w1, hw1, hExec1, hImg1, hCur1, hKeep1⟩ :=
    phasesExec_csr ⟨0, hn⟩ parent hMass s hCtrl hCmd hPar hPtr
  obtain ⟨s2, hr2, hc2, _, hRem2, hd2⟩ :=
    run_prepare_parent_phase input (a := a) (root := ⟨0, hn⟩) (i := n) (Phase.initial s1) rfl (cursor_initial hCur1)
  have hCmdWord : reg (Phase.initial s2) cmd = PaperB.RamForestStack.commandWord a.tags (Command.enter ⟨0, hn⟩) := by
    apply Fin.ext
    rw [initial_reg, hc2.rootVal]
    change (0 : Nat) = (PaperB.RamForestStack.commandWord a.tags (Command.enter ⟨0, hn⟩)).val
    simp [PaperB.RamForestStack.commandWord]
  have hSeed2 : SeedInput a (bucketChildLists ⟨0, hn⟩ parent) ⟨0, hn⟩ (Phase.initial s2) :=
    ⟨rfl, control_initial hc2.ctrl, hRem2, hc2.ptrVal, hCmdWord, by rw [initial_data, hd2, initial_data]; exact hImg1⟩
  obtain ⟨t, _, w3, hEnt3, hEnd3, hKeep3, hw3, hr3, _, _⟩ :=
    run_serialized_tree input hTree rfl hChLe hBase2 (Phase.initial s2) hSeed2
  have hExecAll : PhasesExec input (finishPhases (hi := hi) (hw := hw)) s t
      (w1 + (4 + w3)) := by
    unfold finishPhases
    exact hExec1.append (PhasesExec.cons hr2 (PhasesExec.single serializationPhase hr3))
  refine ⟨t, w1 + (4 + w3), by omega, hExecAll, hEnt3, hEnd3, fun j hj => ?_⟩
  have hKeep3' : t.data[j]? = s2.data[j]? := hKeep3 j hj
  have hjBase : j < a.base := by dsimp [dst] at hj; omega
  rw [hKeep3', hd2, initial_data, hKeep1 j hjBase]

end BasePhases

section InstrLists4

variable {bits : Nat}

private def denseOfEntryInstrs : List (Instr bits 15) :=
  mulAddInstrs tinBase count registers.one 4 0 ++
  mulAddInstrs toutBase count registers.one 6 0 ++
  [ .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩
  , .branchLt registers.ptr count 14 20
  , .add registers.tmp tinBase registers.ptr
  , .loadData registers.value registers.tmp
  , .add registers.tmp toutBase registers.value
  , .storeData registers.tmp registers.ptr
  , .add registers.ptr registers.ptr registers.one
  , .goto 13
  , .halt
  ]

private def heavyInstrs : List (Instr bits 15) :=
  mulAddInstrs tinBase count registers.one 2 0 ++
  mulAddInstrs toutBase count registers.one 4 0 ++
  mulAddInstrs registers.stackBase count registers.one 7 0 ++
  mulAddInstrs childrenBase count registers.one 10 1 ++
  [ .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩
  , .branchLt registers.ptr count 30 53
  , .add registers.tmp registers.stackBase registers.ptr
  , .loadData registers.remain registers.tmp
  , .add registers.tmp registers.tmp registers.one
  , .loadData clk registers.tmp
  , .mov cmd count
  , .imm registers.childBase ⟨0, Nat.one_le_two_pow⟩
  , .branchLt registers.remain clk 37 49
  , .add registers.tmp childrenBase registers.remain
  , .loadData registers.value registers.tmp
  , .add registers.tmp toutBase registers.value
  , .loadData offsetBase registers.tmp
  , .add registers.tmp registers.tmp count
  , .loadData registers.tmp registers.tmp
  , .sub registers.tmp registers.tmp offsetBase
  , .branchLt registers.childBase registers.tmp 45 47
  , .mov cmd registers.value
  , .mov registers.childBase registers.tmp
  , .add registers.remain registers.remain registers.one
  , .goto 36
  , .add registers.tmp tinBase registers.ptr
  , .storeData registers.tmp cmd
  , .add registers.ptr registers.ptr registers.one
  , .goto 29
  , .halt
  ]

private def headInstrs : List (Instr bits 15) :=
  mulAddInstrs tinBase count registers.one 2 0 ++
  mulAddInstrs toutBase count registers.one 3 0 ++
  mulAddInstrs childrenBase count registers.one 6 0 ++
  [ .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩
  , .branchLt registers.ptr count 16 34
  , .add registers.tmp childrenBase registers.ptr
  , .loadData registers.value registers.tmp
  , .branchLt registers.value registers.one 19 21
  , .storeData toutBase registers.zero
  , .goto 32
  , .loadData registers.remain registers.value
  , .add registers.tmp tinBase registers.remain
  , .loadData clk registers.tmp
  , .branchLt clk registers.value 29 25
  , .branchLt registers.value clk 29 26
  , .add registers.tmp toutBase registers.remain
  , .loadData cmd registers.tmp
  , .goto 30
  , .mov cmd registers.value
  , .add registers.tmp toutBase registers.value
  , .storeData registers.tmp cmd
  , .add registers.ptr registers.ptr registers.one
  , .goto 15
  , .halt
  ]

private def childIntervalsInstrs : List (Instr bits 15) :=
  mulAddInstrs tinBase count registers.one 4 0 ++
  mulAddInstrs toutBase count registers.one 8 1 ++
  mulAddInstrs offsetBase count registers.one 9 1 ++
  mulAddInstrs childrenBase count registers.one 10 1 ++
  mulAddInstrs registers.remain count registers.one 1 0 ++
  [ .sub registers.remain registers.remain registers.one
  , .imm registers.ptr ⟨0, Nat.one_le_two_pow⟩
  , .branchLt registers.ptr registers.remain 43 55
  , .add registers.tmp childrenBase registers.ptr
  , .loadData registers.value registers.tmp
  , .add registers.tmp tinBase registers.value
  , .loadData cmd registers.tmp
  , .add registers.tmp registers.tmp count
  , .loadData clk registers.tmp
  , .add registers.tmp toutBase registers.ptr
  , .storeData registers.tmp cmd
  , .add registers.tmp offsetBase registers.ptr
  , .storeData registers.tmp clk
  , .add registers.ptr registers.ptr registers.one
  , .goto 42
  , .halt
  ]

end InstrLists4

section Phase2C

variable {bits : Nat} {inputCap : Nat} {workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

/-! ### Pass 2C.1: `denseOfEntry` (`[6*Q .. 7*Q)`) -/

def denseOfEntryPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) := (denseOfEntryInstrs (bits := bits)).toArray
  Phase.ofLast code 20 rfl rfl rfl

private theorem denseOfEntry_iter {input : Input DomL} {Q : Nat}
    (entryFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hEntryRange : ∀ v, v < Q → entryFn v < Q)
    (hEntryInj : ∀ u₁ u₂, u₁ < Q → u₂ < Q → entryFn u₁ = entryFn u₂ → u₁ = u₂) :
    ∀ (rem v : Nat) (s : State DomL),
      s.pc = 13 →
      Q = v + rem →
      s.data.size = workCap →
      (reg s registers.zero).val = 0 →
      (reg s registers.one).val = 1 →
      (reg s count).val = Q →
      (reg s tinBase).val = 4 * Q →
      (reg s toutBase).val = 6 * Q →
      (reg s registers.ptr).val = v →
      (∀ u, u < Q → (s.data[4 * Q + u]?).map Fin.val = some (entryFn u)) →
      ∃ t : State DomL,
        Steps (denseOfEntryPhase hi hw).code input (7 * rem + 1) s t ∧
        t.pc = 20 ∧
        t.data.size = workCap ∧
        (reg t registers.zero).val = 0 ∧
        (reg t registers.one).val = 1 ∧
        (reg t count).val = Q ∧
        (∀ u, v ≤ u → u < Q → (t.data[6 * Q + entryFn u]?).map Fin.val = some u) ∧
        (∀ j, (∀ u, v ≤ u → u < Q → j ≠ 6 * Q + entryFn u) → t.data[j]? = s.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro v s hpc hEq hSz hz ho hc hTin hTout hPtr hEnt
    let code := (denseOfEntryPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 14 20) := by rw [hpc]; rfl
    have hFalse : ltb (reg s registers.ptr) (reg s count) = false := by
      cases hC : ltb (reg s registers.ptr) (reg s count) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hPtr, hc] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 14 else 20) < 21; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 14 else 20 }
    refine ⟨t, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      hSz, hz, ho, hc, fun u hu1 hu2 => by omega, fun _ _ => rfl⟩
  | succ rem ih =>
    intro v s hpc hEq hSz hz ho hc hTin hTout hPtr hEnt
    let code := (denseOfEntryPhase hi hw).code
    have hvLt : v < Q := by omega
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 14 20) := by rw [hpc]; rfl
    have hTrue : ltb (reg s registers.ptr) (reg s count) = true :=
      (ltb_eq_true _ _).mpr (by rw [hPtr, hc]; exact hvLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 14 else 20) < 21; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 14 else 20 }
    have hpc1 : s1.pc = 14 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp tinBase registers.ptr) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 14 + 1 < 21; omega)
    have h2tVal : (reg s2 registers.tmp).val = 4 * Q + v := by
      rw [h2t, add_no_wrap _ _ (by change (reg s tinBase).val + (reg s registers.ptr).val < 2 ^ bits; rw [hTin, hPtr]; omega)]
      change (reg s tinBase).val + (reg s registers.ptr).val = _; rw [hTin, hPtr]
    have hevLt : entryFn v < Q := hEntryRange v hvLt
    have hwEnt : s2.data[(reg s2 registers.tmp).val]? = some ⟨entryFn v, by omega⟩ := by
      rw [h2tVal, hd2]
      have hEv := hEnt v hvLt
      cases hC : s.data[4 * Q + v]? with
      | none => rw [hC] at hEv; cases hEv
      | some w => rw [hC, Option.map_some] at hEv; congr 1; exact Fin.ext (Option.some.inj hEv)
    have h2 : code[s2.pc]? = some (.loadData registers.value registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3v, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwEnt (by rw [hpc2, hpc1]; change 14 + 1 + 1 < 21; omega)
    have h3 : code[s3.pc]? = some (.add registers.tmp toutBase registers.value) := by rw [hpc3, hpc2, hpc1]; rfl
    obtain ⟨s4, hs4, hpc4, h4t, h4o, hd4⟩ :=
      step_add_at (input := input) h3 (by rw [hpc3, hpc2, hpc1]; change 14 + 1 + 1 + 1 < 21; omega)
    have h4tVal : (reg s4 registers.tmp).val = 6 * Q + entryFn v := by
      have h3to : (reg s3 toutBase).val = 6 * Q := by
        rw [h3o toutBase (fin_ne_of_val (by decide)), h2o toutBase (fin_ne_of_val (by decide))]; exact hTout
      have h3v' : (reg s3 registers.value).val = entryFn v := by rw [h3v]
      rw [h4t, add_no_wrap _ _ (by rw [h3to, h3v']; omega), h3to, h3v']
    have hFit4 : (reg s4 registers.tmp).val < s4.data.size := by rw [h4tVal, hd4, hd3, hd2, hSz]; omega
    have h4 : code[s4.pc]? = some (.storeData registers.tmp registers.ptr) := by rw [hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s5, hs5, hpc5, hr5, hd5⟩ :=
      step_storeData_exists (input := input) h4 hFit4 (by rw [hpc4, hpc3, hpc2, hpc1]; change 14 + 1 + 1 + 1 + 1 < 21; omega)
    have h5p : (reg s5 registers.ptr).val = v := by
      rw [reg_eq_of_regs_eq hr5, h4o registers.ptr (fin_ne_of_val (by decide)),
          h3o registers.ptr (fin_ne_of_val (by decide)), h2o registers.ptr (fin_ne_of_val (by decide))]; exact hPtr
    have h5o : (reg s5 registers.one).val = 1 := by
      rw [reg_eq_of_regs_eq hr5, h4o registers.one (fin_ne_of_val (by decide)),
          h3o registers.one (fin_ne_of_val (by decide)), h2o registers.one (fin_ne_of_val (by decide))]; exact ho
    have h5 : code[s5.pc]? = some (.add registers.ptr registers.ptr registers.one) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s6, hs6, hpc6, h6p, h6o, hd6⟩ :=
      step_add_at (input := input) h5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; change 14 + 1 + 1 + 1 + 1 + 1 < 21; omega)
    have h6 : code[s6.pc]? = some (.goto 13) := by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    have hs67 := step_goto_at (input := input) h6 (by change 13 < 21; omega)
    let s7 : State DomL := { s6 with pc := 13 }
    have h7Sz : s7.data.size = workCap := by change s6.data.size = workCap; rw [s6.data_size]
    have h7reg : ∀ r, r ≠ registers.ptr → r ≠ registers.value → r ≠ registers.tmp → reg s7 r = reg s r := by
      intro r hrp hrv hrt
      change reg s6 r = reg s r
      rw [h6o r hrp, reg_eq_of_regs_eq hr5, h4o r hrt, h3o r hrv, h2o r hrt]; rfl
    have h7p : (reg s7 registers.ptr).val = v + 1 := by
      change (reg s6 registers.ptr).val = _
      rw [h6p, add_no_wrap _ _ (by rw [h5p, h5o]; omega), h5p, h5o]
    have h7data_ne : ∀ j, j ≠ 6 * Q + entryFn v → s7.data[j]? = s.data[j]? := fun j hne => by
      change s6.data[j]? = s.data[j]?
      rw [hd6, hd5, Array.getElem?_set_ne _ (by rw [h4tVal]; exact fun e => hne e.symm), hd4, hd3, hd2]
    have h7data_at : (s7.data[6 * Q + entryFn v]?).map Fin.val = some v := by
      change (s6.data[6 * Q + entryFn v]?).map Fin.val = _
      rw [hd6, hd5]
      have he : 6 * Q + entryFn v = (reg s4 registers.tmp).val := h4tVal.symm
      simp only [he, Array.getElem?_set_self, Option.map_some]
      rw [congrArg Fin.val (h4o registers.ptr (fin_ne_of_val (by decide))),
          congrArg Fin.val (h3o registers.ptr (fin_ne_of_val (by decide))),
          congrArg Fin.val (h2o registers.ptr (fin_ne_of_val (by decide)))]
      exact congrArg some hPtr
    have h7Ent : ∀ u, u < Q → (s7.data[4 * Q + u]?).map Fin.val = some (entryFn u) := fun u hu => by
      rw [h7data_ne (4 * Q + u) (by omega)]; exact hEnt u hu
    obtain ⟨t, htSteps, htpc, htSz, htz, hto, htc, htInv, htFrame⟩ :=
      ih (v + 1) s7 rfl (by omega) h7Sz
        (by rw [h7reg registers.zero (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hz)
        (by rw [h7reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h7reg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hc)
        (by rw [h7reg tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTin)
        (by rw [h7reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout)
        h7p h7Ent
    have hStepOne : Steps code input 7 s s7 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs67 (.zero _)))))))
    refine ⟨t, by simpa only [show 7 + (7 * rem + 1) = 7 * (rem + 1) + 1 by omega] using hStepOne.append htSteps,
      htpc, htSz, htz, hto, htc, ?_, ?_⟩
    · intro u hu1 hu2
      by_cases huEq : u = v
      · subst u
        have hKeep : ∀ u', v + 1 ≤ u' → u' < Q → 6 * Q + entryFn v ≠ 6 * Q + entryFn u' := by
          intro u' hu1' hu2' hEqE
          have hE : entryFn v = entryFn u' := by omega
          have hVu := hEntryInj v u' hvLt hu2' hE
          omega
        rw [htFrame (6 * Q + entryFn v) hKeep, h7data_at]
      · exact htInv u (by omega) hu2
    · intro j hj
      exact (htFrame j (fun u hu1 hu2 => hj u (by omega) hu2)).trans (h7data_ne j (hj v (Nat.le_refl _) hvLt))

theorem run_denseOfEntry {input : Input DomL} {Q : Nat}
    (entryFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hEntryRange : ∀ v, v < Q → entryFn v < Q)
    (hEntryInj : ∀ u₁ u₂, u₁ < Q → u₂ < Q → entryFn u₁ = entryFn u₂ → u₁ = u₂)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hEnt : ∀ u, u < Q → (s.data[4 * Q + u]?).map Fin.val = some (entryFn u)) :
    ∃ t : State DomL,
      run (denseOfEntryPhase hi hw).code input (7 * Q + 15) (Phase.initial s) = some ⟨t, 7 * Q + 15⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (∀ u, u < Q → (t.data[6 * Q + entryFn u]?).map Fin.val = some u) ∧
      (∀ j, (j < 6 * Q ∨ 7 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  let p := denseOfEntryPhase hi hw
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = 21 := rfl
  have hPlPre : Placed p.code 0
      (mulAddInstrs tinBase count registers.one 4 0 ++
       mulAddInstrs toutBase count registers.one 6 0) :=
    placed_append_self_left
      (mulAddInstrs tinBase count registers.one 4 0 ++
       mulAddInstrs toutBase count registers.one 6 0) _
  have hPl1 : Placed p.code 0 (mulAddInstrs tinBase count registers.one 4 0) :=
    placed_append_left hPlPre
  have hPl2 : Placed p.code 5 (mulAddInstrs toutBase count registers.one 6 0) := by
    have h := placed_append_right hPlPre
    simpa only [Nat.zero_add, mulAddInstrs_length] using h
  have hAt12 : p.code[12]? = some (.imm registers.ptr ⟨0, Nat.one_le_two_pow⟩) := rfl
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have ho0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, hTin1, ho1⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz]; omega) hPl1 hc0 ho0 (by omega)
  have hpc1' : s1.pc = 5 := by rw [hpc1]
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have ho1' : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), ho0]
  obtain ⟨s2, hs2, hpc2, hd2, hTout2, ho2⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 hpc1' (by rw [hSz]; omega) hPl2 hc1 ho1' (by omega)
  have hpc2' : s2.pc = 12 := by rw [hpc2]
  obtain ⟨s3, hs3, hpc3, h3p, ho3, hd3⟩ :=
    step_imm_at (input := input) (by rw [hpc2']; exact hAt12) (by rw [hpc2', hSz]; omega)
  have hpc3' : s3.pc = 13 := by rw [hpc3, hpc2']
  have hz3 : (reg s3 registers.zero).val = 0 := by
    rw [ho3 registers.zero (fin_ne_of_val (by decide)), ho2 registers.zero (fin_ne_of_val (by decide)),
        ho1 registers.zero (fin_ne_of_val (by decide)), initial_reg]; exact hz
  have ho3' : (reg s3 registers.one).val = 1 := by
    rw [ho3 registers.one (fin_ne_of_val (by decide)), ho2 registers.one (fin_ne_of_val (by decide))]; exact ho1'
  have hc3 : (reg s3 count).val = Q := by rw [ho3 count (fin_ne_of_val (by decide)), ho2 count (fin_ne_of_val (by decide))]; exact hc1
  have hTin3 : (reg s3 tinBase).val = 4 * Q := by
    rw [ho3 tinBase (fin_ne_of_val (by decide)), ho2 tinBase (fin_ne_of_val (by decide)), hTin1, Nat.add_zero]
  have hTout3 : (reg s3 toutBase).val = 6 * Q := by rw [ho3 toutBase (fin_ne_of_val (by decide)), hTout2, Nat.add_zero]
  have hd3Eq : s3.data = s.data := by rw [hd3, hd2, hd1, initial_data]
  obtain ⟨t, htSteps, htpc, _, htz, hto, htc, htInv, htFrame⟩ :=
    denseOfEntry_iter entryFn hQFit hWork hEntryRange hEntryInj Q 0 s3 hpc3' (by omega)
      (by rw [hd3Eq, s.data_size]) hz3 ho3' hc3 hTin3 hTout3 (by rw [h3p])
      (fun u hu => by rw [hd3Eq]; exact hEnt u hu)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at; rw [htpc]; rfl
  have hAllSteps : Steps p.code input (7 * Q + 14) s0 t := by
    have hSetupSteps : Steps p.code input 13 s0 s3 :=
      (hs1.append hs2).append (Steps.cons hs3 (.zero _))
    simpa only [show 13 + (7 * Q + 1) = 7 * Q + 14 by omega] using hSetupSteps.append htSteps
  refine ⟨t, by simpa only [show 7 * Q + 14 + 1 = 7 * Q + 15 by omega] using hAllSteps.halts hHalt,
    htz, hto, htc, fun u hu => htInv u (Nat.zero_le _) hu, fun j hj => ?_⟩
  rw [htFrame j (fun u _ hu => by have := hEntryRange u hu; omega), hd3Eq]

/-! ### Pass 2C.2: `heavy` (`[2*Q .. 3*Q)`) -/

def heavyScanAux (szFn childFn : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat
  | _, 0, bestC, _ => bestC
  | j, rem + 1, bestC, bestS =>
    let c := childFn j
    let sz := szFn c
    if bestS < sz then heavyScanAux szFn childFn (j + 1) rem c sz
    else heavyScanAux szFn childFn (j + 1) rem bestC bestS

def heavySpec (Q : Nat) (startFn entryFn stopFn childFn : Nat → Nat) (u : Nat) : Nat :=
  let lo := startFn u
  let hi := startFn (u + 1)
  heavyScanAux (fun c => stopFn c - entryFn c) childFn lo (hi - lo) Q 0

def heavyPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) := (heavyInstrs (bits := bits)).toArray
  Phase.ofLast code 53 rfl rfl rfl

private theorem heavyInner_iter {input : Input DomL} {Q hiB : Nat}
    (entryFn stopFn childFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (_hWork : 17 * Q ≤ workCap)
    (hHiLe : hiB ≤ Q - 1)
    (hChild : ∀ j, j < hiB → childFn j < Q ∧ entryFn (childFn j) ≤ stopFn (childFn j) ∧ stopFn (childFn j) ≤ Q) :
    ∀ (rem j bestC bestS : Nat) (s : State DomL),
      s.pc = 36 →
      hiB = j + rem →
      s.data.size = workCap →
      (reg s registers.one).val = 1 →
      (reg s count).val = Q →
      (reg s toutBase).val = 4 * Q →
      (reg s childrenBase).val = 10 * Q + 1 →
      (reg s registers.remain).val = j →
      (reg s clk).val = hiB →
      (reg s cmd).val = bestC →
      (reg s registers.childBase).val = bestS →
      (∀ k, k < hiB → (s.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k)) →
      (∀ c, c < Q → (s.data[4 * Q + c]?).map Fin.val = some (entryFn c)) →
      (∀ c, c < Q → (s.data[5 * Q + c]?).map Fin.val = some (stopFn c)) →
      ∃ t w,
        w ≤ 13 * rem + 1 ∧
        Steps (heavyPhase hi hw).code input w s t ∧
        t.pc = 49 ∧
        t.data = s.data ∧
        (reg t cmd).val = heavyScanAux (fun c => stopFn c - entryFn c) childFn j rem bestC bestS ∧
        (∀ r, r ≠ registers.remain → r ≠ registers.tmp → r ≠ registers.value →
            r ≠ offsetBase → r ≠ cmd → r ≠ registers.childBase → reg t r = reg s r) := by
  intro rem
  induction rem with
  | zero =>
    intro j bestC bestS s hpc hEq hSz ho hc hTout hCh hRem hClk hCmd hCB _ _ _
    let code := (heavyPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt registers.remain clk 37 49) := by rw [hpc]; rfl
    have hFalse : ltb (reg s registers.remain) (reg s clk) = false := by
      cases hC : ltb (reg s registers.remain) (reg s clk) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hRem, hClk] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 37 else 49) < 54; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s registers.remain) (reg s clk) = true then 37 else 49 }
    refine ⟨t, 1, by omega, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      rfl, by rw [← hCmd]; rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    intro j bestC bestS s hpc hEq hSz ho hc hTout hCh hRem hClk hCmd hCB hCData hEData hSData
    let code := (heavyPhase hi hw).code
    have hjLt : j < hiB := by omega
    obtain ⟨hcLt, heLe, hsLe⟩ := hChild j hjLt
    have h0 : code[s.pc]? = some (.branchLt registers.remain clk 37 49) := by rw [hpc]; rfl
    have hTrue : ltb (reg s registers.remain) (reg s clk) = true :=
      (ltb_eq_true _ _).mpr (by rw [hRem, hClk]; exact hjLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 37 else 49) < 54; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s registers.remain) (reg s clk) = true then 37 else 49 }
    have hpc1 : s1.pc = 37 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp childrenBase registers.remain) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 37 + 1 < 54; omega)
    have h2tVal : (reg s2 registers.tmp).val = 10 * Q + 1 + j := by
      rw [h2t, add_no_wrap _ _ (by change (reg s childrenBase).val + (reg s registers.remain).val < 2 ^ bits; rw [hCh, hRem]; omega)]
      change (reg s childrenBase).val + (reg s registers.remain).val = _; rw [hCh, hRem]
    have hwChild : s2.data[(reg s2 registers.tmp).val]? = some ⟨childFn j, by omega⟩ := by
      rw [h2tVal, hd2]
      have hCj := hCData j hjLt
      cases hC : s.data[10 * Q + 1 + j]? with
      | none => rw [hC] at hCj; cases hCj
      | some w => rw [hC, Option.map_some] at hCj; congr 1; exact Fin.ext (Option.some.inj hCj)
    have h2 : code[s2.pc]? = some (.loadData registers.value registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3v, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwChild (by rw [hpc2, hpc1]; change 37 + 1 + 1 < 54; omega)
    have h3 : code[s3.pc]? = some (.add registers.tmp toutBase registers.value) := by rw [hpc3, hpc2, hpc1]; rfl
    obtain ⟨s4, hs4, hpc4, h4t, h4o, hd4⟩ :=
      step_add_at (input := input) h3 (by rw [hpc3, hpc2, hpc1]; change 37 + 1 + 1 + 1 < 54; omega)
    have h4tVal : (reg s4 registers.tmp).val = 4 * Q + childFn j := by
      have h3to : (reg s3 toutBase).val = 4 * Q := by
        rw [h3o toutBase (fin_ne_of_val (by decide)), h2o toutBase (fin_ne_of_val (by decide))]; exact hTout
      have h3v' : (reg s3 registers.value).val = childFn j := by rw [h3v]
      rw [h4t, add_no_wrap _ _ (by rw [h3to, h3v']; omega), h3to, h3v']
    have hwEnt : s4.data[(reg s4 registers.tmp).val]? = some ⟨entryFn (childFn j), by omega⟩ := by
      rw [h4tVal, hd4, hd3, hd2]
      have hEv := hEData (childFn j) hcLt
      cases hC : s.data[4 * Q + childFn j]? with
      | none => rw [hC] at hEv; cases hEv
      | some w => rw [hC, Option.map_some] at hEv; congr 1; exact Fin.ext (Option.some.inj hEv)
    have h4 : code[s4.pc]? = some (.loadData offsetBase registers.tmp) := by rw [hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s5, hs5, hpc5, h5ob, h5o, hd5⟩ :=
      step_loadData_at (input := input) h4 hwEnt (by rw [hpc4, hpc3, hpc2, hpc1]; change 37 + 1 + 1 + 1 + 1 < 54; omega)
    have h5 : code[s5.pc]? = some (.add registers.tmp registers.tmp count) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s6, hs6, hpc6, h6t, h6o, hd6⟩ :=
      step_add_at (input := input) h5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; change 37 + 1 + 1 + 1 + 1 + 1 < 54; omega)
    have h6tVal : (reg s6 registers.tmp).val = 5 * Q + childFn j := by
      have h5t : (reg s5 registers.tmp).val = 4 * Q + childFn j := by
        rw [h5o registers.tmp (fin_ne_of_val (by decide)), h4tVal]
      have h5c : (reg s5 count).val = Q := by
        rw [h5o count (fin_ne_of_val (by decide)), h4o count (fin_ne_of_val (by decide)),
            h3o count (fin_ne_of_val (by decide)), h2o count (fin_ne_of_val (by decide))]; exact hc
      rw [h6t, add_no_wrap _ _ (by rw [h5t, h5c]; omega), h5t, h5c]; omega
    have hwStop : s6.data[(reg s6 registers.tmp).val]? = some ⟨stopFn (childFn j), by omega⟩ := by
      rw [h6tVal, hd6, hd5, hd4, hd3, hd2]
      have hSv := hSData (childFn j) hcLt
      cases hC : s.data[5 * Q + childFn j]? with
      | none => rw [hC] at hSv; cases hSv
      | some w => rw [hC, Option.map_some] at hSv; congr 1; exact Fin.ext (Option.some.inj hSv)
    have h6 : code[s6.pc]? = some (.loadData registers.tmp registers.tmp) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s7, hs7, hpc7, h7t, h7o, hd7⟩ :=
      step_loadData_at (input := input) h6 hwStop (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 37 + 1 + 1 + 1 + 1 + 1 + 1 < 54; omega)
    have h7 : code[s7.pc]? = some (.sub registers.tmp registers.tmp offsetBase) := by
      rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s8, hs8, hpc8, h8t, h8o, hd8⟩ :=
      step_sub_at (input := input) h7 (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 37 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 54; omega)
    have h8tVal : (reg s8 registers.tmp).val = stopFn (childFn j) - entryFn (childFn j) := by
      have h7ob : (reg s7 offsetBase).val = entryFn (childFn j) := by
        rw [h7o offsetBase (fin_ne_of_val (by decide)), h6o offsetBase (fin_ne_of_val (by decide)), h5ob]
      have h7tVal : (reg s7 registers.tmp).val = stopFn (childFn j) := by rw [h7t]
      rw [h8t, PaperB.RamDomBuild.sub_exact_word _ _ (by rw [h7ob, h7tVal]; exact heLe), h7tVal, h7ob]
    have h8 : code[s8.pc]? = some (.branchLt registers.childBase registers.tmp 45 47) := by
      rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    have hs89 := step_branchLt_at (input := input) h8 (by change (if _ then 45 else 47) < 54; split <;> omega)
    have h8cb : (reg s8 registers.childBase).val = bestS := by
      rw [h8o registers.childBase (fin_ne_of_val (by decide)), h7o registers.childBase (fin_ne_of_val (by decide)),
          h6o registers.childBase (fin_ne_of_val (by decide)), h5o registers.childBase (fin_ne_of_val (by decide)),
          h4o registers.childBase (fin_ne_of_val (by decide)), h3o registers.childBase (fin_ne_of_val (by decide)),
          h2o registers.childBase (fin_ne_of_val (by decide))]; exact hCB
    have h8cmd : (reg s8 cmd).val = bestC := by
      rw [h8o cmd (fin_ne_of_val (by decide)), h7o cmd (fin_ne_of_val (by decide)),
          h6o cmd (fin_ne_of_val (by decide)), h5o cmd (fin_ne_of_val (by decide)),
          h4o cmd (fin_ne_of_val (by decide)), h3o cmd (fin_ne_of_val (by decide)),
          h2o cmd (fin_ne_of_val (by decide))]; exact hCmd
    have h8val : (reg s8 registers.value).val = childFn j := by
      rw [h8o registers.value (fin_ne_of_val (by decide)), h7o registers.value (fin_ne_of_val (by decide)),
          h6o registers.value (fin_ne_of_val (by decide)), h5o registers.value (fin_ne_of_val (by decide)),
          h4o registers.value (fin_ne_of_val (by decide)), h3v]
    have h8rem : (reg s8 registers.remain).val = j := by
      rw [h8o registers.remain (fin_ne_of_val (by decide)), h7o registers.remain (fin_ne_of_val (by decide)),
          h6o registers.remain (fin_ne_of_val (by decide)), h5o registers.remain (fin_ne_of_val (by decide)),
          h4o registers.remain (fin_ne_of_val (by decide)), h3o registers.remain (fin_ne_of_val (by decide)),
          h2o registers.remain (fin_ne_of_val (by decide))]; exact hRem
    have h8one : (reg s8 registers.one).val = 1 := by
      rw [h8o registers.one (fin_ne_of_val (by decide)), h7o registers.one (fin_ne_of_val (by decide)),
          h6o registers.one (fin_ne_of_val (by decide)), h5o registers.one (fin_ne_of_val (by decide)),
          h4o registers.one (fin_ne_of_val (by decide)), h3o registers.one (fin_ne_of_val (by decide)),
          h2o registers.one (fin_ne_of_val (by decide))]; exact ho
    have h8regOther : ∀ r, r ≠ registers.remain → r ≠ registers.tmp → r ≠ registers.value →
        r ≠ offsetBase → r ≠ cmd → r ≠ registers.childBase → reg s8 r = reg s r := by
      intro r hr1 hr2 hr3 hr4 hr5 hr6
      rw [h8o r hr2, h7o r hr2, h6o r hr2, h5o r hr4, h4o r hr2, h3o r hr3, h2o r hr2]; rfl
    have h8data : s8.data = s.data := by rw [hd8, hd7, hd6, hd5, hd4, hd3, hd2]
    let s9 : State DomL := { s8 with pc := if ltb (reg s8 registers.childBase) (reg s8 registers.tmp) = true then 45 else 47 }
    let nextC := if bestS < stopFn (childFn j) - entryFn (childFn j) then childFn j else bestC
    let nextS := if bestS < stopFn (childFn j) - entryFn (childFn j) then stopFn (childFn j) - entryFn (childFn j) else bestS
    have hPreMerge : ∃ s11 : State DomL, ∃ wSub, wSub ≤ 2 ∧
        Steps code input wSub s9 s11 ∧
        s11.pc = 47 ∧ s11.data = s.data ∧
        (reg s11 cmd).val = nextC ∧ (reg s11 registers.childBase).val = nextS ∧
        (reg s11 registers.remain).val = j ∧ (reg s11 registers.one).val = 1 ∧
        (∀ r, r ≠ registers.remain → r ≠ registers.tmp → r ≠ registers.value →
            r ≠ offsetBase → r ≠ cmd → r ≠ registers.childBase → reg s11 r = reg s r) := by
      by_cases hLt : bestS < stopFn (childFn j) - entryFn (childFn j)
      · have hBr : ltb (reg s8 registers.childBase) (reg s8 registers.tmp) = true :=
          (ltb_eq_true _ _).mpr (by rw [h8cb, h8tVal]; exact hLt)
        have hpc9 : s9.pc = 45 := by simp only [s9, hBr, ite_true]
        have h9 : code[s9.pc]? = some (.mov cmd registers.value) := by rw [hpc9]; rfl
        obtain ⟨s10, hs10, hpc10, h10c, h10o, hd10⟩ := step_mov_at (input := input) h9 (by rw [hpc9]; change 45 + 1 < 54; omega)
        have h10 : code[s10.pc]? = some (.mov registers.childBase registers.tmp) := by rw [hpc10, hpc9]; rfl
        obtain ⟨s11, hs11, hpc11, h11cb, h11o, hd11⟩ := step_mov_at (input := input) h10 (by rw [hpc10, hpc9]; change 45 + 1 + 1 < 54; omega)
        refine ⟨s11, 2, by omega, Steps.cons hs10 (Steps.cons hs11 (.zero _)), by rw [hpc11, hpc10, hpc9],
          by rw [hd11, hd10, h8data], ?_, ?_, ?_, ?_, ?_⟩
        · have h9val : (reg s9 registers.value).val = childFn j := h8val
          have h10c' : (reg s10 cmd).val = childFn j := by rw [congrArg Fin.val h10c, h9val]
          simp only [nextC, hLt, ite_true, congrArg Fin.val (h11o cmd (fin_ne_of_val (by decide))), h10c']
        · have h9t : (reg s9 registers.tmp).val = stopFn (childFn j) - entryFn (childFn j) := h8tVal
          have h10t' : (reg s10 registers.tmp).val = stopFn (childFn j) - entryFn (childFn j) := by
            rw [congrArg Fin.val (h10o registers.tmp (fin_ne_of_val (by decide))), h9t]
          simp only [nextS, hLt, ite_true, congrArg Fin.val h11cb, h10t']
        · rw [congrArg Fin.val (h11o registers.remain (fin_ne_of_val (by decide))),
              congrArg Fin.val (h10o registers.remain (fin_ne_of_val (by decide)))]; exact h8rem
        · rw [congrArg Fin.val (h11o registers.one (fin_ne_of_val (by decide))),
              congrArg Fin.val (h10o registers.one (fin_ne_of_val (by decide)))]; exact h8one
        · intro r hr1 hr2 hr3 hr4 hr5 hr6
          rw [h11o r hr6, h10o r hr5]; exact h8regOther r hr1 hr2 hr3 hr4 hr5 hr6
      · have hBr : ltb (reg s8 registers.childBase) (reg s8 registers.tmp) = false := by
          cases hC : ltb (reg s8 registers.childBase) (reg s8 registers.tmp) with
          | false => rfl
          | true => have := (ltb_eq_true _ _).mp hC; rw [h8cb, h8tVal] at this; exact False.elim (hLt this)
        have hpc9 : s9.pc = 47 := by simp only [s9, hBr, Bool.false_eq_true, ite_false]
        refine ⟨s9, 0, by omega, .zero _, hpc9, h8data, ?_, ?_, h8rem, h8one, h8regOther⟩
        · simp only [nextC, hLt, ite_false]; exact h8cmd
        · simp only [nextS, hLt, ite_false]; exact h8cb
    obtain ⟨s11, wSub, hwSub, hsSub, hpc11, hd11, h11c, h11cb, h11rem, h11one, h11reg⟩ := hPreMerge
    have h11 : code[s11.pc]? = some (.add registers.remain registers.remain registers.one) := by rw [hpc11]; rfl
    obtain ⟨s12, hs12, hpc12, h12rem, h12o, hd12⟩ :=
      step_add_at (input := input) h11 (by rw [hpc11]; change 47 + 1 < 54; omega)
    have h12 : code[s12.pc]? = some (.goto 36) := by rw [hpc12, hpc11]; rfl
    have hs1213 := step_goto_at (input := input) h12 (by change 36 < 54; omega)
    let s13 : State DomL := { s12 with pc := 36 }
    have h13Sz : s13.data.size = workCap := by change s12.data.size = workCap; rw [s12.data_size]
    have h13rem : (reg s13 registers.remain).val = j + 1 := by
      change (reg s12 registers.remain).val = _
      rw [h12rem, add_no_wrap _ _ (by rw [h11rem, h11one]; omega), h11rem, h11one]
    have h13reg : ∀ r, r ≠ registers.remain → r ≠ registers.tmp → r ≠ registers.value →
        r ≠ offsetBase → r ≠ cmd → r ≠ registers.childBase → reg s13 r = reg s r := by
      intro r hr1 hr2 hr3 hr4 hr5 hr6
      change reg s12 r = reg s r
      rw [h12o r hr1]; exact h11reg r hr1 hr2 hr3 hr4 hr5 hr6
    have h13cmd : (reg s13 cmd).val = nextC := by
      change (reg s12 cmd).val = _
      rw [h12o cmd (fin_ne_of_val (by decide)), h11c]
    have h13cb : (reg s13 registers.childBase).val = nextS := by
      change (reg s12 registers.childBase).val = _
      rw [h12o registers.childBase (fin_ne_of_val (by decide)), h11cb]
    have h13data : s13.data = s.data := by change s12.data = s.data; rw [hd12, hd11]
    obtain ⟨t, wTail, hwTail, htSteps, htpc, htdata, htcmd, htreg⟩ :=
      ih (j + 1) nextC nextS s13 rfl (by omega) (by rw [h13data, hSz])
        (by rw [h13reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h13reg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hc)
        (by rw [h13reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout)
        (by rw [h13reg childrenBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hCh)
        h13rem
        (by rw [h13reg clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hClk)
        h13cmd h13cb
        (fun k hk => by rw [h13data]; exact hCData k hk)
        (fun c hcu => by rw [h13data]; exact hEData c hcu)
        (fun c hcu => by rw [h13data]; exact hSData c hcu)
    have hPreSteps : Steps code input 9 s s9 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
        (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs89 (.zero _)))))))))
    have hOneIter : Steps code input (9 + wSub + 2) s s13 :=
      (hPreSteps.append hsSub).append (Steps.cons hs12 (Steps.cons hs1213 (.zero _)))
    refine ⟨t, (9 + wSub + 2) + wTail, by omega, hOneIter.append htSteps, htpc,
      by rw [htdata, h13data], ?_, fun r hr1 hr2 hr3 hr4 hr5 hr6 =>
        (htreg r hr1 hr2 hr3 hr4 hr5 hr6).trans (h13reg r hr1 hr2 hr3 hr4 hr5 hr6)⟩
    rw [htcmd]
    simp only [heavyScanAux, nextC, nextS]
    split <;> rfl

private theorem heavyOuter_iter {input : Input DomL} {Q : Nat}
    (startFn entryFn stopFn childFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hStartMono : ∀ u, u < Q → startFn u ≤ startFn (u + 1))
    (hStartEnd : startFn Q = Q - 1)
    (hChild : ∀ j, j < Q - 1 → childFn j < Q ∧ entryFn (childFn j) ≤ stopFn (childFn j) ∧ stopFn (childFn j) ≤ Q) :
    ∀ (rem v : Nat) (s : State DomL),
      s.pc = 29 →
      Q = v + rem →
      s.data.size = workCap →
      (reg s registers.zero).val = 0 →
      (reg s registers.one).val = 1 →
      (reg s count).val = Q →
      (reg s tinBase).val = 2 * Q →
      (reg s toutBase).val = 4 * Q →
      (reg s registers.stackBase).val = 7 * Q →
      (reg s childrenBase).val = 10 * Q + 1 →
      (reg s registers.ptr).val = v →
      (∀ u, u ≤ Q → (s.data[7 * Q + u]?).map Fin.val = some (startFn u)) →
      (∀ k, k < Q - 1 → (s.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k)) →
      (∀ c, c < Q → (s.data[4 * Q + c]?).map Fin.val = some (entryFn c)) →
      (∀ c, c < Q → (s.data[5 * Q + c]?).map Fin.val = some (stopFn c)) →
      ∃ t w,
        w ≤ 13 * rem + 13 * (Q - 1 - startFn v) + 1 ∧
        Steps (heavyPhase hi hw).code input w s t ∧
        t.pc = 53 ∧
        (reg t registers.zero).val = 0 ∧
        (reg t registers.one).val = 1 ∧
        (reg t count).val = Q ∧
        (∀ u, v ≤ u → u < Q → (t.data[2 * Q + u]?).map Fin.val = some (heavySpec Q startFn entryFn stopFn childFn u)) ∧
        (∀ j, (j < 2 * Q + v ∨ 3 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro v s hpc hEq hSz hz ho hc hTin hTout hSb hCh hPtr _ _ _ _
    let code := (heavyPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 30 53) := by rw [hpc]; rfl
    have hFalse : ltb (reg s registers.ptr) (reg s count) = false := by
      cases hC : ltb (reg s registers.ptr) (reg s count) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hPtr, hc] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 30 else 53) < 54; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 30 else 53 }
    refine ⟨t, 1, by omega, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      hz, ho, hc, fun u hu1 hu2 => by omega, fun _ _ => rfl⟩
  | succ rem ih =>
    intro v s hpc hEq hSz hz ho hc hTin hTout hSb hCh hPtr hStData hCData hEData hSData
    let code := (heavyPhase hi hw).code
    have hvLt : v < Q := by omega
    have hStartMonoRange : ∀ a b, a ≤ b → b ≤ Q → startFn a ≤ startFn b := by
      intro a b hab hb
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      induction d with
      | zero => simp
      | succ d ihd => exact Nat.le_trans (ihd (by omega) (by omega)) (hStartMono _ (by omega))
    have hLoHi : startFn v ≤ startFn (v + 1) := hStartMono v hvLt
    have hHiEnd : startFn (v + 1) ≤ Q - 1 := by
      have := hStartMonoRange (v + 1) Q (by omega) (Nat.le_refl Q)
      omega
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 30 53) := by rw [hpc]; rfl
    have hTrue : ltb (reg s registers.ptr) (reg s count) = true :=
      (ltb_eq_true _ _).mpr (by rw [hPtr, hc]; exact hvLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 30 else 53) < 54; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 30 else 53 }
    have hpc1 : s1.pc = 30 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp registers.stackBase registers.ptr) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 30 + 1 < 54; omega)
    have h2tVal : (reg s2 registers.tmp).val = 7 * Q + v := by
      rw [h2t, add_no_wrap _ _ (by change (reg s registers.stackBase).val + (reg s registers.ptr).val < 2 ^ bits; rw [hSb, hPtr]; omega)]
      change (reg s registers.stackBase).val + (reg s registers.ptr).val = _; rw [hSb, hPtr]
    have hwLo : s2.data[(reg s2 registers.tmp).val]? = some ⟨startFn v, by omega⟩ := by
      rw [h2tVal, hd2]
      have hLv := hStData v (by omega)
      cases hC : s.data[7 * Q + v]? with
      | none => rw [hC] at hLv; cases hLv
      | some w => rw [hC, Option.map_some] at hLv; congr 1; exact Fin.ext (Option.some.inj hLv)
    have h2 : code[s2.pc]? = some (.loadData registers.remain registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3rem, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwLo (by rw [hpc2, hpc1]; change 30 + 1 + 1 < 54; omega)
    have h3 : code[s3.pc]? = some (.add registers.tmp registers.tmp registers.one) := by rw [hpc3, hpc2, hpc1]; rfl
    obtain ⟨s4, hs4, hpc4, h4t, h4o, hd4⟩ :=
      step_add_at (input := input) h3 (by rw [hpc3, hpc2, hpc1]; change 30 + 1 + 1 + 1 < 54; omega)
    have h4tVal : (reg s4 registers.tmp).val = 7 * Q + v + 1 := by
      have h3t : (reg s3 registers.tmp).val = 7 * Q + v := by
        rw [h3o registers.tmp (fin_ne_of_val (by decide)), h2tVal]
      have h3o' : (reg s3 registers.one).val = 1 := by
        rw [h3o registers.one (fin_ne_of_val (by decide)), h2o registers.one (fin_ne_of_val (by decide))]; exact ho
      rw [h4t, add_no_wrap _ _ (by rw [h3t, h3o']; omega), h3t, h3o']
    have hwHi : s4.data[(reg s4 registers.tmp).val]? = some ⟨startFn (v + 1), by omega⟩ := by
      rw [h4tVal, hd4, hd3, hd2, show 7 * Q + v + 1 = 7 * Q + (v + 1) by omega]
      have hHv := hStData (v + 1) (by omega)
      cases hC : s.data[7 * Q + (v + 1)]? with
      | none => rw [hC] at hHv; cases hHv
      | some w => rw [hC, Option.map_some] at hHv; congr 1; exact Fin.ext (Option.some.inj hHv)
    have h4 : code[s4.pc]? = some (.loadData clk registers.tmp) := by rw [hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s5, hs5, hpc5, h5clk, h5o, hd5⟩ :=
      step_loadData_at (input := input) h4 hwHi (by rw [hpc4, hpc3, hpc2, hpc1]; change 30 + 1 + 1 + 1 + 1 < 54; omega)
    have h5 : code[s5.pc]? = some (.mov cmd count) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s6, hs6, hpc6, h6cmd, h6o, hd6⟩ :=
      step_mov_at (input := input) h5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; change 30 + 1 + 1 + 1 + 1 + 1 < 54; omega)
    have h6 : code[s6.pc]? = some (.imm registers.childBase ⟨0, Nat.one_le_two_pow⟩) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s7, hs7, hpc7, h7cb, h7o, hd7⟩ :=
      step_imm_at (input := input) h6 (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 30 + 1 + 1 + 1 + 1 + 1 + 1 < 54; omega)
    have hpc7' : s7.pc = 36 := by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]
    have h7data : s7.data = s.data := by rw [hd7, hd6, hd5, hd4, hd3, hd2]
    have h7regPre : ∀ r, r ≠ registers.remain → r ≠ clk → r ≠ cmd → r ≠ registers.childBase → r ≠ registers.tmp →
        reg s7 r = reg s r := by
      intro r hr1 hr2 hr3 hr4 hr5
      rw [h7o r hr4, h6o r hr3, h5o r hr2, h4o r hr5, h3o r hr1, h2o r hr5]; rfl
    have h7rem : (reg s7 registers.remain).val = startFn v := by
      rw [h7o registers.remain (fin_ne_of_val (by decide)), h6o registers.remain (fin_ne_of_val (by decide)),
          h5o registers.remain (fin_ne_of_val (by decide)), h4o registers.remain (fin_ne_of_val (by decide)), h3rem]
    have h7clk : (reg s7 clk).val = startFn (v + 1) := by
      rw [h7o clk (fin_ne_of_val (by decide)), h6o clk (fin_ne_of_val (by decide)), h5clk]
    have h7cmd : (reg s7 cmd).val = Q := by
      rw [h7o cmd (fin_ne_of_val (by decide)), h6cmd,
          h5o count (fin_ne_of_val (by decide)), h4o count (fin_ne_of_val (by decide)),
          h3o count (fin_ne_of_val (by decide)), h2o count (fin_ne_of_val (by decide))]
      exact hc
    obtain ⟨s8, wIn, hwIn, hsIn, hpc8, hd8, h8cmd, h8reg⟩ :=
      heavyInner_iter entryFn stopFn childFn hQFit hWork hHiEnd (fun j hj => hChild j (by omega))
        (startFn (v + 1) - startFn v) (startFn v) Q 0 s7 hpc7' (by omega) (by rw [h7data, hSz])
        (by rw [h7regPre registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h7regPre count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hc)
        (by rw [h7regPre toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout)
        (by rw [h7regPre childrenBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hCh)
        h7rem h7clk h7cmd (by rw [h7cb])
        (fun k hk => by rw [h7data]; exact hCData k (by omega))
        (fun c hcu => by rw [h7data]; exact hEData c hcu)
        (fun c hcu => by rw [h7data]; exact hSData c hcu)
    have h8regCore : ∀ r, r ≠ registers.remain → r ≠ clk → r ≠ cmd → r ≠ registers.childBase →
        r ≠ registers.tmp → r ≠ registers.value → r ≠ offsetBase → reg s8 r = reg s r := by
      intro r hr1 hr2 hr3 hr4 hr5 hr6 hr7
      rw [h8reg r hr1 hr5 hr6 hr7 hr3 hr4, h7regPre r hr1 hr2 hr3 hr4 hr5]
    have h8 : code[s8.pc]? = some (.add registers.tmp tinBase registers.ptr) := by rw [hpc8]; rfl
    obtain ⟨s9, hs9, hpc9, h9t, h9o, hd9⟩ := step_add_at (input := input) h8 (by rw [hpc8]; change 49 + 1 < 54; omega)
    have h9tVal : (reg s9 registers.tmp).val = 2 * Q + v := by
      have h8tin : (reg s8 tinBase).val = 2 * Q := by
        rw [h8regCore tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTin
      have h8ptr : (reg s8 registers.ptr).val = v := by
        rw [h8regCore registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hPtr
      rw [h9t, add_no_wrap _ _ (by rw [h8tin, h8ptr]; omega), h8tin, h8ptr]
    have h8data : s8.data = s.data := hd8.trans h7data
    have hFit9 : (reg s9 registers.tmp).val < s9.data.size := by rw [h9tVal, hd9, h8data, hSz]; omega
    have h9 : code[s9.pc]? = some (.storeData registers.tmp cmd) := by rw [hpc9, hpc8]; rfl
    obtain ⟨s10, hs10, hpc10, hr10, hd10⟩ :=
      step_storeData_exists (input := input) h9 hFit9 (by rw [hpc9, hpc8]; change 49 + 1 + 1 < 54; omega)
    have h10p : (reg s10 registers.ptr).val = v := by
      rw [reg_eq_of_regs_eq hr10, h9o registers.ptr (fin_ne_of_val (by decide)),
          h8regCore registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hPtr
    have h10o : (reg s10 registers.one).val = 1 := by
      rw [reg_eq_of_regs_eq hr10, h9o registers.one (fin_ne_of_val (by decide)),
          h8regCore registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho
    have h10 : code[s10.pc]? = some (.add registers.ptr registers.ptr registers.one) := by rw [hpc10, hpc9, hpc8]; rfl
    obtain ⟨s11, hs11, hpc11, h11p, h11o, hd11⟩ :=
      step_add_at (input := input) h10 (by rw [hpc10, hpc9, hpc8]; change 49 + 1 + 1 + 1 < 54; omega)
    have h11 : code[s11.pc]? = some (.goto 29) := by rw [hpc11, hpc10, hpc9, hpc8]; rfl
    have hs1112 := step_goto_at (input := input) h11 (by change 29 < 54; omega)
    let s12 : State DomL := { s11 with pc := 29 }
    have h12Sz : s12.data.size = workCap := by change s11.data.size = workCap; rw [s11.data_size]
    have h12reg : ∀ r, r ≠ registers.ptr → r ≠ registers.remain → r ≠ clk → r ≠ cmd →
        r ≠ registers.childBase → r ≠ registers.tmp → r ≠ registers.value → r ≠ offsetBase →
        reg s12 r = reg s r := by
      intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
      change reg s11 r = reg s r
      rw [h11o r hr0, reg_eq_of_regs_eq hr10, h9o r hr5]
      exact h8regCore r hr1 hr2 hr3 hr4 hr5 hr6 hr7
    have h12p : (reg s12 registers.ptr).val = v + 1 := by
      change (reg s11 registers.ptr).val = _
      rw [h11p, add_no_wrap _ _ (by rw [h10p, h10o]; omega), h10p, h10o]
    have h12data_ne : ∀ j, j ≠ 2 * Q + v → s12.data[j]? = s.data[j]? := fun j hne => by
      change s11.data[j]? = s.data[j]?
      rw [hd11, hd10, Array.getElem?_set_ne _ (by rw [h9tVal]; exact fun e => hne e.symm), hd9, h8data]
    have h12data_at : (s12.data[2 * Q + v]?).map Fin.val = some (heavySpec Q startFn entryFn stopFn childFn v) := by
      change (s11.data[2 * Q + v]?).map Fin.val = _
      rw [hd11, hd10]
      have he : 2 * Q + v = (reg s9 registers.tmp).val := h9tVal.symm
      simp only [he, Array.getElem?_set_self, Option.map_some]
      rw [congrArg Fin.val (h9o cmd (fin_ne_of_val (by decide))), h8cmd]
      rfl
    obtain ⟨t, wTail, hwTail, htSteps, htpc, htz, hto, htc, htInv, htFrame⟩ :=
      ih (v + 1) s12 rfl (by omega) h12Sz
        (by rw [h12reg registers.zero (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hz)
        (by rw [h12reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h12reg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hc)
        (by rw [h12reg tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTin)
        (by rw [h12reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout)
        (by rw [h12reg registers.stackBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hSb)
        (by rw [h12reg childrenBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hCh)
        h12p
        (fun u hu => by rw [h12data_ne (7 * Q + u) (by omega)]; exact hStData u hu)
        (fun k hk => by rw [h12data_ne (10 * Q + 1 + k) (by omega)]; exact hCData k hk)
        (fun c hcu => by rw [h12data_ne (4 * Q + c) (by omega)]; exact hEData c hcu)
        (fun c hcu => by rw [h12data_ne (5 * Q + c) (by omega)]; exact hSData c hcu)
    have hPreOuter : Steps code input 7 s s7 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (.zero _)))))))
    have hPostOuter : Steps code input 4 s8 s12 :=
      Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs1112 (.zero _))))
    have hIterSteps : Steps code input ((7 + wIn + 4) + wTail) s t :=
      ((hPreOuter.append hsIn).append hPostOuter).append htSteps
    refine ⟨t, (7 + wIn + 4) + wTail, by omega, hIterSteps, htpc, htz, hto, htc, ?_, ?_⟩
    · intro u hu1 hu2
      by_cases huEq : u = v
      · subst u
        rw [htFrame (2 * Q + v) (by omega), h12data_at]
      · exact htInv u (by omega) hu2
    · intro j hj
      exact (htFrame j (by omega)).trans (h12data_ne j (by omega))

theorem run_heavy {input : Input DomL} {Q : Nat}
    (startFn entryFn stopFn childFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hStartMono : ∀ u, u < Q → startFn u ≤ startFn (u + 1))
    (hStartEnd : startFn Q = Q - 1)
    (hChild : ∀ j, j < Q - 1 → childFn j < Q ∧ entryFn (childFn j) ≤ stopFn (childFn j) ∧ stopFn (childFn j) ≤ Q)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hStData : ∀ u, u ≤ Q → (s.data[7 * Q + u]?).map Fin.val = some (startFn u))
    (hCData : ∀ k, k < Q - 1 → (s.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k))
    (hEData : ∀ c, c < Q → (s.data[4 * Q + c]?).map Fin.val = some (entryFn c))
    (hSData : ∀ c, c < Q → (s.data[5 * Q + c]?).map Fin.val = some (stopFn c)) :
    ∃ t w,
      w ≤ 26 * Q + 31 ∧
      run (heavyPhase hi hw).code input w (Phase.initial s) = some ⟨t, w⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (∀ u, u < Q → (t.data[2 * Q + u]?).map Fin.val = some (heavySpec Q startFn entryFn stopFn childFn u)) ∧
      (∀ j, (j < 2 * Q ∨ 3 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  let p := heavyPhase hi hw
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = 54 := rfl
  have hPlPre : Placed p.code 0
      (mulAddInstrs tinBase count registers.one 2 0 ++
       mulAddInstrs toutBase count registers.one 4 0 ++
       mulAddInstrs registers.stackBase count registers.one 7 0 ++
       mulAddInstrs childrenBase count registers.one 10 1) :=
    placed_append_self_left _ _
  have hPl1 : Placed p.code 0 (mulAddInstrs tinBase count registers.one 2 0) :=
    placed_append_left (placed_append_left (placed_append_left hPlPre))
  have hPl2 : Placed p.code 3 (mulAddInstrs toutBase count registers.one 4 0) := by
    have h := placed_append_right (placed_append_left (placed_append_left hPlPre))
    simpa only [Nat.zero_add, mulAddInstrs_length] using h
  have hPl3 : Placed p.code 8 (mulAddInstrs registers.stackBase count registers.one 7 0) := by
    have h := placed_append_right (placed_append_left hPlPre)
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hPl4 : Placed p.code 16 (mulAddInstrs childrenBase count registers.one 10 1) := by
    have h := placed_append_right hPlPre
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hAt28 : p.code[28]? = some (.imm registers.ptr ⟨0, Nat.one_le_two_pow⟩) := rfl
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have ho0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, hTin1, ho1⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz]; omega) hPl1 hc0 ho0 (by omega)
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have ho1' : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), ho0]
  obtain ⟨s2, hs2, hpc2, hd2, hTout2, ho2⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 (by rw [hpc1]) (by rw [hSz]; omega) hPl2 hc1 ho1' (by omega)
  have hc2 : (reg s2 count).val = Q := by rw [ho2 count (fin_ne_of_val (by decide)), hc1]
  have ho2' : (reg s2 registers.one).val = 1 := by rw [ho2 registers.one (fin_ne_of_val (by decide)), ho1']
  obtain ⟨s3, hs3, hpc3, hd3, hSb3, ho3⟩ :=
    run_mulAddInstrs (input := input) registers.stackBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s2 (by rw [hpc2]) (by rw [hSz]; omega) hPl3 hc2 ho2' (by omega)
  have hc3 : (reg s3 count).val = Q := by rw [ho3 count (fin_ne_of_val (by decide)), hc2]
  have ho3' : (reg s3 registers.one).val = 1 := by rw [ho3 registers.one (fin_ne_of_val (by decide)), ho2']
  obtain ⟨s4, hs4, hpc4, hd4, hCh4, ho4⟩ :=
    run_mulAddInstrs (input := input) childrenBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s3 (by rw [hpc3]) (by rw [hSz]; omega) hPl4 hc3 ho3' (by omega)
  obtain ⟨s5, hs5, hpc5, h5p, ho5, hd5⟩ :=
    step_imm_at (input := input) (by rw [hpc4]; exact hAt28) (by rw [hpc4, hSz]; omega)
  have hpc5' : s5.pc = 29 := by rw [hpc5, hpc4]
  have hd5Eq : s5.data = s.data := by rw [hd5, hd4, hd3, hd2, hd1, initial_data]
  have hz5 : (reg s5 registers.zero).val = 0 := by
    rw [ho5 registers.zero (fin_ne_of_val (by decide)), ho4 registers.zero (fin_ne_of_val (by decide)),
        ho3 registers.zero (fin_ne_of_val (by decide)), ho2 registers.zero (fin_ne_of_val (by decide)),
        ho1 registers.zero (fin_ne_of_val (by decide)), initial_reg]; exact hz
  have ho5' : (reg s5 registers.one).val = 1 := by
    rw [ho5 registers.one (fin_ne_of_val (by decide)), ho4 registers.one (fin_ne_of_val (by decide))]; exact ho3'
  have hc5 : (reg s5 count).val = Q := by rw [ho5 count (fin_ne_of_val (by decide)), ho4 count (fin_ne_of_val (by decide))]; exact hc3
  have hTin5 : (reg s5 tinBase).val = 2 * Q := by
    rw [ho5 tinBase (fin_ne_of_val (by decide)), ho4 tinBase (fin_ne_of_val (by decide)),
        ho3 tinBase (fin_ne_of_val (by decide)), ho2 tinBase (fin_ne_of_val (by decide)), hTin1, Nat.add_zero]
  have hTout5 : (reg s5 toutBase).val = 4 * Q := by
    rw [ho5 toutBase (fin_ne_of_val (by decide)), ho4 toutBase (fin_ne_of_val (by decide)),
        ho3 toutBase (fin_ne_of_val (by decide)), hTout2, Nat.add_zero]
  have hSb5 : (reg s5 registers.stackBase).val = 7 * Q := by
    rw [ho5 registers.stackBase (fin_ne_of_val (by decide)), ho4 registers.stackBase (fin_ne_of_val (by decide)),
        hSb3, Nat.add_zero]
  have hCh5 : (reg s5 childrenBase).val = 10 * Q + 1 := by
    rw [ho5 childrenBase (fin_ne_of_val (by decide)), hCh4]
  obtain ⟨t, wOut, hwOut, htSteps, htpc, htz, hto, htc, htInv, htFrame⟩ :=
    heavyOuter_iter startFn entryFn stopFn childFn hQFit hWork hStartMono hStartEnd hChild Q 0 s5 hpc5'
      (by omega) (by rw [hd5Eq, s.data_size]) hz5 ho5' hc5 hTin5 hTout5 hSb5 hCh5 (by rw [h5p])
      (fun u hu => by rw [hd5Eq]; exact hStData u hu)
      (fun k hk => by rw [hd5Eq]; exact hCData k hk)
      (fun c hcu => by rw [hd5Eq]; exact hEData c hcu)
      (fun c hcu => by rw [hd5Eq]; exact hSData c hcu)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at; rw [htpc]; rfl
  have hSetupSteps : Steps p.code input 29 s0 s5 :=
    (((hs1.append hs2).append hs3).append hs4).append (Steps.cons hs5 (.zero _))
  refine ⟨t, 29 + wOut + 1, by omega, (hSetupSteps.append htSteps).halts hHalt,
    htz, hto, htc, fun u hu => htInv u (Nat.zero_le _) hu, fun j hj => ?_⟩
  rw [htFrame j (by omega), hd5Eq]

/-! ### Pass 2C.3: `head` (`[3*Q .. 4*Q)`) -/

def headSweepSpec (parentFn heavyFn : Nat → Nat) : Nat → Nat
  | 0 => 0
  | v + 1 =>
    let p := parentFn (v + 1)
    if _h : p < v + 1 then
      if heavyFn p = v + 1 then headSweepSpec parentFn heavyFn p else v + 1
    else v + 1
termination_by v => v

theorem headSweepSpec_succ {parentFn heavyFn : Nat → Nat} {v : Nat}
    (hv : 1 ≤ v) (hp : parentFn v < v) :
    headSweepSpec parentFn heavyFn v =
      if heavyFn (parentFn v) = v then headSweepSpec parentFn heavyFn (parentFn v) else v := by
  cases v with
  | zero => omega
  | succ k =>
    rw [headSweepSpec]
    simp only [hp, ↓reduceDIte]

def headPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) := (headInstrs (bits := bits)).toArray
  Phase.ofLast code 34 rfl rfl rfl

private theorem head_iter {input : Input DomL} {Q : Nat}
    (parentFn heavyFn entryFn denseOfEntryFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hParent : ∀ v, 1 ≤ v → v < Q → parentFn v < v)
    (hHeavyRange : ∀ v, v < Q → heavyFn v ≤ Q)
    (hEntryRange : ∀ v, v < Q → entryFn v < Q)
    (hEntryInj : ∀ u₁ u₂, u₁ < Q → u₂ < Q → entryFn u₁ = entryFn u₂ → u₁ = u₂)
    (hDenseInv : ∀ e, e < Q → denseOfEntryFn e < Q ∧ entryFn (denseOfEntryFn e) = e)
    (hParentPre : ∀ v, 1 ≤ v → v < Q → entryFn (parentFn v) < entryFn v)
    (hHeadBound : ∀ v, v < Q → headSweepSpec parentFn heavyFn v < Q) :
    ∀ (rem e : Nat) (s : State DomL),
      s.pc = 15 →
      Q = e + rem →
      s.data.size = workCap →
      (reg s registers.zero).val = 0 →
      (reg s registers.one).val = 1 →
      (reg s count).val = Q →
      (reg s tinBase).val = 2 * Q →
      (reg s toutBase).val = 3 * Q →
      (reg s childrenBase).val = 6 * Q →
      (reg s registers.ptr).val = e →
      (∀ u, u < Q → (s.data[u]?).map Fin.val = some (parentFn u)) →
      (∀ u, u < Q → (s.data[2 * Q + u]?).map Fin.val = some (heavyFn u)) →
      (∀ u, u < Q → (s.data[6 * Q + u]?).map Fin.val = some (denseOfEntryFn u)) →
      (∀ u, u < Q → entryFn u < e → (s.data[3 * Q + u]?).map Fin.val = some (headSweepSpec parentFn heavyFn u)) →
      ∃ t w,
        w ≤ 18 * rem + 1 ∧
        Steps (headPhase hi hw).code input w s t ∧
        t.pc = 34 ∧
        (reg t registers.zero).val = 0 ∧
        (reg t registers.one).val = 1 ∧
        (reg t count).val = Q ∧
        (∀ u, u < Q → (t.data[3 * Q + u]?).map Fin.val = some (headSweepSpec parentFn heavyFn u)) ∧
        (∀ j, (j < 3 * Q ∨ 4 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro e s hpc hEq hSz hz ho hc _ _ _ hPtr _ _ _ hInv
    let code := (headPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 16 34) := by rw [hpc]; rfl
    have hFalse : ltb (reg s registers.ptr) (reg s count) = false := by
      cases hC : ltb (reg s registers.ptr) (reg s count) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hPtr, hc] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 16 else 34) < 35; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 16 else 34 }
    refine ⟨t, 1, by omega, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      hz, ho, hc, fun u hu => hInv u hu (by have := hEntryRange u hu; omega), fun _ _ => rfl⟩
  | succ rem ih =>
    intro e s hpc hEq hSz hz ho hc hTin hTout hCh hPtr hParData hHvData hDnData hInv
    let code := (headPhase hi hw).code
    have heLt : e < Q := by omega
    obtain ⟨hvLt, hEntV⟩ := hDenseInv e heLt
    let v := denseOfEntryFn e
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 16 34) := by rw [hpc]; rfl
    have hTrue : ltb (reg s registers.ptr) (reg s count) = true :=
      (ltb_eq_true _ _).mpr (by rw [hPtr, hc]; exact heLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 16 else 34) < 35; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s count) = true then 16 else 34 }
    have hpc1 : s1.pc = 16 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp childrenBase registers.ptr) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 16 + 1 < 35; omega)
    have h2tVal : (reg s2 registers.tmp).val = 6 * Q + e := by
      rw [h2t, add_no_wrap _ _ (by change (reg s childrenBase).val + (reg s registers.ptr).val < 2 ^ bits; rw [hCh, hPtr]; omega)]
      change (reg s childrenBase).val + (reg s registers.ptr).val = _; rw [hCh, hPtr]
    have hwV : s2.data[(reg s2 registers.tmp).val]? = some ⟨v, by omega⟩ := by
      rw [h2tVal, hd2]
      have hDv := hDnData e heLt
      cases hC : s.data[6 * Q + e]? with
      | none => rw [hC] at hDv; cases hDv
      | some w => rw [hC, Option.map_some] at hDv; congr 1; exact Fin.ext (Option.some.inj hDv)
    have h2 : code[s2.pc]? = some (.loadData registers.value registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3v, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwV (by rw [hpc2, hpc1]; change 16 + 1 + 1 < 35; omega)
    have h3 : code[s3.pc]? = some (.branchLt registers.value registers.one 19 21) := by rw [hpc3, hpc2, hpc1]; rfl
    have hs34 := step_branchLt_at (input := input) h3 (by change (if _ then 19 else 21) < 35; split <;> omega)
    have h3zero : (reg s3 registers.zero).val = 0 := by
      rw [h3o registers.zero (fin_ne_of_val (by decide)), h2o registers.zero (fin_ne_of_val (by decide))]; exact hz
    have h3one : (reg s3 registers.one).val = 1 := by
      rw [h3o registers.one (fin_ne_of_val (by decide)), h2o registers.one (fin_ne_of_val (by decide))]; exact ho
    have h3cnt : (reg s3 count).val = Q := by
      rw [h3o count (fin_ne_of_val (by decide)), h2o count (fin_ne_of_val (by decide))]; exact hc
    have h3tin : (reg s3 tinBase).val = 2 * Q := by
      rw [h3o tinBase (fin_ne_of_val (by decide)), h2o tinBase (fin_ne_of_val (by decide))]; exact hTin
    have h3tout : (reg s3 toutBase).val = 3 * Q := by
      rw [h3o toutBase (fin_ne_of_val (by decide)), h2o toutBase (fin_ne_of_val (by decide))]; exact hTout
    have h3ch : (reg s3 childrenBase).val = 6 * Q := by
      rw [h3o childrenBase (fin_ne_of_val (by decide)), h2o childrenBase (fin_ne_of_val (by decide))]; exact hCh
    have h3ptr : (reg s3 registers.ptr).val = e := by
      rw [h3o registers.ptr (fin_ne_of_val (by decide)), h2o registers.ptr (fin_ne_of_val (by decide))]; exact hPtr
    have h3val : (reg s3 registers.value).val = v := by rw [h3v]
    have h3data : s3.data = s.data := by rw [hd3, hd2]
    let s4 : State DomL := { s3 with pc := if ltb (reg s3 registers.value) (reg s3 registers.one) = true then 19 else 21 }
    have hPost32 : ∃ s32 : State DomL, ∃ wSub, wSub ≤ 10 ∧
        Steps code input wSub s4 s32 ∧
        s32.pc = 32 ∧
        s32.data.size = workCap ∧
        (reg s32 registers.zero).val = 0 ∧
        (reg s32 registers.one).val = 1 ∧
        (reg s32 count).val = Q ∧
        (reg s32 tinBase).val = 2 * Q ∧
        (reg s32 toutBase).val = 3 * Q ∧
        (reg s32 childrenBase).val = 6 * Q ∧
        (reg s32 registers.ptr).val = e ∧
        (s32.data[3 * Q + v]?).map Fin.val = some (headSweepSpec parentFn heavyFn v) ∧
        (∀ j, j ≠ 3 * Q + v → s32.data[j]? = s.data[j]?) := by
      by_cases hvZero : v < 1
      · have hvEq0 : v = 0 := by omega
        have hBr : ltb (reg s3 registers.value) (reg s3 registers.one) = true :=
          (ltb_eq_true _ _).mpr (by rw [h3val, h3one]; exact hvZero)
        have hpc4 : s4.pc = 19 := by simp only [s4, hBr, ite_true]
        have hFit4 : (reg s4 toutBase).val < s4.data.size := by change (reg s3 toutBase).val < s3.data.size; rw [h3tout, h3data, hSz]; omega
        have h4 : code[s4.pc]? = some (.storeData toutBase registers.zero) := by rw [hpc4]; rfl
        obtain ⟨s5, hs5, hpc5, hr5, hd5⟩ :=
          step_storeData_exists (input := input) h4 hFit4 (by rw [hpc4]; change 19 + 1 < 35; omega)
        have h5 : code[s5.pc]? = some (.goto 32) := by rw [hpc5, hpc4]; rfl
        have hs56 := step_goto_at (input := input) h5 (by change 32 < 35; omega)
        let s6 : State DomL := { s5 with pc := 32 }
        refine ⟨s6, 2, by omega, Steps.cons hs5 (Steps.cons hs56 (.zero _)), rfl,
          by change s5.data.size = workCap; rw [s5.data_size],
          by change (reg s5 registers.zero).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3zero,
          by change (reg s5 registers.one).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3one,
          by change (reg s5 count).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3cnt,
          by change (reg s5 tinBase).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3tin,
          by change (reg s5 toutBase).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3tout,
          by change (reg s5 childrenBase).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3ch,
          by change (reg s5 registers.ptr).val = _; rw [reg_eq_of_regs_eq hr5]; exact h3ptr,
          ?_, ?_⟩
        · change (s5.data[3 * Q + v]?).map Fin.val = _
          rw [hd5, hvEq0, Nat.add_zero]
          have he : 3 * Q = (reg s4 toutBase).val := h3tout.symm
          simp only [he, Array.getElem?_set_self, Option.map_some]
          change some ((reg s3 registers.zero).val) = some (headSweepSpec parentFn heavyFn 0)
          rw [h3zero, headSweepSpec]
        · intro j hj
          change s5.data[j]? = s.data[j]?
          rw [hd5, Array.getElem?_set_ne _ (by change (reg s3 toutBase).val ≠ j; rw [h3tout]; omega), h3data]
      · have hvPos : 1 ≤ v := by omega
        have hParLt : parentFn v < v := hParent v hvPos hvLt
        have hParPre : entryFn (parentFn v) < e := by rw [← hEntV]; exact hParentPre v hvPos hvLt
        have hBr : ltb (reg s3 registers.value) (reg s3 registers.one) = false := by
          cases hC : ltb (reg s3 registers.value) (reg s3 registers.one) with
          | false => rfl
          | true => have := (ltb_eq_true _ _).mp hC; rw [h3val, h3one] at this; omega
        have hpc4 : s4.pc = 21 := by simp only [s4, hBr, Bool.false_eq_true, ite_false]
        have hwPar : s4.data[(reg s4 registers.value).val]? = some ⟨parentFn v, by omega⟩ := by
          change s3.data[(reg s3 registers.value).val]? = _
          rw [h3val, h3data]
          have hPv := hParData v hvLt
          cases hC : s.data[v]? with
          | none => rw [hC] at hPv; cases hPv
          | some w => rw [hC, Option.map_some] at hPv; congr 1; exact Fin.ext (Option.some.inj hPv)
        have h4 : code[s4.pc]? = some (.loadData registers.remain registers.value) := by rw [hpc4]; rfl
        obtain ⟨s5, hs5, hpc5, h5rem, h5o, hd5⟩ :=
          step_loadData_at (input := input) h4 hwPar (by rw [hpc4]; change 21 + 1 < 35; omega)
        have h5 : code[s5.pc]? = some (.add registers.tmp tinBase registers.remain) := by rw [hpc5, hpc4]; rfl
        obtain ⟨s6, hs6, hpc6, h6t, h6o, hd6⟩ :=
          step_add_at (input := input) h5 (by rw [hpc5, hpc4]; change 21 + 1 + 1 < 35; omega)
        have h6tVal : (reg s6 registers.tmp).val = 2 * Q + parentFn v := by
          have h5t : (reg s5 tinBase).val = 2 * Q := by
            rw [h5o tinBase (fin_ne_of_val (by decide))]; exact h3tin
          have h5r : (reg s5 registers.remain).val = parentFn v := by rw [h5rem]
          rw [h6t, add_no_wrap _ _ (by rw [h5t, h5r]; omega), h5t, h5r]
        have hwHv : s6.data[(reg s6 registers.tmp).val]? = some ⟨heavyFn (parentFn v), by have := hHeavyRange (parentFn v) (by omega); omega⟩ := by
          rw [h6tVal, hd6, hd5, h3data]
          have hHv := hHvData (parentFn v) (by omega)
          cases hC : s.data[2 * Q + parentFn v]? with
          | none => rw [hC] at hHv; cases hHv
          | some w => rw [hC, Option.map_some] at hHv; congr 1; exact Fin.ext (Option.some.inj hHv)
        have h6 : code[s6.pc]? = some (.loadData clk registers.tmp) := by rw [hpc6, hpc5, hpc4]; rfl
        obtain ⟨s7, hs7, hpc7, h7clk, h7o, hd7⟩ :=
          step_loadData_at (input := input) h6 hwHv (by rw [hpc6, hpc5, hpc4]; change 21 + 1 + 1 + 1 < 35; omega)
        have h7 : code[s7.pc]? = some (.branchLt clk registers.value 29 25) := by rw [hpc7, hpc6, hpc5, hpc4]; rfl
        have hs78 := step_branchLt_at (input := input) h7 (by change (if _ then 29 else 25) < 35; split <;> omega)
        have h7clkVal : (reg s7 clk).val = heavyFn (parentFn v) := by rw [h7clk]
        have h7valVal : (reg s7 registers.value).val = v := by
          rw [h7o registers.value (fin_ne_of_val (by decide)), h6o registers.value (fin_ne_of_val (by decide)),
              h5o registers.value (fin_ne_of_val (by decide))]; exact h3val
        have h7remVal : (reg s7 registers.remain).val = parentFn v := by
          rw [h7o registers.remain (fin_ne_of_val (by decide)), h6o registers.remain (fin_ne_of_val (by decide)), h5rem]
        have h7tout : (reg s7 toutBase).val = 3 * Q := by
          rw [h7o toutBase (fin_ne_of_val (by decide)), h6o toutBase (fin_ne_of_val (by decide)),
              h5o toutBase (fin_ne_of_val (by decide))]; exact h3tout
        have h7regPre : ∀ r, r ≠ registers.remain → r ≠ clk → r ≠ registers.tmp → reg s7 r = reg s3 r := by
          intro r hr1 hr2 hr3
          rw [h7o r hr2, h6o r hr3, h5o r hr1]; rfl
        have h7data : s7.data = s.data := by rw [hd7, hd6, hd5, h3data]
        let s8 : State DomL := { s7 with pc := if ltb (reg s7 clk) (reg s7 registers.value) = true then 29 else 25 }
        have hReach30 : ∃ s30 : State DomL, ∃ wBr, wBr ≤ 4 ∧
            Steps code input wBr s8 s30 ∧
            s30.pc = 30 ∧ s30.data = s.data ∧
            (reg s30 cmd).val = headSweepSpec parentFn heavyFn v ∧
            (reg s30 toutBase).val = 3 * Q ∧
            (reg s30 registers.value).val = v ∧
            (∀ r, r ≠ registers.remain → r ≠ clk → r ≠ registers.tmp → r ≠ cmd → reg s30 r = reg s3 r) := by
          by_cases hEqHv : heavyFn (parentFn v) = v
          · have hBr1 : ltb (reg s7 clk) (reg s7 registers.value) = false := by
              cases hC : ltb (reg s7 clk) (reg s7 registers.value) with
              | false => rfl
              | true => have := (ltb_eq_true _ _).mp hC; rw [h7clkVal, h7valVal] at this; omega
            have hpc8 : s8.pc = 25 := by simp only [s8, hBr1, Bool.false_eq_true, ite_false]
            have h8 : code[s8.pc]? = some (.branchLt registers.value clk 29 26) := by rw [hpc8]; rfl
            have hs89 := step_branchLt_at (input := input) h8 (by change (if _ then 29 else 26) < 35; split <;> omega)
            have hBr2 : ltb (reg s7 registers.value) (reg s7 clk) = false := by
              cases hC : ltb (reg s7 registers.value) (reg s7 clk) with
              | false => rfl
              | true => have := (ltb_eq_true _ _).mp hC; rw [h7clkVal, h7valVal] at this; omega
            let s9 : State DomL := { s8 with pc := if ltb (reg s8 registers.value) (reg s8 clk) = true then 29 else 26 }
            have hpc9 : s9.pc = 26 := by
              change (if ltb (reg s7 registers.value) (reg s7 clk) = true then 29 else 26) = 26
              simp only [hBr2, Bool.false_eq_true, ite_false]
            have h9 : code[s9.pc]? = some (.add registers.tmp toutBase registers.remain) := by rw [hpc9]; rfl
            obtain ⟨s10, hs10, hpc10, h10t, h10o, hd10⟩ :=
              step_add_at (input := input) h9 (by rw [hpc9]; change 26 + 1 < 35; omega)
            have h10tVal : (reg s10 registers.tmp).val = 3 * Q + parentFn v := by
              have h9to : (reg s9 toutBase).val = 3 * Q := h7tout
              have h9rem : (reg s9 registers.remain).val = parentFn v := h7remVal
              rw [h10t, add_no_wrap _ _ (by rw [h9to, h9rem]; omega), h9to, h9rem]
            have hHeadP := hInv (parentFn v) (by omega) hParPre
            have hwHeadP : s10.data[(reg s10 registers.tmp).val]? =
                some ⟨headSweepSpec parentFn heavyFn (parentFn v), by have := hHeadBound (parentFn v) (by omega); omega⟩ := by
              rw [h10tVal, hd10]
              change s7.data[3 * Q + parentFn v]? = _
              rw [h7data]
              cases hC : s.data[3 * Q + parentFn v]? with
              | none => rw [hC] at hHeadP; cases hHeadP
              | some w => rw [hC, Option.map_some] at hHeadP; congr 1; exact Fin.ext (Option.some.inj hHeadP)
            have h10 : code[s10.pc]? = some (.loadData cmd registers.tmp) := by rw [hpc10, hpc9]; rfl
            obtain ⟨s11, hs11, hpc11, h11cmd, h11o, hd11⟩ :=
              step_loadData_at (input := input) h10 hwHeadP (by rw [hpc10, hpc9]; change 26 + 1 + 1 < 35; omega)
            have h11 : code[s11.pc]? = some (.goto 30) := by rw [hpc11, hpc10, hpc9]; rfl
            have hs1112 := step_goto_at (input := input) h11 (by change 30 < 35; omega)
            let s12 : State DomL := { s11 with pc := 30 }
            refine ⟨s12, 4, by omega,
              Steps.cons hs89 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs1112 (.zero _)))),
              rfl, by change s11.data = _; rw [hd11, hd10]; exact h7data,
              ?_, ?_, ?_, ?_⟩
            · change (reg s11 cmd).val = _
              rw [h11cmd, headSweepSpec_succ hvPos hParLt, ite_eq_left hEqHv]
            · change (reg s11 toutBase).val = _
              rw [congrArg Fin.val (h11o toutBase (fin_ne_of_val (by decide))),
                  congrArg Fin.val (h10o toutBase (fin_ne_of_val (by decide)))]; exact h7tout
            · change (reg s11 registers.value).val = _
              rw [congrArg Fin.val (h11o registers.value (fin_ne_of_val (by decide))),
                  congrArg Fin.val (h10o registers.value (fin_ne_of_val (by decide)))]; exact h7valVal
            · intro r hr1 hr2 hr3 hr4
              change reg s11 r = reg s3 r
              rw [h11o r hr4, h10o r hr3]; exact h7regPre r hr1 hr2 hr3
          · rcases Nat.lt_or_ge (heavyFn (parentFn v)) v with hLt | hGt
            · have hBr1 : ltb (reg s7 clk) (reg s7 registers.value) = true :=
                (ltb_eq_true _ _).mpr (by rw [h7clkVal, h7valVal]; exact hLt)
              have hpc8 : s8.pc = 29 := by simp only [s8, hBr1, ite_true]
              have h8 : code[s8.pc]? = some (.mov cmd registers.value) := by rw [hpc8]; rfl
              obtain ⟨s9, hs9, hpc9, h9cmd, h9o, hd9⟩ :=
                step_mov_at (input := input) h8 (by rw [hpc8]; change 29 + 1 < 35; omega)
              refine ⟨s9, 1, by omega, Steps.cons hs9 (.zero _), by rw [hpc9, hpc8],
                by rw [hd9, h7data], ?_, ?_, ?_, ?_⟩
              · rw [congrArg Fin.val h9cmd, headSweepSpec_succ hvPos hParLt, ite_eq_right hEqHv]; exact h7valVal
              · rw [congrArg Fin.val (h9o toutBase (fin_ne_of_val (by decide)))]; exact h7tout
              · rw [congrArg Fin.val (h9o registers.value (fin_ne_of_val (by decide)))]; exact h7valVal
              · intro r hr1 hr2 hr3 hr4; rw [h9o r hr4]; exact h7regPre r hr1 hr2 hr3
            · have hGtStrict : v < heavyFn (parentFn v) := by omega
              have hBr1 : ltb (reg s7 clk) (reg s7 registers.value) = false := by
                cases hC : ltb (reg s7 clk) (reg s7 registers.value) with
                | false => rfl
                | true => have := (ltb_eq_true _ _).mp hC; rw [h7clkVal, h7valVal] at this; omega
              have hpc8 : s8.pc = 25 := by simp only [s8, hBr1, Bool.false_eq_true, ite_false]
              have h8 : code[s8.pc]? = some (.branchLt registers.value clk 29 26) := by rw [hpc8]; rfl
              have hs89 := step_branchLt_at (input := input) h8 (by change (if _ then 29 else 26) < 35; split <;> omega)
              have hBr2 : ltb (reg s7 registers.value) (reg s7 clk) = true :=
                (ltb_eq_true _ _).mpr (by rw [h7valVal, h7clkVal]; exact hGtStrict)
              let s9 : State DomL := { s8 with pc := if ltb (reg s8 registers.value) (reg s8 clk) = true then 29 else 26 }
              have hpc9 : s9.pc = 29 := by
                change (if ltb (reg s7 registers.value) (reg s7 clk) = true then 29 else 26) = 29
                simp only [hBr2, ite_true]
              have h9 : code[s9.pc]? = some (.mov cmd registers.value) := by rw [hpc9]; rfl
              obtain ⟨s10, hs10, hpc10, h10cmd, h10o, hd10⟩ :=
                step_mov_at (input := input) h9 (by rw [hpc9]; change 29 + 1 < 35; omega)
              refine ⟨s10, 2, by omega, Steps.cons hs89 (Steps.cons hs10 (.zero _)), by rw [hpc10, hpc9],
                by rw [hd10]; exact h7data, ?_, ?_, ?_, ?_⟩
              · rw [congrArg Fin.val h10cmd, headSweepSpec_succ hvPos hParLt, ite_eq_right hEqHv]; exact h7valVal
              · rw [congrArg Fin.val (h10o toutBase (fin_ne_of_val (by decide)))]; exact h7tout
              · rw [congrArg Fin.val (h10o registers.value (fin_ne_of_val (by decide)))]; exact h7valVal
              · intro r hr1 hr2 hr3 hr4; rw [h10o r hr4]; exact h7regPre r hr1 hr2 hr3
        obtain ⟨s30, wBr, hwBr, hsBr, hpc30, hd30, h30cmd, h30tout, h30val, h30reg⟩ := hReach30
        have h30 : code[s30.pc]? = some (.add registers.tmp toutBase registers.value) := by rw [hpc30]; rfl
        obtain ⟨s31, hs31, hpc31, h31t, h31o, hd31⟩ :=
          step_add_at (input := input) h30 (by rw [hpc30]; change 30 + 1 < 35; omega)
        have h31tVal : (reg s31 registers.tmp).val = 3 * Q + v := by
          rw [h31t, add_no_wrap _ _ (by rw [h30tout, h30val]; omega), h30tout, h30val]
        have hFit31 : (reg s31 registers.tmp).val < s31.data.size := by rw [h31tVal, hd31, hd30, hSz]; omega
        have h31 : code[s31.pc]? = some (.storeData registers.tmp cmd) := by rw [hpc31, hpc30]; rfl
        obtain ⟨s32, hs32, hpc32, hr32, hd32⟩ :=
          step_storeData_exists (input := input) h31 hFit31 (by rw [hpc31, hpc30]; change 30 + 1 + 1 < 35; omega)
        have h32reg : ∀ r, r ≠ registers.remain → r ≠ clk → r ≠ registers.tmp → r ≠ cmd → reg s32 r = reg s3 r := by
          intro r hr1 hr2 hr3 hr4
          rw [reg_eq_of_regs_eq hr32, h31o r hr3, h30reg r hr1 hr2 hr3 hr4]
        refine ⟨s32, 4 + wBr + 2, by omega,
          ((Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs78 (.zero _))))).append hsBr).append
            (Steps.cons hs31 (Steps.cons hs32 (.zero _))),
          by rw [hpc32, hpc31, hpc30], by rw [s32.data_size],
          by rw [h32reg registers.zero (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3zero,
          by rw [h32reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3one,
          by rw [h32reg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3cnt,
          by rw [h32reg tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3tin,
          by rw [h32reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3tout,
          by rw [h32reg childrenBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3ch,
          by rw [h32reg registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact h3ptr,
          ?_, ?_⟩
        · rw [hd32]
          have he : 3 * Q + v = (reg s31 registers.tmp).val := h31tVal.symm
          simp only [he, Array.getElem?_set_self, Option.map_some]
          rw [congrArg Fin.val (h31o cmd (fin_ne_of_val (by decide))), h30cmd]
        · intro j hj
          rw [hd32, Array.getElem?_set_ne _ (by rw [h31tVal]; exact fun e => hj e.symm), hd31, hd30]
    obtain ⟨s32, wSub, hwSub, hsSub, hpc32, h32Sz, h32zero, h32one, h32cnt, h32tin, h32tout, h32ch, h32ptr,
      h32at, h32ne⟩ := hPost32
    have h32 : code[s32.pc]? = some (.add registers.ptr registers.ptr registers.one) := by rw [hpc32]; rfl
    obtain ⟨s33, hs33, hpc33, h33p, h33o, hd33⟩ :=
      step_add_at (input := input) h32 (by rw [hpc32]; change 32 + 1 < 35; omega)
    have h33 : code[s33.pc]? = some (.goto 15) := by rw [hpc33, hpc32]; rfl
    have hs3334 := step_goto_at (input := input) h33 (by change 15 < 35; omega)
    let s34 : State DomL := { s33 with pc := 15 }
    have h34Sz : s34.data.size = workCap := by change s33.data.size = workCap; rw [s33.data_size]
    have h34p : (reg s34 registers.ptr).val = e + 1 := by
      change (reg s33 registers.ptr).val = _
      rw [h33p, add_no_wrap _ _ (by rw [h32ptr, h32one]; omega), h32ptr, h32one]
    have h34data_at : (s34.data[3 * Q + v]?).map Fin.val = some (headSweepSpec parentFn heavyFn v) := by
      change (s33.data[3 * Q + v]?).map Fin.val = _; rw [hd33]; exact h32at
    have h34data_ne : ∀ j, j ≠ 3 * Q + v → s34.data[j]? = s.data[j]? := fun j hne => by
      change s33.data[j]? = s.data[j]?; rw [hd33]; exact h32ne j hne
    have h34Inv : ∀ u, u < Q → entryFn u < e + 1 →
        (s34.data[3 * Q + u]?).map Fin.val = some (headSweepSpec parentFn heavyFn u) := by
      intro u hu hEu
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hEu) with hLtE | hEqE
      · have hneUV : u ≠ v := fun eUV => by subst u; rw [hEntV] at hLtE; omega
        rw [h34data_ne (3 * Q + u) (by omega)]
        exact hInv u hu hLtE
      · have hUV : u = v := hEntryInj u v hu hvLt (hEqE.trans hEntV.symm)
        subst u
        exact h34data_at
    obtain ⟨t, wTail, hwTail, htSteps, htpc, htz, hto, htc, htInv, htFrame⟩ :=
      ih (e + 1) s34 rfl (by omega) h34Sz
        (by change (reg s33 registers.zero).val = _; rw [h33o registers.zero (fin_ne_of_val (by decide)), h32zero])
        (by change (reg s33 registers.one).val = _; rw [h33o registers.one (fin_ne_of_val (by decide)), h32one])
        (by change (reg s33 count).val = _; rw [h33o count (fin_ne_of_val (by decide)), h32cnt])
        (by change (reg s33 tinBase).val = _; rw [h33o tinBase (fin_ne_of_val (by decide)), h32tin])
        (by change (reg s33 toutBase).val = _; rw [h33o toutBase (fin_ne_of_val (by decide)), h32tout])
        (by change (reg s33 childrenBase).val = _; rw [h33o childrenBase (fin_ne_of_val (by decide)), h32ch])
        h34p
        (fun u hu => by rw [h34data_ne u (by omega)]; exact hParData u hu)
        (fun u hu => by rw [h34data_ne (2 * Q + u) (by omega)]; exact hHvData u hu)
        (fun u hu => by rw [h34data_ne (6 * Q + u) (by omega)]; exact hDnData u hu)
        h34Inv
    have hPreHead : Steps code input 4 s s4 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs34 (.zero _))))
    have hOneIter : Steps code input (4 + wSub + 2) s s34 :=
      (hPreHead.append hsSub).append (Steps.cons hs33 (Steps.cons hs3334 (.zero _)))
    refine ⟨t, (4 + wSub + 2) + wTail, by omega, hOneIter.append htSteps, htpc, htz, hto, htc, htInv, fun j hj => ?_⟩
    exact (htFrame j hj).trans (h34data_ne j (by omega))

theorem run_head {input : Input DomL} {Q : Nat}
    (parentFn heavyFn entryFn denseOfEntryFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hParent : ∀ v, 1 ≤ v → v < Q → parentFn v < v)
    (hHeavyRange : ∀ v, v < Q → heavyFn v ≤ Q)
    (hEntryRange : ∀ v, v < Q → entryFn v < Q)
    (hEntryInj : ∀ u₁ u₂, u₁ < Q → u₂ < Q → entryFn u₁ = entryFn u₂ → u₁ = u₂)
    (hDenseInv : ∀ e, e < Q → denseOfEntryFn e < Q ∧ entryFn (denseOfEntryFn e) = e)
    (hParentPre : ∀ v, 1 ≤ v → v < Q → entryFn (parentFn v) < entryFn v)
    (hHeadBound : ∀ v, v < Q → headSweepSpec parentFn heavyFn v < Q)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hParData : ∀ u, u < Q → (s.data[u]?).map Fin.val = some (parentFn u))
    (hHvData : ∀ u, u < Q → (s.data[2 * Q + u]?).map Fin.val = some (heavyFn u))
    (hDnData : ∀ u, u < Q → (s.data[6 * Q + u]?).map Fin.val = some (denseOfEntryFn u)) :
    ∃ t w,
      w ≤ 18 * Q + 17 ∧
      run (headPhase hi hw).code input w (Phase.initial s) = some ⟨t, w⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (∀ u, u < Q → (t.data[3 * Q + u]?).map Fin.val = some (headSweepSpec parentFn heavyFn u)) ∧
      (∀ j, (j < 3 * Q ∨ 4 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  let p := headPhase hi hw
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = 35 := rfl
  have hPlPre : Placed p.code 0
      (mulAddInstrs tinBase count registers.one 2 0 ++
       mulAddInstrs toutBase count registers.one 3 0 ++
       mulAddInstrs childrenBase count registers.one 6 0) :=
    placed_append_self_left _ _
  have hPl1 : Placed p.code 0 (mulAddInstrs tinBase count registers.one 2 0) :=
    placed_append_left (placed_append_left hPlPre)
  have hPl2 : Placed p.code 3 (mulAddInstrs toutBase count registers.one 3 0) := by
    have h := placed_append_right (placed_append_left hPlPre)
    simpa only [Nat.zero_add, mulAddInstrs_length] using h
  have hPl3 : Placed p.code 7 (mulAddInstrs childrenBase count registers.one 6 0) := by
    have h := placed_append_right hPlPre
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hAt14 : p.code[14]? = some (.imm registers.ptr ⟨0, Nat.one_le_two_pow⟩) := rfl
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have ho0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, hTin1, ho1⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz]; omega) hPl1 hc0 ho0 (by omega)
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have ho1' : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), ho0]
  obtain ⟨s2, hs2, hpc2, hd2, hTout2, ho2⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 (by rw [hpc1]) (by rw [hSz]; omega) hPl2 hc1 ho1' (by omega)
  have hc2 : (reg s2 count).val = Q := by rw [ho2 count (fin_ne_of_val (by decide)), hc1]
  have ho2' : (reg s2 registers.one).val = 1 := by rw [ho2 registers.one (fin_ne_of_val (by decide)), ho1']
  obtain ⟨s3, hs3, hpc3, hd3, hCh3, ho3⟩ :=
    run_mulAddInstrs (input := input) childrenBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s2 (by rw [hpc2]) (by rw [hSz]; omega) hPl3 hc2 ho2' (by omega)
  obtain ⟨s4, hs4, hpc4, h4p, ho4, hd4⟩ :=
    step_imm_at (input := input) (by rw [hpc3]; exact hAt14) (by rw [hpc3, hSz]; omega)
  have hpc4' : s4.pc = 15 := by rw [hpc4, hpc3]
  have hd4Eq : s4.data = s.data := by rw [hd4, hd3, hd2, hd1, initial_data]
  have hz4 : (reg s4 registers.zero).val = 0 := by
    rw [ho4 registers.zero (fin_ne_of_val (by decide)), ho3 registers.zero (fin_ne_of_val (by decide)),
        ho2 registers.zero (fin_ne_of_val (by decide)), ho1 registers.zero (fin_ne_of_val (by decide)), initial_reg]; exact hz
  have ho4' : (reg s4 registers.one).val = 1 := by
    rw [ho4 registers.one (fin_ne_of_val (by decide)), ho3 registers.one (fin_ne_of_val (by decide))]; exact ho2'
  have hc4 : (reg s4 count).val = Q := by rw [ho4 count (fin_ne_of_val (by decide)), ho3 count (fin_ne_of_val (by decide))]; exact hc2
  have hTin4 : (reg s4 tinBase).val = 2 * Q := by
    rw [ho4 tinBase (fin_ne_of_val (by decide)), ho3 tinBase (fin_ne_of_val (by decide)),
        ho2 tinBase (fin_ne_of_val (by decide)), hTin1, Nat.add_zero]
  have hTout4 : (reg s4 toutBase).val = 3 * Q := by
    rw [ho4 toutBase (fin_ne_of_val (by decide)), ho3 toutBase (fin_ne_of_val (by decide)), hTout2, Nat.add_zero]
  have hCh4 : (reg s4 childrenBase).val = 6 * Q := by rw [ho4 childrenBase (fin_ne_of_val (by decide)), hCh3, Nat.add_zero]
  obtain ⟨t, wOut, hwOut, htSteps, htpc, htz, hto, htc, htInv, htFrame⟩ :=
    head_iter parentFn heavyFn entryFn denseOfEntryFn hQFit hWork hParent hHeavyRange hEntryRange
      hEntryInj hDenseInv hParentPre hHeadBound Q 0 s4 hpc4' (by omega) (by rw [hd4Eq, s.data_size])
      hz4 ho4' hc4 hTin4 hTout4 hCh4 (by rw [h4p])
      (fun u hu => by rw [hd4Eq]; exact hParData u hu)
      (fun u hu => by rw [hd4Eq]; exact hHvData u hu)
      (fun u hu => by rw [hd4Eq]; exact hDnData u hu)
      (fun u _ hLt0 => by omega)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at; rw [htpc]; rfl
  have hSetupSteps : Steps p.code input 15 s0 s4 :=
    ((hs1.append hs2).append hs3).append (Steps.cons hs4 (.zero _))
  refine ⟨t, 15 + wOut + 1, by omega, (hSetupSteps.append htSteps).halts hHalt, htz, hto, htc, htInv, fun j hj => ?_⟩
  rw [htFrame j hj, hd4Eq]

/-! ### Pass 2C.4: `childIntervals` (`[8*Q + 1 .. 10*Q)`) -/

def childIntervalsPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) := (childIntervalsInstrs (bits := bits)).toArray
  Phase.ofLast code 55 rfl rfl rfl

private theorem childIntervals_iter {input : Input DomL} {Q : Nat}
    (entryFn stopFn childFn : Nat → Nat)
    (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hChild : ∀ i, i < Q - 1 → childFn i < Q ∧ entryFn (childFn i) ≤ Q ∧ stopFn (childFn i) ≤ Q) :
    ∀ (rem i : Nat) (s : State DomL),
      s.pc = 42 →
      Q - 1 = i + rem →
      s.data.size = workCap →
      (reg s registers.zero).val = 0 →
      (reg s registers.one).val = 1 →
      (reg s count).val = Q →
      (reg s tinBase).val = 4 * Q →
      (reg s toutBase).val = 8 * Q + 1 →
      (reg s offsetBase).val = 9 * Q + 1 →
      (reg s childrenBase).val = 10 * Q + 1 →
      (reg s registers.remain).val = Q - 1 →
      (reg s registers.ptr).val = i →
      (∀ k, k < Q - 1 → (s.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k)) →
      (∀ c, c < Q → (s.data[4 * Q + c]?).map Fin.val = some (entryFn c)) →
      (∀ c, c < Q → (s.data[5 * Q + c]?).map Fin.val = some (stopFn c)) →
      ∃ t : State DomL,
        Steps (childIntervalsPhase hi hw).code input (13 * rem + 1) s t ∧
        t.pc = 55 ∧
        (reg t registers.zero).val = 0 ∧
        (reg t registers.one).val = 1 ∧
        (reg t count).val = Q ∧
        (∀ k, i ≤ k → k < Q - 1 → (t.data[8 * Q + 1 + k]?).map Fin.val = some (entryFn (childFn k))) ∧
        (∀ k, i ≤ k → k < Q - 1 → (t.data[9 * Q + 1 + k]?).map Fin.val = some (stopFn (childFn k))) ∧
        (∀ j, (j < 8 * Q + 1 + i ∨ (9 * Q ≤ j ∧ j < 9 * Q + 1 + i) ∨ 10 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro i s hpc hEq hSz hz ho hc _ _ _ _ hRem hPtr _ _ _
    let code := (childIntervalsPhase hi hw).code
    have h0 : code[s.pc]? = some (.branchLt registers.ptr registers.remain 43 55) := by rw [hpc]; rfl
    have hFalse : ltb (reg s registers.ptr) (reg s registers.remain) = false := by
      cases hC : ltb (reg s registers.ptr) (reg s registers.remain) with
      | false => rfl
      | true => have := (ltb_eq_true _ _).mp hC; rw [hPtr, hRem] at this; omega
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 43 else 55) < 56; split <;> omega)
    let t : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s registers.remain) = true then 43 else 55 }
    refine ⟨t, Steps.cons hs01 (.zero _), by simp only [t, hFalse, Bool.false_eq_true, ite_false],
      hz, ho, hc, fun k hk1 hk2 => by omega, fun k hk1 hk2 => by omega, fun _ _ => rfl⟩
  | succ rem ih =>
    intro i s hpc hEq hSz hz ho hc hTin hTout hOff hCh hRem hPtr hCData hEData hSData
    let code := (childIntervalsPhase hi hw).code
    have hiLt : i < Q - 1 := by omega
    obtain ⟨hcLt, heLe, hsLe⟩ := hChild i hiLt
    have h0 : code[s.pc]? = some (.branchLt registers.ptr registers.remain 43 55) := by rw [hpc]; rfl
    have hTrue : ltb (reg s registers.ptr) (reg s registers.remain) = true :=
      (ltb_eq_true _ _).mpr (by rw [hPtr, hRem]; exact hiLt)
    have hs01 := step_branchLt_at (input := input) h0 (by change (if _ then 43 else 55) < 56; split <;> omega)
    let s1 : State DomL := { s with pc := if ltb (reg s registers.ptr) (reg s registers.remain) = true then 43 else 55 }
    have hpc1 : s1.pc = 43 := by simp only [s1, hTrue, ite_true]
    have h1 : code[s1.pc]? = some (.add registers.tmp childrenBase registers.ptr) := by rw [hpc1]; rfl
    obtain ⟨s2, hs2, hpc2, h2t, h2o, hd2⟩ := step_add_at (input := input) h1 (by rw [hpc1]; change 43 + 1 < 56; omega)
    have h2tVal : (reg s2 registers.tmp).val = 10 * Q + 1 + i := by
      rw [h2t, add_no_wrap _ _ (by change (reg s childrenBase).val + (reg s registers.ptr).val < 2 ^ bits; rw [hCh, hPtr]; omega)]
      change (reg s childrenBase).val + (reg s registers.ptr).val = _; rw [hCh, hPtr]
    have hwC : s2.data[(reg s2 registers.tmp).val]? = some ⟨childFn i, by omega⟩ := by
      rw [h2tVal, hd2]
      have hCv := hCData i hiLt
      cases hC : s.data[10 * Q + 1 + i]? with
      | none => rw [hC] at hCv; cases hCv
      | some w => rw [hC, Option.map_some] at hCv; congr 1; exact Fin.ext (Option.some.inj hCv)
    have h2 : code[s2.pc]? = some (.loadData registers.value registers.tmp) := by rw [hpc2, hpc1]; rfl
    obtain ⟨s3, hs3, hpc3, h3v, h3o, hd3⟩ :=
      step_loadData_at (input := input) h2 hwC (by rw [hpc2, hpc1]; change 43 + 1 + 1 < 56; omega)
    have h3 : code[s3.pc]? = some (.add registers.tmp tinBase registers.value) := by rw [hpc3, hpc2, hpc1]; rfl
    obtain ⟨s4, hs4, hpc4, h4t, h4o, hd4⟩ :=
      step_add_at (input := input) h3 (by rw [hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 < 56; omega)
    have h4tVal : (reg s4 registers.tmp).val = 4 * Q + childFn i := by
      have h3tin : (reg s3 tinBase).val = 4 * Q := by
        rw [h3o tinBase (fin_ne_of_val (by decide)), h2o tinBase (fin_ne_of_val (by decide))]; exact hTin
      have h3v' : (reg s3 registers.value).val = childFn i := by rw [h3v]
      rw [h4t, add_no_wrap _ _ (by rw [h3tin, h3v']; omega), h3tin, h3v']
    have hwEnt : s4.data[(reg s4 registers.tmp).val]? = some ⟨entryFn (childFn i), by omega⟩ := by
      rw [h4tVal, hd4, hd3, hd2]
      have hEv := hEData (childFn i) hcLt
      cases hC : s.data[4 * Q + childFn i]? with
      | none => rw [hC] at hEv; cases hEv
      | some w => rw [hC, Option.map_some] at hEv; congr 1; exact Fin.ext (Option.some.inj hEv)
    have h4 : code[s4.pc]? = some (.loadData cmd registers.tmp) := by rw [hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s5, hs5, hpc5, h5cmd, h5o, hd5⟩ :=
      step_loadData_at (input := input) h4 hwEnt (by rw [hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 < 56; omega)
    have h5 : code[s5.pc]? = some (.add registers.tmp registers.tmp count) := by
      rw [hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s6, hs6, hpc6, h6t, h6o, hd6⟩ :=
      step_add_at (input := input) h5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h6tVal : (reg s6 registers.tmp).val = 5 * Q + childFn i := by
      have h5t : (reg s5 registers.tmp).val = 4 * Q + childFn i := by
        rw [h5o registers.tmp (fin_ne_of_val (by decide)), h4tVal]
      have h5c : (reg s5 count).val = Q := by
        rw [h5o count (fin_ne_of_val (by decide)), h4o count (fin_ne_of_val (by decide)),
            h3o count (fin_ne_of_val (by decide)), h2o count (fin_ne_of_val (by decide))]; exact hc
      rw [h6t, add_no_wrap _ _ (by rw [h5t, h5c]; omega), h5t, h5c]; omega
    have hwStop : s6.data[(reg s6 registers.tmp).val]? = some ⟨stopFn (childFn i), by omega⟩ := by
      rw [h6tVal, hd6, hd5, hd4, hd3, hd2]
      have hSv := hSData (childFn i) hcLt
      cases hC : s.data[5 * Q + childFn i]? with
      | none => rw [hC] at hSv; cases hSv
      | some w => rw [hC, Option.map_some] at hSv; congr 1; exact Fin.ext (Option.some.inj hSv)
    have h6 : code[s6.pc]? = some (.loadData clk registers.tmp) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s7, hs7, hpc7, h7clk, h7o, hd7⟩ :=
      step_loadData_at (input := input) h6 hwStop (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h7reg : ∀ r, r ≠ registers.tmp → r ≠ registers.value → r ≠ cmd → r ≠ clk → reg s7 r = reg s r := by
      intro r hr1 hr2 hr3 hr4
      rw [h7o r hr4, h6o r hr1, h5o r hr3, h4o r hr1, h3o r hr2, h2o r hr1]; rfl
    have h7data : s7.data = s.data := by rw [hd7, hd6, hd5, hd4, hd3, hd2]
    have h7 : code[s7.pc]? = some (.add registers.tmp toutBase registers.ptr) := by
      rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s8, hs8, hpc8, h8t, h8o, hd8⟩ :=
      step_add_at (input := input) h7 (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h8tVal : (reg s8 registers.tmp).val = 8 * Q + 1 + i := by
      have h7to : (reg s7 toutBase).val = 8 * Q + 1 := by
        rw [h7reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout
      have h7p : (reg s7 registers.ptr).val = i := by
        rw [h7reg registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hPtr
      rw [h8t, add_no_wrap _ _ (by rw [h7to, h7p]; omega), h7to, h7p]
    have hFit8 : (reg s8 registers.tmp).val < s8.data.size := by rw [h8tVal, hd8, h7data, hSz]; omega
    have h8 : code[s8.pc]? = some (.storeData registers.tmp cmd) := by
      rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s9, hs9, hpc9, hr9, hd9⟩ :=
      step_storeData_exists (input := input) h8 hFit8 (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h9 : code[s9.pc]? = some (.add registers.tmp offsetBase registers.ptr) := by
      rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s10, hs10, hpc10, h10t, h10o, hd10⟩ :=
      step_add_at (input := input) h9 (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h10tVal : (reg s10 registers.tmp).val = 9 * Q + 1 + i := by
      have h9off : (reg s9 offsetBase).val = 9 * Q + 1 := by
        rw [reg_eq_of_regs_eq hr9, h8o offsetBase (fin_ne_of_val (by decide)),
            h7reg offsetBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hOff
      have h9p : (reg s9 registers.ptr).val = i := by
        rw [reg_eq_of_regs_eq hr9, h8o registers.ptr (fin_ne_of_val (by decide)),
            h7reg registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hPtr
      rw [h10t, add_no_wrap _ _ (by rw [h9off, h9p]; omega), h9off, h9p]
    have hFit10 : (reg s10 registers.tmp).val < s10.data.size := by
      rw [h10tVal, hd10, hd9, Array.size_set, hd8, h7data, hSz]; omega
    have h10 : code[s10.pc]? = some (.storeData registers.tmp clk) := by
      rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s11, hs11, hpc11, hr11, hd11⟩ :=
      step_storeData_exists (input := input) h10 hFit10 (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h11p : (reg s11 registers.ptr).val = i := by
      rw [reg_eq_of_regs_eq hr11, h10o registers.ptr (fin_ne_of_val (by decide)),
          reg_eq_of_regs_eq hr9, h8o registers.ptr (fin_ne_of_val (by decide)),
          h7reg registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hPtr
    have h11o : (reg s11 registers.one).val = 1 := by
      rw [reg_eq_of_regs_eq hr11, h10o registers.one (fin_ne_of_val (by decide)),
          reg_eq_of_regs_eq hr9, h8o registers.one (fin_ne_of_val (by decide)),
          h7reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho
    have h11 : code[s11.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
      rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    obtain ⟨s12, hs12, hpc12, h12p, h12o, hd12⟩ :=
      step_add_at (input := input) h11 (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; change 43 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 56; omega)
    have h12 : code[s12.pc]? = some (.goto 42) := by
      rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl
    have hs1213 := step_goto_at (input := input) h12 (by change 42 < 56; omega)
    let s13 : State DomL := { s12 with pc := 42 }
    have h13Sz : s13.data.size = workCap := by change s12.data.size = workCap; rw [s12.data_size]
    have h13reg : ∀ r, r ≠ registers.ptr → r ≠ registers.tmp → r ≠ registers.value → r ≠ cmd → r ≠ clk →
        reg s13 r = reg s r := by
      intro r hr0 hr1 hr2 hr3 hr4
      change reg s12 r = reg s r
      rw [h12o r hr0, reg_eq_of_regs_eq hr11, h10o r hr1, reg_eq_of_regs_eq hr9, h8o r hr1]
      exact h7reg r hr1 hr2 hr3 hr4
    have h13p : (reg s13 registers.ptr).val = i + 1 := by
      change (reg s12 registers.ptr).val = _
      rw [h12p, add_no_wrap _ _ (by rw [h11p, h11o]; omega), h11p, h11o]
    have h13data_ne : ∀ j, j ≠ 8 * Q + 1 + i → j ≠ 9 * Q + 1 + i → s13.data[j]? = s.data[j]? := fun j hn1 hn2 => by
      change s12.data[j]? = s.data[j]?
      rw [hd12, hd11, Array.getElem?_set_ne _ (by rw [h10tVal]; exact fun e => hn2 e.symm), hd10, hd9,
          Array.getElem?_set_ne _ (by rw [h8tVal]; exact fun e => hn1 e.symm), hd8, h7data]
    have h13data_ent : (s13.data[8 * Q + 1 + i]?).map Fin.val = some (entryFn (childFn i)) := by
      change (s12.data[8 * Q + 1 + i]?).map Fin.val = _
      rw [hd12, hd11, Array.getElem?_set_ne _ (by rw [h10tVal]; omega), hd10, hd9]
      have he : 8 * Q + 1 + i = (reg s8 registers.tmp).val := h8tVal.symm
      simp only [he, Array.getElem?_set_self, Option.map_some]
      rw [congrArg Fin.val (h8o cmd (fin_ne_of_val (by decide))),
          congrArg Fin.val (h7o cmd (fin_ne_of_val (by decide))),
          congrArg Fin.val (h6o cmd (fin_ne_of_val (by decide))), h5cmd]
    have h13data_stop : (s13.data[9 * Q + 1 + i]?).map Fin.val = some (stopFn (childFn i)) := by
      change (s12.data[9 * Q + 1 + i]?).map Fin.val = _
      rw [hd12, hd11]
      have he : 9 * Q + 1 + i = (reg s10 registers.tmp).val := h10tVal.symm
      simp only [he, Array.getElem?_set_self, Option.map_some]
      rw [congrArg Fin.val (h10o clk (fin_ne_of_val (by decide))),
          congrArg Fin.val (reg_eq_of_regs_eq hr9 clk),
          congrArg Fin.val (h8o clk (fin_ne_of_val (by decide))), h7clk]
    obtain ⟨t, htSteps, htpc, htz, hto, htc, htEnt, htStop, htFrame⟩ :=
      ih (i + 1) s13 rfl (by omega) h13Sz
        (by rw [h13reg registers.zero (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hz)
        (by rw [h13reg registers.one (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact ho)
        (by rw [h13reg count (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hc)
        (by rw [h13reg tinBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTin)
        (by rw [h13reg toutBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hTout)
        (by rw [h13reg offsetBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hOff)
        (by rw [h13reg childrenBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hCh)
        (by rw [h13reg registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]; exact hRem)
        h13p
        (fun k hk => by rw [h13data_ne (10 * Q + 1 + k) (by omega) (by omega)]; exact hCData k hk)
        (fun c hcu => by rw [h13data_ne (4 * Q + c) (by omega) (by omega)]; exact hEData c hcu)
        (fun c hcu => by rw [h13data_ne (5 * Q + c) (by omega) (by omega)]; exact hSData c hcu)
    have hStepOne : Steps code input 13 s s13 :=
      Steps.cons hs01 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
        (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
          (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs1213 (.zero _)))))))))))))
    refine ⟨t, by simpa only [show 13 + (13 * rem + 1) = 13 * (rem + 1) + 1 by omega] using hStepOne.append htSteps,
      htpc, htz, hto, htc, ?_, ?_, ?_⟩
    · intro k hk1 hk2
      by_cases hkEq : k = i
      · subst k; rw [htFrame (8 * Q + 1 + i) (by omega), h13data_ent]
      · exact htEnt k (by omega) hk2
    · intro k hk1 hk2
      by_cases hkEq : k = i
      · subst k; rw [htFrame (9 * Q + 1 + i) (by omega), h13data_stop]
      · exact htStop k (by omega) hk2
    · intro j hj
      exact (htFrame j (by omega)).trans (h13data_ne j (by omega) (by omega))

theorem run_childIntervals {input : Input DomL} {Q : Nat}
    (entryFn stopFn childFn : Nat → Nat)
    (hQ : 1 ≤ Q) (hQFit : 17 * Q < 2 ^ bits) (hWork : 17 * Q ≤ workCap)
    (hChild : ∀ i, i < Q - 1 → childFn i < Q ∧ entryFn (childFn i) ≤ Q ∧ stopFn (childFn i) ≤ Q)
    (s : State DomL)
    (hz : (reg s registers.zero).val = 0)
    (ho : (reg s registers.one).val = 1)
    (hc : (reg s count).val = Q)
    (hCData : ∀ k, k < Q - 1 → (s.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k))
    (hEData : ∀ c, c < Q → (s.data[4 * Q + c]?).map Fin.val = some (entryFn c))
    (hSData : ∀ c, c < Q → (s.data[5 * Q + c]?).map Fin.val = some (stopFn c)) :
    ∃ t w,
      w ≤ 13 * Q + 44 ∧
      run (childIntervalsPhase hi hw).code input w (Phase.initial s) = some ⟨t, w⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q ∧
      (∀ k, k < Q - 1 → (t.data[8 * Q + 1 + k]?).map Fin.val = some (entryFn (childFn k))) ∧
      (∀ k, k < Q - 1 → (t.data[9 * Q + 1 + k]?).map Fin.val = some (stopFn (childFn k))) ∧
      (∀ j, (j < 8 * Q + 1 ∨ 10 * Q ≤ j) → t.data[j]? = s.data[j]?) := by
  let p := childIntervalsPhase hi hw
  let s0 := Phase.initial s
  have hpc0 : s0.pc = 0 := rfl
  have hSz : p.code.size = 56 := rfl
  have hPlPre : Placed p.code 0
      (mulAddInstrs tinBase count registers.one 4 0 ++
       mulAddInstrs toutBase count registers.one 8 1 ++
       mulAddInstrs offsetBase count registers.one 9 1 ++
       mulAddInstrs childrenBase count registers.one 10 1 ++
       mulAddInstrs registers.remain count registers.one 1 0) :=
    placed_append_self_left _ _
  have hPl1 : Placed p.code 0 (mulAddInstrs tinBase count registers.one 4 0) :=
    placed_append_left (placed_append_left (placed_append_left (placed_append_left hPlPre)))
  have hPl2 : Placed p.code 5 (mulAddInstrs toutBase count registers.one 8 1) := by
    have h := placed_append_right (placed_append_left (placed_append_left (placed_append_left hPlPre)))
    simpa only [Nat.zero_add, mulAddInstrs_length] using h
  have hPl3 : Placed p.code 15 (mulAddInstrs offsetBase count registers.one 9 1) := by
    have h := placed_append_right (placed_append_left (placed_append_left hPlPre))
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hPl4 : Placed p.code 26 (mulAddInstrs childrenBase count registers.one 10 1) := by
    have h := placed_append_right (placed_append_left hPlPre)
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hPl5 : Placed p.code 38 (mulAddInstrs registers.remain count registers.one 1 0) := by
    have h := placed_append_right hPlPre
    simpa only [Nat.zero_add, List.length_append, mulAddInstrs_length] using h
  have hAt40 : p.code[40]? = some (.sub registers.remain registers.remain registers.one) := rfl
  have hAt41 : p.code[41]? = some (.imm registers.ptr ⟨0, Nat.one_le_two_pow⟩) := rfl
  have hc0 : (reg s0 count).val = Q := by simp [s0, hc]
  have ho0 : (reg s0 registers.one).val = 1 := by simp [s0, ho]
  obtain ⟨s1, hs1, hpc1, hd1, hTin1, ho1⟩ :=
    run_mulAddInstrs (input := input) tinBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s0 hpc0 (by rw [hSz]; omega) hPl1 hc0 ho0 (by omega)
  have hc1 : (reg s1 count).val = Q := by rw [ho1 count (fin_ne_of_val (by decide)), hc0]
  have ho1' : (reg s1 registers.one).val = 1 := by rw [ho1 registers.one (fin_ne_of_val (by decide)), ho0]
  obtain ⟨s2, hs2, hpc2, hd2, hTout2, ho2⟩ :=
    run_mulAddInstrs (input := input) toutBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s1 (by rw [hpc1]) (by rw [hSz]; omega) hPl2 hc1 ho1' (by omega)
  have hc2 : (reg s2 count).val = Q := by rw [ho2 count (fin_ne_of_val (by decide)), hc1]
  have ho2' : (reg s2 registers.one).val = 1 := by rw [ho2 registers.one (fin_ne_of_val (by decide)), ho1']
  obtain ⟨s3, hs3, hpc3, hd3, hOff3, ho3⟩ :=
    run_mulAddInstrs (input := input) offsetBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s2 (by rw [hpc2]) (by rw [hSz]; omega) hPl3 hc2 ho2' (by omega)
  have hc3 : (reg s3 count).val = Q := by rw [ho3 count (fin_ne_of_val (by decide)), hc2]
  have ho3' : (reg s3 registers.one).val = 1 := by rw [ho3 registers.one (fin_ne_of_val (by decide)), ho2']
  obtain ⟨s4, hs4, hpc4, hd4, hCh4, ho4⟩ :=
    run_mulAddInstrs (input := input) childrenBase count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s3 (by rw [hpc3]) (by rw [hSz]; omega) hPl4 hc3 ho3' (by omega)
  have hc4 : (reg s4 count).val = Q := by rw [ho4 count (fin_ne_of_val (by decide)), hc3]
  have ho4' : (reg s4 registers.one).val = 1 := by rw [ho4 registers.one (fin_ne_of_val (by decide)), ho3']
  obtain ⟨s5, hs5, hpc5, hd5, hRem5, ho5⟩ :=
    run_mulAddInstrs (input := input) registers.remain count registers.one
      (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
      s4 (by rw [hpc4]) (by rw [hSz]; omega) hPl5 hc4 ho4' (by omega)
  have hpc5' : s5.pc = 40 := by rw [hpc5]
  obtain ⟨s6, hs6, hpc6, h6rem, h6o, hd6⟩ :=
    step_sub_at (input := input) (by rw [hpc5']; exact hAt40) (by rw [hpc5', hSz]; omega)
  have h6remVal : (reg s6 registers.remain).val = Q - 1 := by
    have h5rem' : (reg s5 registers.remain).val = Q := by rw [hRem5]; omega
    have h5one' : (reg s5 registers.one).val = 1 := by rw [ho5 registers.one (fin_ne_of_val (by decide))]; exact ho4'
    rw [h6rem, PaperB.RamDomBuild.sub_exact_word _ _ (by rw [h5rem', h5one']; exact hQ), h5rem', h5one']
  have hpc6' : s6.pc = 41 := by rw [hpc6, hpc5']
  obtain ⟨s7, hs7, hpc7, h7p, ho7, hd7⟩ :=
    step_imm_at (input := input) (by rw [hpc6']; exact hAt41) (by rw [hpc6', hSz]; omega)
  have hpc7' : s7.pc = 42 := by rw [hpc7, hpc6']
  have hd7Eq : s7.data = s.data := by rw [hd7, hd6, hd5, hd4, hd3, hd2, hd1, initial_data]
  have hz7 : (reg s7 registers.zero).val = 0 := by
    rw [ho7 registers.zero (fin_ne_of_val (by decide)), h6o registers.zero (fin_ne_of_val (by decide)),
        ho5 registers.zero (fin_ne_of_val (by decide)), ho4 registers.zero (fin_ne_of_val (by decide)),
        ho3 registers.zero (fin_ne_of_val (by decide)), ho2 registers.zero (fin_ne_of_val (by decide)),
        ho1 registers.zero (fin_ne_of_val (by decide)), initial_reg]; exact hz
  have ho7' : (reg s7 registers.one).val = 1 := by
    rw [ho7 registers.one (fin_ne_of_val (by decide)), h6o registers.one (fin_ne_of_val (by decide)),
        ho5 registers.one (fin_ne_of_val (by decide))]; exact ho4'
  have hc7 : (reg s7 count).val = Q := by
    rw [ho7 count (fin_ne_of_val (by decide)), h6o count (fin_ne_of_val (by decide)),
        ho5 count (fin_ne_of_val (by decide))]; exact hc4
  have hTin7 : (reg s7 tinBase).val = 4 * Q := by
    rw [ho7 tinBase (fin_ne_of_val (by decide)), h6o tinBase (fin_ne_of_val (by decide)),
        ho5 tinBase (fin_ne_of_val (by decide)), ho4 tinBase (fin_ne_of_val (by decide)),
        ho3 tinBase (fin_ne_of_val (by decide)), ho2 tinBase (fin_ne_of_val (by decide)), hTin1, Nat.add_zero]
  have hTout7 : (reg s7 toutBase).val = 8 * Q + 1 := by
    rw [ho7 toutBase (fin_ne_of_val (by decide)), h6o toutBase (fin_ne_of_val (by decide)),
        ho5 toutBase (fin_ne_of_val (by decide)), ho4 toutBase (fin_ne_of_val (by decide)),
        ho3 toutBase (fin_ne_of_val (by decide)), hTout2]
  have hOff7 : (reg s7 offsetBase).val = 9 * Q + 1 := by
    rw [ho7 offsetBase (fin_ne_of_val (by decide)), h6o offsetBase (fin_ne_of_val (by decide)),
        ho5 offsetBase (fin_ne_of_val (by decide)), ho4 offsetBase (fin_ne_of_val (by decide)), hOff3]
  have hCh7 : (reg s7 childrenBase).val = 10 * Q + 1 := by
    rw [ho7 childrenBase (fin_ne_of_val (by decide)), h6o childrenBase (fin_ne_of_val (by decide)),
        ho5 childrenBase (fin_ne_of_val (by decide)), hCh4]
  have hRem7 : (reg s7 registers.remain).val = Q - 1 := by
    rw [ho7 registers.remain (fin_ne_of_val (by decide)), h6remVal]
  obtain ⟨t, htSteps, htpc, htz, hto, htc, htEnt, htStop, htFrame⟩ :=
    childIntervals_iter entryFn stopFn childFn hQFit hWork hChild (Q - 1) 0 s7 hpc7' (by omega)
      (by rw [hd7Eq, s.data_size]) hz7 ho7' hc7 hTin7 hTout7 hOff7 hCh7 hRem7 (by rw [h7p])
      (fun k hk => by rw [hd7Eq]; exact hCData k hk)
      (fun c hcu => by rw [hd7Eq]; exact hEData c hcu)
      (fun c hcu => by rw [hd7Eq]; exact hSData c hcu)
  have hHalt : step p.code input t = some (.halted t) := by
    apply step_halt_at; rw [htpc]; rfl
  have hSetupSteps : Steps p.code input 42 s0 s7 :=
    ((((hs1.append hs2).append hs3).append hs4).append hs5).append (Steps.cons hs6 (Steps.cons hs7 (.zero _)))
  have hAllSteps : Steps p.code input (42 + (13 * (Q - 1) + 1)) s0 t := hSetupSteps.append htSteps
  refine ⟨t, 42 + (13 * (Q - 1) + 1) + 1, by omega, hAllSteps.halts hHalt,
    htz, hto, htc, fun k hk => htEnt k (Nat.zero_le _) hk, fun k hk => htStop k (Nat.zero_le _) hk, fun j hj => ?_⟩
  rw [htFrame j (by omega), hd7Eq]

end Phase2C

section StaticBridge

open PaperB.PackedStaticLayout
open PaperB.StaticHeadSweep
open PaperB.StaticLinearHead
open PaperB.StaticTreeReader
open ExactOrderedChildIntervals

def staticInput {Q : Nat} (hn : 1 ≤ Q) (parent : Fin Q → Fin Q) (depth : Fin Q → Nat) :
    PackedStaticLayout.Input Q :=
  ⟨⟨0, hn⟩, PackedStaticLayout.tabulate parent, PackedStaticLayout.tabulate depth⟩

theorem staticInputOK {Q : Nat} (hn : 1 ≤ Q) {parent : Fin Q → Fin Q} {depth : Fin Q → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth) :
    PackedStaticLayout.InputOK (staticInput hn parent depth) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [staticInput, PackedStaticLayout.read_tabulate] using hTree.parent_root
  · simpa only [staticInput, PackedStaticLayout.read_tabulate] using hTree.depth_root
  · intro u hu
    simpa only [staticInput, PackedStaticLayout.read_tabulate] using hTree.depth_step u hu

@[simp] private theorem read_tabulate_fun {N : Nat} {α : Type} (f : Fin N → α) :
    (PackedStaticLayout.tabulate f).read = f :=
  funext (PackedStaticLayout.read_tabulate f)

private theorem dfsSubtree_length_pos {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (hTree : ValidDepthTree root parent depth) (v : Fin N) :
    0 < (dfsSubtree root parent depth v).length := by
  rw [dfsSubtree_unfold hTree v]
  simp

private theorem length_concatMapList {α β : Type} (f : α → List β) (xs : List α) :
    (concatMapList f xs).length = (xs.map (fun c => (f c).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [concatMapList, List.length_append, List.map_cons, List.sum_cons, ih]

private theorem preceding_succ {α β : Type} (f : α → List β) (xs : List α)
    {i : Nat} (hi : i < xs.length) :
    preceding f xs (i + 1) = preceding f xs i + (f (xs[i]'hi)).length := by
  unfold preceding
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

private theorem preceding_step {α β : Type} (f : α → List β) (xs : List α) (i : Nat) :
    preceding f xs i ≤ preceding f xs (i + 1) := by
  by_cases hi : i < xs.length
  · rw [preceding_succ f xs hi]; exact Nat.le_add_right _ _
  · have h1 : xs.take i = xs := List.take_of_length_le (Nat.le_of_not_lt hi)
    have h2 : xs.take (i + 1) = xs := List.take_of_length_le (by omega)
    unfold preceding; rw [h1, h2]; exact Nat.le_refl _

private theorem preceding_mono {α β : Type} (f : α → List β) (xs : List α)
    {a b : Nat} (hab : a ≤ b) :
    preceding f xs a ≤ preceding f xs b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact Nat.le_trans (ih (Nat.le_add_right a d)) (preceding_step f xs (a + d))

private theorem preceding_lt_of_lt {α β : Type} (f : α → List β) (xs : List α)
    (hPos : ∀ c ∈ xs, 0 < (f c).length) {i j : Nat} (hij : i < j) (hj : j < xs.length) :
    preceding f xs i < preceding f xs j := by
  have hi : i < xs.length := by omega
  have h1 := preceding_succ f xs hi
  have h2 := preceding_mono f xs (show i + 1 ≤ j by omega)
  have hMem : xs[i]'hi ∈ xs := List.getElem_mem hi
  have hp := hPos _ hMem
  omega

private theorem preceding_le_sum {α β : Type} (f : α → List β) (xs : List α) (i : Nat) :
    preceding f xs i ≤ (xs.map (fun c => (f c).length)).sum := by
  by_cases hLt : i < xs.length
  · have h := preceding_mono f xs (show i ≤ xs.length by omega)
    simpa only [preceding, List.take_length] using h
  · unfold preceding
    rw [List.take_of_length_le (Nat.le_of_not_lt hLt)]
    exact Nat.le_refl _

private theorem entry_root_zero {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (hTree : ValidDepthTree root parent depth) :
    entry root parent depth root = 0 := by
  have hPre : dfsPreorder root parent depth = dfsSubtree root parent depth root := rfl
  have hU : dfsSubtree root parent depth root =
      root :: concatMapList (dfsSubtree root parent depth) (bucketChildren root parent root) :=
    dfsSubtree_unfold hTree root
  have hLt : entry root parent depth root < (dfsPreorder root parent depth).length :=
    entry_lt_length_dfsPreorder hTree root
  have hRootPos : 0 < (dfsPreorder root parent depth).length := by rw [length_dfsPreorder hTree]; exact Fin.pos root
  have hGet0 : (dfsPreorder root parent depth)[0]? = some root := by rw [hPre, hU]; rfl
  have hNodup := nodup_dfsPreorder hTree
  cases hE : entry root parent depth root with
  | zero => rfl
  | succ k =>
    have hIn : k + 1 < (dfsPreorder root parent depth).length := by omega
    have hEq := (firstOccurrence_eq_iff root (mem_dfsPreorder hTree root) 0).mpr
      ⟨[], concatMapList (dfsSubtree root parent depth) (bucketChildren root parent root),
       by rw [hPre, hU]; rfl, by simp, rfl⟩
    change firstOccurrence root (dfsPreorder root parent depth) = 0 at hEq
    exact hE.symm.trans hEq

private theorem entry_add_subtree_le {Q : Nat} (hn : 1 ≤ Q)
    {parent : Fin Q → Fin Q} {depth : Fin Q → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth) :
    ∀ d (v : Fin Q), depth v = d →
      entry ⟨0, hn⟩ parent depth v + (dfsSubtree ⟨0, hn⟩ parent depth v).length ≤ Q := by
  intro d
  induction d with
  | zero =>
    intro v hdv
    have hvRoot : v = ⟨0, hn⟩ := by
      by_cases hv : v = ⟨0, hn⟩
      · exact hv
      · have hs := hTree.depth_step v hv; omega
    subst hvRoot
    rw [entry_root_zero hTree, Nat.zero_add]
    change (dfsPreorder ⟨0, hn⟩ parent depth).length ≤ Q
    rw [length_dfsPreorder hTree]
    exact Nat.le_refl Q
  | succ d ih =>
    intro v hdv
    have hvNe : v ≠ ⟨0, hn⟩ := by intro e; subst e; rw [hTree.depth_root] at hdv; omega
    have hStep := hTree.depth_step v hvNe
    have hParD : depth (parent v) = d := by omega
    have ihP := ih (parent v) hParD
    have hvMem : v ∈ bucketChildren ⟨0, hn⟩ parent (parent v) :=
      (mem_bucketChildren_iff ⟨0, hn⟩ parent (parent v) v).mpr ⟨hvNe, rfl⟩
    obtain ⟨i, hi, hGet⟩ := List.getElem_of_mem hvMem
    have hChildEnt := child_entry hTree (parent v) i hi
    rw [hGet] at hChildEnt
    have hSumLe : preceding (dfsSubtree ⟨0, hn⟩ parent depth) (bucketChildren ⟨0, hn⟩ parent (parent v)) (i + 1) ≤
        ((bucketChildren ⟨0, hn⟩ parent (parent v)).map (fun c => (dfsSubtree ⟨0, hn⟩ parent depth c).length)).sum :=
      preceding_le_sum _ _ _
    have hSuccP := preceding_succ (dfsSubtree ⟨0, hn⟩ parent depth) (bucketChildren ⟨0, hn⟩ parent (parent v)) hi
    rw [hGet] at hSuccP
    have hUnfP := congrArg List.length (dfsSubtree_unfold hTree (parent v))
    rw [List.length_cons, length_concatMapList] at hUnfP
    omega

private theorem entry_parent_lt_child {Q : Nat} (hn : 1 ≤ Q)
    {parent : Fin Q → Fin Q} {depth : Fin Q → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth)
    (v : Fin Q) (hvNe : v ≠ ⟨0, hn⟩) :
    entry ⟨0, hn⟩ parent depth (parent v) < entry ⟨0, hn⟩ parent depth v := by
  have hvMem : v ∈ bucketChildren ⟨0, hn⟩ parent (parent v) :=
    (mem_bucketChildren_iff ⟨0, hn⟩ parent (parent v) v).mpr ⟨hvNe, rfl⟩
  obtain ⟨i, hi, hGet⟩ := List.getElem_of_mem hvMem
  have hChildEnt := child_entry hTree (parent v) i hi
  rw [hGet] at hChildEnt
  omega

private theorem heavyScanAux_eq_foldl {Q : Nat} (szFn childFn : Nat → Nat)
    (hSzPos : ∀ c, c < Q → 0 < szFn c) :
    ∀ (xs : List (Fin Q)) (off bestC bestS : Nat) (acc : ForestHeavyPath.Scan (Fin Q)),
      (∀ k (hk : k < xs.length), childFn (off + k) = (xs[k]'hk).val) →
      (acc.best = none → bestC = Q ∧ bestS = 0) →
      (∀ w, acc.best = some w → bestC = w.node.val ∧ bestS = w.score) →
      heavyScanAux szFn childFn off xs.length bestC bestS =
        match (xs.foldl (ForestHeavyPath.scanStep (fun c : Fin Q => szFn c.val)) acc).best with
        | none => Q
        | some w => w.node.val := by
  intro xs
  induction xs with
  | nil =>
    intro off bestC bestS acc _ hNone hSome
    simp only [List.length_nil, List.foldl_nil, heavyScanAux]
    cases hB : acc.best with
    | none => exact (hNone hB).1
    | some w => exact (hSome w hB).1
  | cons x xs ih =>
    intro off bestC bestS acc hEq hNone hSome
    simp only [List.length_cons, List.foldl_cons, heavyScanAux]
    have hxEq : childFn off = x.val := by
      have h0 := hEq 0 (Nat.zero_lt_succ _)
      rw [Nat.add_zero] at h0
      exact h0
    rw [hxEq]
    have hxPos : 0 < szFn x.val := hSzPos x.val x.isLt
    let acc' := ForestHeavyPath.scanStep (fun c : Fin Q => szFn c.val) acc x
    have hNextEq : ∀ k (hk : k < xs.length), childFn ((off + 1) + k) = (xs[k]'hk).val := fun k hk => by
      have h1 := hEq (k + 1) (Nat.succ_lt_succ hk)
      rw [show off + (k + 1) = (off + 1) + k by omega] at h1
      exact h1
    cases hB : acc.best with
    | none =>
      obtain ⟨rfl, rfl⟩ := hNone hB
      simp only [hxPos, ite_true]
      apply ih (off + 1) x.val (szFn x.val) acc' hNextEq
      · intro hAbs; simp [acc', ForestHeavyPath.scanStep, hB] at hAbs
      · intro w hw
        simp only [acc', ForestHeavyPath.scanStep, hB, Option.some.injEq] at hw
        subst w; exact ⟨rfl, rfl⟩
    | some old =>
      obtain ⟨rfl, rfl⟩ := hSome old hB
      by_cases hLt : old.score < szFn x.val
      · simp only [hLt, ite_true]
        apply ih (off + 1) x.val (szFn x.val) acc' hNextEq
        · intro hAbs; simp [acc', ForestHeavyPath.scanStep, hB] at hAbs
        · intro w hw
          simp only [acc', ForestHeavyPath.scanStep, hB, hLt, ite_true, Option.some.injEq] at hw
          subst w; exact ⟨rfl, rfl⟩
      · simp only [hLt, ite_false]
        apply ih (off + 1) old.node.val old.score acc' hNextEq
        · intro hAbs; simp [acc', ForestHeavyPath.scanStep, hB] at hAbs
        · intro w hw
          simp only [acc', ForestHeavyPath.scanStep, hB, hLt, ite_false, Option.some.injEq] at hw
          subst w; exact ⟨rfl, rfl⟩

private theorem heavySpec_eq_packed {Q : Nat} (hn : 1 ≤ Q)
    {parent : Fin Q → Fin Q} {depth : Fin Q → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth)
    (startFn entryFn stopFn childFn : Nat → Nat)
    (hEnt : ∀ v : Fin Q, entryFn v.val = entry ⟨0, hn⟩ parent depth v)
    (hStop : ∀ v : Fin Q, stopFn v.val = entry ⟨0, hn⟩ parent depth v + (dfsSubtree ⟨0, hn⟩ parent depth v).length)
    (u : Fin Q)
    (hLen : startFn (u.val + 1) - startFn u.val = (bucketChildren ⟨0, hn⟩ parent u).length)
    (hKids : ∀ k (hk : k < (bucketChildren ⟨0, hn⟩ parent u).length),
      childFn (startFn u.val + k) = ((bucketChildren ⟨0, hn⟩ parent u)[k]'hk).val) :
    heavySpec Q startFn entryFn stopFn childFn u.val =
      match (PackedStaticLayout.build (staticInput hn parent depth)).packed.heavy.read u with
      | none => Q
      | some w => w.val := by
  let x := staticInput hn parent depth
  have hx : PackedStaticLayout.InputOK x := staticInputOK hn hTree
  have hRead := PackedStaticLayout.heavy_read x u
  have hSzEq : ∀ c : Fin Q,
      (PackedStaticLayout.build x).packed.size.read c = stopFn c.val - entryFn c.val := by
    intro c
    rw [PackedStaticLayout.size_read x c, PackedStaticLayout.entry_exact x hx c, PackedStaticLayout.stop_exact x hx c,
        hEnt c, hStop c]
    simp only [x, staticInput, read_tabulate_fun]
  have hBktEq : (PackedStaticLayout.build x).buckets.get u = bucketChildren ⟨0, hn⟩ parent u := by
    rw [PackedStaticLayout.bucket_read x u]
    simp only [x, staticInput, read_tabulate_fun]
  unfold heavySpec
  dsimp only
  rw [hLen]
  have hAux := heavyScanAux_eq_foldl (Q := Q) (fun c => stopFn c - entryFn c) childFn
    (fun c hc => by
      let cf : Fin Q := ⟨c, hc⟩
      have h1 : entryFn c = entry ⟨0, hn⟩ parent depth cf := hEnt cf
      have h2 : stopFn c = entry ⟨0, hn⟩ parent depth cf + (dfsSubtree ⟨0, hn⟩ parent depth cf).length := hStop cf
      have hp := dfsSubtree_length_pos hTree cf
      omega)
    (bucketChildren ⟨0, hn⟩ parent u) (startFn u.val) Q 0
    { seen := 0, comparisons := 0, best := none } hKids
    (fun _ => ⟨rfl, rfl⟩) (fun _ h => by cases h)
  rw [hAux]
  rw [hRead, hBktEq]
  have hFoldEq : (bucketChildren ⟨0, hn⟩ parent u).foldl
      (ForestHeavyPath.scanStep (fun c : Fin Q => stopFn c.val - entryFn c.val))
      { seen := 0, comparisons := 0, best := none } =
    ForestHeavyPath.scan (PackedStaticLayout.build x).packed.size.read (bucketChildren ⟨0, hn⟩ parent u) := by
    unfold ForestHeavyPath.scan
    have hFun : (fun c : Fin Q => stopFn c.val - entryFn c.val) = (PackedStaticLayout.build x).packed.size.read := by
      funext c; exact (hSzEq c).symm
    rw [hFun]
  rw [hFoldEq]
  cases ((ForestHeavyPath.scan (PackedStaticLayout.build x).packed.size.read (bucketChildren ⟨0, hn⟩ parent u)).best) <;> rfl

private theorem headSweepSpec_eq_tables {Q : Nat} (hn : 1 ≤ Q)
    {parent : Fin Q → Fin Q} {depth : Fin Q → Nat}
    (hTree : ValidDepthTree ⟨0, hn⟩ parent depth)
    (hParLt : ∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val)
    (parentFn heavyFn : Nat → Nat)
    (hPar : ∀ v : Fin Q, parentFn v.val = (parent v).val)
    (hHv : ∀ u : Fin Q, heavyFn u.val =
      match (PackedStaticLayout.build (staticInput hn parent depth)).packed.heavy.read u with
      | none => Q
      | some w => w.val) :
    ∀ k (hk : k < Q),
      headSweepSpec parentFn heavyFn k =
        ((StaticHeadSweep.tables (PackedStaticLayout.build (staticInput hn parent depth)).packed).head ⟨k, hk⟩).val := by
  suffices hAll : ∀ bound k (hk : k < Q), k ≤ bound →
      headSweepSpec parentFn heavyFn k =
        ((StaticHeadSweep.tables (PackedStaticLayout.build (staticInput hn parent depth)).packed).head ⟨k, hk⟩).val from
    fun k hk => hAll k k hk (Nat.le_refl k)
  intro bound
  induction bound with
  | zero =>
    intro k hk hLe
    have hk0 : k = 0 := by omega
    subst hk0
    let x := staticInput hn parent depth
    have hx : PackedStaticLayout.InputOK x := staticInputOK hn hTree
    let p := (PackedStaticLayout.build x).packed
    have hRead := StaticHeadSweep.build_read_eq p hx ⟨0, hk⟩
    have hTbl : (StaticHeadSweep.tables p).head ⟨0, hk⟩ = (StaticHeadSweep.build p).heads.read ⟨0, hk⟩ := rfl
    have hNotInh : ¬ StaticHeadSweep.Inherits p ⟨0, hk⟩ := fun h => h.1 rfl
    rw [show ((StaticHeadSweep.tables p).head ⟨0, hk⟩).val = ((StaticHeadSweep.build p).heads.read ⟨0, hk⟩).val by rw [hTbl],
        hRead, ite_eq_right hNotInh, headSweepSpec]
  | succ bound ih =>
    intro k hk hLe
    let x := staticInput hn parent depth
    have hx : PackedStaticLayout.InputOK x := staticInputOK hn hTree
    let p := (PackedStaticLayout.build x).packed
    have hRead := StaticHeadSweep.build_read_eq p hx ⟨k, hk⟩
    have hTbl : (StaticHeadSweep.tables p).head ⟨k, hk⟩ = (StaticHeadSweep.build p).heads.read ⟨k, hk⟩ := rfl
    change _ = ((StaticHeadSweep.tables p).head ⟨k, hk⟩).val
    rw [hTbl, hRead]
    by_cases hk0 : k = 0
    · subst hk0
      have hNotInh : ¬ StaticHeadSweep.Inherits p ⟨0, hk⟩ := fun h => h.1 rfl
      rw [ite_eq_right hNotInh, headSweepSpec]
    · have hkPos : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hParLtK : parentFn k < k := by
        have := hParLt ⟨k, hk⟩ hkPos
        rw [← hPar ⟨k, hk⟩] at this
        exact this
      have hParRead : p.parent.read ⟨k, hk⟩ = parent ⟨k, hk⟩ := by
        change x.parent.read ⟨k, hk⟩ = parent ⟨k, hk⟩
        simp [x, staticInput]
      have hParLtNat : (parent ⟨k, hk⟩).val < k := hParLt ⟨k, hk⟩ hkPos
      have ihP := ih (parent ⟨k, hk⟩).val (parent ⟨k, hk⟩).isLt (by omega)
      rw [headSweepSpec_succ hkPos hParLtK]
      have hParFnK : parentFn k = (parent ⟨k, hk⟩).val := hPar ⟨k, hk⟩
      have hHvEq : heavyFn (parentFn k) = k ↔
          StaticHeadSweep.Inherits p ⟨k, hk⟩ := by
        rw [hParFnK, hHv (parent ⟨k, hk⟩)]
        unfold StaticHeadSweep.Inherits
        rw [hParRead]
        constructor
        · intro hEq
          refine ⟨fun e => hk0 (congrArg Fin.val e), ?_⟩
          cases hR : p.heavy.read (parent ⟨k, hk⟩) with
          | none => rw [hR] at hEq; simp only at hEq; omega
          | some w => rw [hR] at hEq; exact congrArg some (Fin.ext hEq)
        · intro hInh
          rw [hInh.2]
      by_cases hInh : StaticHeadSweep.Inherits p ⟨k, hk⟩
      · have hEq : heavyFn (parentFn k) = k := hHvEq.mpr hInh
        rw [ite_eq_left hEq, ite_eq_left hInh, hParFnK, hParRead]
        have hTblP : (StaticHeadSweep.tables p).head (parent ⟨k, hk⟩) =
            (StaticHeadSweep.build p).heads.read (parent ⟨k, hk⟩) := rfl
        rw [← hTblP]
        simpa only [Fin.eta] using ihP
      · have hNe : heavyFn (parentFn k) ≠ k := fun e => hInh (hHvEq.mp e)
        rw [ite_eq_right hNe, ite_eq_right hInh]

private theorem sumBucketLengths_eq_sum {N : Nat} (f : Fin N → List (Fin N)) (xs : List (Fin N)) :
    sumBucketLengths f xs = (xs.map (fun x => (f x).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold sumBucketLengths
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]

private theorem childImage_exact {bits workCap Q : Nat} (hn : 1 ≤ Q)
    (a : Arena bits workCap Q) (hCh : a.children = Q - 1)
    {parent : Fin Q → Fin Q} {data : Array (Word bits)}
    (hImg : ChildImage a (bucketChildLists ⟨0, hn⟩ parent) data) :
    (data[a.offsets + 0]?).map Fin.val = some 0 ∧
    (data[a.offsets + Q]?).map Fin.val = some (Q - 1) ∧
    (∀ u : Fin Q, ∃ lo hi : Nat,
      (data[a.offsets + u.val]?).map Fin.val = some lo ∧
      (data[a.offsets + u.val + 1]?).map Fin.val = some hi ∧
      hi = lo + (bucketChildren ⟨0, hn⟩ parent u).length ∧
      hi ≤ Q - 1 ∧
      (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hn⟩ parent u).length,
        (data[a.payload + lo + j]?).map Fin.val = some ((bucketChildren ⟨0, hn⟩ parent u)[j]'hj).val)) := by
  have hStep : ∀ u : Fin Q, ∃ lo hi : Nat,
      (data[a.offsets + u.val]?).map Fin.val = some lo ∧
      (data[a.offsets + u.val + 1]?).map Fin.val = some hi ∧
      hi = lo + (bucketChildren ⟨0, hn⟩ parent u).length ∧
      hi ≤ Q - 1 ∧
      (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hn⟩ parent u).length,
        (data[a.payload + lo + j]?).map Fin.val = some ((bucketChildren ⟨0, hn⟩ parent u)[j]'hj).val) := by
    intro u
    obtain ⟨lo, stop, hLo, hSt, hDeg, hFit, hWords⟩ := hImg u
    have hLenEq : (PaperB.RamForestProgram.Finish.childrenOf a (bucketChildLists ⟨0, hn⟩ parent) u).length =
        (bucketChildren ⟨0, hn⟩ parent u).length := by
      simp [PaperB.RamForestProgram.Finish.childrenOf, bucketChildLists_get]
    refine ⟨lo.val, stop.val, by rw [hLo]; rfl, by rw [hSt]; rfl, by omega, by omega, fun j hj => ?_⟩
    have hj' : j < (PaperB.RamForestProgram.Finish.childrenOf a (bucketChildLists ⟨0, hn⟩ parent) u).length := by
      rw [hLenEq]; exact hj
    rw [hWords j hj']
    have hGet : (bucketChildren ⟨0, hn⟩ parent u)[j]? = some ((bucketChildren ⟨0, hn⟩ parent u)[j]'hj) :=
      List.getElem?_eq_getElem hj
    simp [PaperB.RamForestProgram.Finish.childrenOf, bucketChildLists_get, hGet, PaperB.RamForestStack.commandWord]
  -- Chain `data[a.offsets + k]?` to `lo0 + ∑_{i < k} deg i`
  obtain ⟨lo0, _, hLo0, _, _, _, _⟩ := hStep ⟨0, hn⟩
  have hOffChain : ∀ k (hk : k ≤ Q),
      (data[a.offsets + k]?).map Fin.val =
        some (lo0 + (((finElems Q).take k).map (fun x => (bucketChildren ⟨0, hn⟩ parent x).length)).sum) := by
    intro k
    induction k with
    | zero =>
      intro _; simpa only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] using hLo0
    | succ k ih =>
      intro hk
      have hkLt : k < Q := by omega
      obtain ⟨lok, hik, hLok, hHik, hEqk, _, _⟩ := hStep ⟨k, hkLt⟩
      have ihk := ih (by omega)
      rw [hLok, Option.some.injEq] at ihk
      have hTake : (finElems Q).take (k + 1) = (finElems Q).take k ++ [⟨k, hkLt⟩] := by
        have hkLen : k < (finElems Q).length := by rw [length_finElems]; exact hkLt
        rw [List.take_succ_eq_append_getElem hkLen, PaperB.RamForestProgram.Finish.finElems_index Q ⟨k, hkLt⟩]
      rw [hTake, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hRhs :
          lo0 + ((((finElems Q).take k).map (fun x => (bucketChildren ⟨0, hn⟩ parent x).length)).sum +
            (bucketChildren ⟨0, hn⟩ parent ⟨k, hkLt⟩).length) = hik := by
        omega
      rw [hRhs]
      exact hHik
  have hQChain := hOffChain Q (Nat.le_refl Q)
  have hTakeAll : (finElems Q).take Q = finElems Q := by
    apply List.take_of_length_le; rw [length_finElems]; exact Nat.le_refl Q
  rw [hTakeAll, ← sumBucketLengths_eq_sum, total_bucketChildren_edges ⟨0, hn⟩ parent] at hQChain
  obtain ⟨_, hiLast, _, hLastAt, _, hLastLe, _⟩ := hStep ⟨Q - 1, by omega⟩
  change (data[a.offsets + (Q - 1) + 1]?).map Fin.val = some hiLast at hLastAt
  rw [show a.offsets + (Q - 1) + 1 = a.offsets + Q by omega] at hLastAt
  rw [hLastAt, Option.some.injEq] at hQChain
  have hLo0Zero : lo0 = 0 := by omega
  have hEndEq : hiLast = Q - 1 := by omega
  refine ⟨by simpa only [hLo0Zero] using hLo0, by rw [hLastAt, hEndEq], hStep⟩

end StaticBridge

section MainPipeline

open PaperB.PackedStaticLayout
open PaperB.StaticHeadSweep
open PaperB.StaticTreeReader
open ExactOrderedChildIntervals

def linkNonEmpty {bits : Nat} {L : Layout bits} (p : Phase L) : List (Phase L) → Phase L
  | [] => p
  | q :: qs => p.link (linkNonEmpty q qs)

theorem run_linkNonEmpty {bits : Nat} {L : Layout bits} {input : Input L} :
    ∀ (ps : List (Phase L)) (p : Phase L) {s t : State L} {w : Nat},
      PhasesExec input (p :: ps) s t w →
      ∃ u states,
        u.regs = t.regs ∧
        u.data = t.data ∧
        run (linkNonEmpty p ps).code input w (Phase.initial s) = some ⟨u, w⟩ ∧
        SuccessfulTrace (linkNonEmpty p ps).code input (Phase.initial s) states ⟨u, w⟩ ∧
        tracePeakWords input states = footprint L
  | [], p, s, t, w, h => by
    cases h with
    | cons hr hNil =>
      cases hNil with
      | nil =>
        rw [Nat.add_zero]
        obtain ⟨states, hTrace⟩ := run_has_successfulTrace hr
        exact ⟨t, states, rfl, rfl, hr, hTrace, hTrace.peak_eq⟩
  | q :: qs, p, s, t, w, h => by
    cases h with
    | cons hr hTail =>
      obtain ⟨mid, _, hMidRegs, hMidData, hMidRun, _, _⟩ := run_linkNonEmpty qs q hTail
      have hMidInit : Phase.initial mid = Phase.initial _ := rfl
      have hMidRun' : run (linkNonEmpty q qs).code input _ (Phase.initial _) = some ⟨mid, _⟩ := hMidRun
      have hSize : 0 < (linkNonEmpty q qs).code.size :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (linkNonEmpty q qs).haltFits
      obtain ⟨v, states, hvRegs, hvData, hvRun, hvTrace, hvPeak⟩ :=
        run_linked_pair p (linkNonEmpty q qs).code hSize hr hMidRun'
      refine ⟨v, states, hvRegs.trans hMidRegs, hvData.trans hMidData, ?_, ?_, hvPeak⟩
      · exact hvRun
      · exact hvTrace

private def domAndStaticTreeTail {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    List (Phase (layout bits inputCap workCap hi hw)) :=
  [ copySetupPhase hi hw 0 0 6 0 1 0 0
  , copyLoopPhase hi hw
  , setArenaCtrlPhase hi hw 6
  ] ++
  finishPhases (hi := hi) (hw := hw) ++
  [ reloadQPhase hi hw hTen
  , copySetupPhase hi hw 0 0 11 0 1 0 0
  , copyLoopPhase hi hw
  , setArenaCtrlPhase hi hw 11
  ] ++
  csrPhases (hi := hi) (hw := hw) ++
  [ reloadQPhase hi hw hTen
  , copySetupPhase hi hw 15 0 7 0 1 1 0
  , copyLoopPhase hi hw
  , copySetupPhase hi hw 16 1 10 1 1 0 1
  , copyLoopPhase hi hw
  , denseOfEntryPhase hi hw
  , heavyPhase hi hw
  , headPhase hi hw
  , childIntervalsPhase hi hw
  ]

def domAndStaticTreePhases {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    List (Phase (layout bits inputCap workCap hi hw)) :=
  domBuildPhase hi hw hTen :: domAndStaticTreeTail hi hw hTen

def domAndStaticTreePhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  linkNonEmpty (domBuildPhase hi hw hTen) (domAndStaticTreeTail hi hw hTen)

def domAndStaticTreeProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  (domAndStaticTreePhase hi hw hTen).code

private theorem run_tail_finish {bits inputCap workCap Q : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {input : Input (layout bits inputCap workCap hi hw)}
    (hQ : 1 ≤ Q) (hDataCap : 17 * Q ≤ workCap) (hWordCap : 17 * Q < 2 ^ bits)
    (parent : Fin Q → Fin Q) (depth : Fin Q → Nat)
    (hTree : ValidDepthTree ⟨0, hQ⟩ parent depth)
    (s1 : State (layout bits inputCap workCap hi hw))
    (hPar1 : ∀ v : Fin Q, (s1.data[v.val]?).map Fin.val = some (parent v).val)
    (hz1 : (reg s1 registers.zero).val = 0)
    (ho1 : (reg s1 registers.one).val = 1)
    (hc1 : (reg s1 count).val = Q) :
    ∃ s5 w5,
      w5 ≤ 113 * Q + 112 ∧
      PhasesExec input
        ([ copySetupPhase hi hw 0 0 6 0 1 0 0
         , copyLoopPhase hi hw
         , setArenaCtrlPhase hi hw 6
         ] ++ finishPhases (hi := hi) (hw := hw)) s1 s5 w5 ∧
      ColumnAt (n := Q) (4 * Q) (ForestLayout.layout (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ (2 * Q)).entries s5.data ∧
      ColumnAt (n := Q) (4 * Q + Q) (ForestLayout.layout (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ (2 * Q)).ends s5.data ∧
      (∀ j, j < 4 * Q → s5.data[j]? = s1.data[j]?) := by
  obtain ⟨s2, hr2, hd2, hz2, ho2, hc2, hTin2, hTout2, hRem2, hClk2⟩ :=
    run_copySetup (input := input) 0 0 6 0 1 0 0 Q s1 hz1 ho1 hc1
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, hr3, hz3, ho3, hc3, hCopy3, hKeep3⟩ :=
    run_copyLoop (input := input) (Q := Q) (src := 0) (dst := 6 * Q) (len := Q)
      (by omega) (by omega) (Or.inl (by omega)) (by omega) s2
      hz2 ho2 hc2 (by simpa only [Nat.zero_mul, Nat.add_zero] using hTin2)
      (by simpa only [Nat.add_zero] using hTout2)
      (by simpa only [Nat.one_mul, Nat.add_zero, Nat.sub_zero] using hRem2) hClk2
  let aFinish : Arena bits workCap Q :=
    { base := 6 * Q, children := Q - 1, room := by omega, wordFits := by omega }
  obtain ⟨s4, hr4, hd4, hCtrl4, hCmd4, hPtr4, _⟩ :=
    run_setArenaCtrl (input := input) hQ aFinish rfl s3 hz3 ho3 hc3
  have hMass : rowPrefix (parentDegree ⟨0, hQ⟩ parent) Q ≤ Q - 1 := rowPrefix_parentDegree_le hQ ⟨0, hQ⟩ parent
  have hPar4 : ParentAt aFinish parent s4.data := by
    intro v
    rw [hd4, hCopy3 v.val v.isLt, hd2]
    simpa only [Nat.zero_add] using hPar1 v
  have hDstFinish : aFinish.base - 2 * Q = 4 * Q := by simp [aFinish]; omega
  obtain ⟨s5, w5, hw5, hExec5, hEnt5, hEnd5, hKeep5⟩ :=
    phasesExec_finish (input := input) hQ (a := aFinish) hTree hMass (by simp [aFinish]) (by simp [aFinish]; omega)
      s4 hCtrl4 hCmd4 hPar4 hPtr4
  rw [hDstFinish] at hEnt5 hEnd5 hKeep5
  refine ⟨s5, _, ?_, PhasesExec.cons hr2 (PhasesExec.cons hr3 (PhasesExec.cons hr4 hExec5)),
    hEnt5, hEnd5, fun j hj => ?_⟩
  · simp only [copySetupInstrs_length, setArenaCtrlInstrs_length]
    omega
  · rw [hKeep5 j hj, hd4, hKeep3 j (Or.inl (by omega)), hd2]

private theorem run_tail_csr {bits inputCap workCap Q mReach : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {inStart inSrc : Nat → Nat}
    {input : Input (layout bits inputCap workCap hi hw)}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    (hDataCap : 17 * Q ≤ workCap) (hWordCap : 17 * Q < 2 ^ bits) (hTen : 10 ≤ 2 ^ bits)
    (parent : Fin Q → Fin Q)
    (s5 : State (layout bits inputCap workCap hi hw))
    (hPar5 : ∀ v : Fin Q, (s5.data[v.val]?).map Fin.val = some (parent v).val) :
    ∃ s15 w_csr,
      w_csr ≤ 63 * Q + 208 ∧
      PhasesExec input
        ([ reloadQPhase hi hw hTen
         , copySetupPhase hi hw 0 0 11 0 1 0 0
         , copyLoopPhase hi hw
         , setArenaCtrlPhase hi hw 11
         ] ++ csrPhases (hi := hi) (hw := hw) ++
         [ reloadQPhase hi hw hTen
         , copySetupPhase hi hw 15 0 7 0 1 1 0
         , copyLoopPhase hi hw
         , copySetupPhase hi hw 16 1 10 1 1 0 1
         , copyLoopPhase hi hw
         ]) s5 s15 w_csr ∧
      (reg s15 registers.zero).val = 0 ∧
      (reg s15 registers.one).val = 1 ∧
      (reg s15 count).val = Q ∧
      (∀ j, j < 7 * Q → s15.data[j]? = s5.data[j]?) ∧
      (s15.data[7 * Q]?).map Fin.val = some 0 ∧
      (s15.data[8 * Q]?).map Fin.val = some (Q - 1) ∧
      (∀ u : Fin Q,
        ∃ lo hiB : Nat,
          (s15.data[7 * Q + u.val]?).map Fin.val = some lo ∧
          (s15.data[7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
          hiB = lo + (bucketChildren ⟨0, sp.qPos⟩ parent u).length ∧
          hiB ≤ Q - 1 ∧
          (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, sp.qPos⟩ parent u).length,
            (s15.data[10 * Q + 1 + lo + j]?).map Fin.val =
              some ((bucketChildren ⟨0, sp.qPos⟩ parent u)[j]'hj).val)) := by
  have hQ : 1 ≤ Q := sp.qPos
  obtain ⟨s6, hr6, hd6, hz6, ho6, hc6⟩ := run_reloadQ sp hTen (by omega) s5
  obtain ⟨s7, hr7, hd7, hz7, ho7, hc7, hTin7, hTout7, hRem7, hClk7⟩ :=
    run_copySetup (input := input) 0 0 11 0 1 0 0 Q s6 hz6 ho6 hc6
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s8, hr8, hz8, ho8, hc8, hCopy8, hKeep8⟩ :=
    run_copyLoop (input := input) (Q := Q) (src := 0) (dst := 11 * Q) (len := Q)
      (by omega) (by omega) (Or.inl (by omega)) (by omega) s7
      hz7 ho7 hc7 (by simpa only [Nat.zero_mul, Nat.add_zero] using hTin7)
      (by simpa only [Nat.add_zero] using hTout7)
      (by simpa only [Nat.one_mul, Nat.add_zero, Nat.sub_zero] using hRem7) hClk7
  let aCsr : Arena bits workCap Q :=
    { base := 11 * Q, children := Q - 1, room := by omega, wordFits := by omega }
  obtain ⟨s9, hr9, hd9, hCtrl9, hCmd9, hPtr9, _⟩ :=
    run_setArenaCtrl (input := input) hQ aCsr rfl s8 hz8 ho8 hc8
  have hMass : rowPrefix (parentDegree ⟨0, hQ⟩ parent) Q ≤ Q - 1 := rowPrefix_parentDegree_le hQ ⟨0, hQ⟩ parent
  have hPar9 : ParentAt aCsr parent s9.data := by
    intro v
    rw [hd9, hCopy8 v.val v.isLt, hd7, hd6]
    simpa only [Nat.zero_add] using hPar5 v
  obtain ⟨s10, w10, hw10, hExec10, hImg10, _, hKeep10⟩ :=
    phasesExec_csr (input := input) (a := aCsr) ⟨0, hQ⟩ parent hMass s9 hCtrl9 hCmd9 hPar9 hPtr9
  obtain ⟨s11, hr11, hd11, hz11, ho11, hc11⟩ := run_reloadQ sp hTen (by omega) s10
  obtain ⟨s12, hr12, hd12, hz12, ho12, hc12, hTin12, hTout12, hRem12, hClk12⟩ :=
    run_copySetup (input := input) 15 0 7 0 1 1 0 Q s11 hz11 ho11 hc11
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s13, hr13, hz13, ho13, hc13, hCopy13, hKeep13⟩ :=
    run_copyLoop (input := input) (Q := Q) (src := 15 * Q) (dst := 7 * Q) (len := Q + 1)
      (by omega) (by omega) (Or.inr (by omega)) (by omega) s12
      hz12 ho12 hc12 (by simpa only [Nat.add_zero] using hTin12)
      (by simpa only [Nat.add_zero] using hTout12)
      (by simpa only [Nat.one_mul, Nat.sub_zero] using hRem12) hClk12
  obtain ⟨s14, hr14, hd14, hz14, ho14, hc14, hTin14, hTout14, hRem14, hClk14⟩ :=
    run_copySetup (input := input) 16 1 10 1 1 0 1 Q s13 hz13 ho13 hc13
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s15, hr15, hz15, ho15, hc15, hCopy15, hKeep15⟩ :=
    run_copyLoop (input := input) (Q := Q) (src := 16 * Q + 1) (dst := 10 * Q + 1) (len := Q - 1)
      (by omega) (by omega) (Or.inr (by omega)) (by omega) s14
      hz14 ho14 hc14 hTin14 hTout14 (by simpa only [Nat.one_mul, Nat.add_zero] using hRem14) hClk14
  have hImg10' := childImage_exact hQ aCsr rfl hImg10
  have haOff : aCsr.offsets = 15 * Q := by simp [aCsr, Arena.offsets]; omega
  have haPay : aCsr.payload = 16 * Q + 1 := by simp [aCsr, Arena.payload]; omega
  have hReadStart15 : ∀ u, u ≤ Q → s15.data[7 * Q + u]? = s10.data[aCsr.offsets + u]? := fun u hu => by
    rw [hKeep15 (7 * Q + u) (Or.inl (by omega)), hd14, hCopy13 u (by omega), hd12, hd11, haOff]
  have hReadChild15 : ∀ k, k < Q - 1 → s15.data[10 * Q + 1 + k]? = s10.data[aCsr.payload + k]? := fun k hk => by
    rw [hCopy15 k hk, hd14, hKeep13 _ (Or.inr (by omega)), hd12, hd11, haPay]
  have hExecFirst : PhasesExec input
      ([ reloadQPhase hi hw hTen
       , copySetupPhase hi hw 0 0 11 0 1 0 0
       , copyLoopPhase hi hw
       , setArenaCtrlPhase hi hw 11
       ] ++ csrPhases (hi := hi) (hw := hw)) s5 s10 _ :=
    PhasesExec.cons hr6 (PhasesExec.cons hr7 (PhasesExec.cons hr8 (PhasesExec.cons hr9 hExec10)))
  have hExecSecond : PhasesExec input
      [ reloadQPhase hi hw hTen
      , copySetupPhase hi hw 15 0 7 0 1 1 0
      , copyLoopPhase hi hw
      , copySetupPhase hi hw 16 1 10 1 1 0 1
      , copyLoopPhase hi hw
      ] s10 s15 _ :=
    PhasesExec.cons hr11 (PhasesExec.cons hr12 (PhasesExec.cons hr13 (PhasesExec.cons hr14
      (PhasesExec.single (copyLoopPhase hi hw) hr15))))
  have hExecAll := hExecFirst.append hExecSecond
  rw [List.append_assoc] at hExecAll
  refine ⟨s15, _, ?_, hExecAll, hz15, ho15, hc15, ?_, ?_, ?_, ?_⟩
  · simp only [copySetupInstrs_length, setArenaCtrlInstrs_length]
    omega
  · intro j hj
    rw [hKeep15 j (Or.inl (by omega)), hd14, hKeep13 j (Or.inl hj), hd12, hd11,
        hKeep10 j (by simp [aCsr]; omega), hd9, hKeep8 j (Or.inl (by omega)), hd7, hd6]
  · rw [show 7 * Q = 7 * Q + 0 by omega, hReadStart15 0 (Nat.zero_le _)]
    exact hImg10'.1
  · rw [show 8 * Q = 7 * Q + Q by omega, hReadStart15 Q (Nat.le_refl _)]
    exact hImg10'.2.1
  · intro u
    obtain ⟨lo, hiB, hLo, hHi, hEq, hLe, hWords⟩ := hImg10'.2.2 u
    refine ⟨lo, hiB, ?_, ?_, hEq, hLe, fun j hj => ?_⟩
    · rw [hReadStart15 u.val (by omega)]; exact hLo
    · rw [show 7 * Q + u.val + 1 = 7 * Q + (u.val + 1) by omega, hReadStart15 (u.val + 1) (by omega),
          show aCsr.offsets + (u.val + 1) = aCsr.offsets + u.val + 1 by omega]
      exact hHi
    · rw [show 10 * Q + 1 + lo + j = 10 * Q + 1 + (lo + j) by omega, hReadChild15 (lo + j) (by omega),
          show aCsr.payload + (lo + j) = aCsr.payload + lo + j by omega]
      exact hWords j hj

private theorem run_tail_phase2c {bits inputCap workCap Q : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {input : Input (layout bits inputCap workCap hi hw)}
    (hQ : 1 ≤ Q) (hDataCap : 17 * Q ≤ workCap) (hWordCap : 17 * Q < 2 ^ bits)
    (parent : Fin Q → Fin Q) (depth : Fin Q → Nat)
    (hTree : ValidDepthTree ⟨0, hQ⟩ parent depth)
    (hParLt : ∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val)
    (s15 : State (layout bits inputCap workCap hi hw))
    (hz15 : (reg s15 registers.zero).val = 0)
    (ho15 : (reg s15 registers.one).val = 1)
    (hc15 : (reg s15 count).val = Q)
    (hPar15 : ∀ v : Fin Q, (s15.data[v.val]?).map Fin.val = some (parent v).val)
    (hEnt15 : ∀ v : Fin Q, (s15.data[4 * Q + v.val]?).map Fin.val = some (entry ⟨0, hQ⟩ parent depth v))
    (hStop15 : ∀ v : Fin Q,
      (s15.data[5 * Q + v.val]?).map Fin.val =
        some (entry ⟨0, hQ⟩ parent depth v + (dfsSubtree ⟨0, hQ⟩ parent depth v).length))
    (hStartZero15 : (s15.data[7 * Q]?).map Fin.val = some 0)
    (hStartEnd15 : (s15.data[8 * Q]?).map Fin.val = some (Q - 1))
    (hBuckets15 : ∀ u : Fin Q,
      ∃ lo hiB : Nat,
        (s15.data[7 * Q + u.val]?).map Fin.val = some lo ∧
        (s15.data[7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
        hiB = lo + (bucketChildren ⟨0, hQ⟩ parent u).length ∧
        hiB ≤ Q - 1 ∧
        (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hQ⟩ parent u).length,
          (s15.data[10 * Q + 1 + lo + j]?).map Fin.val =
            some ((bucketChildren ⟨0, hQ⟩ parent u)[j]'hj).val)) :
    let x := staticInput hQ parent depth
    let built := PackedStaticLayout.build x
    let tables := StaticHeadSweep.tables built.packed
    ∃ s19 w_2c,
      w_2c ≤ 64 * Q + 107 ∧
      PhasesExec input
        [ denseOfEntryPhase hi hw
        , heavyPhase hi hw
        , headPhase hi hw
        , childIntervalsPhase hi hw
        ] s15 s19 w_2c ∧
      (∀ u : Fin Q, (s19.data[2 * Q + u.val]?).map Fin.val =
        some (match built.packed.heavy.read u with | none => Q | some h => h.val)) ∧
      (∀ v : Fin Q, (s19.data[3 * Q + v.val]?).map Fin.val = some (tables.head v).val) ∧
      (∀ v : Fin Q,
        built.endpoints.entry.read v < built.endpoints.stop.read v ∧
        built.endpoints.stop.read v ≤ Q ∧
        (s19.data[6 * Q + built.endpoints.entry.read v]?).map Fin.val = some v.val) ∧
      (∀ u : Fin Q,
        ∃ lo hiB : Nat,
          (s19.data[7 * Q + u.val]?).map Fin.val = some lo ∧
          (s19.data[7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
          hiB = lo + (bucketChildren ⟨0, hQ⟩ parent u).length ∧
          hiB ≤ Q - 1 ∧
          (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hQ⟩ parent u).length,
            let c := (bucketChildren ⟨0, hQ⟩ parent u)[j]'hj
            (s19.data[10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
            (s19.data[8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read c) ∧
            (s19.data[9 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.stop.read c)) ∧
          (∀ i j : Nat, i < j → j < hiB - lo →
            ∃ ei ej : Nat,
              (s19.data[8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
              (s19.data[8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
              ei < ej)) ∧
      (∀ j, j < 2 * Q ∨ (4 * Q ≤ j ∧ j < 6 * Q) ∨ (7 * Q ≤ j ∧ j ≤ 8 * Q) →
        s19.data[j]? = s15.data[j]?) := by
  let x := staticInput hQ parent depth
  let built := PackedStaticLayout.build x
  let tables := StaticHeadSweep.tables built.packed
  have hxOK : PackedStaticLayout.InputOK x := staticInputOK hQ hTree
  let entryFn : Nat → Nat := fun u =>
    if hu : u < Q then entry ⟨0, hQ⟩ parent depth ⟨u, hu⟩ else 0
  let stopFn : Nat → Nat := fun u =>
    if hu : u < Q then entry ⟨0, hQ⟩ parent depth ⟨u, hu⟩ + (dfsSubtree ⟨0, hQ⟩ parent depth ⟨u, hu⟩).length else 0
  let parentFn : Nat → Nat := fun u =>
    if hu : u < Q then (parent ⟨u, hu⟩).val else 0
  have hParLtNat : ∀ v, 1 ≤ v → v < Q → parentFn v < v := fun v hv1 hvQ => by
    simp only [parentFn, hvQ, ↓reduceDIte]
    exact hParLt ⟨v, hvQ⟩ hv1
  have hEntryRange : ∀ u, u < Q → entryFn u < Q := fun u hu => by
    simp only [entryFn, hu, ↓reduceDIte]
    have := entry_lt_length_dfsPreorder hTree ⟨u, hu⟩
    rwa [length_dfsPreorder hTree] at this
  have hEntryInj : ∀ u₁ u₂, u₁ < Q → u₂ < Q → entryFn u₁ = entryFn u₂ → u₁ = u₂ := by
    intro u₁ u₂ h1 h2 hEq
    simp only [entryFn, h1, h2, ↓reduceDIte] at hEq
    have hRk := PackedStaticLayout.entry_exact x hxOK
    have hEq' : (StaticLinearHead.entryColumn x).read ⟨u₁, h1⟩ = (StaticLinearHead.entryColumn x).read ⟨u₂, h2⟩ := by
      change (PackedStaticLayout.build x).endpoints.entry.read ⟨u₁, h1⟩ =
        (PackedStaticLayout.build x).endpoints.entry.read ⟨u₂, h2⟩
      rw [hRk ⟨u₁, h1⟩, hRk ⟨u₂, h2⟩]
      simpa only [x, staticInput, read_tabulate_fun] using hEq
    have hInj := StaticLinearHead.rank_injective x hxOK (by apply Fin.ext; exact hEq')
    exact congrArg Fin.val hInj
  have hEntFn15 : ∀ u, u < Q → (s15.data[4 * Q + u]?).map Fin.val = some (entryFn u) := fun u hu => by
    simp only [entryFn, hu, ↓reduceDIte]
    exact hEnt15 ⟨u, hu⟩
  have hStopFn15 : ∀ u, u < Q → (s15.data[5 * Q + u]?).map Fin.val = some (stopFn u) := fun u hu => by
    simp only [stopFn, hu, ↓reduceDIte]
    exact hStop15 ⟨u, hu⟩
  let startFn : Nat → Nat := fun u =>
    if _ : u ≤ Q then
      match s15.data[7 * Q + u]? with | some w => w.val | none => 0
    else 0
  let childFn : Nat → Nat := fun k =>
    if _ : k < Q - 1 then
      match s15.data[10 * Q + 1 + k]? with | some w => w.val | none => 0
    else 0
  have hStData15 : ∀ u, u ≤ Q → (s15.data[7 * Q + u]?).map Fin.val = some (startFn u) := by
    intro u hu
    have hSz15 : 7 * Q + u < s15.data.size := by
      rw [s15.data_size]
      exact Nat.lt_of_lt_of_le (by omega) hDataCap
    cases hC : s15.data[7 * Q + u]? with
    | none => exact False.elim (by have := (Array.getElem?_eq_none_iff).mp hC; omega)
    | some w => simp only [startFn, hu, ↓reduceDIte, hC, Option.map_some]
  have hCData15 : ∀ k, k < Q - 1 → (s15.data[10 * Q + 1 + k]?).map Fin.val = some (childFn k) := by
    intro k hk
    have hSz15 : 10 * Q + 1 + k < s15.data.size := by
      rw [s15.data_size]
      exact Nat.lt_of_lt_of_le (by omega) hDataCap
    cases hC : s15.data[10 * Q + 1 + k]? with
    | none => exact False.elim (by have := (Array.getElem?_eq_none_iff).mp hC; omega)
    | some w => simp only [childFn, hk, ↓reduceDIte, hC, Option.map_some]
  -- Step 10: `denseOfEntryPhase`
  obtain ⟨s16, hr16, hz16, ho16, hc16, hDense16, hKeep16⟩ :=
    run_denseOfEntry (input := input) entryFn (by omega) hDataCap hEntryRange hEntryInj
      s15 hz15 ho15 hc15 hEntFn15
  -- Step 11: `heavyPhase`
  have hStartMono : ∀ u, u < Q → startFn u ≤ startFn (u + 1) := by
    intro u hu
    obtain ⟨lo, hiB, hLo, hHi, hEq, _, _⟩ := hBuckets15 ⟨u, hu⟩
    have hS0 := hStData15 u (by omega)
    have hS1 := hStData15 (u + 1) (by omega)
    rw [hLo, Option.some.injEq] at hS0
    rw [show 7 * Q + (u + 1) = 7 * Q + u + 1 by omega, hHi, Option.some.injEq] at hS1
    omega
  have hStartEndEq : startFn Q = Q - 1 := by
    have hS := hStData15 Q (Nat.le_refl Q)
    rw [show 7 * Q + Q = 8 * Q by omega, hStartEnd15, Option.some.injEq] at hS
    exact hS.symm
  have hChildProps : ∀ j, j < Q - 1 → childFn j < Q ∧ entryFn (childFn j) ≤ stopFn (childFn j) ∧ stopFn (childFn j) ≤ Q := by
    intro j hj
    have hWalk : ∀ k, k ≤ Q → j < startFn k → ∃ u : Fin Q, u.val < k ∧ startFn u.val ≤ j ∧ j < startFn (u.val + 1) := by
      intro k
      induction k with
      | zero =>
        intro _ hLt0
        have hS0 := hStData15 0 (Nat.zero_le Q)
        rw [Nat.add_zero, hStartZero15, Option.some.injEq] at hS0
        omega
      | succ k ihk =>
        intro hk hLtS
        by_cases hLtPrev : j < startFn k
        · obtain ⟨u, hu1, hu2, hu3⟩ := ihk (by omega) hLtPrev
          exact ⟨u, by omega, hu2, hu3⟩
        · exact ⟨⟨k, by omega⟩, Nat.lt_succ_self _, Nat.le_of_not_lt hLtPrev, hLtS⟩
    obtain ⟨u, _, huLo, huHi⟩ := hWalk Q (Nat.le_refl Q) (by rw [hStartEndEq]; exact hj)
    obtain ⟨lo, hiB, hLo, hHi, hEq, hLeB, hWords⟩ := hBuckets15 u
    have hS0 := hStData15 u.val (by omega)
    have hS1 := hStData15 (u.val + 1) (by omega)
    rw [hLo, Option.some.injEq] at hS0
    rw [show 7 * Q + (u.val + 1) = 7 * Q + u.val + 1 by omega, hHi, Option.some.injEq] at hS1
    let c := (bucketChildren ⟨0, hQ⟩ parent u)[j - lo]'(by omega)
    have hK := hWords (j - lo) (by omega)
    have hC15 := hCData15 j hj
    rw [show 10 * Q + 1 + j = 10 * Q + 1 + lo + (j - lo) by omega, hK, Option.some.injEq] at hC15
    have hcEq : childFn j = c.val := hC15.symm
    rw [hcEq]
    have hLe := entry_add_subtree_le hQ hTree (depth c) c rfl
    refine ⟨c.isLt, ?_, ?_⟩
    · simp only [entryFn, stopFn, c.isLt, ↓reduceDIte]; omega
    · simp only [stopFn, c.isLt, ↓reduceDIte]; omega
  obtain ⟨s17, w17, hw17, hr17, hz17, ho17, hc17, hHv17, hKeep17⟩ :=
    run_heavy (input := input) startFn entryFn stopFn childFn (by omega) hDataCap hStartMono hStartEndEq hChildProps
      s16 hz16 ho16 hc16
      (fun u hu => by rw [hKeep16 (7 * Q + u) (Or.inr (by omega))]; exact hStData15 u hu)
      (fun k hk => by rw [hKeep16 (10 * Q + 1 + k) (Or.inr (by omega))]; exact hCData15 k hk)
      (fun c hc => by rw [hKeep16 (4 * Q + c) (Or.inl (by omega))]; exact hEntFn15 c hc)
      (fun c hc => by rw [hKeep16 (5 * Q + c) (Or.inl (by omega))]; exact hStopFn15 c hc)
  -- Step 12: `headPhase`
  let denseOfEntryFn : Nat → Nat := fun e =>
    if _ : e < Q then
      match s17.data[6 * Q + e]? with | some w => w.val | none => 0
    else 0
  have hDenseInv : ∀ e, e < Q → denseOfEntryFn e < Q ∧ entryFn (denseOfEntryFn e) = e := by
    intro e he
    have hPreLen : e < (dfsPreorder ⟨0, hQ⟩ parent depth).length := by rw [length_dfsPreorder hTree]; exact he
    let v : Fin Q := (dfsPreorder ⟨0, hQ⟩ parent depth)[e]'hPreLen
    have hvEnt : entry ⟨0, hQ⟩ parent depth v = e := by
      have hNodup := nodup_dfsPreorder hTree
      exact (firstOccurrence_eq_iff v (mem_dfsPreorder hTree v) e).mpr
        ⟨(dfsPreorder ⟨0, hQ⟩ parent depth).take e, (dfsPreorder ⟨0, hQ⟩ parent depth).drop (e + 1),
         by simp [v],
         fun hMem => by
           obtain ⟨j, hj, hGet⟩ := List.getElem_of_mem hMem
           have hjTake : j < e := by simp only [List.length_take] at hj; omega
           rw [List.getElem_take] at hGet
           have hNoDupPair := List.pairwise_iff_getElem.mp hNodup
           exact hNoDupPair j e (by omega) hPreLen hjTake hGet,
         by simp [List.length_take]; omega⟩
    have hEntV : entryFn v.val = e := by simp only [entryFn, v.isLt, ↓reduceDIte, hvEnt]
    have hD17 : (s17.data[6 * Q + e]?).map Fin.val = some v.val := by
      rw [hKeep17 (6 * Q + e) (Or.inr (by omega)), ← hEntV]
      exact hDense16 v.val v.isLt
    cases hC : s17.data[6 * Q + e]? with
    | none => rw [hC] at hD17; cases hD17
    | some w =>
      rw [hC, Option.map_some, Option.some.injEq] at hD17
      simp only [denseOfEntryFn, he, ↓reduceDIte, hC]
      rw [hD17]
      exact ⟨v.isLt, hEntV⟩
  have hHeavyEq : ∀ u : Fin Q,
      heavySpec Q startFn entryFn stopFn childFn u.val =
        match built.packed.heavy.read u with
        | none => Q
        | some w => w.val := by
    intro u
    obtain ⟨lo, hiB, hLo, hHi, hEq, hHiLe, hWords⟩ := hBuckets15 u
    have hS0 := hStData15 u.val (by omega)
    have hS1 := hStData15 (u.val + 1) (by omega)
    rw [hLo, Option.some.injEq] at hS0
    rw [show 7 * Q + (u.val + 1) = 7 * Q + u.val + 1 by omega, hHi, Option.some.injEq] at hS1
    have hLen : startFn (u.val + 1) - startFn u.val = (bucketChildren ⟨0, hQ⟩ parent u).length := by omega
    have hKids : ∀ k (hk : k < (bucketChildren ⟨0, hQ⟩ parent u).length),
        childFn (startFn u.val + k) = ((bucketChildren ⟨0, hQ⟩ parent u)[k]'hk).val := by
      intro k hk
      have hK := hWords k hk
      have hC15 := hCData15 (startFn u.val + k) (by omega)
      rw [show 10 * Q + 1 + (startFn u.val + k) = 10 * Q + 1 + lo + k by omega, hK, Option.some.injEq] at hC15
      exact hC15.symm
    exact heavySpec_eq_packed hQ hTree startFn entryFn stopFn childFn
      (fun v => by simp only [entryFn, v.isLt, ↓reduceDIte])
      (fun v => by simp only [stopFn, v.isLt, ↓reduceDIte])
      u hLen hKids
  have hHeavyRange : ∀ v, v < Q → heavySpec Q startFn entryFn stopFn childFn v ≤ Q := by
    intro v hv
    rw [hHeavyEq ⟨v, hv⟩]
    cases built.packed.heavy.read ⟨v, hv⟩ with
    | none => exact Nat.le_refl Q
    | some w => exact Nat.le_of_lt w.isLt
  have hParentPre : ∀ v, 1 ≤ v → v < Q → entryFn (parentFn v) < entryFn v := by
    intro v hv1 hvQ
    have hvNe : (⟨v, hvQ⟩ : Fin Q) ≠ ⟨0, hQ⟩ := fun e => by
      have hv0 : v = 0 := congrArg Fin.val e
      omega
    have hE := entry_parent_lt_child hQ hTree ⟨v, hvQ⟩ hvNe
    simpa only [entryFn, parentFn, hvQ, ↓reduceDIte, Fin.isLt] using hE
  have hHeadEq : ∀ k (hk : k < Q),
      headSweepSpec parentFn (heavySpec Q startFn entryFn stopFn childFn) k = (tables.head ⟨k, hk⟩).val :=
    headSweepSpec_eq_tables hQ hTree hParLt parentFn (heavySpec Q startFn entryFn stopFn childFn)
      (fun v => by simp only [parentFn, v.isLt, ↓reduceDIte]) hHeavyEq
  have hHeadBound : ∀ v, v < Q → headSweepSpec parentFn (heavySpec Q startFn entryFn stopFn childFn) v < Q := by
    intro v hv
    rw [hHeadEq v hv]
    exact Fin.isLt _
  obtain ⟨s18, w18, hw18, hr18, hz18, ho18, hc18, hHead18, hKeep18⟩ :=
    run_head (input := input) parentFn (heavySpec Q startFn entryFn stopFn childFn) entryFn denseOfEntryFn
      (by omega) hDataCap hParLtNat hHeavyRange hEntryRange hEntryInj hDenseInv hParentPre hHeadBound
      s17 hz17 ho17 hc17
      (fun u hu => by
        rw [hKeep17 u (Or.inl (by omega)), hKeep16 u (Or.inl (by omega))]
        simpa only [parentFn, hu, ↓reduceDIte] using hPar15 ⟨u, hu⟩)
      (fun u hu => hHv17 u hu)
      (fun u hu => by
        cases hC : s17.data[6 * Q + u]? with
        | none =>
          have hSz17 : 6 * Q + u < s17.data.size := by
            rw [s17.data_size]
            exact Nat.lt_of_lt_of_le (by omega) hDataCap
          exact False.elim (by have := (Array.getElem?_eq_none_iff).mp hC; omega)
        | some w => simp [denseOfEntryFn, hu, hC])
  -- Step 13: `childIntervalsPhase`
  have hChildPropsCI : ∀ i, i < Q - 1 → childFn i < Q ∧ entryFn (childFn i) ≤ Q ∧ stopFn (childFn i) ≤ Q := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hChildProps i hi
    exact ⟨h1, by omega, h3⟩
  obtain ⟨s19, w19, hw19, hr19, hz19, ho19, hc19, hCE19, hCS19, hKeep19⟩ :=
    run_childIntervals (input := input) entryFn stopFn childFn hQ (by omega) hDataCap hChildPropsCI
      s18 hz18 ho18 hc18
      (fun k hk => by
        rw [hKeep18 (10 * Q + 1 + k) (Or.inr (by omega)),
            hKeep17 (10 * Q + 1 + k) (Or.inr (by omega)),
            hKeep16 (10 * Q + 1 + k) (Or.inr (by omega))]
        exact hCData15 k hk)
      (fun c hc => by
        rw [hKeep18 (4 * Q + c) (Or.inr (by omega)),
            hKeep17 (4 * Q + c) (Or.inr (by omega)),
            hKeep16 (4 * Q + c) (Or.inl (by omega))]
        exact hEntFn15 c hc)
      (fun c hc => by
        rw [hKeep18 (5 * Q + c) (Or.inr (by omega)),
            hKeep17 (5 * Q + c) (Or.inr (by omega)),
            hKeep16 (5 * Q + c) (Or.inl (by omega))]
        exact hStopFn15 c hc)
  have hEntExact : ∀ v : Fin Q, built.endpoints.entry.read v = entryFn v.val := fun v => by
    refine (PackedStaticLayout.entry_exact x hxOK v).trans ?_
    simp only [x, staticInput, read_tabulate_fun, entryFn, v.isLt, ↓reduceDIte, Fin.eta]
  have hStopExact : ∀ v : Fin Q, built.endpoints.stop.read v = stopFn v.val := fun v => by
    refine (PackedStaticLayout.stop_exact x hxOK v).trans ?_
    simp only [x, staticInput, read_tabulate_fun, stopFn, v.isLt, ↓reduceDIte, Fin.eta]
  have hKeep15_10 : ∀ j, 10 * Q + 1 ≤ j → j < 11 * Q → s19.data[j]? = s15.data[j]? := fun j h1 h2 => by
    rw [hKeep19 j (Or.inr (by omega)), hKeep18 j (Or.inr (by omega)),
        hKeep17 j (Or.inr (by omega)), hKeep16 j (Or.inr (by omega))]
  have hFrame19 : ∀ j, j < 2 * Q ∨ (4 * Q ≤ j ∧ j < 6 * Q) ∨ (7 * Q ≤ j ∧ j ≤ 8 * Q) →
      s19.data[j]? = s15.data[j]? := fun j hj => by
    rcases hj with hj | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hKeep19 j (Or.inl (by omega)), hKeep18 j (Or.inl (by omega)),
          hKeep17 j (Or.inl (by omega)), hKeep16 j (Or.inl (by omega))]
    · rw [hKeep19 j (Or.inl (by omega)), hKeep18 j (Or.inr (by omega)),
          hKeep17 j (Or.inr (by omega)), hKeep16 j (Or.inl (by omega))]
    · rw [hKeep19 j (Or.inl (by omega)), hKeep18 j (Or.inr (by omega)),
          hKeep17 j (Or.inr (by omega)), hKeep16 j (Or.inr (by omega))]
  refine ⟨s19, _, by omega,
    PhasesExec.cons hr16 (PhasesExec.cons hr17 (PhasesExec.cons hr18 (PhasesExec.single (childIntervalsPhase hi hw) hr19))),
    fun u => by
      rw [hKeep19 (2 * Q + u.val) (Or.inl (by omega)),
          hKeep18 (2 * Q + u.val) (Or.inl (by omega)), hHv17 u.val u.isLt, hHeavyEq u],
    fun v => by
      rw [hKeep19 (3 * Q + v.val) (Or.inl (by omega)), hHead18 v.val v.isLt, hHeadEq v.val v.isLt],
    fun v => ?_, fun u => ?_, hFrame19⟩
  · rw [hEntExact v, hStopExact v]
    have hPos := dfsSubtree_length_pos hTree v
    have hLeQ := entry_add_subtree_le hQ hTree (depth v) v rfl
    have hvEta : (⟨v.val, v.isLt⟩ : Fin Q) = v := Fin.eta v v.isLt
    refine ⟨?_, ?_, ?_⟩
    · simp only [entryFn, stopFn, v.isLt, ↓reduceDIte, hvEta]; omega
    · simp only [stopFn, v.isLt, ↓reduceDIte, hvEta]; exact hLeQ
    · rw [hKeep19 (6 * Q + entryFn v.val) (Or.inl (by have := hEntryRange v.val v.isLt; omega)),
          hKeep18 (6 * Q + entryFn v.val) (Or.inr (by omega)),
          hKeep17 (6 * Q + entryFn v.val) (Or.inr (by omega))]
      exact hDense16 v.val v.isLt
  · obtain ⟨lo, hiB, hLo15, hHi15, hEqB, hLeB, hWords15⟩ := hBuckets15 u
    refine ⟨lo, hiB, ?_, ?_, hEqB, hLeB, ?_, ?_⟩
    · rw [hFrame19 (7 * Q + u.val) (Or.inr (Or.inr ⟨by omega, by omega⟩)), hLo15]
    · rw [hFrame19 (7 * Q + u.val + 1) (Or.inr (Or.inr ⟨by omega, by omega⟩)), hHi15]
    · intro j hj
      let c := (bucketChildren ⟨0, hQ⟩ parent u)[j]'hj
      have hcEq : childFn (lo + j) = c.val := by
        have hK := hWords15 j hj
        have hC := hCData15 (lo + j) (by omega)
        rw [show 10 * Q + 1 + (lo + j) = 10 * Q + 1 + lo + j by omega, hK, Option.some.injEq] at hC
        exact hC.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hKeep15_10 (10 * Q + 1 + lo + j) (by omega) (by omega), hWords15 j hj]
      · rw [show 8 * Q + 1 + lo + j = 8 * Q + 1 + (lo + j) by omega,
            hCE19 (lo + j) (by omega), hcEq, hEntExact c]
      · rw [show 9 * Q + 1 + lo + j = 9 * Q + 1 + (lo + j) by omega,
            hCS19 (lo + j) (by omega), hcEq, hStopExact c]
    · intro i j hij hjLt
      have hiLen : i < (bucketChildren ⟨0, hQ⟩ parent u).length := by omega
      have hjLen : j < (bucketChildren ⟨0, hQ⟩ parent u).length := by omega
      let ci := (bucketChildren ⟨0, hQ⟩ parent u)[i]'hiLen
      let cj := (bucketChildren ⟨0, hQ⟩ parent u)[j]'hjLen
      have hPos : ∀ c ∈ bucketChildren ⟨0, hQ⟩ parent u, 0 < (dfsSubtree ⟨0, hQ⟩ parent depth c).length :=
        fun c _ => dfsSubtree_length_pos hTree c
      have hPrec := preceding_lt_of_lt (dfsSubtree ⟨0, hQ⟩ parent depth) (bucketChildren ⟨0, hQ⟩ parent u) hPos hij hjLen
      have hEi := child_entry hTree u i hiLen
      have hEj := child_entry hTree u j hjLen
      have hC_i : (s19.data[8 * Q + 1 + lo + i]?).map Fin.val = some (built.endpoints.entry.read ci) := by
        have hKi := hWords15 i hiLen
        have hcEqi : childFn (lo + i) = ci.val := by
          have hC := hCData15 (lo + i) (by omega)
          rw [show 10 * Q + 1 + (lo + i) = 10 * Q + 1 + lo + i by omega, hKi, Option.some.injEq] at hC
          exact hC.symm
        rw [show 8 * Q + 1 + lo + i = 8 * Q + 1 + (lo + i) by omega,
            hCE19 (lo + i) (by omega), hcEqi, hEntExact ci]
      have hC_j : (s19.data[8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read cj) := by
        have hKj := hWords15 j hjLen
        have hcEqj : childFn (lo + j) = cj.val := by
          have hC := hCData15 (lo + j) (by omega)
          rw [show 10 * Q + 1 + (lo + j) = 10 * Q + 1 + lo + j by omega, hKj, Option.some.injEq] at hC
          exact hC.symm
        rw [show 8 * Q + 1 + lo + j = 8 * Q + 1 + (lo + j) by omega,
            hCE19 (lo + j) (by omega), hcEqj, hEntExact cj]
      have hci : (⟨ci.val, ci.isLt⟩ : Fin Q) = ci := Fin.eta ci ci.isLt
      have hcj : (⟨cj.val, cj.isLt⟩ : Fin Q) = cj := Fin.eta cj cj.isLt
      refine ⟨built.endpoints.entry.read ci, built.endpoints.entry.read cj, hC_i, hC_j, ?_⟩
      rw [hEntExact ci, hEntExact cj]
      simp only [entryFn, ci.isLt, cj.isLt, ↓reduceDIte, hci, hcj]
      dsimp only [ci, cj]
      rw [hEi, hEj]
      omega

theorem run_domAndStaticTree {bits inputCap workCap Q mReach : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {inStart inSrc : Nat → Nat}
    {input : Input (layout bits inputCap workCap hi hw)}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    (hDataCap : 17 * Q ≤ workCap) (hWordCap : 17 * Q < 2 ^ bits)
    (s0 : State (layout bits inputCap workCap hi hw)) :
    let hTen : 10 ≤ 2 ^ bits := by have := sp.qPos; omega
    ∃ t trace work,
      ∃ (parent : Fin Q → Fin Q) (depth : Fin Q → Nat),
        let x := staticInput sp.qPos parent depth
        let built := PackedStaticLayout.build x
        let tables := StaticHeadSweep.tables built.packed
        work ≤ 1050 * (Q + mReach) * OracleContract.L Q ^ 2 ∧
        run (domAndStaticTreeProgram hi hw hTen) input work (Phase.initial s0) = some ⟨t, work⟩ ∧
        SuccessfulTrace (domAndStaticTreeProgram hi hw hTen) input (Phase.initial s0) trace ⟨t, work⟩ ∧
        tracePeakWords input trace = inputCap + workCap + 15 ∧
        ParentSpec (denseDigraph Q inStart inSrc) ⟨0, sp.qPos⟩ parent ∧
        ValidDepthTree ⟨0, sp.qPos⟩ parent depth ∧
        EX16.Valid tables ∧
        (∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val) ∧
        (∀ v : Fin Q, (t.data[v.val]?).map Fin.val = some (parent v).val) ∧
        (∀ v : Fin Q, (t.data[Q + v.val]?).map Fin.val = some (depth v)) ∧
        (∀ u : Fin Q, (t.data[2 * Q + u.val]?).map Fin.val =
          some (match built.packed.heavy.read u with | none => Q | some h => h.val)) ∧
        (∀ v : Fin Q, (t.data[3 * Q + v.val]?).map Fin.val = some (tables.head v).val) ∧
        (∀ v : Fin Q, (t.data[4 * Q + v.val]?).map Fin.val = some (built.endpoints.entry.read v)) ∧
        (∀ v : Fin Q, (t.data[5 * Q + v.val]?).map Fin.val = some (built.endpoints.stop.read v)) ∧
        (∀ v : Fin Q,
          built.endpoints.entry.read v < built.endpoints.stop.read v ∧
          built.endpoints.stop.read v ≤ Q ∧
          (t.data[6 * Q + built.endpoints.entry.read v]?).map Fin.val = some v.val) ∧
        (t.data[7 * Q]?).map Fin.val = some 0 ∧
        (t.data[8 * Q]?).map Fin.val = some (Q - 1) ∧
        (∀ u : Fin Q,
          ∃ lo hi : Nat,
            (t.data[7 * Q + u.val]?).map Fin.val = some lo ∧
            (t.data[7 * Q + u.val + 1]?).map Fin.val = some hi ∧
            hi = lo + (bucketChildren ⟨0, sp.qPos⟩ parent u).length ∧
            hi ≤ Q - 1 ∧
            (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, sp.qPos⟩ parent u).length,
              let c := (bucketChildren ⟨0, sp.qPos⟩ parent u)[j]'hj
              (t.data[10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
              (t.data[8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read c) ∧
              (t.data[9 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.stop.read c)) ∧
            (∀ i j : Nat, i < j → j < hi - lo →
              ∃ ei ej : Nat,
                (t.data[8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
                (t.data[8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
                ei < ej)) := by
  intro hTen
  have hQ : 1 ≤ Q := sp.qPos
  have hLPos : 1 ≤ OracleContract.L Q := OracleContract.one_le_L Q
  have hLSqPos : 1 ≤ OracleContract.L Q ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul hLPos hLPos
  -- Stage 1: Phase 1 (`domBuildPhase`)
  obtain ⟨s1, _, w1, parent, depth, hw1, hr1, _, _, hSpec, hTree, hPar1, hDep1, hParLt, hz1, ho1, hc1⟩ :=
    run_domBuild_parentSpec sp s0
  -- Stage 2: Finish
  obtain ⟨s5, wFin, hwFin, hExecFin, hEnt5, hEnd5, hKeep5⟩ :=
    run_tail_finish (input := input) hQ hDataCap hWordCap parent depth hTree s1 hPar1 hz1 ho1 hc1
  -- Stage 3: CSR + copies
  obtain ⟨s15, wCsr, hwCsr, hExecCsr, hz15, ho15, hc15, hKeep15, hStartZero15, hStartEnd15, hBuckets15⟩ :=
    run_tail_csr sp hDataCap hWordCap hTen parent s5
      (fun v => by rw [hKeep5 v.val (by omega)]; exact hPar1 v)
  let x := staticInput hQ parent depth
  let built := PackedStaticLayout.build x
  let tables := StaticHeadSweep.tables built.packed
  have hxOK : PackedStaticLayout.InputOK x := staticInputOK hQ hTree
  have hValidTables : EX16.Valid tables := PackedStaticLayout.valid x hxOK
  have hLayout := layout_bucket_correct (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ parent depth hTree
    (bucketChildLists_get ⟨0, hQ⟩ parent)
  have hFinalSz := PaperB.ForestLayout.layout_sizes (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ (2 * Q)
  have hEnt15 : ∀ v : Fin Q, (s15.data[4 * Q + v.val]?).map Fin.val = some (entry ⟨0, hQ⟩ parent depth v) := fun v => by
    rw [hKeep15 (4 * Q + v.val) (by omega), hEnt5 v]
    have hSzE : v.val < (ForestLayout.layout (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ (2 * Q)).entries.size := by
      rw [hFinalSz.1]; exact v.isLt
    rw [Array.getElem?_eq_getElem hSzE]
    exact congrArg some (hLayout.2.2 v).1
  have hStop15 : ∀ v : Fin Q,
      (s15.data[5 * Q + v.val]?).map Fin.val =
        some (entry ⟨0, hQ⟩ parent depth v + (dfsSubtree ⟨0, hQ⟩ parent depth v).length) := fun v => by
    rw [hKeep15 (5 * Q + v.val) (by omega), show 5 * Q + v.val = 4 * Q + Q + v.val by omega, hEnd5 v]
    have hSzS : v.val < (ForestLayout.layout (bucketChildLists ⟨0, hQ⟩ parent) ⟨0, hQ⟩ (2 * Q)).ends.size := by
      rw [hFinalSz.2]; exact v.isLt
    rw [Array.getElem?_eq_getElem hSzS]
    exact congrArg some (hLayout.2.2 v).2
  -- Stage 4: Phase 2C
  obtain ⟨s19, w2c, hw2c, hExec2c, hHv19, hHd19, hDense19, hBuckets19, hFrame19⟩ :=
    run_tail_phase2c (input := input) hQ hDataCap hWordCap parent depth hTree hParLt s15 hz15 ho15 hc15
      (fun v => by rw [hKeep15 v.val (by omega), hKeep5 v.val (by omega)]; exact hPar1 v)
      hEnt15 hStop15 hStartZero15 hStartEnd15 hBuckets15
  have hExecMid : PhasesExec input (domAndStaticTreeTail hi hw hTen) s1 s19 (wFin + (wCsr + w2c)) := by
    unfold domAndStaticTreeTail
    exact hExecFin.append (hExecCsr.append hExec2c)
  have hExecAll : PhasesExec input (domAndStaticTreePhases hi hw hTen) s0 s19 (w1 + (wFin + (wCsr + w2c))) :=
    PhasesExec.cons hr1 hExecMid
  obtain ⟨t, trace, _, hDataEq, hRunFinal, hTraceFinal, hPeakFinal⟩ :=
    run_linkNonEmpty (domAndStaticTreeTail hi hw hTen) (domBuildPhase hi hw hTen) hExecAll
  have hFootEq : footprint (RamForestProgram.layout bits inputCap workCap hi hw) = inputCap + workCap + 15 := rfl
  rw [hFootEq] at hPeakFinal
  have hWorkBound : w1 + (wFin + (wCsr + w2c)) ≤ 1050 * (Q + mReach) * OracleContract.L Q ^ 2 := by
    have hRemLe : wFin + (wCsr + w2c) ≤ 732 * (Q + mReach) * OracleContract.L Q ^ 2 := by
      have h1 : wFin + (wCsr + w2c) ≤ 732 * (Q + mReach) := by omega
      exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ hLSqPos)
    have hSplit :
        318 * (Q + mReach) * OracleContract.L Q ^ 2 + 732 * (Q + mReach) * OracleContract.L Q ^ 2 =
          1050 * (Q + mReach) * OracleContract.L Q ^ 2 := by
      rw [← Nat.add_mul, ← Nat.add_mul]
    omega
  refine ⟨t, trace, _, parent, depth, hWorkBound, hRunFinal, hTraceFinal, hPeakFinal,
    hSpec, hTree, hValidTables, hParLt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [hDataEq, hFrame19 v.val (Or.inl (by omega)), hKeep15 v.val (by omega), hKeep5 v.val (by omega)]
    exact hPar1 v
  · intro v
    rw [hDataEq, hFrame19 (Q + v.val) (Or.inl (by omega)), hKeep15 (Q + v.val) (by omega), hKeep5 (Q + v.val) (by omega)]
    exact hDep1 v
  · intro u; rw [hDataEq]; exact hHv19 u
  · intro v; rw [hDataEq]; exact hHd19 v
  · intro v
    rw [hDataEq, hFrame19 (4 * Q + v.val) (Or.inr (Or.inl ⟨by omega, by omega⟩)), hEnt15 v]
    apply congrArg some
    refine Eq.trans ?_ (PackedStaticLayout.entry_exact x hxOK v).symm
    simp only [x, staticInput, read_tabulate_fun]
  · intro v
    rw [hDataEq, hFrame19 (5 * Q + v.val) (Or.inr (Or.inl ⟨by omega, by omega⟩)), hStop15 v]
    apply congrArg some
    refine Eq.trans ?_ (PackedStaticLayout.stop_exact x hxOK v).symm
    simp only [x, staticInput, read_tabulate_fun]
  · intro v; rw [hDataEq]; exact hDense19 v
  · rw [hDataEq, hFrame19 (7 * Q) (Or.inr (Or.inr ⟨Nat.le_refl _, by omega⟩)), hStartZero15]
  · rw [hDataEq, hFrame19 (8 * Q) (Or.inr (Or.inr ⟨by omega, Nat.le_refl _⟩)), hStartEnd15]
  · intro u; rw [hDataEq]; exact hBuckets19 u

end MainPipeline


