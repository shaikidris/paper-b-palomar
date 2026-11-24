module

public import PaperB.RamStaticLCA
public import PaperB.RamChildRow
public import PaperB.RamPairHitRow
public import PaperB.RamKnownNodeCheck
public import PaperB.RamExitEval
public import PaperB.RamIntervalGuard
public import PaperB.RamPairGuard
public import PaperB.RamSealedTranslation
public import PaperB.OracleSealedIndexLayout
public import PaperB.SealedQueryRegisters

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Reusable building blocks for `PaperB.RamOracleQuery`:
1. Zero-workspace sub-program lifting (`RelocatedZeroWork`) preserving scratch `data[0..31]`
   and unmapped registers, without unfolding opaque kernels such as `exitEvalProgram`.
2. Micro-step lemmas and lifted correctness wrappers for `sealedTranslation`,
   `IntervalGuard.romFor`, `PairGuard.rom`, `PaperB.EX53.program`,
   `Predecessor.worker`, `ThreeCalls.EqualityTail.checkedProgram`,
   `KnownNodeCheck.knownNodeProgram`, and `ExitEval.exitEvalProgram`.
3. Sealed-slice adapters connecting `OracleSealedIndexLayout` slices to
   `EX53.Packed`, `Predecessor.Slice`, and `ColumnReduction.Columns`.
-/

namespace PaperB.RamOracleQueryParts

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap ltb_eq_true zero)
open PaperB.RamProgram
open PaperB.OracleSealedIndexLayout
open PaperB.SealedQueryR

/-! ### 1. Zero-Workspace Sub-Program Lifter (`workCap = 0` → `workCap = 32`) -/

def embedMap {bits r₁ r₂ : Nat} (ρ : Fin r₁ → Fin r₂) :
    Instr bits r₁ → Instr bits r₂
  | .imm d w => .imm (ρ d) w
  | .mov d r => .mov (ρ d) (ρ r)
  | .add d x y => .add (ρ d) (ρ x) (ρ y)
  | .sub d x y => .sub (ρ d) (ρ x) (ρ y)
  | .band d x y => .band (ρ d) (ρ x) (ρ y)
  | .loadInput d a => .loadInput (ρ d) (ρ a)
  | .loadData d a => .loadData (ρ d) (ρ a)
  | .storeData a r => .storeData (ρ a) (ρ r)
  | .branchLt x y yes no => .branchLt (ρ x) (ρ y) yes no
  | .goto p => .goto p
  | .halt => .halt
  | .shr1 d r => .shr1 (ρ d) (ρ r)

def patchAndRelocate {bits r₁ r₂ : Nat} (ρ : Fin r₁ → Fin r₂) (base retPC : Nat)
    (op : Instr bits r₁) : Instr bits r₂ :=
  match op with
  | .halt => .goto retPC
  | op => embedMap ρ (relocateInstr base op)

structure RelocatedZeroWork {bits : Nat} {L₀ L : Layout bits}
    (ρ : Fin L₀.registerCount → Fin L.registerCount)
    (sub : Program L₀) (linked : Program L) (base retPC : Nat) : Prop where
  inj : ∀ {a b}, ρ a = ρ b → a = b
  work_zero : L₀.workCap = 0
  sub_fits : base + sub.size ≤ linked.size
  ret_fits : retPC < linked.size
  placed : ∀ (i : Nat) (op : Instr bits L₀.registerCount),
    sub[i]? = some op →
    linked[base + i]? = some (patchAndRelocate ρ base retPC op)

structure StateAgreement {bits : Nat} {L₀ L : Layout bits}
    (ρ : Fin L₀.registerCount → Fin L.registerCount)
    (base : Nat) (s₀ : State L₀) (s : State L) : Prop where
  pc_eq : s.pc = base + s₀.pc
  reg_eq : ∀ r : Fin L₀.registerCount, reg s (ρ r) = reg s₀ r

private def setReg {bits : Nat} {L : Layout bits} (s : State L)
    (d : Fin L.registerCount) (w : Word bits) (p : Nat) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := p
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_setReg {bits : Nat} {L : Layout bits} (s : State L)
    (d j : Fin L.registerCount) (w : Word bits) (p : Nat) :
    reg (setReg s d w p) j = if j = d then w else reg s j := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hj : j.val < s.regs.size := by simpa only [s.regs_size] using j.isLt
  change (s.regs.set d.val w hd)[j.val]'(by simpa only [Array.size_set] using hj) =
    if j = d then w else s.regs[j.val]'hj
  by_cases h : j = d
  · subst h; simp
  · have hv : j.val ≠ d.val := fun e => h (Fin.ext e)
    simp [Array.getElem_set, h, Ne.symm hv]

private theorem writeReg_agrees {bits : Nat} {L₀ L : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    {base : Nat} {s₀ : State L₀} {s : State L}
    (ha : StateAgreement ρ base s₀ s)
    (d : Fin L₀.registerCount) (w : Word bits)
    {p₀ : Nat} :
    StateAgreement ρ base (setReg s₀ d w p₀)
      (setReg s (ρ d) w (base + p₀)) := by
  refine ⟨rfl, fun r => ?_⟩
  rw [reg_setReg, reg_setReg]
  by_cases h : r = d
  · subst h; simp
  · have hρ : ρ r ≠ ρ d := fun e => h (hinj e)
    simp [h, hρ, ha.reg_eq r]

private theorem writeReg_frame {bits : Nat} {L₀ L : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    {s : State L} (d : Fin L₀.registerCount) (w : Word bits) {p : Nat}
    {j : Fin L.registerCount} (hj : ∀ r, ρ r ≠ j) :
    reg (setReg s (ρ d) w p) j = reg s j := by
  rw [reg_setReg, ite_eq_right (Ne.symm (hj d))]

private theorem step_relocated_zeroWork {bits : Nat} {L₀ L : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    {sub : Program L₀} {linked : Program L} {base retPC : Nat}
    (rel : RelocatedZeroWork ρ sub linked base retPC)
    {i₀ : Input L₀} {i : Input L} (hi : i₀.words = i.words)
    {s₀ t₀ : State L₀} {s : State L}
    (ha : StateAgreement ρ base s₀ s)
    (hstep : step sub i₀ s₀ = some (.next t₀)) :
    ∃ t : State L,
      step linked i s = some (.next t) ∧
      StateAgreement ρ base t₀ t ∧
      (∀ j : Fin L.registerCount, (∀ r, ρ r ≠ j) → reg t j = reg s j) ∧
      t.data = s.data := by
  cases hf : sub[s₀.pc]? with
  | none =>
    simp [step, hf] at hstep
  | some op =>
    have hplaced := rel.placed s₀.pc op hf
    have hpcS : s.pc = base + s₀.pc := ha.pc_eq
    have fallthrough (d : Fin L₀.registerCount) (w : Word bits)
        (hadv : (if s₀.pc + 1 < sub.size then
            some (Transition.next (setReg s₀ d w (s₀.pc + 1))) else none) =
          some (Transition.next t₀)) :
        t₀ = setReg s₀ d w (s₀.pc + 1) ∧ s₀.pc + 1 < sub.size := by
      by_cases hlt : s₀.pc + 1 < sub.size
      · rw [ite_eq_left hlt] at hadv
        exact ⟨(Transition.next.inj (Option.some.inj hadv)).symm, hlt⟩
      · rw [ite_eq_right hlt] at hadv
        cases hadv
    have jumpTo (p : Nat)
        (hadv : (if p < sub.size then some (Transition.next { s₀ with pc := p }) else none) =
          some (Transition.next t₀)) :
        t₀ = { s₀ with pc := p } ∧ p < sub.size := by
      by_cases hlt : p < sub.size
      · rw [ite_eq_left hlt] at hadv
        exact ⟨(Transition.next.inj (Option.some.inj hadv)).symm, hlt⟩
      · rw [ite_eq_right hlt] at hadv
        cases hadv
    cases op with
    | halt =>
      simp [step, hf] at hstep
    | loadData d a =>
      have hsz : s₀.data.size = 0 := s₀.data_size.trans rel.work_zero
      have hnone : s₀.data[(reg s₀ a).val]? = none :=
        getElem?_neg s₀.data _ (by rw [hsz]; omega)
      simp [step, hf, hnone] at hstep
    | storeData a src =>
      have hsz : s₀.data.size = 0 := s₀.data_size.trans rel.work_zero
      have hneg : ¬ ((reg s₀ a).val < s₀.data.size) := by rw [hsz]; omega
      simp [step, hf, hneg] at hstep
    | imm d w =>
      have hadv : (if s₀.pc + 1 < sub.size then
            some (Transition.next (setReg s₀ d w (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d w hadv
      let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.imm (ρ d) w) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      refine ⟨t, ?_, writeReg_agrees rel.inj ha d w,
        fun j hj => writeReg_frame d w hj, rfl⟩
      have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
      unfold step; rw [hlinked]
      change (if s.pc + 1 < linked.size then
          some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
      rw [ite_eq_left hnext, hpc1]
    | mov d src =>
      have hadv : (if s₀.pc + 1 < sub.size then
            some (Transition.next (setReg s₀ d (reg s₀ src) (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d (reg s₀ src) hadv
      let t : State L := setReg s (ρ d) (reg s (ρ src)) (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.mov (ρ d) (ρ src)) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      have hreg : reg s (ρ src) = reg s₀ src := ha.reg_eq src
      refine ⟨t, ?_, ?_, fun j hj => writeReg_frame d _ hj, rfl⟩
      · have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change (if s.pc + 1 < linked.size then
          some (Transition.next (setReg s (ρ d) (reg s (ρ src)) (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
      · dsimp only [t]; rw [hreg]; exact writeReg_agrees rel.inj ha d (reg s₀ src)
    | add d x y =>
      have hadv : (if s₀.pc + 1 < sub.size then
          some (Transition.next (setReg s₀ d (add (reg s₀ x) (reg s₀ y)) (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d (add (reg s₀ x) (reg s₀ y)) hadv
      let w := add (reg s (ρ x)) (reg s (ρ y))
      let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.add (ρ d) (ρ x) (ρ y)) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      have hw : w = add (reg s₀ x) (reg s₀ y) := by
        dsimp only [w]; rw [ha.reg_eq x, ha.reg_eq y]
      refine ⟨t, ?_, ?_, fun j hj => writeReg_frame d w hj, rfl⟩
      · have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change (if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
      · dsimp only [t]; rw [hw]; exact writeReg_agrees rel.inj ha d _
    | sub d x y =>
      have hadv : (if s₀.pc + 1 < sub.size then
          some (Transition.next (setReg s₀ d (WordOps.sub (reg s₀ x) (reg s₀ y)) (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d (WordOps.sub (reg s₀ x) (reg s₀ y)) hadv
      let w := WordOps.sub (reg s (ρ x)) (reg s (ρ y))
      let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.sub (ρ d) (ρ x) (ρ y)) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      have hw : w = WordOps.sub (reg s₀ x) (reg s₀ y) := by
        dsimp only [w]; rw [ha.reg_eq x, ha.reg_eq y]
      refine ⟨t, ?_, ?_, fun j hj => writeReg_frame d w hj, rfl⟩
      · have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change (if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
      · dsimp only [t]; rw [hw]; exact writeReg_agrees rel.inj ha d _
    | band d x y =>
      have hadv : (if s₀.pc + 1 < sub.size then
          some (Transition.next (setReg s₀ d (WordOps.band (reg s₀ x) (reg s₀ y)) (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d (WordOps.band (reg s₀ x) (reg s₀ y)) hadv
      let w := WordOps.band (reg s (ρ x)) (reg s (ρ y))
      let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.band (ρ d) (ρ x) (ρ y)) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      have hw : w = WordOps.band (reg s₀ x) (reg s₀ y) := by
        dsimp only [w]; rw [ha.reg_eq x, ha.reg_eq y]
      refine ⟨t, ?_, ?_, fun j hj => writeReg_frame d w hj, rfl⟩
      · have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change (if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
      · dsimp only [t]; rw [hw]; exact writeReg_agrees rel.inj ha d _
    | shr1 d src =>
      let w₀ : Word bits :=
        ⟨(reg s₀ src).val / 2, Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (reg s₀ src).isLt⟩
      have hadv : (if s₀.pc + 1 < sub.size then
            some (Transition.next (setReg s₀ d w₀ (s₀.pc + 1))) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := fallthrough d w₀ hadv
      let w : Word bits :=
        ⟨(reg s (ρ src)).val / 2, Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (reg s (ρ src)).isLt⟩
      let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
      have hlinked : linked[s.pc]? = some (.shr1 (ρ d) (ρ src)) := by
        rw [hpcS]; exact hplaced
      have hnext : s.pc + 1 < linked.size := by
        have := rel.sub_fits; omega
      have hw : w = w₀ := by
        apply Fin.ext
        change (reg s (ρ src)).val / 2 = (reg s₀ src).val / 2
        rw [ha.reg_eq src]
      refine ⟨t, ?_, ?_, fun j hj => writeReg_frame d w hj, rfl⟩
      · have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change (if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
      · dsimp only [t]; rw [hw]; exact writeReg_agrees rel.inj ha d w₀
    | loadInput d addr =>
      cases hload : i₀.words[(reg s₀ addr).val]? with
      | none =>
        unfold step at hstep; rw [hf] at hstep
        change Option.bind (i₀.words[(reg s₀ addr).val]?) _ = _ at hstep
        rw [hload] at hstep
        cases hstep
      | some w =>
        have hadv : (if s₀.pc + 1 < sub.size then
              some (Transition.next (setReg s₀ d w (s₀.pc + 1))) else none) =
            some (Transition.next t₀) := by
          unfold step at hstep; rw [hf] at hstep
          change Option.bind (i₀.words[(reg s₀ addr).val]?) _ = _ at hstep
          rw [hload] at hstep; exact hstep
        obtain ⟨rfl, hlt⟩ := fallthrough d w hadv
        let t : State L := setReg s (ρ d) w (base + (s₀.pc + 1))
        have hlinked : linked[s.pc]? = some (.loadInput (ρ d) (ρ addr)) := by
          rw [hpcS]; exact hplaced
        have hread : i.words[(reg s (ρ addr)).val]? = some w := by
          have ha_eq : reg s (ρ addr) = reg s₀ addr := ha.reg_eq addr
          rw [ha_eq, ← hi]; exact hload
        have hnext : s.pc + 1 < linked.size := by
          have := rel.sub_fits; omega
        refine ⟨t, ?_, writeReg_agrees rel.inj ha d w,
          fun j hj => writeReg_frame d w hj, rfl⟩
        have hpc1 : s.pc + 1 = base + (s₀.pc + 1) := by rw [hpcS, Nat.add_assoc]
        unfold step; rw [hlinked]
        change Option.bind (i.words[(reg s (ρ addr)).val]?)
          (fun v => if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) v (s.pc + 1))) else none) = _
        rw [hread]
        change (if s.pc + 1 < linked.size then
            some (Transition.next (setReg s (ρ d) w (s.pc + 1))) else none) = _
        rw [ite_eq_left hnext, hpc1]
    | branchLt x y ltPC gePC =>
      let target₀ := if ltb (reg s₀ x) (reg s₀ y) then ltPC else gePC
      have hadv : (if target₀ < sub.size then some (Transition.next { s₀ with pc := target₀ }) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := jumpTo target₀ hadv
      let t : State L := { s with pc := base + target₀ }
      have hlinked : linked[s.pc]? = some (.branchLt (ρ x) (ρ y) (base + ltPC) (base + gePC)) := by
        rw [hpcS]; exact hplaced
      have hcond : (if ltb (reg s (ρ x)) (reg s (ρ y)) then base + ltPC else base + gePC) =
          base + target₀ := by
        have hx : reg s (ρ x) = reg s₀ x := ha.reg_eq x
        have hy : reg s (ρ y) = reg s₀ y := ha.reg_eq y
        rw [hx, hy]
        dsimp only [target₀]
        split <;> rfl
      have hnext : (if ltb (reg s (ρ x)) (reg s (ρ y)) then base + ltPC else base + gePC) < linked.size := by
        rw [hcond]; have := rel.sub_fits; omega
      refine ⟨t, ?_, ⟨rfl, ha.reg_eq⟩, fun _ _ => rfl, rfl⟩
      simpa only [t, hcond] using step_branchLt_at hlinked hnext
    | goto target =>
      have hadv : (if target < sub.size then some (Transition.next { s₀ with pc := target }) else none) =
          some (Transition.next t₀) := by
        unfold step at hstep; rw [hf] at hstep; exact hstep
      obtain ⟨rfl, hlt⟩ := jumpTo target hadv
      let t : State L := { s with pc := base + target }
      have hlinked : linked[s.pc]? = some (.goto (base + target)) := by
        rw [hpcS]; exact hplaced
      have hnext : base + target < linked.size := by
        have := rel.sub_fits; omega
      exact ⟨t, step_goto_at hlinked hnext, ⟨rfl, ha.reg_eq⟩, fun _ _ => rfl, rfl⟩

private theorem steps_relocated_zeroWork {bits : Nat} {L₀ L : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    {sub : Program L₀} {linked : Program L} {base retPC : Nat}
    (rel : RelocatedZeroWork ρ sub linked base retPC)
    {i₀ : Input L₀} {i : Input L} (hi : i₀.words = i.words)
    {k : Nat} {s₀ u₀ : State L₀} {s : State L}
    (htr : Steps sub i₀ k s₀ u₀)
    (ha : StateAgreement ρ base s₀ s) :
    ∃ u : State L,
      Steps linked i k s u ∧
      StateAgreement ρ base u₀ u ∧
      (∀ j : Fin L.registerCount, (∀ r, ρ r ≠ j) → reg u j = reg s j) ∧
      u.data = s.data := by
  induction htr generalizing s with
  | zero a =>
    exact ⟨s, Steps.zero s, ha, fun _ _ => rfl, rfl⟩
  | cons head tail ih =>
    rename_i a b c n
    obtain ⟨t, hst, hat, hframe, hdata⟩ := step_relocated_zeroWork rel hi ha head
    obtain ⟨u, htu, hau, hframe', hdata'⟩ := ih hat
    exact ⟨u, Steps.cons hst htu, hau,
      fun j hj => (hframe' j hj).trans (hframe j hj), hdata'.trans hdata⟩

/-- Lift ANY successful `workCap = 0` `RamProgram.run` placed via `RelocatedZeroWork`
into a wider-workspace `Program L`, executing the exact same step count `res.executed`,
jumping cleanly to `retPC`, preserving unmapped registers and ALL scratch `data`. -/
theorem run_relocatedZeroWork {bits : Nat} {L₀ L : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    {sub : Program L₀} {linked : Program L} {base retPC : Nat}
    (rel : RelocatedZeroWork ρ sub linked base retPC)
    {i₀ : Input L₀} {i : Input L} (hi : i₀.words = i.words)
    {fuel : Nat} {s₀ : State L₀} {res : Result L₀}
    (hrun : run sub i₀ fuel s₀ = some res)
    {s : State L} (ha : StateAgreement ρ base s₀ s) :
    ∃ t : State L,
      Steps linked i res.executed s t ∧
      t.pc = retPC ∧
      (∀ r : Fin L₀.registerCount, reg t (ρ r) = reg res.finalState r) ∧
      (∀ j : Fin L.registerCount, (∀ r, ρ r ≠ j) → reg t j = reg s j) ∧
      t.data = s.data := by
  obtain ⟨k, u₀, hsteps, hhalt, hcount⟩ := run_has_steps_then_halt hrun
  obtain ⟨hf, hfin⟩ := halted_fetch_and_state hhalt
  subst hfin
  obtain ⟨u, hsu, hau, hframe, hdata⟩ := steps_relocated_zeroWork rel hi hsteps ha
  have hplaced := rel.placed res.finalState.pc .halt hf
  have hfetch : linked[u.pc]? = some (.goto retPC) := by
    rw [hau.pc_eq]; exact hplaced
  have hjump := step_goto_at (input := i) hfetch rel.ret_fits
  refine ⟨{ u with pc := retPC }, ?_, rfl, hau.reg_eq, hframe, hdata⟩
  rw [hcount]
  exact hsu.append (Steps.cons hjump (Steps.zero _))

/-! ### 2. Micro-Steps & Slice Placement Helpers (`registerCount = 16`) -/

section MicroSteps

variable {bits : Nat} {L : Layout bits} (h16 : L.registerCount = 16)

def r16 (i : Fin 16) : Fin L.registerCount :=
  ⟨i.val, by rw [h16]; exact i.isLt⟩

def PlacedSlice (block linked : Program L) (base : Nat) : Prop :=
  base + block.size ≤ linked.size ∧
  ∀ (i : Nat) (op : Instr bits L.registerCount),
    block[i]? = some op → linked[base + i]? = some op

theorem placedSlice_self (p : Program L) : PlacedSlice p p 0 := by
  refine ⟨by omega, fun i op hop => ?_⟩
  simpa only [Nat.zero_add] using hop

theorem placedSlice_append_left {a b linked : Program L} {base : Nat}
    (h : PlacedSlice (a ++ b) linked base) : PlacedSlice a linked base := by
  refine ⟨by have := h.1; simp only [Array.size_append] at this; omega, fun i op hop => ?_⟩
  have hi : i < a.size := by
    by_cases hlt : i < a.size
    · exact hlt
    · rw [getElem?_neg a i hlt] at hop; cases hop
  have hab : (a ++ b)[i]? = some op := by
    rw [Array.getElem?_append_left hi]; exact hop
  exact h.2 i op hab

theorem placedSlice_append_right {a b linked : Program L} {base : Nat}
    (h : PlacedSlice (a ++ b) linked base) : PlacedSlice b linked (base + a.size) := by
  refine ⟨by have := h.1; simp only [Array.size_append] at this; omega, fun i op hop => ?_⟩
  have hab : (a ++ b)[a.size + i]? = some op := by
    rw [Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hop
  have hlink := h.2 (a.size + i) op hab
  simpa only [Nat.add_assoc] using hlink

theorem placedSlice_fetch {block linked : Program L} {base k : Nat}
    {op : Instr bits L.registerCount}
    (hpl : PlacedSlice block linked base) (hk : block[k]? = some op) :
    linked[base + k]? = some op :=
  hpl.2 k op hk

theorem sub_no_wrap {bits : Nat} (x y : Word bits) (h : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  rw [WordOps.sub_val]
  have hx : x.val < 2 ^ bits := x.isLt
  have hEq : 2 ^ bits + x.val - y.val = 2 ^ bits + (x.val - y.val) := by omega
  rw [hEq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem placedSlice_relocatedZeroWork {L₀ : Layout bits}
    {ρ : Fin L₀.registerCount → Fin L.registerCount}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b) (hwork : L₀.workCap = 0)
    {sub : Program L₀} {linked : Program L} {base retPC : Nat}
    (hret : retPC < linked.size)
    (hpl : PlacedSlice (sub.map (patchAndRelocate ρ base retPC)) linked base) :
    RelocatedZeroWork ρ sub linked base retPC where
  inj := hinj
  work_zero := hwork
  sub_fits := by simpa only [Array.size_map] using hpl.1
  ret_fits := hret
  placed i op hop := by
    have hmap : (sub.map (patchAndRelocate ρ base retPC))[i]? =
        some (patchAndRelocate ρ base retPC op) := by
      rw [Array.getElem?_map, hop, Option.map_some]
    exact hpl.2 i _ hmap

def putReg (s : State L) (d : Fin 16) (w : Word bits) : State L :=
  let dr := r16 h16 d
  let hd : dr.val < s.regs.size := by simpa only [s.regs_size] using dr.isLt
  { s with
    regs := s.regs.set dr.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

theorem putReg_pc (s : State L) (d : Fin 16) (w : Word bits) :
    (putReg h16 s d w).pc = s.pc + 1 := rfl

theorem putReg_data (s : State L) (d : Fin 16) (w : Word bits) :
    (putReg h16 s d w).data = s.data := rfl

theorem reg_withPC (s : State L) (p : Nat) (j : Fin 16) :
    reg { s with pc := p } (r16 h16 j) = reg s (r16 h16 j) := rfl

theorem reg_putReg (s : State L) (d j : Fin 16) (w : Word bits) :
    reg (putReg h16 s d w) (r16 h16 j) =
      if j = d then w else reg s (r16 h16 j) := by
  have hd : (r16 h16 d).val < s.regs.size := by
    simpa only [s.regs_size] using (r16 h16 d).isLt
  have hj : (r16 h16 j).val < s.regs.size := by
    simpa only [s.regs_size] using (r16 h16 j).isLt
  change (s.regs.set (r16 h16 d).val w hd)[(r16 h16 j).val]'(by
      simpa only [Array.size_set] using hj) =
    if j = d then w else s.regs[(r16 h16 j).val]'hj
  by_cases he : j = d
  · subst he; simp [r16]
  · have hv : j.val ≠ d.val := fun h => he (Fin.ext h)
    simp [r16, Array.getElem_set, he, Ne.symm hv]

theorem step_imm_next {code : Program L} {input : Input L} {s : State L}
    {d : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.imm (r16 h16 d) w))
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg h16 s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg h16 s d w)) else none) = _
  rw [ite_eq_left hn]

theorem step_mov_next {code : Program L} {input : Input L} {s : State L}
    {d src : Fin 16}
    (hf : code[s.pc]? = some (.mov (r16 h16 d) (r16 h16 src)))
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg h16 s d (reg s (r16 h16 src)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg h16 s d (reg s (r16 h16 src)))) else none) = _
  rw [ite_eq_left hn]

theorem step_add_next {code : Program L} {input : Input L} {s : State L}
    {d x y : Fin 16}
    (hf : code[s.pc]? = some (.add (r16 h16 d) (r16 h16 x) (r16 h16 y)))
    (hn : s.pc + 1 < code.size) :
    step code input s =
      some (.next (putReg h16 s d (add (reg s (r16 h16 x)) (reg s (r16 h16 y))))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg h16 s d (add (reg s (r16 h16 x)) (reg s (r16 h16 y)))))
    else none) = _
  rw [ite_eq_left hn]

theorem step_sub_next {code : Program L} {input : Input L} {s : State L}
    {d x y : Fin 16}
    (hf : code[s.pc]? = some (.sub (r16 h16 d) (r16 h16 x) (r16 h16 y)))
    (hn : s.pc + 1 < code.size) :
    step code input s =
      some (.next (putReg h16 s d (sub (reg s (r16 h16 x)) (reg s (r16 h16 y))))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg h16 s d (sub (reg s (r16 h16 x)) (reg s (r16 h16 y)))))
    else none) = _
  rw [ite_eq_left hn]

theorem step_loadInput_next {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput (r16 h16 d) (r16 h16 addr)))
    (hread : input.words[(reg s (r16 h16 addr)).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg h16 s d w)) := by
  have h1 : step code input s =
      (input.words[(reg s (r16 h16 addr)).val]? >>= fun v =>
        if s.pc + 1 < code.size then some (Transition.next (putReg h16 s d v)) else none) := by
    unfold step; rw [hf]; rfl
  rw [h1, hread]
  change (if s.pc + 1 < code.size then some (Transition.next (putReg h16 s d w)) else none) = _
  rw [ite_eq_left hn]

theorem step_loadData_next {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData (r16 h16 d) (r16 h16 addr)))
    (hread : s.data[(reg s (r16 h16 addr)).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg h16 s d w)) := by
  have h1 : step code input s =
      (s.data[(reg s (r16 h16 addr)).val]? >>= fun v =>
        if s.pc + 1 < code.size then some (Transition.next (putReg h16 s d v)) else none) := by
    unfold step; rw [hf]; rfl
  rw [h1, hread]
  change (if s.pc + 1 < code.size then some (Transition.next (putReg h16 s d w)) else none) = _
  rw [ite_eq_left hn]

theorem step_storeData_next {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin 16}
    (hf : code[s.pc]? = some (.storeData (r16 h16 addr) (r16 h16 src)))
    (hfit : (reg s (r16 h16 addr)).val < s.data.size)
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next
      { s with
        data := s.data.set (reg s (r16 h16 addr)).val (reg s (r16 h16 src)) hfit
        pc := s.pc + 1
        data_size := by simp only [Array.size_set, s.data_size] }) := by
  unfold step
  rw [hf]
  change (if h : (reg s (r16 h16 addr)).val < s.data.size then
    if s.pc + 1 < code.size then
      some (Transition.next { s with
        data := s.data.set (reg s (r16 h16 addr)).val (reg s (r16 h16 src)) h
        pc := s.pc + 1
        data_size := by simp only [Array.size_set, s.data_size] })
    else none else none) = _
  rw [dite_eq_left hfit, ite_eq_left hn]

theorem step_branchLt_next {code : Program L} {input : Input L} {s : State L}
    {x y : Fin 16} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt (r16 h16 x) (r16 h16 y) yesPC noPC))
    (hfit : (if (reg s (r16 h16 x)).val < (reg s (r16 h16 y)).val then yesPC else noPC) < code.size) :
    step code input s = some (.next
      { s with pc := if (reg s (r16 h16 x)).val < (reg s (r16 h16 y)).val then yesPC else noPC }) := by
  have hltb : ltb (reg s (r16 h16 x)) (reg s (r16 h16 y)) =
      decide ((reg s (r16 h16 x)).val < (reg s (r16 h16 y)).val) := rfl
  have hst := step_branchLt_at (code := code) (input := input) (s := s)
    (x := r16 h16 x) (y := r16 h16 y) (yesPC := yesPC) (noPC := noPC) hf
    (by simpa only [hltb, decide_eq_true_eq] using hfit)
  simpa only [hltb, decide_eq_true_eq] using hst

theorem run_of_steps_halt {code : Program L} {input : Input L}
    {s u : State L} {k fuel : Nat}
    (hst : Steps code input k s u) (hh : step code input u = some (.halted u))
    (hfuel : k + 1 ≤ fuel) :
    run code input fuel s = some ⟨u, k + 1⟩ :=
  run_stable_of_le hfuel (hst.halts hh)

end MicroSteps

/-! ### 3. Relocated Library Kernels (`L.registerCount = 16`) -/

section LiftedKernels

variable {bits : Nat} {L : Layout bits} (h16 : L.registerCount = 16)

def liftMap {L₀ : Layout bits} (ρ : Fin L₀.registerCount → Fin L.registerCount)
    (base retPC : Nat) (sub : Program L₀) : Program L :=
  sub.map (patchAndRelocate ρ base retPC)

@[simp] theorem liftMap_size {L₀ : Layout bits}
    (ρ : Fin L₀.registerCount → Fin L.registerCount)
    (base retPC : Nat) (sub : Program L₀) :
    (liftMap ρ base retPC sub).size = sub.size := by
  simp [liftMap]

private theorem r16_inj : ∀ {a b : Fin 16}, r16 h16 a = r16 h16 b → a = b := by
  intro a b h; exact Fin.ext (congrArg (fun x : Fin L.registerCount => x.val) h)

def ρ16 {L₀ : Layout bits} (h₀ : L₀.registerCount = 16) :
    Fin L₀.registerCount → Fin L.registerCount :=
  fun i => r16 h16 ⟨i.val, h₀ ▸ i.isLt⟩

theorem ρ16_inj {L₀ : Layout bits} (h₀ : L₀.registerCount = 16) :
    ∀ {a b : Fin L₀.registerCount}, ρ16 h16 h₀ a = ρ16 h16 h₀ b → a = b := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin L.registerCount => x.val) h)

def ρ7 : Fin 7 → Fin L.registerCount :=
  fun i => r16 h16 ⟨i.val, by omega⟩

theorem ρ7_inj : ∀ {a b : Fin 7}, ρ7 h16 a = ρ7 h16 b → a = b := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin L.registerCount => x.val) h)

private def castState16 (L₀ : Layout bits) (h₀ : L₀.registerCount = 16)
    (s : State L) : State L₀ :=
  { regs := Array.ofFn (fun i : Fin L₀.registerCount => reg s (r16 h16 ⟨i.val, h₀ ▸ i.isLt⟩))
    data := Array.replicate L₀.workCap ⟨0, Nat.two_pow_pos bits⟩
    pc := 0
    regs_size := by simp
    data_size := by simp }

private theorem reg_castState16 (L₀ : Layout bits) (h₀ : L₀.registerCount = 16)
    (s : State L) (q : Fin L₀.registerCount) :
    reg (castState16 h16 L₀ h₀ s) q = reg s (r16 h16 ⟨q.val, h₀ ▸ q.isLt⟩) := by
  change (Array.ofFn (fun i : Fin L₀.registerCount => reg s (r16 h16 ⟨i.val, h₀ ▸ i.isLt⟩)))[q.val]'(by
    simp only [Array.size_ofFn]; exact q.isLt) = _
  rw [Array.getElem_ofFn]

private theorem castState16_agrees (L₀ : Layout bits) (h₀ : L₀.registerCount = 16)
    {base : Nat} {s : State L} (hpc : s.pc = base) :
    StateAgreement (ρ16 h16 h₀) base (castState16 h16 L₀ h₀ s) s :=
  ⟨hpc, fun r => (reg_castState16 h16 L₀ h₀ s r).symm⟩

/-- Lifted `sealedTranslation`: computes `I[I[header] + target]` into `r5`,
taking 4 steps, jumping to `retPC`, preserving scratch `data`. -/
theorem lifted_sealedTranslation
    {linked : Program L} {base retPC : Nat}
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (sealedTranslationLayout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (sealedTranslation L.inputFits)) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    (header mapBase target : Word bits)
    (hr0 : reg s (r16 h16 0) = header)
    (hr3 : reg s (r16 h16 3) = target)
    (hheader : input.words[header.val]? = some mapBase)
    (hmap : mapBase.val + target.val < L.inputCap) :
    ∃ t : State L,
      Steps linked input 4 s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 4)).val = mapBase.val + target.val ∧
      reg t (r16 h16 5) =
        input.words[mapBase.val + target.val]'(by rw [input.size_eq]; exact hmap) ∧
      t.data = s.data := by
  let L₀ := sealedTranslationLayout bits L.inputCap L.inputFits
  have rel : RelocatedZeroWork (ρ16 h16 (rfl : L₀.registerCount = 16))
      (sealedTranslation L.inputFits) linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  have h0₀ : s₀.regs[0]'(by rw [s₀.regs_size]; change 0 < 16; decide) = header :=
    (reg_castState16 h16 L₀ rfl s ⟨0, by change 0 < 16; decide⟩).trans hr0
  have h3₀ : s₀.regs[3]'(by rw [s₀.regs_size]; change 3 < 16; decide) = target :=
    (reg_castState16 h16 L₀ rfl s ⟨3, by change 3 < 16; decide⟩).trans hr3
  obtain ⟨t₀, hrun₀, ht4, ht5⟩ :=
    sealedTranslation_correct L.inputFits i₀ s₀ header mapBase target rfl h0₀ h3₀ hheader hmap
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun₀ (castState16_agrees h16 L₀ rfl hpc)
  refine ⟨t, hst, htpc, ?_, ?_, hdata⟩
  · have h4 := htreg ⟨4, by change 4 < 16; decide⟩
    change reg t (r16 h16 4) = t₀.regs[4]'(by rw [t₀.regs_size]; change 4 < 16; decide) at h4
    rw [h4]; exact ht4
  · have h5 := htreg ⟨5, by change 5 < 16; decide⟩
    change reg t (r16 h16 5) = t₀.regs[5]'(by rw [t₀.regs_size]; change 5 < 16; decide) at h5
    rw [h5]; exact ht5

/-- Lifted `IntervalGuard.romFor lo hi x zero one`: tests `reg lo ≤ reg x < reg hi`,
taking 3 or 4 (`≤ 4`) steps, leaving result `0` or `1` in `r0` and preserving `data`. -/
theorem lifted_intervalGuard
    {linked : Program L} {base retPC : Nat}
    (loReg hiReg xReg : Fin 16) (zeroW oneW : Word bits)
    (hz : zeroW.val = 0) (ho : oneW.val = 1)
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (IntervalGuard.romFor (L := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits) rfl loReg hiReg xReg zeroW oneW))
      linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base) :
    let lo := (reg s (r16 h16 loReg)).val
    let hi := (reg s (r16 h16 hiReg)).val
    let x := (reg s (r16 h16 xReg)).val
    let ok := lo ≤ x ∧ x < hi
    let k : Nat := if x < lo then 3 else 4
    ∃ t : State L,
      Steps linked input k s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 0)).val = (if ok then 1 else 0) ∧
      (∀ j : Fin 16, j ≠ 0 → reg t (r16 h16 j) = reg s (r16 h16 j)) ∧
      t.data = s.data := by
  let L₀ := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits
  let sub := IntervalGuard.romFor (L := L₀) rfl loReg hiReg xReg zeroW oneW
  have rel : RelocatedZeroWork (ρ16 h16 rfl) sub linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  obtain ⟨t₀, hrun₀, _, hr0, hframe₀, _⟩ :=
    IntervalGuard.run_spec_for rfl loReg hiReg xReg zeroW oneW hz ho i₀ s₀ rfl
  have heqR : ∀ q : Fin 16, reg s₀ (IntervalGuard.r rfl q) = reg s (r16 h16 q) := fun q =>
    reg_castState16 h16 L₀ rfl s q
  let k : Nat := if (reg s (r16 h16 xReg)).val < (reg s (r16 h16 loReg)).val then 3 else 4
  have hrun' := hrun₀ k
  have hkEq : (if (reg s₀ (IntervalGuard.r rfl xReg)).val < (reg s₀ (IntervalGuard.r rfl loReg)).val then 3 else 4) = k := by
    dsimp only [k]; rw [heqR xReg, heqR loReg]
  rw [hkEq, ite_eq_left (Nat.le_refl k)] at hrun'
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun' (castState16_agrees h16 L₀ rfl hpc)
  refine ⟨t, hst, htpc, ?_, ?_, hdata⟩
  · have h0 : (reg t (r16 h16 0)).val = (reg t₀ (IntervalGuard.r rfl 0)).val :=
      congrArg Fin.val (htreg ⟨0, by change 0 < 16; decide⟩)
    rw [h0, hr0]
    rw [heqR loReg, heqR hiReg, heqR xReg]
  · intro j hj
    have hj0 : (⟨j.val, j.isLt⟩ : Fin L₀.registerCount) ≠ IntervalGuard.r rfl 0 := by
      intro he; exact hj (Fin.ext (congrArg Fin.val he))
    have hregJ : reg t (r16 h16 j) = reg t₀ ⟨j.val, j.isLt⟩ := htreg ⟨j.val, j.isLt⟩
    exact hregJ.trans ((hframe₀ ⟨j.val, j.isLt⟩ hj0).trans (heqR j))

/-- Lifted `PairGuard.rom zero one`: tests `(reg 1).val = (reg 3).val`,
taking 4 steps, setting `r0 = 0` iff equal else `1`, preserving `data`. -/
theorem lifted_pairGuard
    {linked : Program L} {base retPC : Nat}
    (zeroW oneW : Word bits) (hz : zeroW.val = 0) (ho : oneW.val = 1)
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits) rfl zeroW oneW))
      linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base) :
    let eqID := (reg s (r16 h16 1)).val = (reg s (r16 h16 3)).val
    ∃ t : State L,
      Steps linked input 4 s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 0)).val = (if eqID then 0 else 1) ∧
      t.data = s.data := by
  let L₀ := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits
  let sub := PairGuard.rom (L := L₀) rfl zeroW oneW
  have rel : RelocatedZeroWork (ρ16 h16 rfl) sub linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  obtain ⟨t₀, hrun₀, _, hr0, _, _⟩ :=
    PairGuard.run_spec rfl zeroW oneW hz ho (fun _ _ => rfl) i₀ s₀ rfl
  have hrun' := hrun₀ 4
  rw [ite_eq_left (Nat.le_refl 4)] at hrun'
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun' (castState16_agrees h16 L₀ rfl hpc)
  have heqR : ∀ q : Fin 16, reg s₀ (PairGuard.r rfl q) = reg s (r16 h16 q) := fun q =>
    reg_castState16 h16 L₀ rfl s q
  refine ⟨t, hst, htpc, ?_, hdata⟩
  have h0 : (reg t (r16 h16 0)).val = (reg t₀ (PairGuard.r rfl 0)).val :=
    congrArg Fin.val (htreg ⟨0, by change 0 < 16; decide⟩)
  rw [h0, hr0]
  rw [heqR 1, heqR 3]

/-- Lifted `PaperB.EX53.program`: computes `LCA(x, y)` in `14 * k + 19` steps,
jumping to `retPC`, leaving `r0 = P.node a` and preserving `data`. -/
theorem lifted_staticLCA {n : Nat}
    {linked : Program L} {base retPC : Nat}
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (EX53.layout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (EX53.program L.inputFits)) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    {T : _root_.EX16.Tables (Fin n)}
    (P : EX53.Packed (⟨input.words, input.size_eq⟩ : Input (EX53.layout bits L.inputCap L.inputFits)) T)
    {x y a : Fin n} {k : Nat} (trace : _root_.EX16.Execution T x y a k)
    (hreg : ∀ r : Fin 16, reg s (r16 h16 r) = reg (EX53.initial P x y) r) :
    ∃ t : State L,
      Steps linked input (14 * k + 19) s t ∧
      t.pc = retPC ∧
      reg t (r16 h16 0) = P.node a ∧
      t.data = s.data := by
  let L₀ := EX53.layout bits L.inputCap L.inputFits
  have rel : RelocatedZeroWork (ρ16 h16 rfl) (EX53.program L.inputFits) linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  obtain ⟨res, hrun, hexec, hans⟩ := EX53.runWorker P trace
  have ha : StateAgreement (ρ16 h16 rfl) base (EX53.initial P x y) s :=
    ⟨hpc, fun r => hreg r⟩
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun ha
  refine ⟨t, ?_, htpc, ?_, hdata⟩
  · simpa only [hexec] using hst
  · exact (htreg EX53.rx).trans hans

/-- Lifted 7-register `Predecessor.worker`: computes `count = lower t` into `r0`
in `≤ 11 * (Nat.log2 (p.len + 1) + 1)` steps, jumping to `retPC` and preserving `data`. -/
theorem lifted_predWorker
    {linked : Program L} {base retPC : Nat}
    (hpl : PlacedSlice (liftMap (ρ7 h16) base retPC (Predecessor.worker L.inputFits)) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    (p : Predecessor.Slice (bits := bits) (cap := L.inputCap) (hcap := L.inputFits)
      ⟨input.words, input.size_eq⟩)
    (key : Word bits) (hsorted : p.Sorted)
    (hreg : ∀ r : Fin 7, reg s (ρ7 h16 r) = reg (Predecessor.init p key) r) :
    ∃ (t : State L) (steps : Nat),
      steps ≤ 11 * (Nat.log2 (p.len + 1) + 1) ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      Predecessor.Answer p key (reg t (r16 h16 0)).val ∧
      (∀ j : Fin 16, 7 ≤ j.val → reg t (r16 h16 j) = reg s (r16 h16 j)) ∧
      t.data = s.data := by
  let L₀ := Predecessor.layout bits L.inputCap L.inputFits
  have rel : RelocatedZeroWork (ρ7 h16) (Predecessor.worker L.inputFits) linked base retPC :=
    placedSlice_relocatedZeroWork (ρ7_inj h16) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  obtain ⟨res, hrun, hans, _, hsteps⟩ := Predecessor.worker_correct p key hsorted
  have ha : StateAgreement (ρ7 h16) base (Predecessor.init p key) s :=
    ⟨hpc, hreg⟩
  obtain ⟨t, hst, htpc, htreg, hframe, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun ha
  refine ⟨t, res.executed, hsteps, hst, htpc, ?_, ?_, hdata⟩
  · have h0 := htreg ⟨0, by change 0 < 7; decide⟩
    change reg t (r16 h16 0) = reg res.finalState ⟨0, by change 0 < 7; decide⟩ at h0
    rw [h0]
    exact hans
  · intro j hj
    apply hframe (r16 h16 j)
    intro r he
    have hv := congrArg (fun x : Fin L.registerCount => x.val) he
    change r.val = (r16 h16 j).val at hv
    have hr7 : r.val < 7 := r.isLt
    change r.val = j.val at hv
    omega

/-- Lifted `ThreeCalls.EqualityTail.checkedProgram`: computes exact pair-search hit/miss
in `≤ 33 * (Nat.log2 (a.size + 1) + 1) + 39` steps, jumping to `retPC` and preserving `data`. -/
theorem lifted_pairSearch
    {linked : Program L} {base retPC : Nat}
    (hone : 1 < 2 ^ bits)
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (ThreeCalls.layout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (ThreeCalls.EqualityTail.checkedProgram L.inputFits hone (ThreeCalls.concreteSetup bits hone)))
      linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    {a : Array PairLookup.Key}
    (c : PairLookup.ColumnReduction.Columns (bits := bits) input.words a)
    (hs : PairLookup.StrictSorted a) (x y : Word bits)
    (h7 : reg s (r16 h16 7) = c.first.base)
    (h8 : (reg s (r16 h16 8)).val = c.first.len)
    (h9 : reg s (r16 h16 9) = c.second.base)
    (h11 : reg s (r16 h16 11) = x)
    (h12 : reg s (r16 h16 12) = y)
    (h4 : reg s (r16 h16 4) = zero bits)
    (h5 : reg s (r16 h16 5) = zero bits) :
    ∃ (t : State L) (steps : Nat),
      steps ≤ 33 * (Nat.log2 (a.size + 1) + 1) + 39 ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 0) = (⟨1, hone⟩ : Word bits) ↔
        (PairLookup.lookup a (x.val, y.val)).1.isSome = true) ∧
      (∀ row : Nat, (PairLookup.lookup a (x.val, y.val)).1 = some row →
        reg t (r16 h16 0) = (⟨1, hone⟩ : Word bits) ∧
        (reg t (r16 h16 3)).val = row) ∧
      t.data = s.data := by
  let L₀ := ThreeCalls.layout bits L.inputCap L.inputFits
  let sub := ThreeCalls.EqualityTail.checkedProgram L.inputFits hone (ThreeCalls.concreteSetup bits hone)
  have rel : RelocatedZeroWork (ρ16 h16 rfl) sub linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input (Predecessor.layout bits L.inputCap L.inputFits) := ⟨input.words, input.size_eq⟩
  let j₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  have heqR : ∀ q : Fin 16, ThreeCalls.setupReg s₀ q = reg s (r16 h16 q) := fun q =>
    reg_castState16 h16 L₀ rfl s ⟨q.val, q.isLt⟩
  obtain ⟨res, hrun, hflag, hhit, _⟩ :=
    ThreeCalls.pair_search_correct_from_pc0_with_index (i := i₀) (j := j₀)
      L.inputFits hone c hs x y rfl s₀ rfl
      ((heqR 7).trans h7) (by rw [heqR 8]; exact h8) ((heqR 9).trans h9)
      ((heqR 11).trans h11) ((heqR 12).trans h12)
      ((heqR 4).trans h4) ((heqR 5).trans h5)
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : j₀.words = input.words) hrun (castState16_agrees h16 L₀ rfl hpc)
  have hres0 : reg t (r16 h16 0) = ThreeCalls.setupReg res.finalState 0 :=
    htreg ⟨0, by change 0 < 16; decide⟩
  have hres3 : reg t (r16 h16 3) = ThreeCalls.setupReg res.finalState 3 :=
    htreg ⟨3, by change 3 < 16; decide⟩
  refine ⟨t, res.executed, run_executed_le hrun, hst, htpc, ?_, ?_, hdata⟩
  · simpa only [hres0] using hflag
  · intro row hrow
    obtain ⟨hb, hr3⟩ := hhit row hrow
    exact ⟨hres0.trans hb, (congrArg Fin.val hres3).trans hr3⟩

/-- Lifted `KnownNodeCheck.knownNodeProgram`: checks `WordColumns.known w a y` in `≤ 16` steps,
jumping to `retPC` and preserving `data`. -/
theorem lifted_knownCheck
    {linked : Program L} {base retPC : Nat}
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (KnownNodeCheck.knownNodeProgram L.inputFits)) linked base)
    (hret : retPC < linked.size)
    (w : RetainedProperLoss.WordColumns bits)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    (labelsBase entryBase stopBase a y : Nat) (zeroW oneW : Word bits)
    (hZero : zeroW.val = 0) (hOne : oneW.val = 1)
    (haE : a < w.entry.size) (haS : a < w.stop.size) (hy : y < w.labels.size)
    (hlE : w.labelAt y < w.entry.size)
    (hr1 : (reg s (r16 h16 1)).val = a) (hr2 : (reg s (r16 h16 2)).val = y)
    (hr3 : (reg s (r16 h16 3)).val = labelsBase) (hr4 : (reg s (r16 h16 4)).val = entryBase)
    (hr5 : (reg s (r16 h16 5)).val = stopBase)
    (hr6 : reg s (r16 h16 6) = zeroW) (hr7 : reg s (r16 h16 7) = oneW)
    (hLFit : labelsBase + w.labels.size ≤ L.inputCap)
    (hEFit : entryBase + w.entry.size ≤ L.inputCap)
    (hSFit : stopBase + w.stop.size ≤ L.inputCap)
    (hLabels : ∀ j (hj : j < w.labels.size), input.words[labelsBase + j]? = some (w.labels[j]'hj))
    (hEntry : ∀ j (hj : j < w.entry.size), input.words[entryBase + j]? = some (w.entry[j]'hj))
    (hStop : ∀ j (hj : j < w.stop.size), input.words[stopBase + j]? = some (w.stop[j]'hj)) :
    ∃ (t : State L) (steps : Nat),
      steps ≤ 16 ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      reg t (r16 h16 0) = (if w.known a y then oneW else zeroW) ∧
      ((reg t (r16 h16 0)).val = 1 ↔ w.known a y = true) ∧
      t.data = s.data := by
  let L₀ := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits
  have rel : RelocatedZeroWork (ρ16 h16 rfl) (KnownNodeCheck.knownNodeProgram L.inputFits) linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  have heqR : ∀ q : Fin 16, reg s₀ ⟨q.val, q.isLt⟩ = reg s (r16 h16 q) := fun q =>
    reg_castState16 h16 L₀ rfl s q
  obtain ⟨steps, t₀, _, h16b, hrun, _, _, hr0, hiff, _⟩ :=
    KnownNodeCheck.knownNodeProgram_wordColumns_spec w i₀ s₀ rfl labelsBase entryBase stopBase
      a y zeroW oneW hZero hOne haE haS hy hlE
      (by rw [heqR 1]; exact hr1) (by rw [heqR 2]; exact hr2)
      (by rw [heqR 3]; exact hr3) (by rw [heqR 4]; exact hr4)
      (by rw [heqR 5]; exact hr5) ((heqR 6).trans hr6) ((heqR 7).trans hr7)
      hLFit hEFit hSFit hLabels hEntry hStop
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : i₀.words = input.words) hrun (castState16_agrees h16 L₀ rfl hpc)
  have h0 := htreg ⟨0, by change 0 < 16; decide⟩
  change reg t (r16 h16 0) = reg t₀ 0 at h0
  exact ⟨t, steps, h16b, hst, htpc, h0.trans hr0, by rw [h0]; exact hiff, hdata⟩

/-- Lifted `ExitEval.exitEvalProgram`: evaluates `PriorBase.run mem R w.tags prior v u d`
into `r0..r5` (`intervalCodec`) in `≤ 96 * (foldStored mem R w.tags u d).steps + 28` steps,
jumping to `retPC` and preserving `data`. Uses `exitEvalProgram_spec` directly (no `StoreOK`). -/
theorem lifted_exitEval
    {linked : Program L} {base retPC : Nat}
    {endpoints : Nat} {mem : Array (Word bits)}
    {_hMemSz : mem.size = L.inputCap}
    {fits : mem.size ≤ 2 ^ bits}
    {R : ExitMap.JumpMapRoute.StoredExit.Region bits mem.size} {F : JumpForest}
    {ref : Nat → ExitMap.CheckedFold.Stored}
    {w : ExitMap.Retention.Width bits (max R.slots endpoints)}
    (ok : ExitMap.JumpMapRoute.StoredExit.Occupied mem R F ref w)
    (prior : Array (Option ExitMap.Values))
    (hb : ExitMap.SealedPriorBase.BaseBound (max R.slots endpoints) prior)
    (B : ExitMap.SealedPriorBase.BaseView prior.size mem.size)
    (hPlaced : ExitMap.SealedPriorBase.Placed w prior hb mem B)
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (ExitEval.exitEvalLayout bits mem.size fits).registerCount = 16))
      base retPC (ExitEval.exitEvalProgram (fits := fits) w.tags)) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (hWords : input.words = mem)
    (depthBase : Nat)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = depthBase + x.val)
    {u : Nat} (hu : u < F.size) (v : Fin prior.size) (d : Nat)
    (s : State L) (hpc : s.pc = base)
    (hr6 : (reg s (r16 h16 6)).val = u)
    (hr7 : (reg s (r16 h16 7)).val = d)
    (hr8 : (reg s (r16 h16 8)).val = v.val)
    (hr9 : (reg s (r16 h16 9)).val = depthBase)
    (hr10 : (reg s (r16 h16 10)).val = R.base.val)
    (hr11 : (reg s (r16 h16 11)).val = B.start) :
    ∃ (t : State L) (k : Nat),
      k ≤ 96 * (ExitMap.JumpMapRoute.StoredExit.foldStored mem R w.tags u d).steps + 28 ∧
      Steps linked input k s t ∧
      t.pc = retPC ∧
      ExitEval.IntervalWords w.tags
        (ExitMap.JumpMapRoute.StoredExit.PriorBase.run mem R w.tags prior v u d).x0
        (reg t (r16 h16 0)) (reg t (r16 h16 1)) (reg t (r16 h16 2)) ∧
      ExitEval.IntervalWords w.tags
        (ExitMap.JumpMapRoute.StoredExit.PriorBase.run mem R w.tags prior v u d).x1
        (reg t (r16 h16 3)) (reg t (r16 h16 4)) (reg t (r16 h16 5)) ∧
      t.data = s.data := by
  let L₀ := ExitEval.exitEvalLayout bits mem.size fits
  have rel : RelocatedZeroWork (ρ16 h16 rfl) (ExitEval.exitEvalProgram (fits := fits) w.tags)
      linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input L₀ := ⟨mem, rfl⟩
  let s₀ : State L₀ := castState16 h16 L₀ rfl s
  have heqR : ∀ q : Fin 16, reg s₀ ⟨q.val, q.isLt⟩ = reg s (r16 h16 q) := fun q =>
    reg_castState16 h16 L₀ rfl s q
  obtain ⟨t₀, _, k, hk, hrun, _, _, hVals, _⟩ :=
    ExitEval.exitEvalProgram_spec ok prior hb B hPlaced i₀ rfl depthBase hDepthContig hu v d s₀ rfl
      ((congrArg Fin.val (heqR 6)).trans hr6) ((congrArg Fin.val (heqR 7)).trans hr7)
      ((congrArg Fin.val (heqR 8)).trans hr8) ((congrArg Fin.val (heqR 9)).trans hr9)
      ((congrArg Fin.val (heqR 10)).trans hr10) ((congrArg Fin.val (heqR 11)).trans hr11)
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel hWords.symm hrun (castState16_agrees h16 L₀ rfl hpc)
  have hr0 : reg t (r16 h16 0) = reg t₀ 0 := htreg 0
  have hr1 : reg t (r16 h16 1) = reg t₀ 1 := htreg 1
  have hr2 : reg t (r16 h16 2) = reg t₀ 2 := htreg 2
  have hr3 : reg t (r16 h16 3) = reg t₀ 3 := htreg 3
  have hr4 : reg t (r16 h16 4) = reg t₀ 4 := htreg 4
  have hr5 : reg t (r16 h16 5) = reg t₀ 5 := htreg 5
  refine ⟨t, k, hk, hst, htpc, ?_, ?_, hdata⟩
  · rw [hr0, hr1, hr2]; exact hVals.1
  · rw [hr3, hr4, hr5]; exact hVals.2

end LiftedKernels

/-! ### 4. Sealed-Slice Adapters (`StaticHeaderSpec` / `SliceAt` → Kernel Inputs) -/

section SealedAdapters

/-- Construct `PaperB.PairLookup.ColumnReduction.Columns` directly from a
`FlatPairDictionary.Represents` slice placed inside `I` at `dictPtr`. -/
def columnsOfDictSlice {bits : Nat} {H : LabelledQuotient}
    (I : Array (Word bits)) (dictPtr : Nat)
    (wDict : Array (Word bits)) (hSlice : SliceAt I dictPtr wDict)
    {s : RetainedProperLoss.Columns H}
    (hRep : ForestSlimIndex.FlatPairDictionary.Represents wDict s)
    (hIlt : I.size < 2 ^ bits) :
    PairLookup.ColumnReduction.Columns (bits := bits) I s.dict :=
  let rows := ForestSlimIndex.FlatPairDictionary.rowCount wDict
  have hKW : ForestSlimIndex.FlatPairDictionary.slotBase rows ≤ wDict.size := hRep.valid.keysWithin
  have hBase1 : 1 + rows ≤ wDict.size := by
    unfold ForestSlimIndex.FlatPairDictionary.slotBase
      ForestSlimIndex.FlatPairDictionary.secondBase at hKW
    omega
  have hBase2 : 1 + rows + rows ≤ wDict.size := by
    unfold ForestSlimIndex.FlatPairDictionary.slotBase
      ForestSlimIndex.FlatPairDictionary.secondBase at hKW
    omega
  have hRows : rows = s.dict.size := hRep.rows
  have hFit1 : (dictPtr + 1) + rows < 2 ^ bits := by
    have := hSlice.1; omega
  have hFit2 : (dictPtr + 1 + rows) + rows < 2 ^ bits := by
    have := hSlice.1; omega
  { first :=
      { base := ⟨dictPtr + 1, by omega⟩
        len := rows
        fits := hFit1
        within := by
          change (dictPtr + 1) + rows ≤ I.size
          have := hSlice.1; omega }
    second :=
      { base := ⟨dictPtr + 1 + rows, by omega⟩
        len := rows
        fits := hFit2
        within := by
          change (dictPtr + 1 + rows) + rows ≤ I.size
          have := hSlice.1; omega }
    first_len := hRows
    second_len := hRows
    first_word i hi := by
      have hiR : i < (ForestSlimIndex.FlatPairDictionary.firstSlice wDict hRep.valid).len := by
        rw [ForestSlimIndex.FlatPairDictionary.firstSlice_len]
        change i < rows
        rw [hRows]
        exact hi
      have h1 := hRep.first_eq i hiR hi
      have hidx : 1 + i < wDict.size := by omega
      have hSliceEq := hSlice.2 (1 + i) hidx
      have hLtI : dictPtr + (1 + i) < I.size := by have := hSlice.1; omega
      have hposI := getElem?_pos I (dictPtr + (1 + i)) hLtI
      rw [hposI] at hSliceEq
      have hw : I[dictPtr + (1 + i)]'hLtI = wDict[1 + i]'hidx := Option.some.inj hSliceEq
      have hLtI' : (dictPtr + 1) + i < I.size := by change (dictPtr + 1) + i < I.size; have := hSlice.1; omega
      have hIdxEq : (dictPtr + 1) + i = dictPtr + (1 + i) := by omega
      have hElem : I[(dictPtr + 1) + i]'hLtI' = I[dictPtr + (1 + i)]'hLtI := by
        simp only [hIdxEq]
      change (I[(dictPtr + 1) + i]'hLtI').val = (s.dict[i]'hi).1
      rw [hElem, hw]
      exact h1
    second_word i hi := by
      have hiR : i < (ForestSlimIndex.FlatPairDictionary.secondSlice wDict hRep.valid).len := by
        rw [ForestSlimIndex.FlatPairDictionary.secondSlice_len]
        change i < rows
        rw [hRows]
        exact hi
      have h2 := hRep.second_eq i hiR hi
      have hidx : 1 + rows + i < wDict.size := by omega
      have hSliceEq := hSlice.2 (1 + rows + i) hidx
      have hLtI : dictPtr + (1 + rows + i) < I.size := by have := hSlice.1; omega
      have hposI := getElem?_pos I (dictPtr + (1 + rows + i)) hLtI
      rw [hposI] at hSliceEq
      have hw : I[dictPtr + (1 + rows + i)]'hLtI = wDict[1 + rows + i]'hidx := Option.some.inj hSliceEq
      have hLtI' : (dictPtr + 1 + rows) + i < I.size := by
        change (dictPtr + 1 + rows) + i < I.size; have := hSlice.1; omega
      have hIdxEq : (dictPtr + 1 + rows) + i = dictPtr + (1 + rows + i) := by omega
      have hElem : I[(dictPtr + 1 + rows) + i]'hLtI' = I[dictPtr + (1 + rows + i)]'hLtI := by
        simp only [hIdxEq]
      change (I[(dictPtr + 1 + rows) + i]'hLtI').val = (s.dict[i]'hi).2
      rw [hElem, hw]
      exact h2 }

end SealedAdapters

/-! ### 5. Reusable Query Micro-Blocks (`ancestorCheckBlock` & `childSearchBlock`) -/

section ReusableBlocks

variable {bits : Nat} {L : Layout bits} (h16 : L.registerCount = 16)

private def ancestorPre (hdrEntryW hdrStopW : Word bits) (nodeReg targetReg : Fin 16) :
    Program L :=
  #[.imm (r16 h16 15) hdrEntryW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 nodeReg),
    .loadInput (r16 h16 10) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 targetReg),
    .loadInput (r16 h16 12) (r16 h16 15),
    .imm (r16 h16 15) hdrStopW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 nodeReg),
    .loadInput (r16 h16 11) (r16 h16 15)]

private theorem ancestorPre_size (hdrEntryW hdrStopW : Word bits) (nodeReg targetReg : Fin 16) :
    (ancestorPre h16 hdrEntryW hdrStopW nodeReg targetReg (L := L)).size = 10 := rfl

def ancestorCheckBlock (hdrEntryW hdrStopW zeroW oneW : Word bits)
    (nodeReg targetReg : Fin 16) (base retPC : Nat) : Program L :=
  ancestorPre h16 hdrEntryW hdrStopW nodeReg targetReg ++
  liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
    (base + 10) retPC
    (IntervalGuard.romFor (L := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits) rfl 10 11 12 zeroW oneW)

@[simp] theorem ancestorCheckBlock_size (hdrEntryW hdrStopW zeroW oneW : Word bits)
    (nodeReg targetReg : Fin 16) (base retPC : Nat) :
    (ancestorCheckBlock (L := L) h16 hdrEntryW hdrStopW zeroW oneW nodeReg targetReg base retPC).size = 16 := by
  simp [ancestorCheckBlock, ancestorPre, IntervalGuard.romFor]

theorem ancestorCheckBlock_spec
    {linked : Program L} {base retPC : Nat}
    (hdrEntryW hdrStopW zeroW oneW : Word bits)
    (hz : zeroW.val = 0) (ho : oneW.val = 1)
    (nodeReg targetReg : Fin 16)
    (hNode : nodeReg ≠ 10 ∧ nodeReg ≠ 12 ∧ nodeReg ≠ 14 ∧ nodeReg ≠ 15)
    (hTgt : targetReg ≠ 10 ∧ targetReg ≠ 14 ∧ targetReg ≠ 15)
    (hpl : PlacedSlice (ancestorCheckBlock (L := L) h16 hdrEntryW hdrStopW zeroW oneW nodeReg targetReg base retPC) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    {entryBaseW stopBaseW : Word bits}
    (hEH : input.words[hdrEntryW.val]? = some entryBaseW)
    (hSH : input.words[hdrStopW.val]? = some stopBaseW)
    {entryNode entryTgt stopNode : Word bits}
    (hEN : input.words[entryBaseW.val + (reg s (r16 h16 nodeReg)).val]? = some entryNode)
    (hET : input.words[entryBaseW.val + (reg s (r16 h16 targetReg)).val]? = some entryTgt)
    (hSN : input.words[stopBaseW.val + (reg s (r16 h16 nodeReg)).val]? = some stopNode) :
    ∃ (t : State L) (steps : Nat),
      steps ≤ 14 ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 0)).val =
        (if entryNode.val ≤ entryTgt.val ∧ entryTgt.val < stopNode.val then 1 else 0) ∧
      t.data = s.data := by
  have hPrePl : PlacedSlice (ancestorPre h16 hdrEntryW hdrStopW nodeReg targetReg (L := L)) linked base :=
    placedSlice_append_left hpl
  have hGPl : PlacedSlice
      (liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
        (base + 10) retPC (IntervalGuard.romFor rfl 10 11 12 zeroW oneW))
      linked (base + 10) := by
    simpa only [ancestorPre_size] using placedSlice_append_right hpl
  have hSz : base + 16 ≤ linked.size := by
    have := hpl.1; simp only [ancestorCheckBlock_size] at this; exact this
  have hLtEN : entryBaseW.val + (reg s (r16 h16 nodeReg)).val < 2 ^ bits := by
    have hb : entryBaseW.val + (reg s (r16 h16 nodeReg)).val < input.words.size := by
      by_cases hlt : entryBaseW.val + (reg s (r16 h16 nodeReg)).val < input.words.size
      · exact hlt
      · rw [getElem?_neg input.words _ hlt] at hEN; cases hEN
    rw [input.size_eq] at hb; exact Nat.lt_of_lt_of_le hb L.inputFits
  have hLtET : entryBaseW.val + (reg s (r16 h16 targetReg)).val < 2 ^ bits := by
    have hb : entryBaseW.val + (reg s (r16 h16 targetReg)).val < input.words.size := by
      by_cases hlt : entryBaseW.val + (reg s (r16 h16 targetReg)).val < input.words.size
      · exact hlt
      · rw [getElem?_neg input.words _ hlt] at hET; cases hET
    rw [input.size_eq] at hb; exact Nat.lt_of_lt_of_le hb L.inputFits
  have hLtSN : stopBaseW.val + (reg s (r16 h16 nodeReg)).val < 2 ^ bits := by
    have hb : stopBaseW.val + (reg s (r16 h16 nodeReg)).val < input.words.size := by
      by_cases hlt : stopBaseW.val + (reg s (r16 h16 nodeReg)).val < input.words.size
      · exact hlt
      · rw [getElem?_neg input.words _ hlt] at hSN; cases hSN
    rw [input.size_eq] at hb; exact Nat.lt_of_lt_of_le hb L.inputFits
  let s1 := putReg h16 s 15 hdrEntryW
  let s2 := putReg h16 s1 14 entryBaseW
  let s3 := putReg h16 s2 15 (add entryBaseW (reg s (r16 h16 nodeReg)))
  let s4 := putReg h16 s3 10 entryNode
  let s5 := putReg h16 s4 15 (add entryBaseW (reg s (r16 h16 targetReg)))
  let s6 := putReg h16 s5 12 entryTgt
  let s7 := putReg h16 s6 15 hdrStopW
  let s8 := putReg h16 s7 14 stopBaseW
  let s9 := putReg h16 s8 15 (add stopBaseW (reg s (r16 h16 nodeReg)))
  let s10 := putReg h16 s9 11 stopNode
  have h0 : step linked input s = some (.next s1) :=
    step_imm_next h16 (by rw [hpc]; exact placedSlice_fetch hPrePl (k := 0) rfl) (by omega)
  have h1 : step linked input s1 = some (.next s2) := by
    have hs1pc : s1.pc = base + 1 := by simp only [s1, putReg_pc, hpc]
    have hs1r : input.words[(reg s1 (r16 h16 15)).val]? = some entryBaseW := by
      simpa [s1, reg_putReg] using hEH
    exact step_loadInput_next h16 (by rw [hs1pc]; exact placedSlice_fetch hPrePl (k := 1) rfl) hs1r (by omega)
  have h2 : step linked input s2 = some (.next s3) := by
    have hs2pc : s2.pc = base + 2 := by simp only [s2, s1, putReg_pc, hpc]
    have h14 : reg s2 (r16 h16 14) = entryBaseW := by simp [s2, reg_putReg]
    have hn : reg s2 (r16 h16 nodeReg) = reg s (r16 h16 nodeReg) := by
      simp [s2, s1, reg_putReg, hNode.2.2.1, hNode.2.2.2]
    have hs := step_add_next h16 (input := input) (s := s2) (d := 15) (x := 14) (y := nodeReg)
      (by rw [hs2pc]; exact placedSlice_fetch hPrePl (k := 2) rfl) (by omega)
    simpa [s3, h14, hn] using hs
  have h3 : step linked input s3 = some (.next s4) := by
    have hs3pc : s3.pc = base + 3 := by simp only [s3, s2, s1, putReg_pc, hpc]
    have hval : (reg s3 (r16 h16 15)).val = entryBaseW.val + (reg s (r16 h16 nodeReg)).val := by
      simpa [s3, reg_putReg] using add_no_wrap entryBaseW (reg s (r16 h16 nodeReg)) hLtEN
    have hr : input.words[(reg s3 (r16 h16 15)).val]? = some entryNode := by rw [hval]; exact hEN
    exact step_loadInput_next h16 (by rw [hs3pc]; exact placedSlice_fetch hPrePl (k := 3) rfl) hr (by omega)
  have h4 : step linked input s4 = some (.next s5) := by
    have hs4pc : s4.pc = base + 4 := by simp only [s4, s3, s2, s1, putReg_pc, hpc]
    have h14 : reg s4 (r16 h16 14) = entryBaseW := by
      simp [s4, s3, s2, reg_putReg]
    have ht : reg s4 (r16 h16 targetReg) = reg s (r16 h16 targetReg) := by
      simp [s4, s3, s2, s1, reg_putReg, hTgt.1, hTgt.2.1, hTgt.2.2]
    have hs := step_add_next h16 (input := input) (s := s4) (d := 15) (x := 14) (y := targetReg)
      (by rw [hs4pc]; exact placedSlice_fetch hPrePl (k := 4) rfl) (by omega)
    simpa [s5, h14, ht] using hs
  have h5 : step linked input s5 = some (.next s6) := by
    have hs5pc : s5.pc = base + 5 := by simp only [s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hval : (reg s5 (r16 h16 15)).val = entryBaseW.val + (reg s (r16 h16 targetReg)).val := by
      simpa [s5, reg_putReg] using add_no_wrap entryBaseW (reg s (r16 h16 targetReg)) hLtET
    have hr : input.words[(reg s5 (r16 h16 15)).val]? = some entryTgt := by rw [hval]; exact hET
    exact step_loadInput_next h16 (by rw [hs5pc]; exact placedSlice_fetch hPrePl (k := 5) rfl) hr (by omega)
  have h6 : step linked input s6 = some (.next s7) := by
    have hs6pc : s6.pc = base + 6 := by simp only [s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hs6pc]; exact placedSlice_fetch hPrePl (k := 6) rfl) (by omega)
  have h7 : step linked input s7 = some (.next s8) := by
    have hs7pc : s7.pc = base + 7 := by simp only [s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hr : input.words[(reg s7 (r16 h16 15)).val]? = some stopBaseW := by
      simpa [s7, reg_putReg] using hSH
    exact step_loadInput_next h16 (by rw [hs7pc]; exact placedSlice_fetch hPrePl (k := 7) rfl) hr (by omega)
  have h8 : step linked input s8 = some (.next s9) := by
    have hs8pc : s8.pc = base + 8 := by simp only [s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have h14 : reg s8 (r16 h16 14) = stopBaseW := by simp [s8, reg_putReg]
    have hn : reg s8 (r16 h16 nodeReg) = reg s (r16 h16 nodeReg) := by
      simp [s8, s7, s6, s5, s4, s3, s2, s1, reg_putReg, hNode.1, hNode.2.1, hNode.2.2.1, hNode.2.2.2]
    have hs := step_add_next h16 (input := input) (s := s8) (d := 15) (x := 14) (y := nodeReg)
      (by rw [hs8pc]; exact placedSlice_fetch hPrePl (k := 8) rfl) (by omega)
    simpa [s9, h14, hn] using hs
  have h9 : step linked input s9 = some (.next s10) := by
    have hs9pc : s9.pc = base + 9 := by simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hval : (reg s9 (r16 h16 15)).val = stopBaseW.val + (reg s (r16 h16 nodeReg)).val := by
      simpa [s9, reg_putReg] using add_no_wrap stopBaseW (reg s (r16 h16 nodeReg)) hLtSN
    have hr : input.words[(reg s9 (r16 h16 15)).val]? = some stopNode := by rw [hval]; exact hSN
    exact step_loadInput_next h16 (by rw [hs9pc]; exact placedSlice_fetch hPrePl (k := 9) rfl) hr (by omega)
  have hs10pc : s10.pc = base + 10 := by
    simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
  have hs10data : s10.data = s.data := by
    simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_data]
  have hpre : Steps linked input 10 s s10 :=
    Steps.cons h0 (Steps.cons h1 (Steps.cons h2 (Steps.cons h3 (Steps.cons h4
      (Steps.cons h5 (Steps.cons h6 (Steps.cons h7 (Steps.cons h8 (Steps.cons h9 (Steps.zero s10))))))))))
  obtain ⟨t, hst, htpc, htr0, _, htdata⟩ :=
    lifted_intervalGuard h16 10 11 12 zeroW oneW hz ho hGPl hret input s10 hs10pc
  have hr10 : reg s10 (r16 h16 10) = entryNode := by
    simp [s10, s9, s8, s7, s6, s5, s4, reg_putReg]
  have hr11 : reg s10 (r16 h16 11) = stopNode := by
    simp [s10, reg_putReg]
  have hr12 : reg s10 (r16 h16 12) = entryTgt := by
    simp [s10, s9, s8, s7, s6, reg_putReg]
  rw [hr10, hr11, hr12] at htr0
  rw [hr10, hr12] at hst
  refine ⟨t, 10 + (if entryTgt.val < entryNode.val then 3 else 4), ?_, hpre.append hst, htpc, htr0, htdata.trans hs10data⟩
  split <;> omega

private def childPre (hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW : Word bits) :
    Program L :=
  #[.imm (r16 h16 15) hdrEntryW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 2),
    .loadInput (r16 h16 3) (r16 h16 15),
    .mov (r16 h16 12) (r16 h16 3),
    .imm (r16 h16 15) hdrChildStartW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 1),
    .loadInput (r16 h16 8) (r16 h16 15),
    .imm (r16 h16 6) oneW,
    .add (r16 h16 15) (r16 h16 15) (r16 h16 6),
    .loadInput (r16 h16 9) (r16 h16 15),
    .sub (r16 h16 1) (r16 h16 9) (r16 h16 8),
    .imm (r16 h16 0) zeroW,
    .imm (r16 h16 15) hdrChildEntriesW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 2) (r16 h16 14) (r16 h16 8),
    .imm (r16 h16 4) zeroW,
    .imm (r16 h16 5) zeroW]

private theorem childPre_size (hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW : Word bits) :
    (childPre (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW).size = 19 := rfl

private def childMid (hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW : Word bits)
    (base retPC : Nat) : Program L :=
  #[.imm (r16 h16 6) oneW,
    .branchLt (r16 h16 0) (r16 h16 6) (base + 46) (base + 33),
    .mov (r16 h16 9) (r16 h16 0),
    .sub (r16 h16 7) (r16 h16 0) (r16 h16 6),
    .add (r16 h16 8) (r16 h16 8) (r16 h16 7),
    .imm (r16 h16 15) hdrChildEntriesW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 8),
    .loadInput (r16 h16 10) (r16 h16 15),
    .imm (r16 h16 15) hdrChildStopsW,
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 8),
    .loadInput (r16 h16 11) (r16 h16 15),
    .imm (r16 h16 15) hdrChildIdsW,
    .goto (base + 48),
    .imm (r16 h16 0) zeroW,
    .goto retPC]

private theorem childMid_size (hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW : Word bits)
    (base retPC : Nat) :
    (childMid (L := L) h16 hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW base retPC).size = 17 := rfl

private def childPost (base retPC : Nat) : Program L :=
  #[.branchLt (r16 h16 0) (r16 h16 6) retPC (base + 55),
    .loadInput (r16 h16 14) (r16 h16 15),
    .add (r16 h16 15) (r16 h16 14) (r16 h16 8),
    .loadInput (r16 h16 1) (r16 h16 15),
    .mov (r16 h16 2) (r16 h16 9),
    .goto retPC]

private theorem childPost_size (base retPC : Nat) :
    (childPost (L := L) h16 base retPC).size = 6 := rfl

/-- Given `r1 = d`, `r2 = z`, computes `child(d, z)` using `Predecessor.worker` +
`IntervalGuard`. Returns `r0 = 1, r1 = childIds[pos], r2 = count` on hit, or `r0 = 0` on miss. -/
def childSearchBlock
    (hdrEntryW hdrChildStartW hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW : Word bits)
    (base retPC : Nat) : Program L :=
  childPre h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW ++
  liftMap (ρ7 h16) (base + 19) (base + 31) (Predecessor.worker L.inputFits) ++
  childMid h16 hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW base retPC ++
  liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
    (base + 48) (base + 54)
    (IntervalGuard.romFor (L := KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits) rfl 10 11 12 zeroW oneW) ++
  childPost h16 base retPC

@[simp] theorem childSearchBlock_size
    (hdrEntryW hdrChildStartW hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW : Word bits)
    (base retPC : Nat) :
    (childSearchBlock (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW hdrChildStopsW
      hdrChildIdsW zeroW oneW base retPC).size = 60 := by
  have hPw : (Predecessor.worker (bits := bits) L.inputFits).size = 12 := Predecessor.worker_size
  simp [childSearchBlock, childPre, childMid, childPost, hPw, IntervalGuard.romFor]

theorem childSearchBlock_spec
    {linked : Program L} {base retPC : Nat}
    (hdrEntryW hdrChildStartW hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW : Word bits)
    (hz : zeroW.val = 0) (ho : oneW.val = 1)
    (hpl : PlacedSlice (childSearchBlock (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW
      hdrChildStopsW hdrChildIdsW zeroW oneW base retPC) linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    {entryBaseW cStartBaseW cEntBaseW cStopBaseW cIdBaseW : Word bits}
    (hEH : input.words[hdrEntryW.val]? = some entryBaseW)
    (hCSH : input.words[hdrChildStartW.val]? = some cStartBaseW)
    (hCEH : input.words[hdrChildEntriesW.val]? = some cEntBaseW)
    (hCPH : input.words[hdrChildStopsW.val]? = some cStopBaseW)
    (hCIH : input.words[hdrChildIdsW.val]? = some cIdBaseW)
    {entryZ : Word bits}
    (hEZ : input.words[entryBaseW.val + (reg s (r16 h16 2)).val]? = some entryZ)
    {cStart0 cStart1 : Word bits}
    (hCS0 : input.words[cStartBaseW.val + (reg s (r16 h16 1)).val]? = some cStart0)
    (hCS1 : input.words[cStartBaseW.val + (reg s (r16 h16 1)).val + 1]? = some cStart1)
    (hOrder : cStart0.val ≤ cStart1.val)
    (hSliceFit : cStartBaseW.val + (reg s (r16 h16 1)).val + 1 < 2 ^ bits)
    (hEntFit : cEntBaseW.val + cStart0.val + (cStart1.val - cStart0.val) < 2 ^ bits)
    (hEntWithin : cEntBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ L.inputCap)
    (hStopWithin : cStopBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ L.inputCap)
    (hIdWithin : cIdBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ L.inputCap)
    (hSorted : ∀ (i j : Nat) (hi : i < cStart1.val - cStart0.val) (hj : j < cStart1.val - cStart0.val),
      i ≤ j →
      (input.words[cEntBaseW.val + cStart0.val + i]'(by rw [input.size_eq]; omega)).val ≤
      (input.words[cEntBaseW.val + cStart0.val + j]'(by rw [input.size_eq]; omega)).val) :
    let len := cStart1.val - cStart0.val
    ∃ (t : State L) (steps : Nat),
      steps ≤ 11 * (Nat.log2 (len + 1) + 1) + 44 ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      t.data = s.data ∧
      (∀ count : Nat,
        Predecessor.Answer (bits := bits) (cap := L.inputCap) (hcap := L.inputFits)
          (input := ⟨input.words, input.size_eq⟩)
          ⟨add cEntBaseW cStart0, cStart1.val - cStart0.val, by
            have hAdd := add_no_wrap cEntBaseW cStart0 (by omega)
            rw [hAdd]; exact hEntFit, by
            have hAdd := add_no_wrap cEntBaseW cStart0 (by omega)
            rw [hAdd]; exact hEntWithin⟩ entryZ count →
        (count = 0 → (reg t (r16 h16 0)).val = 0) ∧
        (∀ pos : Nat, count = pos + 1 → (hpos : pos < cStart1.val - cStart0.val) →
          let lo := (input.words[cEntBaseW.val + (cStart0.val + pos)]'(by rw [input.size_eq]; omega)).val
          let hi := (input.words[cStopBaseW.val + (cStart0.val + pos)]'(by rw [input.size_eq]; omega)).val
          let cid := input.words[cIdBaseW.val + (cStart0.val + pos)]'(by rw [input.size_eq]; omega)
          if lo ≤ entryZ.val ∧ entryZ.val < hi then
            (reg t (r16 h16 0)).val = 1 ∧ reg t (r16 h16 1) = cid ∧ (reg t (r16 h16 2)).val = count
          else
            (reg t (r16 h16 0)).val = 0)) := by
  intro len
  have hPw : (Predecessor.worker (bits := bits) L.inputFits).size = 12 := Predecessor.worker_size
  have hPrePl : PlacedSlice (childPre h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW (L := L))
      linked base :=
    placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left hpl)))
  have hPredPl : PlacedSlice (liftMap (ρ7 h16) (base + 19) (base + 31) (Predecessor.worker L.inputFits))
      linked (base + 19) := by
    have hR := placedSlice_append_right (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left hpl)))
    rw [childPre_size] at hR
    exact hR
  have hMidPl : PlacedSlice
      (childMid h16 hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW base retPC (L := L))
      linked (base + 31) := by
    have hR := placedSlice_append_right (placedSlice_append_left (placedSlice_append_left hpl))
    have hSz12 : (childPre (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW ++
        liftMap (ρ7 h16) (base + 19) (base + 31) (Predecessor.worker L.inputFits)).size = 31 := by
      simp [childPre_size, hPw]
    rw [hSz12] at hR
    exact hR
  have hGuardPl : PlacedSlice
      (liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
        (base + 48) (base + 54) (IntervalGuard.romFor rfl 10 11 12 zeroW oneW))
      linked (base + 48) := by
    have hR := placedSlice_append_right (placedSlice_append_left hpl)
    have hSz13 : (childPre (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW ++
        liftMap (ρ7 h16) (base + 19) (base + 31) (Predecessor.worker L.inputFits) ++
        childMid h16 hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW base retPC).size = 48 := by
      simp [childPre_size, childMid_size, hPw]
    rw [hSz13] at hR
    exact hR
  have hPostPl : PlacedSlice (childPost (L := L) h16 base retPC) linked (base + 54) := by
    have hR := placedSlice_append_right hpl
    have hSz14 : (childPre (L := L) h16 hdrEntryW hdrChildStartW hdrChildEntriesW zeroW oneW ++
        liftMap (ρ7 h16) (base + 19) (base + 31) (Predecessor.worker L.inputFits) ++
        childMid h16 hdrChildEntriesW hdrChildStopsW hdrChildIdsW zeroW oneW base retPC ++
        liftMap (ρ16 h16 (rfl : (KnownNodeCheck.knownCheckLayout bits L.inputCap L.inputFits).registerCount = 16))
          (base + 48) (base + 54) (IntervalGuard.romFor rfl 10 11 12 zeroW oneW)).size = 54 := by
      simp [childPre_size, childMid_size, hPw, IntervalGuard.romFor]
    rw [hSz14] at hR
    exact hR
  have hSz : base + 60 ≤ linked.size := by
    have := hpl.1; simp only [childSearchBlock_size] at this; exact this
  have hLtEZ : entryBaseW.val + (reg s (r16 h16 2)).val < 2 ^ bits := by
    have hb : entryBaseW.val + (reg s (r16 h16 2)).val < input.words.size := by
      by_cases hlt : entryBaseW.val + (reg s (r16 h16 2)).val < input.words.size
      · exact hlt
      · rw [getElem?_neg input.words _ hlt] at hEZ; cases hEZ
    rw [input.size_eq] at hb; exact Nat.lt_of_lt_of_le hb L.inputFits
  have hAddCE : (add cEntBaseW cStart0).val = cEntBaseW.val + cStart0.val :=
    add_no_wrap cEntBaseW cStart0 (by omega)
  have hSubLen : (sub cStart1 cStart0).val = len := sub_no_wrap cStart1 cStart0 hOrder
  let s1 := putReg h16 s 15 hdrEntryW
  let s2 := putReg h16 s1 14 entryBaseW
  let s3 := putReg h16 s2 15 (add entryBaseW (reg s (r16 h16 2)))
  let s4 := putReg h16 s3 3 entryZ
  let s5 := putReg h16 s4 12 entryZ
  let s6 := putReg h16 s5 15 hdrChildStartW
  let s7 := putReg h16 s6 14 cStartBaseW
  let s8 := putReg h16 s7 15 (add cStartBaseW (reg s (r16 h16 1)))
  let s9 := putReg h16 s8 8 cStart0
  let s10 := putReg h16 s9 6 oneW
  let s11 := putReg h16 s10 15 (add (add cStartBaseW (reg s (r16 h16 1))) oneW)
  let s12 := putReg h16 s11 9 cStart1
  let s13 := putReg h16 s12 1 (sub cStart1 cStart0)
  let s14 := putReg h16 s13 0 zeroW
  let s15 := putReg h16 s14 15 hdrChildEntriesW
  let s16 := putReg h16 s15 14 cEntBaseW
  let s17 := putReg h16 s16 2 (add cEntBaseW cStart0)
  let s18 := putReg h16 s17 4 zeroW
  let s19 := putReg h16 s18 5 zeroW
  have hs0 : step linked input s = some (.next s1) :=
    step_imm_next h16 (by rw [hpc]; exact placedSlice_fetch hPrePl (k := 0) rfl) (by omega)
  have hs1 : step linked input s1 = some (.next s2) := by
    have hp : s1.pc = base + 1 := by simp [s1, putReg_pc, hpc]
    have hr : input.words[(reg s1 (r16 h16 15)).val]? = some entryBaseW := by
      simpa [s1, reg_putReg] using hEH
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 1) rfl) hr (by omega)
  have hs2 : step linked input s2 = some (.next s3) := by
    have hp : s2.pc = base + 2 := by simp [s2, s1, putReg_pc, hpc]
    have h14 : reg s2 (r16 h16 14) = entryBaseW := by simp [s2, reg_putReg]
    have h2 : reg s2 (r16 h16 2) = reg s (r16 h16 2) := by simp [s2, s1, reg_putReg]
    simpa [s3, h14, h2] using step_add_next h16 (input := input) (s := s2) (d := 15) (x := 14) (y := 2)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 2) rfl) (by omega)
  have hs3 : step linked input s3 = some (.next s4) := by
    have hp : s3.pc = base + 3 := by simp [s3, s2, s1, putReg_pc, hpc]
    have hv : (reg s3 (r16 h16 15)).val = entryBaseW.val + (reg s (r16 h16 2)).val := by
      simpa [s3, reg_putReg] using add_no_wrap entryBaseW (reg s (r16 h16 2)) hLtEZ
    have hr : input.words[(reg s3 (r16 h16 15)).val]? = some entryZ := by rw [hv]; exact hEZ
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 3) rfl) hr (by omega)
  have hs4 : step linked input s4 = some (.next s5) := by
    have hp : s4.pc = base + 4 := by simp [s4, s3, s2, s1, putReg_pc, hpc]
    have h3 : reg s4 (r16 h16 3) = entryZ := by simp [s4, reg_putReg]
    simpa [s5, h3] using step_mov_next h16 (input := input) (s := s4) (d := 12) (src := 3)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 4) rfl) (by omega)
  have hs5 : step linked input s5 = some (.next s6) := by
    have hp : s5.pc = base + 5 := by simp [s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 5) rfl) (by omega)
  have hs6 : step linked input s6 = some (.next s7) := by
    have hp : s6.pc = base + 6 := by simp [s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hr : input.words[(reg s6 (r16 h16 15)).val]? = some cStartBaseW := by
      simpa [s6, reg_putReg] using hCSH
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 6) rfl) hr (by omega)
  have hs7 : step linked input s7 = some (.next s8) := by
    have hp : s7.pc = base + 7 := by simp [s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have h14 : reg s7 (r16 h16 14) = cStartBaseW := by simp [s7, reg_putReg]
    have h1 : reg s7 (r16 h16 1) = reg s (r16 h16 1) := by
      simp [s7, s6, s5, s4, s3, s2, s1, reg_putReg]
    simpa [s8, h14, h1] using step_add_next h16 (input := input) (s := s7) (d := 15) (x := 14) (y := 1)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 7) rfl) (by omega)
  have hs8 : step linked input s8 = some (.next s9) := by
    have hp : s8.pc = base + 8 := by simp [s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hv : (reg s8 (r16 h16 15)).val = cStartBaseW.val + (reg s (r16 h16 1)).val := by
      simpa [s8, reg_putReg] using add_no_wrap cStartBaseW (reg s (r16 h16 1)) (by omega)
    have hr : input.words[(reg s8 (r16 h16 15)).val]? = some cStart0 := by rw [hv]; exact hCS0
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 8) rfl) hr (by omega)
  have hs9 : step linked input s9 = some (.next s10) := by
    have hp : s9.pc = base + 9 := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 9) rfl) (by omega)
  have hs10 : step linked input s10 = some (.next s11) := by
    have hp : s10.pc = base + 10 := by
      simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have h15 : reg s10 (r16 h16 15) = add cStartBaseW (reg s (r16 h16 1)) := by
      simp [s10, s9, s8, reg_putReg]
    have h6 : reg s10 (r16 h16 6) = oneW := by simp [s10, reg_putReg]
    simpa [s11, h15, h6] using step_add_next h16 (input := input) (s := s10) (d := 15) (x := 15) (y := 6)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 10) rfl) (by omega)
  have hs11 : step linked input s11 = some (.next s12) := by
    have hp : s11.pc = base + 11 := by
      simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hv : (reg s11 (r16 h16 15)).val = cStartBaseW.val + (reg s (r16 h16 1)).val + 1 := by
      have hA : (add cStartBaseW (reg s (r16 h16 1))).val = cStartBaseW.val + (reg s (r16 h16 1)).val :=
        add_no_wrap cStartBaseW (reg s (r16 h16 1)) (by omega)
      have hB : (add (add cStartBaseW (reg s (r16 h16 1))) oneW).val =
          (add cStartBaseW (reg s (r16 h16 1))).val + oneW.val :=
        add_no_wrap _ oneW (by rw [hA, ho]; exact hSliceFit)
      simpa [s11, reg_putReg, hA, ho] using hB
    have hr : input.words[(reg s11 (r16 h16 15)).val]? = some cStart1 := by rw [hv]; exact hCS1
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 11) rfl) hr (by omega)
  have hs12 : step linked input s12 = some (.next s13) := by
    have hp : s12.pc = base + 12 := by
      simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have h9 : reg s12 (r16 h16 9) = cStart1 := by simp [s12, reg_putReg]
    have h8 : reg s12 (r16 h16 8) = cStart0 := by simp [s12, s11, s10, s9, reg_putReg]
    simpa [s13, h9, h8] using step_sub_next h16 (input := input) (s := s12) (d := 1) (x := 9) (y := 8)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 12) rfl) (by omega)
  have hs13 : step linked input s13 = some (.next s14) := by
    have hp : s13.pc = base + 13 := by
      simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 13) rfl) (by omega)
  have hs14 : step linked input s14 = some (.next s15) := by
    have hp : s14.pc = base + 14 := by
      simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 14) rfl) (by omega)
  have hs15 : step linked input s15 = some (.next s16) := by
    have hp : s15.pc = base + 15 := by
      simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have hr : input.words[(reg s15 (r16 h16 15)).val]? = some cEntBaseW := by
      simpa [s15, reg_putReg] using hCEH
    exact step_loadInput_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 15) rfl) hr (by omega)
  have hs16 : step linked input s16 = some (.next s17) := by
    have hp : s16.pc = base + 16 := by
      simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    have h14 : reg s16 (r16 h16 14) = cEntBaseW := by simp [s16, reg_putReg]
    have h8 : reg s16 (r16 h16 8) = cStart0 := by
      simp [s16, s15, s14, s13, s12, s11, s10, s9, reg_putReg]
    simpa [s17, h14, h8] using step_add_next h16 (input := input) (s := s16) (d := 2) (x := 14) (y := 8)
      (by rw [hp]; exact placedSlice_fetch hPrePl (k := 16) rfl) (by omega)
  have hs17 : step linked input s17 = some (.next s18) := by
    have hp : s17.pc = base + 17 := by
      simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 17) rfl) (by omega)
  have hs18 : step linked input s18 = some (.next s19) := by
    have hp : s18.pc = base + 18 := by
      simp [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
    exact step_imm_next h16 (by rw [hp]; exact placedSlice_fetch hPrePl (k := 18) rfl) (by omega)
  have hs19pc : s19.pc = base + 19 := by
    simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_pc, hpc]
  have hs19data : s19.data = s.data := by
    simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, putReg_data]
  have hPreSteps : Steps linked input 19 s s19 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
      (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
      (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.zero s19)))))))))))))))))))
  let iPred : Input (Predecessor.layout bits L.inputCap L.inputFits) := ⟨input.words, input.size_eq⟩
  let pSlice : Predecessor.Slice (bits := bits) (cap := L.inputCap) (hcap := L.inputFits) iPred :=
    { base := add cEntBaseW cStart0
      len := len
      fits := by rw [hAddCE]; exact hEntFit
      within := by rw [hAddCE]; exact hEntWithin }
  have hpSorted : pSlice.Sorted := by
    intro i j hi hj hij
    have hi' : i < cStart1.val - cStart0.val := hi
    have hj' : j < cStart1.val - cStart0.val := hj
    have he := hSorted i j hi' hj' hij
    have hIdxL : pSlice.base.val + i = cEntBaseW.val + cStart0.val + i := by
      change (add cEntBaseW cStart0).val + i = _
      rw [hAddCE]
    have hIdxR : pSlice.base.val + j = cEntBaseW.val + cStart0.val + j := by
      change (add cEntBaseW cStart0).val + j = _
      rw [hAddCE]
    have hGet : ∀ a b (ha : a < iPred.words.size) (hb : b < input.words.size),
        a = b → (iPred.words[a]'ha).val = (input.words[b]'hb).val := by
      intro a b ha hb e; subst e; rfl
    have hL : (pSlice.get i hi).val = (input.words[cEntBaseW.val + cStart0.val + i]'(by rw [input.size_eq]; omega)).val :=
      hGet _ _ _ _ hIdxL
    have hR : (pSlice.get j hj).val = (input.words[cEntBaseW.val + cStart0.val + j]'(by rw [input.size_eq]; omega)).val :=
      hGet _ _ _ _ hIdxR
    rw [hL, hR]; exact he
  have hPredReg : ∀ r : Fin 7, reg s19 (ρ7 h16 r) = reg (Predecessor.init pSlice entryZ) r := by
    intro r
    have h1 : reg s19 (r16 h16 1) = sub cStart1 cStart0 := by
      simp [s19, s18, s17, s16, s15, s14, s13, reg_putReg]
    have h2 : reg s19 (r16 h16 2) = add cEntBaseW cStart0 := by
      simp [s19, s18, s17, reg_putReg]
    have h3 : reg s19 (r16 h16 3) = entryZ := by
      simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, reg_putReg]
    have h6 : reg s19 (r16 h16 6) = oneW := by
      simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, reg_putReg]
    match r with
    | ⟨0, _⟩ =>
      apply Fin.ext
      have h0 : reg s19 (r16 h16 0) = zeroW := by
        simp [s19, s18, s17, s16, s15, s14, reg_putReg]
      change (reg s19 (r16 h16 0)).val = (reg (Predecessor.init pSlice entryZ) ⟨0, by omega⟩).val
      rw [h0, hz]; rfl
    | ⟨1, _⟩ =>
      apply Fin.ext
      change (reg s19 (r16 h16 1)).val = (reg (Predecessor.init pSlice entryZ) ⟨1, by omega⟩).val
      rw [h1, hSubLen]; rfl
    | ⟨2, _⟩ => exact h2
    | ⟨3, _⟩ => exact h3
    | ⟨4, _⟩ =>
      apply Fin.ext
      have h4 : reg s19 (r16 h16 4) = zeroW := by simp [s19, s18, reg_putReg]
      change (reg s19 (r16 h16 4)).val = (reg (Predecessor.init pSlice entryZ) ⟨4, by omega⟩).val
      rw [h4, hz]; rfl
    | ⟨5, _⟩ =>
      apply Fin.ext
      have h5 : reg s19 (r16 h16 5) = zeroW := by simp [s19, reg_putReg]
      change (reg s19 (r16 h16 5)).val = (reg (Predecessor.init pSlice entryZ) ⟨5, by omega⟩).val
      rw [h5, hz]; rfl
    | ⟨6, hr6⟩ =>
      apply Fin.ext
      have hb := pSlice.fits
      have h1lt : 1 < 2 ^ bits := by omega
      change (reg s19 (r16 h16 6)).val =
        (if h : 1 < 2 ^ bits then (⟨1, h⟩ : Word bits) else ⟨0, Nat.two_pow_pos bits⟩).val
      rw [h6, ho, dite_eq_left h1lt]
    | ⟨k + 7, hr⟩ => omega
  obtain ⟨u, kPred, hkPred, hPredSteps, hupc, hAns, huPreserve, hudata⟩ :=
    lifted_predWorker h16 hPredPl (by omega) input s19 hs19pc pSlice entryZ hpSorted hPredReg
  change kPred ≤ 11 * (Nat.log2 (len + 1) + 1) at hkPred
  have hu8 : reg u (r16 h16 8) = cStart0 := by
    rw [huPreserve 8 (by decide)]
    simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, reg_putReg]
  have hu12 : reg u (r16 h16 12) = entryZ := by
    rw [huPreserve 12 (by decide)]
    simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, reg_putReg]
  let u1 := putReg h16 u 6 oneW
  have hmid0 : step linked input u = some (.next u1) :=
    step_imm_next h16 (by rw [hupc]; exact placedSlice_fetch hMidPl (k := 0) rfl) (by rw [hupc]; omega)
  have hu1pc : u1.pc = base + 32 := by simp only [u1, putReg_pc, hupc]
  by_cases hZeroCnt : (reg u (r16 h16 0)).val = 0
  · have hlt06 : (reg u1 (r16 h16 0)).val < (reg u1 (r16 h16 6)).val := by
      have h0 : reg u1 (r16 h16 0) = reg u (r16 h16 0) := by simp [u1, reg_putReg]
      have h6 : reg u1 (r16 h16 6) = oneW := by simp [u1, reg_putReg]
      rw [h0, h6, hZeroCnt, ho]; omega
    let u2 : State L := { u1 with pc := base + 46 }
    have hmid1 : step linked input u1 = some (.next u2) := by
      have hbr := step_branchLt_next h16 (code := linked) (input := input) (s := u1) (x := 0) (y := 6)
        (yesPC := base + 46) (noPC := base + 33)
        (by rw [hu1pc]; exact placedSlice_fetch hMidPl (k := 1) rfl) (by rw [ite_eq_left hlt06]; omega)
      simpa only [u2, ite_eq_left hlt06] using hbr
    let u3 := putReg h16 u2 0 zeroW
    have hmid15 : step linked input u2 = some (.next u3) :=
      step_imm_next h16 (by simp [u2]; exact placedSlice_fetch hMidPl (k := 15) rfl) (by change base + 46 + 1 < _; omega)
    let tFin : State L := { u3 with pc := retPC }
    have hmid16 : step linked input u3 = some (.next tFin) :=
      step_goto_at (by simp [u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 16) rfl) hret
    have hTail : Steps linked input 4 u tFin :=
      Steps.cons hmid0 (Steps.cons hmid1 (Steps.cons hmid15 (Steps.cons hmid16 (Steps.zero tFin))))
    refine ⟨tFin, 19 + kPred + 4, by omega, hPreSteps.append (hPredSteps.append hTail), rfl, ?_, ?_⟩
    · simp [tFin, u3, u2, u1, putReg_data, hudata, hs19data]
    · intro count hOther
      have hEqCnt : count = 0 := (Predecessor.Answer.unique hOther hAns).trans hZeroCnt
      refine ⟨fun _ => ?_, fun pos hPos _ => by omega⟩
      have hr0 : reg tFin (r16 h16 0) = zeroW := by
        simp only [tFin, u3, reg_withPC, reg_putReg]; rfl
      rw [hr0, hz]
  · have hPosCnt : 1 ≤ (reg u (r16 h16 0)).val := by omega
    have hCountLe : (reg u (r16 h16 0)).val ≤ len := hAns.1
    let pos0 := (reg u (r16 h16 0)).val - 1
    have hPosLt : pos0 < len := by omega
    have hSubCnt : (sub (reg u (r16 h16 0)) oneW).val = pos0 := by
      rw [sub_no_wrap _ _ (by rw [ho]; exact hPosCnt), ho]
    have hAddPos : (add cStart0 (sub (reg u (r16 h16 0)) oneW)).val = cStart0.val + pos0 := by
      have hFit : cStart0.val + pos0 < 2 ^ bits := by omega
      simpa only [hSubCnt] using add_no_wrap cStart0 (sub (reg u (r16 h16 0)) oneW) (by rw [hSubCnt]; exact hFit)
    have hge06 : ¬ (reg u1 (r16 h16 0)).val < (reg u1 (r16 h16 6)).val := by
      have h0 : reg u1 (r16 h16 0) = reg u (r16 h16 0) := by simp [u1, reg_putReg]
      have h6 : reg u1 (r16 h16 6) = oneW := by simp [u1, reg_putReg]
      rw [h0, h6, ho]; omega
    let loW := input.words[cEntBaseW.val + (cStart0.val + pos0)]'(by rw [input.size_eq]; omega)
    let hiW := input.words[cStopBaseW.val + (cStart0.val + pos0)]'(by rw [input.size_eq]; omega)
    let cidW := input.words[cIdBaseW.val + (cStart0.val + pos0)]'(by rw [input.size_eq]; omega)
    let u2 : State L := { u1 with pc := base + 33 }
    let u3 := putReg h16 u2 9 (reg u (r16 h16 0))
    let u4 := putReg h16 u3 7 (sub (reg u (r16 h16 0)) oneW)
    let u5 := putReg h16 u4 8 (add cStart0 (sub (reg u (r16 h16 0)) oneW))
    let u6 := putReg h16 u5 15 hdrChildEntriesW
    let u7 := putReg h16 u6 14 cEntBaseW
    let u8 := putReg h16 u7 15 (add cEntBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)))
    let u9 := putReg h16 u8 10 loW
    let u10 := putReg h16 u9 15 hdrChildStopsW
    let u11 := putReg h16 u10 14 cStopBaseW
    let u12 := putReg h16 u11 15 (add cStopBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)))
    let u13 := putReg h16 u12 11 hiW
    let u14 := putReg h16 u13 15 hdrChildIdsW
    let u15 : State L := { u14 with pc := base + 48 }
    have hmid1 : step linked input u1 = some (.next u2) := by
      have hbr := step_branchLt_next h16 (code := linked) (input := input) (s := u1) (x := 0) (y := 6)
        (yesPC := base + 46) (noPC := base + 33)
        (by rw [hu1pc]; exact placedSlice_fetch hMidPl (k := 1) rfl) (by rw [ite_eq_right hge06]; omega)
      simpa only [u2, ite_eq_right hge06] using hbr
    have hmid2 : step linked input u2 = some (.next u3) := by
      have h0 : reg u2 (r16 h16 0) = reg u (r16 h16 0) := by simp only [u2, u1, reg_withPC, reg_putReg]; exact ite_eq_right (by decide)
      simpa [u3, h0] using step_mov_next h16 (input := input) (s := u2) (d := 9) (src := 0)
        (by change linked[base + 33]? = _; exact placedSlice_fetch hMidPl (k := 2) rfl)
        (by change base + 33 + 1 < _; omega)
    have hmid3 : step linked input u3 = some (.next u4) := by
      have h0 : reg u3 (r16 h16 0) = reg u (r16 h16 0) := by simp only [u3, u2, u1, reg_putReg, reg_withPC]; exact ite_eq_right (by decide)
      have h6 : reg u3 (r16 h16 6) = oneW := by simp only [u3, u2, u1, reg_putReg, reg_withPC]; rfl
      simpa [u4, h0, h6] using step_sub_next h16 (input := input) (s := u3) (d := 7) (x := 0) (y := 6)
        (by simp [u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 3) rfl)
        (by simp only [u3, u2, putReg_pc]; omega)
    have hmid4 : step linked input u4 = some (.next u5) := by
      have h8 : reg u4 (r16 h16 8) = cStart0 := by simp only [u4, u3, u2, u1, reg_putReg, reg_withPC]; exact hu8
      have h7 : reg u4 (r16 h16 7) = sub (reg u (r16 h16 0)) oneW := by simp [u4, reg_putReg]
      simpa [u5, h8, h7] using step_add_next h16 (input := input) (s := u4) (d := 8) (x := 8) (y := 7)
        (by simp [u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 4) rfl)
        (by simp only [u4, u3, u2, putReg_pc]; omega)
    have hmid5 : step linked input u5 = some (.next u6) :=
      step_imm_next h16 (by simp [u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 5) rfl)
        (by simp only [u5, u4, u3, u2, putReg_pc]; omega)
    have hmid6 : step linked input u6 = some (.next u7) := by
      have hr : input.words[(reg u6 (r16 h16 15)).val]? = some cEntBaseW := by
        simpa [u6, reg_putReg] using hCEH
      exact step_loadInput_next h16 (by simp [u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 6) rfl)
        hr (by simp only [u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid7 : step linked input u7 = some (.next u8) := by
      have h14 : reg u7 (r16 h16 14) = cEntBaseW := by simp [u7, reg_putReg]
      have h8 : reg u7 (r16 h16 8) = add cStart0 (sub (reg u (r16 h16 0)) oneW) := by
        simp [u7, u6, u5, reg_putReg]
      simpa [u8, h14, h8] using step_add_next h16 (input := input) (s := u7) (d := 15) (x := 14) (y := 8)
        (by simp [u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 7) rfl)
        (by simp only [u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid8 : step linked input u8 = some (.next u9) := by
      have hv : (reg u8 (r16 h16 15)).val = cEntBaseW.val + (cStart0.val + pos0) := by
        have hFit : cEntBaseW.val + (cStart0.val + pos0) < 2 ^ bits := by omega
        have hA := add_no_wrap cEntBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) (by rw [hAddPos]; exact hFit)
        have hR : reg u8 (r16 h16 15) = add cEntBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) := by
          simp only [u8, reg_putReg]; rfl
        rw [hR, hA, hAddPos]
      have hr : input.words[(reg u8 (r16 h16 15)).val]? = some loW := by
        rw [hv]; exact getElem?_pos input.words _ (by rw [input.size_eq]; omega)
      exact step_loadInput_next h16
        (by simp [u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 8) rfl)
        hr (by simp only [u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid9 : step linked input u9 = some (.next u10) :=
      step_imm_next h16 (by simp [u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 9) rfl)
        (by simp only [u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid10 : step linked input u10 = some (.next u11) := by
      have hr : input.words[(reg u10 (r16 h16 15)).val]? = some cStopBaseW := by
        simpa [u10, reg_putReg] using hCPH
      exact step_loadInput_next h16
        (by simp [u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 10) rfl)
        hr (by simp only [u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid11 : step linked input u11 = some (.next u12) := by
      have h14 : reg u11 (r16 h16 14) = cStopBaseW := by simp [u11, reg_putReg]
      have h8 : reg u11 (r16 h16 8) = add cStart0 (sub (reg u (r16 h16 0)) oneW) := by
        simp [u11, u10, u9, u8, u7, u6, u5, reg_putReg]
      simpa [u12, h14, h8] using step_add_next h16 (input := input) (s := u11) (d := 15) (x := 14) (y := 8)
        (by simp [u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 11) rfl)
        (by simp only [u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid12 : step linked input u12 = some (.next u13) := by
      have hv : (reg u12 (r16 h16 15)).val = cStopBaseW.val + (cStart0.val + pos0) := by
        have hFit : cStopBaseW.val + (cStart0.val + pos0) < 2 ^ bits :=
          Nat.lt_of_lt_of_le (by omega) L.inputFits
        have hA := add_no_wrap cStopBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) (by rw [hAddPos]; exact hFit)
        have hR : reg u12 (r16 h16 15) = add cStopBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) := by
          simp only [u12, reg_putReg]; rfl
        rw [hR, hA, hAddPos]
      have hr : input.words[(reg u12 (r16 h16 15)).val]? = some hiW := by
        rw [hv]; exact getElem?_pos input.words _ (by rw [input.size_eq]; omega)
      exact step_loadInput_next h16
        (by simp [u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 12) rfl)
        hr (by simp only [u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid13 : step linked input u13 = some (.next u14) :=
      step_imm_next h16
        (by simp [u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; exact placedSlice_fetch hMidPl (k := 13) rfl)
        (by simp only [u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]; omega)
    have hmid14 : step linked input u14 = some (.next u15) :=
      step_goto_at
        (by simp [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, putReg_pc]
            exact placedSlice_fetch hMidPl (k := 14) rfl)
        (by omega)
    have hMidSteps : Steps linked input 15 u u15 :=
      Steps.cons hmid0 (Steps.cons hmid1 (Steps.cons hmid2 (Steps.cons hmid3 (Steps.cons hmid4
        (Steps.cons hmid5 (Steps.cons hmid6 (Steps.cons hmid7 (Steps.cons hmid8 (Steps.cons hmid9
        (Steps.cons hmid10 (Steps.cons hmid11 (Steps.cons hmid12 (Steps.cons hmid13 (Steps.cons hmid14
          (Steps.zero u15)))))))))))))))
    have hu15pc : u15.pc = base + 48 := rfl
    let kG : Nat := if entryZ.val < loW.val then 3 else 4
    obtain ⟨v, hGSteps, hvpc, hvr0, hvFrame, hvdata⟩ :=
      lifted_intervalGuard h16 10 11 12 zeroW oneW hz ho hGuardPl (by omega) input u15 hu15pc
    have hkGle : kG ≤ 4 := by dsimp only [kG]; split <;> omega
    have hr10 : reg u15 (r16 h16 10) = loW := by
      simp only [u15, u14, u13, u12, u11, u10, u9, reg_withPC, reg_putReg]; rfl
    have hr11 : reg u15 (r16 h16 11) = hiW := by
      simp only [u15, u14, u13, reg_withPC, reg_putReg]; rfl
    have hr12 : reg u15 (r16 h16 12) = entryZ := by
      simp only [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, reg_withPC, reg_putReg]
      exact hu12
    rw [hr10, hr11, hr12] at hvr0
    rw [hr10, hr12] at hGSteps
    have hv6 : reg v (r16 h16 6) = oneW := by
      rw [hvFrame 6 (by decide)]
      simp only [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, reg_withPC, reg_putReg]
      rfl
    have hv8 : reg v (r16 h16 8) = add cStart0 (sub (reg u (r16 h16 0)) oneW) := by
      rw [hvFrame 8 (by decide)]
      simp only [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, reg_withPC, reg_putReg]
      rfl
    have hv9 : reg v (r16 h16 9) = reg u (r16 h16 0) := by
      rw [hvFrame 9 (by decide)]
      simp only [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, reg_withPC, reg_putReg]
      rfl
    have hv15 : reg v (r16 h16 15) = hdrChildIdsW := by
      rw [hvFrame 15 (by decide)]
      simp only [u15, u14, reg_withPC, reg_putReg]; rfl
    have hu15data : u15.data = s.data := by
      simp [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, putReg_data, hudata, hs19data]
    by_cases hOk : loW.val ≤ entryZ.val ∧ entryZ.val < hiW.val
    · have hvr0_1 : (reg v (r16 h16 0)).val = 1 := by simpa only [ite_eq_left hOk] using hvr0
      have hgeV : ¬ (reg v (r16 h16 0)).val < (reg v (r16 h16 6)).val := by rw [hvr0_1, hv6, ho]; omega
      let w1 : State L := { v with pc := base + 55 }
      let w2 := putReg h16 w1 14 cIdBaseW
      let w3 := putReg h16 w2 15 (add cIdBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)))
      let w4 := putReg h16 w3 1 cidW
      let w5 := putReg h16 w4 2 (reg u (r16 h16 0))
      let tFin : State L := { w5 with pc := retPC }
      have hp0 : step linked input v = some (.next w1) := by
        have hbr := step_branchLt_next h16 (code := linked) (input := input) (s := v) (x := 0) (y := 6)
          (yesPC := retPC) (noPC := base + 55)
          (by rw [hvpc]; exact placedSlice_fetch hPostPl (k := 0) rfl) (by rw [ite_eq_right hgeV]; omega)
        simpa only [w1, ite_eq_right hgeV] using hbr
      have hp1 : step linked input w1 = some (.next w2) := by
        have hr : input.words[(reg w1 (r16 h16 15)).val]? = some cIdBaseW := by
          simpa only [w1, reg_withPC, hv15] using hCIH
        exact step_loadInput_next h16 (by simp [w1]; exact placedSlice_fetch hPostPl (k := 1) rfl) hr
          (by change base + 55 + 1 < _; omega)
      have hp2 : step linked input w2 = some (.next w3) := by
        have h14 : reg w2 (r16 h16 14) = cIdBaseW := by simp [w2, reg_putReg]
        have h8 : reg w2 (r16 h16 8) = add cStart0 (sub (reg u (r16 h16 0)) oneW) := by
          simp only [w2, w1, reg_putReg]; exact hv8
        simpa [w3, h14, h8] using step_add_next h16 (input := input) (s := w2) (d := 15) (x := 14) (y := 8)
          (by simp [w2, w1, putReg_pc]; exact placedSlice_fetch hPostPl (k := 2) rfl)
          (by simp only [w2, w1, putReg_pc]; omega)
      have hp3 : step linked input w3 = some (.next w4) := by
        have hv : (reg w3 (r16 h16 15)).val = cIdBaseW.val + (cStart0.val + pos0) := by
          have hFit : cIdBaseW.val + (cStart0.val + pos0) < 2 ^ bits :=
            Nat.lt_of_lt_of_le (by omega) L.inputFits
          have hA := add_no_wrap cIdBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) (by rw [hAddPos]; exact hFit)
          have hR : reg w3 (r16 h16 15) = add cIdBaseW (add cStart0 (sub (reg u (r16 h16 0)) oneW)) := by
            simp only [w3, reg_putReg]; rfl
          rw [hR, hA, hAddPos]
        have hr : input.words[(reg w3 (r16 h16 15)).val]? = some cidW := by
          rw [hv]; exact getElem?_pos input.words _ (by rw [input.size_eq]; omega)
        exact step_loadInput_next h16
          (by simp [w3, w2, w1, putReg_pc]; exact placedSlice_fetch hPostPl (k := 3) rfl) hr
          (by simp only [w3, w2, w1, putReg_pc]; omega)
      have hp4 : step linked input w4 = some (.next w5) := by
        have h9 : reg w4 (r16 h16 9) = reg u (r16 h16 0) := by
          simp only [w4, w3, w2, w1, reg_putReg]; exact hv9
        simpa [w5, h9] using step_mov_next h16 (input := input) (s := w4) (d := 2) (src := 9)
          (by simp [w4, w3, w2, w1, putReg_pc]; exact placedSlice_fetch hPostPl (k := 4) rfl)
          (by simp only [w4, w3, w2, w1, putReg_pc]; omega)
      have hp5 : step linked input w5 = some (.next tFin) :=
        step_goto_at
          (by simp [w5, w4, w3, w2, w1, putReg_pc]; exact placedSlice_fetch hPostPl (k := 5) rfl) hret
      have hPostSteps : Steps linked input 6 v tFin :=
        Steps.cons hp0 (Steps.cons hp1 (Steps.cons hp2 (Steps.cons hp3 (Steps.cons hp4 (Steps.cons hp5 (Steps.zero tFin))))))
      refine ⟨tFin, 19 + (kPred + (15 + (kG + 6))), by omega,
        hPreSteps.append (hPredSteps.append (hMidSteps.append (hGSteps.append hPostSteps))), rfl, ?_, ?_⟩
      · simp [tFin, w5, w4, w3, w2, w1, putReg_data, hvdata, hu15data]
      · intro count hOther
        have hEqCnt : count = pos0 + 1 := by
          have := Predecessor.Answer.unique hOther hAns; omega
        refine ⟨fun h0 => by omega, fun pos hPos _ => ?_⟩
        have hPosEq : pos = pos0 := by omega
        subst hPosEq
        rw [ite_eq_left hOk]
        refine ⟨?_, ?_, ?_⟩
        · have hr0 : reg tFin (r16 h16 0) = reg v (r16 h16 0) := by
            simp only [tFin, w5, w4, w3, w2, w1, reg_withPC, reg_putReg]; rfl
          rw [hr0]; exact hvr0_1
        · simp only [tFin, w5, w4, reg_withPC, reg_putReg]; rfl
        · have hr2 : (reg tFin (r16 h16 2)).val = (reg u (r16 h16 0)).val := by
            simp only [tFin, w5, reg_withPC, reg_putReg]; rfl
          rw [hr2]; omega
    · have hvr0_0 : (reg v (r16 h16 0)).val = 0 := by simpa only [ite_eq_right hOk] using hvr0
      have hltV : (reg v (r16 h16 0)).val < (reg v (r16 h16 6)).val := by rw [hvr0_0, hv6, ho]; omega
      let tFin : State L := { v with pc := retPC }
      have hp0 : step linked input v = some (.next tFin) := by
        have hbr := step_branchLt_next h16 (code := linked) (input := input) (s := v) (x := 0) (y := 6)
          (yesPC := retPC) (noPC := base + 55)
          (by rw [hvpc]; exact placedSlice_fetch hPostPl (k := 0) rfl) (by rw [ite_eq_left hltV]; exact hret)
        simpa only [tFin, ite_eq_left hltV] using hbr
      refine ⟨tFin, 19 + (kPred + (15 + (kG + 1))), by omega,
        hPreSteps.append (hPredSteps.append (hMidSteps.append (hGSteps.append (Steps.cons hp0 (Steps.zero tFin))))),
        rfl, ?_, ?_⟩
      · exact hvdata.trans hu15data
      · intro count hOther
        have hEqCnt : count = pos0 + 1 := by
          have := Predecessor.Answer.unique hOther hAns; omega
        refine ⟨fun h0 => by omega, fun pos hPos _ => ?_⟩
        have hPosEq : pos = pos0 := by omega
        subst hPosEq
        rw [ite_eq_right hOk]
        have hr0 : reg tFin (r16 h16 0) = reg v (r16 h16 0) := rfl
        rw [hr0]; exact hvr0_0

end ReusableBlocks

end PaperB.RamOracleQueryParts
