module

public import PaperB.RamProgram
public import PaperB.RamForestProgram
public import PaperB.RamForestRawBuild
public import PaperB.WordOps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamDataSliceAdapter

open PaperB.Machine (Word)
open PaperB.WordOps (add band ltb)
open PaperB.RamProgram
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.RawBuild
open PaperB.LabelledQuotient
open PaperB.RetainedProperLoss

section LifterDefs

/-- Scratch register index `15` in the 16-register outer machine. -/
def scratchReg : Fin 16 := ⟨15, by decide⟩

/-- Embed a 15-register index into `Fin 16`. -/
def liftReg (r : Fin 15) : Fin 16 := ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩

theorem liftReg_ne_scratch (r : Fin 15) : liftReg r ≠ scratchReg := by
  intro h
  have hv := congrArg (fun x : Fin 16 => x.val) h
  change r.val = 15 at hv
  have hr := r.isLt
  omega

theorem liftReg_inj {a b : Fin 15} (h : liftReg a = liftReg b) : a = b :=
  Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

private def castProg {bits r₁ r₂ : Nat} (h : r₁ = r₂)
    (p : Array (Instr bits r₁)) : Array (Instr bits r₂) :=
  h ▸ p

/-- Single instruction within the stride-4 block (`off ∈ {0, 1, 2, 3}`) for
sub-instruction `op` at sub-PC `k`, given pointer slots `inPtrAddr`, `dataPtrAddr`,
and unique exit PC `exitPC`. -/
def liftInstrAt {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (exitPC k : Nat) (op : Instr bits 15) (off : Nat) : Instr bits 16 :=
  match op, off with
  | .imm d v, 0 => .imm (liftReg d) v
  | .imm _ _, 1 => .goto (4 * (k + 1))
  | .mov d s, 0 => .mov (liftReg d) (liftReg s)
  | .mov _ _, 1 => .goto (4 * (k + 1))
  | .add d x y, 0 => .add (liftReg d) (liftReg x) (liftReg y)
  | .add _ _ _, 1 => .goto (4 * (k + 1))
  | .sub d x y, 0 => .sub (liftReg d) (liftReg x) (liftReg y)
  | .sub _ _ _, 1 => .goto (4 * (k + 1))
  | .band d x y, 0 => .band (liftReg d) (liftReg x) (liftReg y)
  | .band _ _ _, 1 => .goto (4 * (k + 1))
  | .shr1 d s, 0 => .shr1 (liftReg d) (liftReg s)
  | .shr1 _ _, 1 => .goto (4 * (k + 1))
  | .loadInput _ _, 0 => .imm scratchReg inPtrAddr
  | .loadInput _ _, 1 => .loadData scratchReg scratchReg
  | .loadInput _ a, 2 => .add scratchReg scratchReg (liftReg a)
  | .loadInput d _, 3 => .loadData (liftReg d) scratchReg
  | .loadData _ _, 0 => .imm scratchReg dataPtrAddr
  | .loadData _ _, 1 => .loadData scratchReg scratchReg
  | .loadData _ a, 2 => .add scratchReg scratchReg (liftReg a)
  | .loadData d _, 3 => .loadData (liftReg d) scratchReg
  | .storeData _ _, 0 => .imm scratchReg dataPtrAddr
  | .storeData _ _, 1 => .loadData scratchReg scratchReg
  | .storeData a _, 2 => .add scratchReg scratchReg (liftReg a)
  | .storeData _ src, 3 => .storeData scratchReg (liftReg src)
  | .branchLt x y ltPC gePC, 0 => .branchLt (liftReg x) (liftReg y) (4 * ltPC) (4 * gePC)
  | .goto target, 0 => .goto (4 * target)
  | .halt, 0 => .goto exitPC
  | _, _ => .halt

/-- Lift one 15-register instruction into its 4-instruction stride-4 block. -/
def liftInstr {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (exitPC k : Nat) (op : Instr bits 15) : List (Instr bits 16) :=
  [ liftInstrAt inPtrAddr dataPtrAddr exitPC k op 0,
    liftInstrAt inPtrAddr dataPtrAddr exitPC k op 1,
    liftInstrAt inPtrAddr dataPtrAddr exitPC k op 2,
    liftInstrAt inPtrAddr dataPtrAddr exitPC k op 3 ]

/-- Lift a 15-register code array into a 16-register code array of size
`4 * subCode.size + 1`, with a unique exit `.halt` at `4 * subCode.size`. -/
def liftCode {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (subCode : Array (Instr bits 15)) : Array (Instr bits 16) :=
  Array.ofFn fun idx : Fin (4 * subCode.size + 1) =>
    if h : idx.val < 4 * subCode.size then
      let k := idx.val / 4
      let off := idx.val % 4
      have hk : k < subCode.size := by omega
      liftInstrAt inPtrAddr dataPtrAddr (4 * subCode.size) k (subCode[k]'hk) off
    else
      .halt

theorem liftCode_size {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (subCode : Array (Instr bits 15)) :
    (liftCode inPtrAddr dataPtrAddr subCode).size = 4 * subCode.size + 1 := by
  simp [liftCode]

theorem liftCode_at {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (subCode : Array (Instr bits 15)) {k off : Nat} (hk : k < subCode.size) (hoff : off < 4) :
    (liftCode inPtrAddr dataPtrAddr subCode)[4 * k + off]? =
      some (liftInstrAt inPtrAddr dataPtrAddr (4 * subCode.size) k (subCode[k]'hk) off) := by
  have hlt : 4 * k + off < 4 * subCode.size := by omega
  have hbound : 4 * k + off < (liftCode inPtrAddr dataPtrAddr subCode).size := by
    rw [liftCode_size]; omega
  rw [Array.getElem?_eq_getElem hbound]
  simp only [liftCode, Array.getElem_ofFn, hlt, ↓reduceDIte]
  have hdiv : (4 * k + off) / 4 = k := by omega
  have hmod : (4 * k + off) % 4 = off := by omega
  simp only [hdiv, hmod]

theorem liftCode_exit {bits : Nat} (inPtrAddr dataPtrAddr : Word bits)
    (subCode : Array (Instr bits 15)) :
    (liftCode inPtrAddr dataPtrAddr subCode)[4 * subCode.size]? = some .halt := by
  have hbound : 4 * subCode.size < (liftCode inPtrAddr dataPtrAddr subCode).size := by
    rw [liftCode_size]; omega
  rw [Array.getElem?_eq_getElem hbound]
  simp only [liftCode, Array.getElem_ofFn]
  have hnot : ¬ (4 * subCode.size < 4 * subCode.size) := Nat.lt_irrefl _
  simp [hnot]

/-- Lift any 15-register `Program subL` into a 16-register `Program bigL`. -/
def liftProgram {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Program subL) : Program bigL :=
  castProg hBig.symm (liftCode inPtrAddr dataPtrAddr (castProg hSub subCode))

theorem liftProgram_size {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Program subL) :
    (liftProgram hSub hBig inPtrAddr dataPtrAddr subCode).size = 4 * subCode.size + 1 := by
  rcases subL with ⟨rSub, _, _, _, _⟩
  rcases bigL with ⟨rBig, _, _, _, _⟩
  cases hSub
  cases hBig
  exact liftCode_size inPtrAddr dataPtrAddr subCode

theorem liftProgram_exit {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Program subL) :
    (liftProgram hSub hBig inPtrAddr dataPtrAddr subCode)[4 * subCode.size]? = some .halt := by
  rcases subL with ⟨rSub, _, _, _, _⟩
  rcases bigL with ⟨rBig, _, _, _, _⟩
  cases hSub
  cases hBig
  exact liftCode_exit inPtrAddr dataPtrAddr subCode

/-- Predicate asserting that `linkedCode` contains the non-exit instructions of
`liftCode inPtrAddr dataPtrAddr subCode` relocated at `base` (compatible with both
`RelocatedSlice` and `FixedROM.join` replacing `4 * subCode.size`). -/
def BodyRelocated {bits : Nat} {bigL : Layout bits}
    (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Array (Instr bits 15))
    (linkedCode : Program bigL) (base : Nat) : Prop :=
  ∀ i : Nat, i < 4 * subCode.size → ∀ op : Instr bits 16,
    (liftCode inPtrAddr dataPtrAddr subCode)[i]? = some op →
      linkedCode[base + i]? = some (relocateInstr base (cast (congrArg (Instr bits) hBig.symm) op))

theorem bodyRelocated_self {bits : Nat} {bigL : Layout bits}
    (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Array (Instr bits 15)) :
    BodyRelocated hBig inPtrAddr dataPtrAddr subCode
      (castProg hBig.symm (liftCode inPtrAddr dataPtrAddr subCode)) 0 := by
  rcases bigL with ⟨rBig, _, _, _, _⟩
  cases hBig
  intro i _ op hop
  have hrel : relocateInstr 0 op = op := by
    cases op <;> simp [relocateInstr]
  simpa only [castProg, Nat.zero_add, cast_eq, hrel] using hop

theorem bodyRelocated_of_relocatedSlice {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (inPtrAddr dataPtrAddr : Word bits) (subCode : Program subL)
    (linkedCode : Program bigL) (base : Nat)
    (hRel : RelocatedSlice (liftProgram hSub hBig inPtrAddr dataPtrAddr subCode) linkedCode base) :
    BodyRelocated hBig inPtrAddr dataPtrAddr (castProg hSub subCode) linkedCode base := by
  rcases subL with ⟨rSub, _, _, _, _⟩
  rcases bigL with ⟨rBig, _, _, _, _⟩
  cases hSub
  cases hBig
  intro i _ op hop
  exact hRel i op hop

end LifterDefs

section Simulation

/-- Simulation invariant linking a 15-register sub-state `subS` and a 16-register
outer state `bigS` placed at `base` inside `linkedCode`. -/
structure SliceSim {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (dataBase base : Nat) (initData : Array (Word bits))
    (subS : State subL) (bigS : State bigL) : Prop where
  pc_eq : bigS.pc = base + 4 * subS.pc
  regs_eq : ∀ i : Fin 15, bigS.regs[i.val]? = subS.regs[i.val]?
  dataSlice_eq : ∀ j : Nat, j < subL.workCap → bigS.data[dataBase + j]? = subS.data[j]?
  frame_eq : ∀ w : Nat, (w < dataBase ∨ dataBase + subL.workCap ≤ w) →
    bigS.data[w]? = initData[w]?

/-- Memory-slice framing and pointer conditions for running a lifted 15-register
program inside a 16-register machine. -/
structure SliceConfig {bits : Nat} (subL bigL : Layout bits)
    (inPtrAddr dataPtrAddr : Word bits) (inBase dataBase : Nat)
    (subInput : Input subL) (initData : Array (Word bits)) : Prop where
  inBaseLt : inBase < 2 ^ bits
  dataBaseLt : dataBase < 2 ^ bits
  inPtr_lt : inPtrAddr.val < bigL.workCap
  dataPtr_lt : dataPtrAddr.val < bigL.workCap
  inFit : inBase + subL.inputCap ≤ bigL.workCap
  dataFit : dataBase + subL.workCap ≤ bigL.workCap
  inPtr_at : initData[inPtrAddr.val]? = some ⟨inBase, inBaseLt⟩
  dataPtr_at : initData[dataPtrAddr.val]? = some ⟨dataBase, dataBaseLt⟩
  inPtr_outside : inPtrAddr.val < dataBase ∨ dataBase + subL.workCap ≤ inPtrAddr.val
  dataPtr_outside : dataPtrAddr.val < dataBase ∨ dataBase + subL.workCap ≤ dataPtrAddr.val
  slices_disjoint : inBase + subL.inputCap ≤ dataBase ∨ dataBase + subL.workCap ≤ inBase
  inSlice_eq : ∀ j : Nat, j < subL.inputCap → initData[inBase + j]? = subInput.words[j]?

private def putReg {bits : Nat} {L : Layout bits}
    (s : State L) (d : Fin L.registerCount) (w : Word bits) : State L :=
  { s with
    regs := s.regs.set d.val w (by simpa only [s.regs_size] using d.isLt)
    regs_size := by simp only [Array.size_set, s.regs_size]
    pc := s.pc + 1 }

private theorem reg_putReg_same {bits : Nat} {L : Layout bits}
    (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    reg (putReg s d w) d = w := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  change (s.regs.set d.val w hd)[d.val]'(by simpa only [Array.size_set] using hd) = w
  simp

private theorem reg_putReg_other {bits : Nat} {L : Layout bits}
    (s : State L) (d r : Fin L.registerCount) (w : Word bits) (hr : r ≠ d) :
    reg (putReg s d w) r = reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hro : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  have hv : r.val ≠ d.val := fun he => hr (Fin.ext he)
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hro) = s.regs[r.val]'hro
  simp [Array.getElem_set, Ne.symm hv]

private theorem readReg15_eq {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    {dataBase base : Nat} {initData : Array (Word bits)}
    {subS : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS : State ⟨16, bIn, bWork, hbi, hbw⟩}
    (hSim : SliceSim rfl rfl dataBase base initData subS bigS)
    (i : Fin 15) :
    reg bigS (liftReg i) = reg subS i := by
  have hb : i.val < bigS.regs.size := by rw [bigS.regs_size]; exact Nat.lt_succ_of_lt i.isLt
  have hs : i.val < subS.regs.size := by rw [subS.regs_size]; exact i.isLt
  have hget := hSim.regs_eq i
  rw [Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hs] at hget
  exact Option.some.inj hget

private theorem step_imm_L {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {dst : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm dst w))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ reg t dst = w ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s dst w, ?_, rfl, reg_putReg_same s dst w,
    fun r hr => reg_putReg_other s dst r w hr, rfl⟩
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then some (Transition.next (putReg s dst w)) else none) = _
  rw [ite_eq_left hnext]

private theorem step_mov_L {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {dst src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.mov dst src))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ reg t dst = reg s src ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s dst (reg s src), ?_, rfl, reg_putReg_same s dst (reg s src),
    fun r hr => reg_putReg_other s dst r (reg s src) hr, rfl⟩
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (putReg s dst (reg s src))) else none) = _
  rw [ite_eq_left hnext]

private theorem step_band_L {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {dst x y : Fin L.registerCount}
    (hf : code[s.pc]? = some (.band dst x y))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ reg t dst = band (reg s x) (reg s y) ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s dst (band (reg s x) (reg s y)), ?_, rfl,
    reg_putReg_same s dst (band (reg s x) (reg s y)),
    fun r hr => reg_putReg_other s dst r (band (reg s x) (reg s y)) hr, rfl⟩
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (putReg s dst (band (reg s x) (reg s y)))) else none) = _
  rw [ite_eq_left hnext]

private theorem step_storeData_L {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.storeData addr src))
    (hnext : s.pc + 1 < code.size)
    (hbound : (reg s addr).val < s.data.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ t.regs = s.regs ∧
      t.data = s.data.set (reg s addr).val (reg s src) hbound := by
  let t : State L :=
    { s with
      data := s.data.set (reg s addr).val (reg s src) hbound
      data_size := by simp only [Array.size_set, s.data_size]
      pc := s.pc + 1 }
  refine ⟨t, ?_, rfl, rfl, rfl⟩
  unfold step
  rw [hf]
  change (if h : (reg s addr).val < s.data.size then
      (if s.pc + 1 < code.size then some (Transition.next
        { s with
          data := s.data.set (reg s addr).val (reg s src) h
          data_size := by simp only [Array.size_set, s.data_size]
          pc := s.pc + 1 })
      else none)
    else none) = _
  rw [dite_eq_left_of_eq_true (eq_true hbound), ite_eq_left hnext]

private theorem step_put_inv {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s t : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hStep : step code input s = some (Transition.next t))
    (hDef : step code input s =
      if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) :
    s.pc + 1 < code.size ∧ t = putReg s d w := by
  rw [hDef] at hStep
  by_cases hn : s.pc + 1 < code.size
  · rw [ite_eq_left hn] at hStep
    exact ⟨hn, (Transition.next.inj (Option.some.inj hStep)).symm⟩
  · rw [ite_eq_right hn] at hStep
    cases hStep

private theorem step_load_inv {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s t : State L}
    {d : Fin L.registerCount} (arr : Array (Word bits)) (addr : Nat)
    (hStep : step code input s = some (Transition.next t))
    (hDef : step code input s =
      (arr[addr]? >>= fun w =>
        if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none)) :
    ∃ (hBound : addr < arr.size),
      s.pc + 1 < code.size ∧ t = putReg s d (arr[addr]'hBound) := by
  rw [hDef] at hStep
  by_cases ha : addr < arr.size
  · rw [Array.getElem?_eq_getElem ha] at hStep
    change (if s.pc + 1 < code.size then
        some (Transition.next (putReg s d (arr[addr]'ha))) else none) =
      some (Transition.next t) at hStep
    by_cases hn : s.pc + 1 < code.size
    · rw [ite_eq_left hn] at hStep
      exact ⟨ha, hn, (Transition.next.inj (Option.some.inj hStep)).symm⟩
    · rw [ite_eq_right hn] at hStep
      cases hStep
  · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hStep
    cases hStep

private theorem step_store_inv {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s t : State L}
    {addr src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.storeData addr src))
    (hStep : step code input s = some (Transition.next t)) :
    ∃ (hBound : (reg s addr).val < s.data.size),
      s.pc + 1 < code.size ∧
      t = { s with
        data := s.data.set (reg s addr).val (reg s src) hBound
        data_size := by simp only [Array.size_set, s.data_size]
        pc := s.pc + 1 } := by
  unfold step at hStep
  rw [hf] at hStep
  change (if h : (reg s addr).val < s.data.size then
      (if s.pc + 1 < code.size then some (Transition.next
        { s with
          data := s.data.set (reg s addr).val (reg s src) h
          data_size := by simp only [Array.size_set, s.data_size]
          pc := s.pc + 1 })
      else none)
    else none) = some (Transition.next t) at hStep
  by_cases ha : (reg s addr).val < s.data.size
  · rw [dite_eq_left_of_eq_true (eq_true ha)] at hStep
    by_cases hn : s.pc + 1 < code.size
    · rw [ite_eq_left hn] at hStep
      exact ⟨ha, hn, (Transition.next.inj (Option.some.inj hStep)).symm⟩
    · rw [ite_eq_right hn] at hStep
      cases hStep
  · rw [dite_eq_right_of_eq_false (eq_false ha)] at hStep
    cases hStep

private theorem reg15_preserved_of_write15 {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    {subS : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS bigT : State ⟨16, bIn, bWork, hbi, hbw⟩}
    {d : Fin 15} {w : Word bits}
    (hPrev : ∀ i : Fin 15, bigS.regs[i.val]? = subS.regs[i.val]?)
    (hSame : reg bigT (liftReg d) = w)
    (hOther : ∀ r : Fin 16, r ≠ liftReg d → reg bigT r = reg bigS r) :
    ∀ i : Fin 15, bigT.regs[i.val]? = (putReg subS d w).regs[i.val]? := by
  intro i
  have hbi' : i.val < bigT.regs.size := by rw [bigT.regs_size]; exact Nat.lt_succ_of_lt i.isLt
  have hsi' : i.val < (putReg subS d w).regs.size := by
    simp [putReg, subS.regs_size]
  rw [Array.getElem?_eq_getElem hbi', Array.getElem?_eq_getElem hsi']
  by_cases hi : i = d
  · subst hi
    change some (reg bigT (liftReg i)) =
      some ((putReg subS i w).regs[i.val]'(by simp [putReg, subS.regs_size]))
    rw [hSame]
    simp [putReg]
  · have hne : liftReg i ≠ liftReg d := fun h => hi (liftReg_inj h)
    have hr := hOther (liftReg i) hne
    have hbs : i.val < bigS.regs.size := by rw [bigS.regs_size]; exact Nat.lt_succ_of_lt i.isLt
    have hss : i.val < subS.regs.size := by rw [subS.regs_size]; exact i.isLt
    have hget := hPrev i
    rw [Array.getElem?_eq_getElem hbs, Array.getElem?_eq_getElem hss] at hget
    have hprevReg : reg bigS (liftReg i) = reg subS i := Option.some.inj hget
    have hneNat : i.val ≠ d.val := fun h => hi (Fin.ext h)
    have hSubReg : reg (putReg subS d w) i = reg subS i :=
      reg_putReg_other subS d i w hi
    change some (reg bigT (liftReg i)) = some (reg (putReg subS d w) i)
    rw [hr, hprevReg, hSubReg]

private theorem reg15_preserved_of_scratch {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    {subS : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS bigT : State ⟨16, bIn, bWork, hbi, hbw⟩}
    (hPrev : ∀ i : Fin 15, bigS.regs[i.val]? = subS.regs[i.val]?)
    (hOther : ∀ r : Fin 16, r ≠ scratchReg → reg bigT r = reg bigS r) :
    ∀ i : Fin 15, bigT.regs[i.val]? = subS.regs[i.val]? := by
  intro i
  have hbi' : i.val < bigT.regs.size := by rw [bigT.regs_size]; exact Nat.lt_succ_of_lt i.isLt
  have hbs : i.val < bigS.regs.size := by rw [bigS.regs_size]; exact Nat.lt_succ_of_lt i.isLt
  rw [Array.getElem?_eq_getElem hbi', ← hPrev i, Array.getElem?_eq_getElem hbs]
  exact congrArg some (hOther (liftReg i) (liftReg_ne_scratch i))

private theorem step_lift_alu2 {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    {subCode : Array (Instr bits 15)}
    {linkedCode : Program ⟨16, bIn, bWork, hbi, hbw⟩}
    {bigInput : Input ⟨16, bIn, bWork, hbi, hbw⟩}
    {inPtrAddr dataPtrAddr : Word bits}
    {base dataBase : Nat} {initData : Array (Word bits)}
    {subS subT : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS : State ⟨16, bIn, bWork, hbi, hbw⟩}
    (hBody : BodyRelocated (bits := bits) (bigL := ⟨16, bIn, bWork, hbi, hbw⟩)
      rfl inPtrAddr dataPtrAddr subCode linkedCode base)
    (hExitLt : base + 4 * subCode.size < linkedCode.size)
    (hk : subS.pc < subCode.size)
    (hSim : SliceSim rfl rfl dataBase base initData subS bigS)
    {d : Fin 15} {w : Word bits}
    (hSubNext : subS.pc + 1 < subCode.size)
    (hSubT : subT = putReg subS d w)
    (hStep0 : ∃ t₁ : State ⟨16, bIn, bWork, hbi, hbw⟩,
      step linkedCode bigInput bigS = some (Transition.next t₁) ∧
      t₁.pc = bigS.pc + 1 ∧ reg t₁ (liftReg d) = w ∧
      (∀ r : Fin 16, r ≠ liftReg d → reg t₁ r = reg bigS r) ∧
      t₁.data = bigS.data)
    (hOp1 : liftInstrAt inPtrAddr dataPtrAddr (4 * subCode.size) subS.pc (subCode[subS.pc]'hk) 1 =
      .goto (4 * (subS.pc + 1))) :
    ∃ bigT : State ⟨16, bIn, bWork, hbi, hbw⟩,
      Steps linkedCode bigInput 2 bigS bigT ∧
      SliceSim rfl rfl dataBase base initData subT bigT := by
  obtain ⟨t₁, hs₁, hpc₁, hsame₁, hother₁, hdata₁⟩ := hStep0
  have hfetch1 : linkedCode[t₁.pc]? = some (.goto (base + 4 * (subS.pc + 1))) := by
    have hp₁ : t₁.pc = base + (4 * subS.pc + 1) := by rw [hpc₁, hSim.pc_eq]; omega
    rw [hp₁]
    have hCode1 := liftCode_at inPtrAddr dataPtrAddr subCode hk (show 1 < 4 by decide)
    rw [hOp1] at hCode1
    exact hBody (4 * subS.pc + 1) (by omega) _ hCode1
  have hgtBound : base + 4 * (subS.pc + 1) < linkedCode.size := by omega
  have hs₂ := step_goto_at (input := bigInput) hfetch1 hgtBound
  refine ⟨{ t₁ with pc := base + 4 * (subS.pc + 1) },
    Steps.cons hs₁ (Steps.cons hs₂ (Steps.zero _)), ?_⟩
  subst hSubT
  refine ⟨rfl, reg15_preserved_of_write15 hSim.regs_eq hsame₁ hother₁, ?_, ?_⟩
  · intro j hj
    rw [hdata₁, hSim.dataSlice_eq j hj]
    rfl
  · intro w hw
    rw [hdata₁]
    exact hSim.frame_eq w hw

private theorem step_lift_one {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    (subInput : Input ⟨15, inCap, sWork, hsi, hsw⟩)
    (linkedCode : Program ⟨16, bIn, bWork, hbi, hbw⟩)
    (bigInput : Input ⟨16, bIn, bWork, hbi, hbw⟩)
    (inPtrAddr dataPtrAddr : Word bits)
    (inBase dataBase base : Nat) (initData : Array (Word bits))
    (hCfg : SliceConfig ⟨15, inCap, sWork, hsi, hsw⟩ ⟨16, bIn, bWork, hbi, hbw⟩
      inPtrAddr dataPtrAddr inBase dataBase subInput initData)
    (hBody : BodyRelocated (bits := bits) (bigL := ⟨16, bIn, bWork, hbi, hbw⟩)
      rfl inPtrAddr dataPtrAddr subCode linkedCode base)
    (hExitLt : base + 4 * subCode.size < linkedCode.size)
    {subS subT : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS : State ⟨16, bIn, bWork, hbi, hbw⟩}
    (hSub : step subCode subInput subS = some (Transition.next subT))
    (hSim : SliceSim rfl rfl dataBase base initData subS bigS) :
    ∃ (m : Nat) (bigT : State ⟨16, bIn, bWork, hbi, hbw⟩),
      m ≤ 4 ∧ Steps linkedCode bigInput m bigS bigT ∧
      SliceSim rfl rfl dataBase base initData subT bigT := by
  have hk : subS.pc < subCode.size := by
    by_cases h : subS.pc < subCode.size
    · exact h
    · have hn : subCode[subS.pc]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp [step, hn] at hSub
  have hFetchSub : subCode[subS.pc]? = some (subCode[subS.pc]'hk) :=
    Array.getElem?_eq_getElem hk
  have hFetch0 : ∀ off < 4,
      linkedCode[base + (4 * subS.pc + off)]? =
        some (relocateInstr base
          (liftInstrAt inPtrAddr dataPtrAddr (4 * subCode.size) subS.pc (subCode[subS.pc]'hk) off)) := by
    intro off hoff
    exact hBody (4 * subS.pc + off) (by omega) _ (liftCode_at inPtrAddr dataPtrAddr subCode hk hoff)
  have hNext0 : bigS.pc + 1 < linkedCode.size := by rw [hSim.pc_eq]; omega
  have hinFit : inBase + inCap ≤ bWork := hCfg.inFit
  have hdataFit : dataBase + sWork ≤ bWork := hCfg.dataFit
  cases hop : subCode[subS.pc]'hk with
  | imm d v =>
    obtain ⟨hNextSub, hSubTEq⟩ := step_put_inv hSub (by
      unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.imm (liftReg d) v) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      (step_imm_L hf0 hNext0) (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | mov d s =>
    obtain ⟨hNextSub, hSubTEq⟩ := step_put_inv (w := reg subS s) hSub (by
      unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.mov (liftReg d) (liftReg s)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hStep0 := step_mov_L (input := bigInput) hf0 hNext0
    rw [readReg15_eq hSim s] at hStep0
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      hStep0 (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | add d x y =>
    obtain ⟨hNextSub, hSubTEq⟩ := step_put_inv (w := add (reg subS x) (reg subS y)) hSub (by
      unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.add (liftReg d) (liftReg x) (liftReg y)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hStep0 := step_add_at (input := bigInput) hf0 hNext0
    rw [readReg15_eq hSim x, readReg15_eq hSim y] at hStep0
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      hStep0 (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | sub d x y =>
    obtain ⟨hNextSub, hSubTEq⟩ :=
      step_put_inv (w := PaperB.WordOps.sub (reg subS x) (reg subS y)) hSub (by
        unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.sub (liftReg d) (liftReg x) (liftReg y)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hStep0 := step_sub_at (input := bigInput) hf0 hNext0
    rw [readReg15_eq hSim x, readReg15_eq hSim y] at hStep0
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      hStep0 (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | band d x y =>
    obtain ⟨hNextSub, hSubTEq⟩ := step_put_inv (w := band (reg subS x) (reg subS y)) hSub (by
      unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.band (liftReg d) (liftReg x) (liftReg y)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hStep0 := step_band_L (input := bigInput) hf0 hNext0
    rw [readReg15_eq hSim x, readReg15_eq hSim y] at hStep0
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      hStep0 (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | shr1 d s =>
    let wShr : Word bits := ⟨(reg subS s).val / 2,
      Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (reg subS s).isLt⟩
    obtain ⟨hNextSub, hSubTEq⟩ := step_put_inv (w := wShr) hSub (by
      unfold step; rw [hFetchSub, hop]; rfl)
    have hf0 : linkedCode[bigS.pc]? = some (.shr1 (liftReg d) (liftReg s)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    obtain ⟨t₁, hs₁, hpc₁, hval₁, hother₁, hdata₁⟩ :=
      step_shr1_at (input := bigInput) hf0 hNext0
    have hsame₁ : reg t₁ (liftReg d) = wShr := by
      apply Fin.ext
      rw [hval₁, readReg15_eq hSim s]
    obtain ⟨bigT, hst, hsim'⟩ := step_lift_alu2 hBody hExitLt hk hSim hNextSub hSubTEq
      ⟨t₁, hs₁, hpc₁, hsame₁, hother₁, hdata₁⟩ (by simp [hop, liftInstrAt])
    exact ⟨2, bigT, by decide, hst, hsim'⟩
  | loadInput d a =>
    obtain ⟨hBound, hNextSub, hSubTEq⟩ := step_load_inv (d := d) subInput.words (reg subS a).val
      hSub (by unfold step; rw [hFetchSub, hop]; rfl)
    have hAddrLt : (reg subS a).val < inCap := by
      simpa only [subInput.size_eq] using hBound
    have hwEq : subInput.words[(reg subS a).val]? = some (subInput.words[(reg subS a).val]'hBound) :=
      Array.getElem?_eq_getElem hBound
    have hf0 : linkedCode[bigS.pc]? = some (.imm scratchReg inPtrAddr) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    obtain ⟨t₁, hs₁, hpc₁, hreg₁, hother₁, hdata₁⟩ := step_imm_L hf0 hNext0
    have hpc₁' : t₁.pc = base + (4 * subS.pc + 1) := by rw [hpc₁, hSim.pc_eq]; omega
    have hf1 : linkedCode[t₁.pc]? = some (.loadData scratchReg scratchReg) := by
      rw [hpc₁']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 1 (by decide)
    have hInPtrMem : t₁.data[(reg t₁ scratchReg).val]? = some ⟨inBase, hCfg.inBaseLt⟩ := by
      rw [hdata₁, hreg₁, hSim.frame_eq _ hCfg.inPtr_outside]
      exact hCfg.inPtr_at
    obtain ⟨t₂, hs₂, hpc₂, hreg₂, hother₂, hdata₂⟩ :=
      step_loadData_at hf1 hInPtrMem (by rw [hpc₁']; omega)
    have hpc₂' : t₂.pc = base + (4 * subS.pc + 2) := by rw [hpc₂, hpc₁']; omega
    have hf2 : linkedCode[t₂.pc]? = some (.add scratchReg scratchReg (liftReg a)) := by
      rw [hpc₂']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 2 (by decide)
    obtain ⟨t₃, hs₃, hpc₃, hreg₃, hother₃, hdata₃⟩ :=
      step_add_at (input := bigInput) hf2 (by rw [hpc₂']; omega)
    have haVal : reg t₂ (liftReg a) = reg subS a := by
      rw [hother₂ _ (liftReg_ne_scratch a), hother₁ _ (liftReg_ne_scratch a),
        readReg15_eq hSim a]
    have hSumLt : (reg t₂ scratchReg).val + (reg t₂ (liftReg a)).val < 2 ^ bits := by
      have hreg2Val : (reg t₂ scratchReg).val = inBase := congrArg Fin.val hreg₂
      have haValNat : (reg t₂ (liftReg a)).val = (reg subS a).val := congrArg Fin.val haVal
      omega
    have hAddrSum : (reg t₃ scratchReg).val = inBase + (reg subS a).val := by
      rw [hreg₃, WordOps.add_no_wrap _ _ hSumLt, hreg₂, haVal]
    have hpc₃' : t₃.pc = base + (4 * subS.pc + 3) := by rw [hpc₃, hpc₂']; omega
    have hf3 : linkedCode[t₃.pc]? = some (.loadData (liftReg d) scratchReg) := by
      rw [hpc₃']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 3 (by decide)
    have hSliceOutside : inBase + (reg subS a).val < dataBase ∨
        dataBase + sWork ≤ inBase + (reg subS a).val := by
      have hd : inBase + inCap ≤ dataBase ∨ dataBase + sWork ≤ inBase := hCfg.slices_disjoint
      rcases hd with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hInMem : t₃.data[(reg t₃ scratchReg).val]? =
        some (subInput.words[(reg subS a).val]'hBound) := by
      rw [hAddrSum, hdata₃, hdata₂, hdata₁, hSim.frame_eq _ hSliceOutside,
        hCfg.inSlice_eq _ hAddrLt, hwEq]
    obtain ⟨t₄, hs₄, hpc₄, hreg₄, hother₄, hdata₄⟩ :=
      step_loadData_at hf3 hInMem (by rw [hpc₃']; omega)
    refine ⟨4, t₄, Nat.le_refl _,
      Steps.cons hs₁ (Steps.cons hs₂ (Steps.cons hs₃ (Steps.cons hs₄ (Steps.zero _)))), ?_⟩
    subst hSubTEq
    refine ⟨by change t₄.pc = base + 4 * (subS.pc + 1); rw [hpc₄, hpc₃']; omega, ?_, ?_, ?_⟩
    · intro i
      have h123 : ∀ r : Fin 15, t₃.regs[r.val]? = subS.regs[r.val]? := by
        apply reg15_preserved_of_scratch _ hother₃
        apply reg15_preserved_of_scratch _ hother₂
        exact reg15_preserved_of_scratch hSim.regs_eq hother₁
      exact reg15_preserved_of_write15 h123 hreg₄ hother₄ i
    · intro j hj
      rw [hdata₄, hdata₃, hdata₂, hdata₁, hSim.dataSlice_eq j hj]
      rfl
    · intro w hw
      rw [hdata₄, hdata₃, hdata₂, hdata₁]
      exact hSim.frame_eq w hw
  | loadData d a =>
    obtain ⟨hBound, hNextSub, hSubTEq⟩ := step_load_inv (d := d) subS.data (reg subS a).val
      hSub (by unfold step; rw [hFetchSub, hop]; rfl)
    have hAddrLt : (reg subS a).val < sWork := by
      simpa only [subS.data_size] using hBound
    have hwEq : subS.data[(reg subS a).val]? = some (subS.data[(reg subS a).val]'hBound) :=
      Array.getElem?_eq_getElem hBound
    have hf0 : linkedCode[bigS.pc]? = some (.imm scratchReg dataPtrAddr) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    obtain ⟨t₁, hs₁, hpc₁, hreg₁, hother₁, hdata₁⟩ := step_imm_L hf0 hNext0
    have hpc₁' : t₁.pc = base + (4 * subS.pc + 1) := by rw [hpc₁, hSim.pc_eq]; omega
    have hf1 : linkedCode[t₁.pc]? = some (.loadData scratchReg scratchReg) := by
      rw [hpc₁']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 1 (by decide)
    have hDataPtrMem : t₁.data[(reg t₁ scratchReg).val]? = some ⟨dataBase, hCfg.dataBaseLt⟩ := by
      rw [hdata₁, hreg₁, hSim.frame_eq _ hCfg.dataPtr_outside]
      exact hCfg.dataPtr_at
    obtain ⟨t₂, hs₂, hpc₂, hreg₂, hother₂, hdata₂⟩ :=
      step_loadData_at hf1 hDataPtrMem (by rw [hpc₁']; omega)
    have hpc₂' : t₂.pc = base + (4 * subS.pc + 2) := by rw [hpc₂, hpc₁']; omega
    have hf2 : linkedCode[t₂.pc]? = some (.add scratchReg scratchReg (liftReg a)) := by
      rw [hpc₂']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 2 (by decide)
    obtain ⟨t₃, hs₃, hpc₃, hreg₃, hother₃, hdata₃⟩ :=
      step_add_at (input := bigInput) hf2 (by rw [hpc₂']; omega)
    have haVal : reg t₂ (liftReg a) = reg subS a := by
      rw [hother₂ _ (liftReg_ne_scratch a), hother₁ _ (liftReg_ne_scratch a),
        readReg15_eq hSim a]
    have hSumLt : (reg t₂ scratchReg).val + (reg t₂ (liftReg a)).val < 2 ^ bits := by
      have hreg2Val : (reg t₂ scratchReg).val = dataBase := congrArg Fin.val hreg₂
      have haValNat : (reg t₂ (liftReg a)).val = (reg subS a).val := congrArg Fin.val haVal
      omega
    have hAddrSum : (reg t₃ scratchReg).val = dataBase + (reg subS a).val := by
      rw [hreg₃, WordOps.add_no_wrap _ _ hSumLt, hreg₂, haVal]
    have hpc₃' : t₃.pc = base + (4 * subS.pc + 3) := by rw [hpc₃, hpc₂']; omega
    have hf3 : linkedCode[t₃.pc]? = some (.loadData (liftReg d) scratchReg) := by
      rw [hpc₃']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 3 (by decide)
    have hDataMem : t₃.data[(reg t₃ scratchReg).val]? =
        some (subS.data[(reg subS a).val]'hBound) := by
      rw [hAddrSum, hdata₃, hdata₂, hdata₁, hSim.dataSlice_eq _ hAddrLt, hwEq]
    obtain ⟨t₄, hs₄, hpc₄, hreg₄, hother₄, hdata₄⟩ :=
      step_loadData_at hf3 hDataMem (by rw [hpc₃']; omega)
    refine ⟨4, t₄, Nat.le_refl _,
      Steps.cons hs₁ (Steps.cons hs₂ (Steps.cons hs₃ (Steps.cons hs₄ (Steps.zero _)))), ?_⟩
    subst hSubTEq
    refine ⟨by change t₄.pc = base + 4 * (subS.pc + 1); rw [hpc₄, hpc₃']; omega, ?_, ?_, ?_⟩
    · intro i
      have h123 : ∀ r : Fin 15, t₃.regs[r.val]? = subS.regs[r.val]? := by
        apply reg15_preserved_of_scratch _ hother₃
        apply reg15_preserved_of_scratch _ hother₂
        exact reg15_preserved_of_scratch hSim.regs_eq hother₁
      exact reg15_preserved_of_write15 h123 hreg₄ hother₄ i
    · intro j hj
      rw [hdata₄, hdata₃, hdata₂, hdata₁, hSim.dataSlice_eq j hj]
      rfl
    · intro w hw
      rw [hdata₄, hdata₃, hdata₂, hdata₁]
      exact hSim.frame_eq w hw
  | storeData a src =>
    obtain ⟨hSubDataBound, hNextSub, hSubTEq⟩ :=
      step_store_inv (hFetchSub.trans (congrArg some hop)) hSub
    have hAddrLt : (reg subS a).val < sWork := by
      simpa only [subS.data_size] using hSubDataBound
    have hf0 : linkedCode[bigS.pc]? = some (.imm scratchReg dataPtrAddr) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    obtain ⟨t₁, hs₁, hpc₁, hreg₁, hother₁, hdata₁⟩ := step_imm_L hf0 hNext0
    have hpc₁' : t₁.pc = base + (4 * subS.pc + 1) := by rw [hpc₁, hSim.pc_eq]; omega
    have hf1 : linkedCode[t₁.pc]? = some (.loadData scratchReg scratchReg) := by
      rw [hpc₁']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 1 (by decide)
    have hDataPtrMem : t₁.data[(reg t₁ scratchReg).val]? = some ⟨dataBase, hCfg.dataBaseLt⟩ := by
      rw [hdata₁, hreg₁, hSim.frame_eq _ hCfg.dataPtr_outside]
      exact hCfg.dataPtr_at
    obtain ⟨t₂, hs₂, hpc₂, hreg₂, hother₂, hdata₂⟩ :=
      step_loadData_at hf1 hDataPtrMem (by rw [hpc₁']; omega)
    have hpc₂' : t₂.pc = base + (4 * subS.pc + 2) := by rw [hpc₂, hpc₁']; omega
    have hf2 : linkedCode[t₂.pc]? = some (.add scratchReg scratchReg (liftReg a)) := by
      rw [hpc₂']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 2 (by decide)
    obtain ⟨t₃, hs₃, hpc₃, hreg₃, hother₃, hdata₃⟩ :=
      step_add_at (input := bigInput) hf2 (by rw [hpc₂']; omega)
    have haVal : reg t₂ (liftReg a) = reg subS a := by
      rw [hother₂ _ (liftReg_ne_scratch a), hother₁ _ (liftReg_ne_scratch a),
        readReg15_eq hSim a]
    have hSumLt : (reg t₂ scratchReg).val + (reg t₂ (liftReg a)).val < 2 ^ bits := by
      have hreg2Val : (reg t₂ scratchReg).val = dataBase := congrArg Fin.val hreg₂
      have haValNat : (reg t₂ (liftReg a)).val = (reg subS a).val := congrArg Fin.val haVal
      omega
    have hAddrSum : (reg t₃ scratchReg).val = dataBase + (reg subS a).val := by
      rw [hreg₃, WordOps.add_no_wrap _ _ hSumLt, hreg₂, haVal]
    have hpc₃' : t₃.pc = base + (4 * subS.pc + 3) := by rw [hpc₃, hpc₂']; omega
    have hf3 : linkedCode[t₃.pc]? = some (.storeData scratchReg (liftReg src)) := by
      rw [hpc₃']; simpa [hop, liftInstrAt, relocateInstr] using hFetch0 3 (by decide)
    have hBigBound : (reg t₃ scratchReg).val < t₃.data.size := by
      have ht3Sz : t₃.data.size = bWork := t₃.data_size
      omega
    obtain ⟨t₄, hs₄, hpc₄, hregs₄, hdata₄⟩ :=
      step_storeData_L hf3 (by rw [hpc₃']; omega) hBigBound
    have hSrcVal : reg t₃ (liftReg src) = reg subS src := by
      rw [hother₃ _ (liftReg_ne_scratch src), hother₂ _ (liftReg_ne_scratch src),
        hother₁ _ (liftReg_ne_scratch src), readReg15_eq hSim src]
    refine ⟨4, t₄, Nat.le_refl _,
      Steps.cons hs₁ (Steps.cons hs₂ (Steps.cons hs₃ (Steps.cons hs₄ (Steps.zero _)))), ?_⟩
    subst hSubTEq
    refine ⟨by change t₄.pc = base + 4 * (subS.pc + 1); rw [hpc₄, hpc₃']; omega, ?_, ?_, ?_⟩
    · intro i
      have h123 : ∀ r : Fin 15, t₃.regs[r.val]? = subS.regs[r.val]? := by
        apply reg15_preserved_of_scratch _ hother₃
        apply reg15_preserved_of_scratch _ hother₂
        exact reg15_preserved_of_scratch hSim.regs_eq hother₁
      have h43 : t₄.regs[i.val]? = t₃.regs[i.val]? := by simp only [hregs₄]
      exact h43.trans (h123 i)
    · intro j hj
      have hj' : j < sWork := hj
      rw [hdata₄, Array.getElem?_set]
      by_cases hjj : (reg t₃ scratchReg).val = dataBase + j
      · have hjEq : (reg subS a).val = j := by omega
        subst hjEq
        simp only [hjj, ↓reduceIte, Array.getElem?_set, hSrcVal]
      · have hjNe : (reg subS a).val ≠ j := by omega
        simp only [hjj, ↓reduceIte, hdata₃, hdata₂, hdata₁, Array.getElem?_set, hjNe]
        exact hSim.dataSlice_eq j hj'
    · intro w hw
      have hw' : w < dataBase ∨ dataBase + sWork ≤ w := hw
      rw [hdata₄, Array.getElem?_set]
      have hne : (reg t₃ scratchReg).val ≠ w := by omega
      simp only [hne, ↓reduceIte, hdata₃, hdata₂, hdata₁]
      exact hSim.frame_eq w hw'
  | branchLt x y ltPC gePC =>
    let nextSub := if ltb (reg subS x) (reg subS y) then ltPC else gePC
    have hNextSub : nextSub < subCode.size := by
      unfold step at hSub
      rw [hFetchSub, hop] at hSub
      change (if nextSub < subCode.size then
          some (Transition.next { subS with pc := nextSub }) else none) =
        some (Transition.next subT) at hSub
      by_cases h : nextSub < subCode.size
      · exact h
      · rw [ite_eq_right h] at hSub; cases hSub
    have hSubTEq : subT = { subS with pc := nextSub } := by
      have hs' := step_branchLt_at (input := subInput)
        (hFetchSub.trans (congrArg some hop)) hNextSub
      exact Transition.next.inj (Option.some.inj (hSub.symm.trans hs'))
    have hf0 : linkedCode[bigS.pc]? =
        some (.branchLt (liftReg x) (liftReg y) (base + 4 * ltPC) (base + 4 * gePC)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hCondEq :
        (if ltb (reg bigS (liftReg x)) (reg bigS (liftReg y)) then
            base + 4 * ltPC else base + 4 * gePC) =
          base + 4 * nextSub := by
      rw [readReg15_eq hSim x, readReg15_eq hSim y]
      change (if ltb (reg subS x) (reg subS y) then base + 4 * ltPC else base + 4 * gePC) =
        base + 4 * (if ltb (reg subS x) (reg subS y) then ltPC else gePC)
      split <;> rfl
    have hBound :
        (if ltb (reg bigS (liftReg x)) (reg bigS (liftReg y)) then
            base + 4 * ltPC else base + 4 * gePC) < linkedCode.size := by
      rw [hCondEq]; omega
    have hs₁ := step_branchLt_at (input := bigInput) hf0 hBound
    rw [hCondEq] at hs₁
    refine ⟨1, { bigS with pc := base + 4 * nextSub }, by decide,
      Steps.cons hs₁ (Steps.zero _), ?_⟩
    subst hSubTEq
    exact ⟨rfl, hSim.regs_eq, hSim.dataSlice_eq, hSim.frame_eq⟩
  | goto target =>
    have hNextSub : target < subCode.size := by
      unfold step at hSub
      rw [hFetchSub, hop] at hSub
      change (if target < subCode.size then
          some (Transition.next { subS with pc := target }) else none) =
        some (Transition.next subT) at hSub
      by_cases h : target < subCode.size
      · exact h
      · rw [ite_eq_right h] at hSub; cases hSub
    have hSubTEq : subT = { subS with pc := target } := by
      have hs' := step_goto_at (input := subInput)
        (hFetchSub.trans (congrArg some hop)) hNextSub
      exact Transition.next.inj (Option.some.inj (hSub.symm.trans hs'))
    have hf0 : linkedCode[bigS.pc]? = some (.goto (base + 4 * target)) := by
      rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
      simpa [hop, liftInstrAt, relocateInstr] using hFetch0 0 (by decide)
    have hs₁ := step_goto_at (input := bigInput) hf0 (by omega)
    refine ⟨1, { bigS with pc := base + 4 * target }, by decide,
      Steps.cons hs₁ (Steps.zero _), ?_⟩
    subst hSubTEq
    exact ⟨rfl, hSim.regs_eq, hSim.dataSlice_eq, hSim.frame_eq⟩
  | halt =>
    have hh := step_halt_at (input := subInput) (hFetchSub.trans (congrArg some hop))
    rw [hh] at hSub
    cases hSub

private theorem step_lift_halt {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    (subInput : Input ⟨15, inCap, sWork, hsi, hsw⟩)
    (linkedCode : Program ⟨16, bIn, bWork, hbi, hbw⟩)
    (bigInput : Input ⟨16, bIn, bWork, hbi, hbw⟩)
    (inPtrAddr dataPtrAddr : Word bits)
    (dataBase base : Nat) (initData : Array (Word bits))
    (hBody : BodyRelocated (bits := bits) (bigL := ⟨16, bIn, bWork, hbi, hbw⟩)
      rfl inPtrAddr dataPtrAddr subCode linkedCode base)
    (hExitLt : base + 4 * subCode.size < linkedCode.size)
    {subS subT : State ⟨15, inCap, sWork, hsi, hsw⟩}
    {bigS : State ⟨16, bIn, bWork, hbi, hbw⟩}
    (hSub : step subCode subInput subS = some (Transition.halted subT))
    (hSim : SliceSim rfl rfl dataBase base initData subS bigS) :
    ∃ bigT : State ⟨16, bIn, bWork, hbi, hbw⟩,
      Steps linkedCode bigInput 1 bigS bigT ∧
      bigT.pc = base + 4 * subCode.size ∧
      (∀ i : Fin 15, bigT.regs[i.val]? = subT.regs[i.val]?) ∧
      (∀ j : Nat, j < sWork → bigT.data[dataBase + j]? = subT.data[j]?) ∧
      (∀ w : Nat, (w < dataBase ∨ dataBase + sWork ≤ w) →
        bigT.data[w]? = initData[w]?) := by
  have hk : subS.pc < subCode.size := by
    by_cases h : subS.pc < subCode.size
    · exact h
    · have hn : subCode[subS.pc]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp [step, hn] at hSub
  have hFetchSub : subCode[subS.pc]? = some (subCode[subS.pc]'hk) :=
    Array.getElem?_eq_getElem hk
  have hIsHalt : subCode[subS.pc]'hk = .halt ∧ subT = subS := by
    unfold step at hSub
    rw [hFetchSub] at hSub
    cases hop : subCode[subS.pc]'hk
    all_goals rw [hop] at hSub
    case halt =>
      exact ⟨rfl, (Transition.halted.inj (Option.some.inj hSub)).symm⟩
    case imm | mov | add | sub | band | shr1 =>
      change (if _ : subS.pc + 1 < subCode.size then
          some (Transition.next _) else none) = some (Transition.halted subT) at hSub
      split at hSub <;> cases hSub
    case loadInput d a =>
      change (subInput.words[(reg subS a).val]? >>= fun _ =>
          if _ : subS.pc + 1 < subCode.size then some (Transition.next _) else none) =
        some (Transition.halted subT) at hSub
      cases hArr : subInput.words[(reg subS a).val]? with
      | none => rw [hArr] at hSub; cases hSub
      | some w =>
        rw [hArr] at hSub
        change (if _ : subS.pc + 1 < subCode.size then
            some (Transition.next _) else none) = some (Transition.halted subT) at hSub
        split at hSub <;> cases hSub
    case loadData d a =>
      change (subS.data[(reg subS a).val]? >>= fun _ =>
          if _ : subS.pc + 1 < subCode.size then some (Transition.next _) else none) =
        some (Transition.halted subT) at hSub
      cases hArr : subS.data[(reg subS a).val]? with
      | none => rw [hArr] at hSub; cases hSub
      | some w =>
        rw [hArr] at hSub
        change (if _ : subS.pc + 1 < subCode.size then
            some (Transition.next _) else none) = some (Transition.halted subT) at hSub
        split at hSub <;> cases hSub
    case storeData =>
      change (if _ : _ then (if _ : _ then some (Transition.next _) else none) else none) =
        some (Transition.halted subT) at hSub
      split at hSub
      · split at hSub <;> cases hSub
      · cases hSub
    case branchLt x y ltPC gePC =>
      let npc := if ltb (reg subS x) (reg subS y) then ltPC else gePC
      change (if npc < subCode.size then
          some (Transition.next { subS with pc := npc }) else none) =
        some (Transition.halted subT) at hSub
      by_cases h : npc < subCode.size
      · rw [ite_eq_left h] at hSub; cases hSub
      · rw [ite_eq_right h] at hSub; cases hSub
    case goto target =>
      change (if target < subCode.size then
          some (Transition.next { subS with pc := target }) else none) =
        some (Transition.halted subT) at hSub
      by_cases h : target < subCode.size
      · rw [ite_eq_left h] at hSub; cases hSub
      · rw [ite_eq_right h] at hSub; cases hSub
  obtain ⟨hHalt, hEq⟩ := hIsHalt
  have hFetch0 : linkedCode[bigS.pc]? = some (.goto (base + 4 * subCode.size)) := by
    rw [hSim.pc_eq, show base + 4 * subS.pc = base + (4 * subS.pc + 0) by omega]
    have hc := hBody (4 * subS.pc + 0) (by omega) _
      (liftCode_at inPtrAddr dataPtrAddr subCode hk (show 0 < 4 by decide))
    simpa [hHalt, liftInstrAt, relocateInstr] using hc
  have hs₁ := step_goto_at (input := bigInput) hFetch0 hExitLt
  subst hEq
  exact ⟨{ bigS with pc := base + 4 * subCode.size }, Steps.cons hs₁ (Steps.zero _),
    rfl, hSim.regs_eq, hSim.dataSlice_eq, hSim.frame_eq⟩

private theorem liftCode_steps_aux {bits : Nat}
    {inCap sWork bIn bWork : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : sWork ≤ 2 ^ bits}
    {hbi : bIn ≤ 2 ^ bits} {hbw : bWork ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    (subInput : Input ⟨15, inCap, sWork, hsi, hsw⟩)
    (linkedCode : Program ⟨16, bIn, bWork, hbi, hbw⟩)
    (bigInput : Input ⟨16, bIn, bWork, hbi, hbw⟩)
    (inPtrAddr dataPtrAddr : Word bits)
    (inBase dataBase base : Nat) (initData : Array (Word bits))
    (hCfg : SliceConfig ⟨15, inCap, sWork, hsi, hsw⟩ ⟨16, bIn, bWork, hbi, hbw⟩
      inPtrAddr dataPtrAddr inBase dataBase subInput initData)
    (hBody : BodyRelocated (bits := bits) (bigL := ⟨16, bIn, bWork, hbi, hbw⟩)
      rfl inPtrAddr dataPtrAddr subCode linkedCode base)
    (hExitLt : base + 4 * subCode.size < linkedCode.size) :
    ∀ (fuel : Nat) (subS : State ⟨15, inCap, sWork, hsi, hsw⟩)
      (r : Result ⟨15, inCap, sWork, hsi, hsw⟩)
      (bigS : State ⟨16, bIn, bWork, hbi, hbw⟩),
      run subCode subInput fuel subS = some r →
      SliceSim rfl rfl dataBase base initData subS bigS →
      ∃ (m : Nat) (bigT : State ⟨16, bIn, bWork, hbi, hbw⟩),
        m ≤ 4 * r.executed ∧
        Steps linkedCode bigInput m bigS bigT ∧
        bigT.pc = base + 4 * subCode.size ∧
        (∀ i : Fin 15, bigT.regs[i.val]? = r.finalState.regs[i.val]?) ∧
        (∀ j : Nat, j < sWork → bigT.data[dataBase + j]? = r.finalState.data[j]?) ∧
        (∀ w : Nat, (w < dataBase ∨ dataBase + sWork ≤ w) →
          bigT.data[w]? = initData[w]?) := by
  intro fuel
  induction fuel with
  | zero =>
    intro subS r bigS hRun _
    simp [run] at hRun
  | succ n ih =>
    intro subS r bigS hRun hSim
    cases hStep : step subCode subInput subS with
    | none => simp [run, hStep] at hRun
    | some trans =>
      cases trans with
      | halted subT =>
        have hEq : (⟨subT, 1⟩ : Result ⟨15, inCap, sWork, hsi, hsw⟩) = r := by
          simpa [run, hStep] using hRun
        subst r
        obtain ⟨bigT, hst, hpc, hregs, hdata, hframe⟩ :=
          step_lift_halt subCode subInput linkedCode bigInput inPtrAddr dataPtrAddr
            dataBase base initData hBody hExitLt hStep hSim
        exact ⟨1, bigT, by dsimp; decide, hst, hpc, hregs, hdata, hframe⟩
      | next subMid =>
        cases hTail : run subCode subInput n subMid with
        | none => simp [run, hStep, hTail] at hRun
        | some q =>
          have hEq : { q with executed := q.executed + 1 } = r := by
            simpa [run, hStep, hTail] using hRun
          subst r
          obtain ⟨m₁, bigMid, hm₁, hst₁, hSimMid⟩ :=
            step_lift_one subCode subInput linkedCode bigInput inPtrAddr dataPtrAddr
              inBase dataBase base initData hCfg hBody hExitLt hStep hSim
          obtain ⟨m₂, bigT, hm₂, hst₂, hpc, hregs, hdata, hframe⟩ :=
            ih subMid q bigMid hTail hSimMid
          exact ⟨m₁ + m₂, bigT, by dsimp; omega, hst₁.append hst₂, hpc, hregs, hdata, hframe⟩

/-- Exact relocated simulation & frame theorem: any 15-register `subCode` placed
via `BodyRelocated` at `base` inside `linkedCode` simulates a successful `run`
to exit PC `base + 4 * subCode.size` in `≤ 4 * r.executed` steps, preserving all
memory outside `[dataBase, dataBase + subL.workCap)`. -/
theorem liftProgram_relocated_steps {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (subCode : Program subL) (subInput : Input subL)
    (linkedCode : Program bigL) (bigInput : Input bigL)
    (inPtrAddr dataPtrAddr : Word bits)
    (inBase dataBase base : Nat)
    (fuel : Nat) (subStart : State subL) (r : Result subL) (bigStart : State bigL)
    (hRun : run subCode subInput fuel subStart = some r)
    (hCfg : SliceConfig subL bigL inPtrAddr dataPtrAddr inBase dataBase subInput bigStart.data)
    (hBody : BodyRelocated hBig inPtrAddr dataPtrAddr (castProg hSub subCode) linkedCode base)
    (hExitLt : base + 4 * subCode.size < linkedCode.size)
    (hSim : SliceSim hSub hBig dataBase base bigStart.data subStart bigStart) :
    ∃ (m : Nat) (bigT : State bigL),
      m ≤ 4 * r.executed ∧
      Steps linkedCode bigInput m bigStart bigT ∧
      bigT.pc = base + 4 * subCode.size ∧
      (∀ i : Fin 15, bigT.regs[i.val]? = r.finalState.regs[i.val]?) ∧
      (∀ j : Nat, j < subL.workCap → bigT.data[dataBase + j]? = r.finalState.data[j]?) ∧
      (∀ w : Nat, (w < dataBase ∨ dataBase + subL.workCap ≤ w) →
        bigT.data[w]? = bigStart.data[w]?) := by
  rcases subL with ⟨rSub, inCap, sWork, hsi, hsw⟩
  rcases bigL with ⟨rBig, bIn, bWork, hbi, hbw⟩
  cases hSub
  cases hBig
  exact liftCode_steps_aux subCode subInput linkedCode bigInput inPtrAddr dataPtrAddr
    inBase dataBase base bigStart.data hCfg hBody hExitLt fuel subStart r bigStart hRun hSim

/-- Standalone `run` simulation & frame theorem for `liftProgram`: halts at
`pc = 4 * subCode.size` in `m ≤ 4 * r.executed + 1` steps, producing a
`SuccessfulTrace` with exact `tracePeakWords = footprint bigL` and exact
preservation outside `[dataBase, dataBase + subL.workCap)`. -/
theorem liftProgram_run {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    (subCode : Program subL) (subInput : Input subL) (bigInput : Input bigL)
    (inPtrAddr dataPtrAddr : Word bits) (inBase dataBase : Nat)
    (fuel : Nat) (subStart : State subL) (r : Result subL) (bigStart : State bigL)
    (hRun : run subCode subInput fuel subStart = some r)
    (hCfg : SliceConfig subL bigL inPtrAddr dataPtrAddr inBase dataBase subInput bigStart.data)
    (hSim : SliceSim hSub hBig dataBase 0 bigStart.data subStart bigStart) :
    let code := liftProgram hSub hBig inPtrAddr dataPtrAddr subCode
    ∃ (m : Nat) (bigT : State bigL) (trace : List (State bigL)),
      m ≤ 4 * r.executed + 1 ∧
      run code bigInput m bigStart = some ⟨bigT, m⟩ ∧
      SuccessfulTrace code bigInput bigStart trace ⟨bigT, m⟩ ∧
      tracePeakWords bigInput trace = footprint bigL ∧
      bigT.pc = 4 * subCode.size ∧
      (∀ i : Fin 15, bigT.regs[i.val]? = r.finalState.regs[i.val]?) ∧
      (∀ j : Nat, j < subL.workCap → bigT.data[dataBase + j]? = r.finalState.data[j]?) ∧
      (∀ w : Nat, (w < dataBase ∨ dataBase + subL.workCap ≤ w) →
        bigT.data[w]? = bigStart.data[w]?) := by
  intro code
  have hExitLt : 0 + 4 * subCode.size < code.size := by
    rw [liftProgram_size hSub hBig inPtrAddr dataPtrAddr subCode]; omega
  obtain ⟨m₀, bigT, hm₀, hst, hpc, hregs, hdata, hframe⟩ :=
    liftProgram_relocated_steps hSub hBig subCode subInput code bigInput inPtrAddr dataPtrAddr
      inBase dataBase 0 fuel subStart r bigStart hRun hCfg
      (by
        rcases subL with ⟨rSub, _, _, _, _⟩
        rcases bigL with ⟨rBig, _, _, _, _⟩
        cases hSub; cases hBig
        exact bodyRelocated_self rfl inPtrAddr dataPtrAddr subCode)
      hExitLt hSim
  have hExitFetch : code[bigT.pc]? = some .halt := by
    rw [hpc]
    simpa only [Nat.zero_add] using liftProgram_exit hSub hBig inPtrAddr dataPtrAddr subCode
  have hRunBig : run code bigInput (m₀ + 1) bigStart = some ⟨bigT, m₀ + 1⟩ :=
    hst.halts (step_halt_at hExitFetch)
  obtain ⟨trace, hTrace⟩ := run_has_successfulTrace hRunBig
  exact ⟨m₀ + 1, bigT, trace, by omega, hRunBig, hTrace, hTrace.peak_eq,
    by simpa only [Nat.zero_add] using hpc, hregs, hdata, hframe⟩

end Simulation

section RawForestSlice

/-- One-shot specialization of `PaperB.RamForestProgram.RawBuild.run_raw_forest_build`
through `liftProgram`: runs `rawForestBuildProgram` inside a 16-register outer
machine on `[inBase, inBase + subInCap)` and `[dataBase, dataBase + subWorkCap)`,
writing `packedPayload w` at `[dataBase, dataBase + w.wordCount)` in
`≤ 46649 * ((H.vertexCount + H.arcCount) * L ^ 2)` steps while preserving all
outer work memory outside `[dataBase, dataBase + subWorkCap)`. -/
theorem run_raw_forest_build_slice {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat) (acyc : H.IsAcyclic)
    {subInCap subWorkCap bigInCap bigWorkCap : Nat}
    {hsi : subInCap ≤ 2 ^ bits} {hsw : subWorkCap ≤ 2 ^ bits}
    {hbi : bigInCap ≤ 2 ^ bits} {hbw : bigWorkCap ≤ 2 ^ bits}
    (subInput : Input (RamForestProgram.layout bits subInCap subWorkCap hsi hsw))
    (hRaw : RawQuotientInput subInput H)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ subWorkCap)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits)
    (bigInput : Input ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)
    (inPtrAddr dataPtrAddr : Word bits) (inBase dataBase : Nat)
    (bigStart : State ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)
    (hpc : bigStart.pc = 0)
    (hCfg : SliceConfig (RamForestProgram.layout bits subInCap subWorkCap hsi hsw)
      ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩
      inPtrAddr dataPtrAddr inBase dataBase subInput bigStart.data) :
    let subCode := rawForestBuildProgram hsi hsw h8
    let code := liftProgram (bits := bits)
      (subL := RamForestProgram.layout bits subInCap subWorkCap hsi hsw)
      (bigL := ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)
      rfl rfl inPtrAddr dataPtrAddr subCode
    let L := OracleContract.L H.vertexCount
    ∃ (w : WordColumns bits) (bigT : State ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)
      (trace : List (State ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)) (steps : Nat),
      w.wordCount ≤ subWorkCap ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      w.wordCount ≤ 19 * H.vertexCount ∧
      steps ≤ 46649 * ((H.vertexCount + H.arcCount) * L ^ 2) ∧
      SerializedProperLossIndex H w ∧
      run code bigInput steps bigStart = some ⟨bigT, steps⟩ ∧
      SuccessfulTrace code bigInput bigStart trace ⟨bigT, steps⟩ ∧
      tracePeakWords bigInput trace = bigInCap + bigWorkCap + 16 ∧
      bigT.pc = 4 * subCode.size ∧
      (∀ j : Nat, j < w.wordCount →
        bigT.data[dataBase + j]? = (packedPayload w)[j]?) ∧
      (∀ wIdx : Nat, (wIdx < dataBase ∨ dataBase + subWorkCap ≤ wIdx) →
        bigT.data[wIdx]? = bigStart.data[wIdx]?) := by
  intro subCode code L
  let s₀ : State (RamForestProgram.layout bits subInCap subWorkCap hsi hsw) :=
    { regs := Array.ofFn fun i : Fin 15 =>
        bigStart.regs[i.val]'(by rw [bigStart.regs_size]; exact Nat.lt_succ_of_lt i.isLt)
      data := Array.ofFn fun j : Fin subWorkCap =>
        bigStart.data[dataBase + j.val]'(by
          rw [bigStart.data_size]
          dsimp only
          have h1 : dataBase + subWorkCap ≤ bigWorkCap := hCfg.dataFit
          have hjLt : j.val < subWorkCap := j.isLt
          omega)
      pc := 0
      regs_size := by simp
      data_size := by simp }
  obtain ⟨w, tSub, _, work, hwCap, hExt, hWorkLe, _, hw18, hw19, hIdx, hRunSub, _⟩ :=
    run_raw_forest_build h8 H flat acyc subInput hRaw hWork hWidth s₀
  have hSim : SliceSim (subL := RamForestProgram.layout bits subInCap subWorkCap hsi hsw)
      (bigL := ⟨16, bigInCap, bigWorkCap, hbi, hbw⟩)
      rfl rfl dataBase 0 bigStart.data (PaperB.RamProgram.FixedROM.Phase.initial s₀) bigStart := by
    refine ⟨by simp [PaperB.RamProgram.FixedROM.Phase.initial, hpc], ?_, ?_, fun _ _ => rfl⟩
    · intro i
      have hbi' : i.val < bigStart.regs.size := by
        rw [bigStart.regs_size]; exact Nat.lt_succ_of_lt i.isLt
      rw [Array.getElem?_eq_getElem hbi']
      simp [PaperB.RamProgram.FixedROM.Phase.initial, s₀, Array.getElem_ofFn]
    · intro j hj
      have hbd : dataBase + j < bigStart.data.size := by
        rw [bigStart.data_size]
        dsimp only
        have h1 : dataBase + subWorkCap ≤ bigWorkCap := hCfg.dataFit
        have hj' : j < subWorkCap := hj
        omega
      rw [Array.getElem?_eq_getElem hbd]
      simp [PaperB.RamProgram.FixedROM.Phase.initial, s₀, Array.getElem_ofFn, hj]
  obtain ⟨m, bigT, trace, hmLe, hRunBig, hTraceBig, hPeakBig, hpcT, _, hDataT, hFrameT⟩ :=
    liftProgram_run rfl rfl subCode subInput bigInput inPtrAddr dataPtrAddr inBase dataBase
      work (PaperB.RamProgram.FixedROM.Phase.initial s₀) ⟨tSub, work⟩ bigStart hRunSub hCfg hSim
  have hpos : 1 ≤ H.vertexCount := Fin.pos H.root
  have hLpos : 1 ≤ L := OracleContract.one_le_L H.vertexCount
  have hMulPos : 1 ≤ (H.vertexCount + H.arcCount) * L ^ 2 :=
    Nat.mul_pos (by omega) (Nat.pow_pos hLpos)
  have hmBound : m ≤ 46649 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
    have h4 : 4 * work + 1 ≤ 4 * (11662 * ((H.vertexCount + H.arcCount) * L ^ 2)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 4 hWorkLe) 1
    have hMul : 4 * (11662 * ((H.vertexCount + H.arcCount) * L ^ 2)) + 1 =
        46648 * ((H.vertexCount + H.arcCount) * L ^ 2) + 1 := by
      rw [← Nat.mul_assoc]
    have hStep : 46648 * ((H.vertexCount + H.arcCount) * L ^ 2) + 1 ≤
        46649 * ((H.vertexCount + H.arcCount) * L ^ 2) := by
      rw [show 46649 = 46648 + 1 by decide, Nat.add_mul 46648 1 ((H.vertexCount + H.arcCount) * L ^ 2),
        Nat.one_mul]
      exact Nat.add_le_add_left hMulPos _
    exact Nat.le_trans hmLe (Nat.le_trans h4 (hMul ▸ hStep))
  have hPeakEq : tracePeakWords bigInput trace = bigInCap + bigWorkCap + 16 := by
    change tracePeakWords bigInput trace = bigInCap + bigWorkCap + 16 at hPeakBig
    exact hPeakBig
  refine ⟨w, bigT, trace, m, hwCap, hw18, hw19, hmBound, hIdx, hRunBig, hTraceBig,
    hPeakEq, hpcT, ?_, hFrameT⟩
  intro j hj
  have hjCap : j < (RamForestProgram.layout bits subInCap subWorkCap hsi hsw).workCap :=
    Nat.lt_of_lt_of_le hj hwCap
  rw [hDataT j hjCap, ← hExt]
  have hjSub : j < tSub.data.size := by rw [tSub.data_size]; exact Nat.lt_of_lt_of_le hj hwCap
  rw [Array.getElem?_eq_getElem hjSub]
  have hjExt : j < (tSub.data.extract 0 w.wordCount).size := by
    rw [Array.size_extract, tSub.data_size]
    exact Nat.lt_min.mpr ⟨hj, Nat.lt_of_lt_of_le hj hwCap⟩
  rw [Array.getElem?_eq_getElem hjExt, Array.getElem_extract]
  simp only [Nat.zero_add]

end RawForestSlice

end PaperB.RamDataSliceAdapter
