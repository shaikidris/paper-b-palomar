module

public import PaperB.SealedQuery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.SealedQueryR

open PaperB.Machine (Word)
open PaperB.SealedQuery (Params Observation)

namespace Phase

variable {bits R : Nat}

@[simp] theorem input_words (p : Phase bits R) : p.input.words = p.index :=
  rfl

theorem initial_abi (p : Phase bits R) (q : Params bits) (i : Fin 4) :
    (p.initialState q).regs[i.val]'(by
      rw [(p.initialState q).regs_size]
      exact Nat.lt_of_lt_of_le i.isLt p.hR) = q.reg i := by
  simp only [initialState, Array.getElem_ofFn, initReg, dif_pos i.isLt]

theorem initial_suffix_zero (p : Phase bits R) (q : Params bits)
    (i : Fin R) (hi : 4 ≤ i.val) :
    ((p.initialState q).regs[i.val]'(by
      rw [(p.initialState q).regs_size]
      exact i.isLt)).val = 0 := by
  simp only [initialState, Array.getElem_ofFn, initReg,
    dif_neg (Nat.not_lt_of_ge hi), zeroWord]

theorem initial_workspace_zero (p : Phase bits R) (q : Params bits)
    (i : Fin p.workCap) :
    ((p.initialState q).data[i.val]'(by
      rw [(p.initialState q).data_size]
      exact i.isLt)).val = 0 := by
  simp only [initialState, Array.getElem_replicate, zeroWord]

universe u

/-- With the compiled phase fixed, a caller's retained original input is
not consulted. The actual machine receives only `p.index` as its input. -/
theorem originalInput_inaccessible {Original : Type u} (p : Phase bits R)
    (fuel : Nat) (x y : Original × Params bits) (h : x.2 = y.2) :
    (fun z : Original × Params bits => p.observe z.2 fuel) x =
      (fun z : Original × Params bits => p.observe z.2 fuel) y :=
  congrArg (fun q => p.observe q fuel) h

theorem observe_counts (p : Phase bits R) (q : Params bits) (fuel : Nat)
    {o : Observation} (h : p.observe q fuel = some o) :
    ∃ r : RamProgram.Result p.layout,
      RamProgram.run p.code p.input fuel (p.initialState q) = some r ∧
      o.executed = r.executed ∧
      o.executed ≤ fuel ∧
      o.initializedRegisters = R ∧
      o.initializedWorkspace = p.workCap ∧
      o.operations = o.executed + R + p.workCap ∧
      o.words = p.index.size + p.workCap + R ∧
      RamProgram.storageWords p.input r.finalState = o.words := by
  cases hr : RamProgram.run p.code p.input fuel (p.initialState q) with
  | none => simp only [observe, hr] at h <;> cases h
  | some r =>
    have ho : p.report (p.initialState q) r = o := by
      simp only [observe, hr] at h
      change some (p.report (p.initialState q) r) = some o at h
      exact Option.some.inj h
    subst o
    have hregs : (p.initialState q).regs.size = R :=
      (p.initialState q).regs_size
    have hdata : (p.initialState q).data.size = p.workCap :=
      (p.initialState q).data_size
    refine ⟨r, ?_, rfl, RamProgram.run_executed_le hr, hregs, hdata, ?_, ?_, ?_⟩
    · first | exact hr | rfl
    · change r.executed + (p.initialState q).regs.size +
          (p.initialState q).data.size = r.executed + R + p.workCap
      rw [hregs, hdata]
    · exact RamProgram.storageWords_eq p.input (p.initialState q)
    · exact (RamProgram.storageWords_eq p.input r.finalState).trans
        (RamProgram.storageWords_eq p.input (p.initialState q)).symm

end Phase

/-- Sixteen registers and no workspace, for linked-pair/LCA bytecode. -/
def layout16 {bits : Nat} (index : Array (Word bits))
    (hI : index.size ≤ 2 ^ bits) : RamProgram.Layout bits :=
  layoutFor 16 (by decide) index 0 hI (Nat.zero_le _)

theorem layout16_sizes {bits : Nat} (index : Array (Word bits))
    (hI : index.size ≤ 2 ^ bits) :
    (layout16 index hI).registerCount = 16 ∧
    (layout16 index hI).inputCap = index.size ∧
    (layout16 index hI).workCap = 0 :=
  ⟨rfl, rfl, rfl⟩

def phase16 {bits : Nat} (index : Array (Word bits))
    (hI : index.size ≤ 2 ^ bits)
    (code : RamProgram.Program (layout16 index hI)) : Phase bits 16 where
  hR := by decide
  index := index
  workCap := 0
  hI := hI
  hWork := Nat.zero_le _
  code := code

theorem phase16_sizes {bits : Nat} (index : Array (Word bits))
    (hI : index.size ≤ 2 ^ bits)
    (code : RamProgram.Program (layout16 index hI)) (q : Params bits) :
    let p := phase16 index hI code
    let s := p.initialState q
    s.regs.size = 16 ∧ s.data.size = 0 ∧
      RamProgram.storageWords p.input s = index.size + 16 := by
  let p := phase16 index hI code
  let s := p.initialState q
  change s.regs.size = 16 ∧ s.data.size = 0 ∧
    RamProgram.storageWords p.input s = index.size + 16
  have hw : RamProgram.storageWords p.input s = index.size + 0 + 16 :=
    RamProgram.storageWords_eq p.input s
  exact ⟨s.regs_size, s.data_size, by simpa only [Nat.add_zero] using hw⟩

end PaperB.SealedQueryR
