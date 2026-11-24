module

public import PaperB.RamProgram
public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.SealedQuery

open PaperB.Machine (Word)

def layoutFor {bits : Nat} (index : Array (Word bits)) (workCap : Nat)
    (hI : index.size ≤ 2 ^ bits) (hWork : workCap ≤ 2 ^ bits) :
    RamProgram.Layout bits where
  registerCount := 4
  inputCap := index.size
  workCap := workCap
  inputFits := hI
  workFits := hWork

/-- The query phase has bytecode and a flat index, but no original graph. -/
structure Phase (bits : Nat) where
  index : Array (Word bits)
  workCap : Nat
  hI : index.size ≤ 2 ^ bits
  hWork : workCap ≤ 2 ^ bits
  code : RamProgram.Program (layoutFor index workCap hI hWork)

namespace Phase

variable {bits : Nat}

def layout (p : Phase bits) : RamProgram.Layout bits :=
  layoutFor p.index p.workCap p.hI p.hWork

/-- Wrap the existing array without copying it into mutable storage. -/
def input (p : Phase bits) : RamProgram.Input p.layout :=
  ⟨p.index, rfl⟩

@[simp] theorem input_words (p : Phase bits) : p.input.words = p.index :=
  rfl

def initialState (p : Phase bits) (q : Params bits) : RamProgram.State p.layout where
  regs := Array.ofFn q.reg
  data := Array.replicate p.workCap (zeroWord bits)
  pc := 0
  regs_size := by simp [layout, layoutFor]
  data_size := by simp [layout, layoutFor]

private def report (p : Phase bits) (s : RamProgram.State p.layout)
    (r : RamProgram.Result p.layout) : Observation :=
  let w := r.finalState.regs[0]'(by
    simpa only [r.finalState.regs_size, layout, layoutFor] using
      (show 0 < (4 : Nat) by decide))
  let nr := s.regs.size
  let nw := s.data.size
  { answer := decide (w.val ≠ 0)
    executed := r.executed
    initializedRegisters := nr
    initializedWorkspace := nw
    operations := r.executed + nr + nw
    words := RamProgram.storageWords p.input s }

/-- Report only successful halts. Charge each executed instruction (including
halt) and one operation per initialized register or workspace word.
The answer test is an observation of the result, not an extra instruction. -/
def observe (p : Phase bits) (q : Params bits) (fuel : Nat) : Option Observation :=
  let s := p.initialState q
  (RamProgram.run p.code p.input fuel s).map (p.report s)

universe u

/-- With the sealed phase and the bounded arguments fixed, an original input
retained by the caller cannot affect the query. The adapter uses only the
parameter projection, and its sole RAM input is `p.index` by `input_words`. -/
theorem originalInput_inaccessible {Original : Type u} (p : Phase bits)
    (fuel : Nat) (x y : Original × Params bits) (h : x.2 = y.2) :
    (fun z : Original × Params bits => p.observe z.2 fuel) x =
      (fun z : Original × Params bits => p.observe z.2 fuel) y :=
  congrArg (fun q => p.observe q fuel) h

theorem observe_counts (p : Phase bits) (q : Params bits) (fuel : Nat)
    {o : Observation} (h : p.observe q fuel = some o) :
    ∃ r : RamProgram.Result p.layout,
      RamProgram.run p.code p.input fuel (p.initialState q) = some r ∧
      o.executed = r.executed ∧
      o.executed ≤ fuel ∧
      o.initializedRegisters = 4 ∧
      o.initializedWorkspace = p.workCap ∧
      o.operations = o.executed + 4 + p.workCap ∧
      o.words = p.index.size + p.workCap + 4 ∧
      RamProgram.storageWords p.input r.finalState = o.words := by
  cases hr : RamProgram.run p.code p.input fuel (p.initialState q) with
  | none => simp only [observe, hr] at h <;> cases h
  | some r =>
    have ho : p.report (p.initialState q) r = o := by
      simp only [observe, hr] at h
      change some (p.report (p.initialState q) r) = some o at h
      exact Option.some.inj h
    subst o
    have hregs : (p.initialState q).regs.size = 4 :=
      (p.initialState q).regs_size
    have hdata : (p.initialState q).data.size = p.workCap :=
      (p.initialState q).data_size
    refine ⟨r, ?_, rfl, RamProgram.run_executed_le hr, hregs, hdata, ?_, ?_, ?_⟩
    · first | exact hr | rfl
    · change r.executed + (p.initialState q).regs.size +
          (p.initialState q).data.size = r.executed + 4 + p.workCap
      rw [hregs, hdata]
    · exact RamProgram.storageWords_eq p.input (p.initialState q)
    · exact (RamProgram.storageWords_eq p.input r.finalState).trans
        (RamProgram.storageWords_eq p.input (p.initialState q)).symm

end Phase
end PaperB.SealedQuery
