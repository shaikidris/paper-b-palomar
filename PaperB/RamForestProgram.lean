module

public import PaperB.RamProgram
public import PaperB.RamForestStack
public import PaperB.RamForestDispatch
public import PaperB.RamPushChildRow
public import PaperB.RamForestDriverCost

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram

open PaperB.RamProgram

abbrev layout (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) : Layout bits :=
  ⟨15, inputCap, workCap, hi, hw⟩

def registers : PaperB.RamPushChildRow.Registers 15 where
  atIndex i := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right 8 7)⟩
  injective := by
    intro a b h
    exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

def cmd          : Fin 15 := 8
def count        : Fin 15 := 9
def clk          : Fin 15 := 10
def tinBase      : Fin 15 := 11
def toutBase     : Fin 15 := 12
def offsetBase   : Fin 15 := 13
def childrenBase : Fin 15 := 14

section

variable {bits inputCap workCap : Nat}

def prepareRow : List (Instr bits 15) :=
  [.add registers.tmp offsetBase cmd,
   .loadData registers.value registers.tmp,
   .add registers.tmp registers.tmp registers.one,
   .loadData registers.remain registers.tmp,
   .sub registers.remain registers.remain registers.value,
   .add registers.childBase childrenBase registers.value]

private abbrev guardPart (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  PaperB.RamForestDriverCost.guardBlock (bits := bits) (L := layout bits inputCap workCap hi hw)
    registers.zero registers.ptr 1 31

private abbrev popPart : List (Instr bits 15) :=
  PaperB.RamForestStack.popCode (w := bits) registers.ptr registers.stackBase cmd registers.one

private abbrev dispatchPart (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  PaperB.RamForestDispatch.dispatchCode (bits := bits) (L := layout bits inputCap workCap hi hw)
    cmd count 5 27

private abbrev enterPart : List (Instr bits 15) :=
  PaperB.RamForestStack.enterCode (w := bits) clk registers.one tinBase cmd registers.tmp

private abbrev pushPart : List (Instr bits 15) :=
  PaperB.RamForestStack.pushCode (w := bits) registers.ptr registers.stackBase
    registers.value registers.one registers.tmp

private abbrev rowPart : List (Instr bits 15) :=
  PaperB.RamPushChildRow.codeBlock (w := bits) registers 18

private abbrev exitPart (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  PaperB.RamForestDispatch.exitCode (bits := bits) (L := layout bits inputCap workCap hi hw)
    cmd count toutBase clk registers.tmp

private abbrev prefix8 (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  guardPart hi hw ++ popPart (bits := bits) ++ dispatchPart hi hw ++ enterPart (bits := bits)

private abbrev tail27 (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  exitPart hi hw ++ [.goto 0] ++ [.halt]

private abbrev tail15 (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  pushPart (bits := bits) ++ rowPart (bits := bits) ++ [.goto 0] ++ tail27 hi hw

private def assembly (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  prefix8 hi hw ++ prepareRow (bits := bits) ++ [.add registers.value count cmd] ++ tail15 hi hw

def program (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  (assembly hi hw).toArray

private abbrev prefix15 (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  prefix8 hi hw ++ prepareRow (bits := bits) ++ [.add registers.value count cmd]

private abbrev prefix26 (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  prefix15 hi hw ++ pushPart (bits := bits) ++ rowPart (bits := bits)

variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}

theorem program_size : (program hi hw).size = 32 := by
  rw [program, List.size_toArray] <;> rfl

private theorem placeAt (pre block suffix : List (Instr bits 15)) (pc : Nat)
    (hpc : pre.length = pc) (hsplit : assembly hi hw = pre ++ (block ++ suffix)) :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) pc block := by
  rw [program, hsplit, ← hpc]
  exact placed_link (bits := bits) (L := layout bits inputCap workCap hi hw) pre block suffix

private theorem fetchAt (pre : List (Instr bits 15)) (op : Instr bits 15)
    (suffix : List (Instr bits 15)) (pc : Nat)
    (hpc : pre.length = pc) (hsplit : assembly hi hw = pre ++ ([op] ++ suffix)) :
    (program hi hw)[pc]? = some op := by
  have h := placeAt (hi := hi) (hw := hw) pre [op] suffix pc hpc hsplit
  simpa only [Nat.add_zero] using h 0 op rfl

theorem guard_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 0
      (PaperB.RamForestDriverCost.guardBlock (bits := bits) (L := layout bits inputCap workCap hi hw)
        registers.zero registers.ptr 1 31) :=
  placeAt (hi := hi) (hw := hw) [] (guardPart hi hw)
    (popPart (bits := bits) ++ dispatchPart hi hw ++ enterPart (bits := bits) ++
      prepareRow (bits := bits) ++ [.add registers.value count cmd] ++ tail15 hi hw)
    0 rfl (by simp only [assembly, prefix8, List.nil_append, List.append_assoc])

theorem pop_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 1
      (PaperB.RamForestStack.popCode (w := bits) registers.ptr registers.stackBase cmd registers.one) :=
  placeAt (hi := hi) (hw := hw) (guardPart hi hw) (popPart (bits := bits))
    (dispatchPart hi hw ++ enterPart (bits := bits) ++ prepareRow (bits := bits) ++
      [.add registers.value count cmd] ++ tail15 hi hw)
    1 rfl (by simp only [assembly, prefix8, List.append_assoc])

theorem dispatch_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 4
      (PaperB.RamForestDispatch.dispatchCode (bits := bits) (L := layout bits inputCap workCap hi hw)
        cmd count 5 27) :=
  placeAt (hi := hi) (hw := hw) (guardPart hi hw ++ popPart (bits := bits))
    (dispatchPart hi hw)
    (enterPart (bits := bits) ++ prepareRow (bits := bits) ++
      [.add registers.value count cmd] ++ tail15 hi hw)
    4 rfl (by simp only [assembly, prefix8, List.append_assoc])

theorem enter_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 5
      (PaperB.RamForestStack.enterCode (w := bits) clk registers.one tinBase cmd registers.tmp) :=
  placeAt (hi := hi) (hw := hw)
    (guardPart hi hw ++ popPart (bits := bits) ++ dispatchPart hi hw) (enterPart (bits := bits))
    (prepareRow (bits := bits) ++ [.add registers.value count cmd] ++ tail15 hi hw)
    5 rfl (by simp only [assembly, prefix8, List.append_assoc])

theorem row_setup_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 8
      (prepareRow (bits := bits)) :=
  placeAt (hi := hi) (hw := hw) (prefix8 hi hw) (prepareRow (bits := bits))
    ([.add registers.value count cmd] ++ tail15 hi hw)
    8 rfl (by simp only [assembly, List.append_assoc])

theorem tag_fetch : (program hi hw)[14]? = some (.add registers.value count cmd) :=
  fetchAt (hi := hi) (hw := hw) (prefix8 hi hw ++ prepareRow (bits := bits))
    (.add registers.value count cmd) (tail15 hi hw)
    14 rfl (by simp only [assembly, List.append_assoc])

theorem push_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 15
      (PaperB.RamForestStack.pushCode (w := bits) registers.ptr registers.stackBase
        registers.value registers.one registers.tmp) :=
  placeAt (hi := hi) (hw := hw) (prefix15 hi hw) (pushPart (bits := bits))
    (rowPart (bits := bits) ++ [.goto 0] ++ tail27 hi hw)
    15 rfl (by simp only [assembly, prefix15, tail15, List.append_assoc])

theorem row_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 18
      (PaperB.RamPushChildRow.codeBlock (w := bits) registers 18) :=
  placeAt (hi := hi) (hw := hw) (prefix15 hi hw ++ pushPart (bits := bits))
    (rowPart (bits := bits)) ([.goto 0] ++ tail27 hi hw)
    18 rfl (by simp only [assembly, prefix15, tail15, List.append_assoc])

theorem enter_back_fetch : (program hi hw)[26]? = some (.goto 0) :=
  fetchAt (hi := hi) (hw := hw) (prefix26 hi hw) (.goto 0) (tail27 hi hw)
    26 rfl (by simp only [assembly, prefix26, prefix15, tail15, List.append_assoc])

theorem exit_placed :
    Placed (L := layout bits inputCap workCap hi hw) (program hi hw) 27
      (PaperB.RamForestDispatch.exitCode (bits := bits) (L := layout bits inputCap workCap hi hw)
        cmd count toutBase clk registers.tmp) :=
  placeAt (hi := hi) (hw := hw) (prefix26 hi hw ++ [.goto 0]) (exitPart hi hw)
    ([.goto 0] ++ [.halt])
    27 rfl (by simp only [assembly, prefix26, prefix15, tail15, tail27, List.append_assoc])

theorem exit_back_fetch : (program hi hw)[30]? = some (.goto 0) :=
  fetchAt (hi := hi) (hw := hw) (prefix26 hi hw ++ [.goto 0] ++ exitPart hi hw) (.goto 0)
    [.halt]
    30 rfl (by simp only [assembly, prefix26, prefix15, tail15, tail27, List.append_assoc])

theorem halt_fetch : (program hi hw)[31]? = some .halt :=
  fetchAt (hi := hi) (hw := hw) (prefix26 hi hw ++ [.goto 0] ++ exitPart hi hw ++ [.goto 0])
    .halt [] 31 rfl
    (by simp only [assembly, prefix26, prefix15, tail15, tail27, List.append_assoc, List.append_nil])

end

theorem program_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) :
    program (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
      program (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ :=
  rfl

end PaperB.RamForestProgram
