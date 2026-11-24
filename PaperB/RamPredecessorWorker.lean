module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.Predecessor

open PaperB.Machine (Word)
open PaperB.WordOps (add ltb)

abbrev layout (bits cap : Nat) (hcap : cap ≤ 2 ^ bits) : Layout bits :=
  ⟨7, cap, 0, hcap, Nat.zero_le _⟩

private abbrev rLo   : Fin 7 := ⟨0, by decide⟩
private abbrev rHi   : Fin 7 := ⟨1, by decide⟩
private abbrev rBase : Fin 7 := ⟨2, by decide⟩
private abbrev rKey  : Fin 7 := ⟨3, by decide⟩
private abbrev rMid  : Fin 7 := ⟨4, by decide⟩
private abbrev rTmp  : Fin 7 := ⟨5, by decide⟩
private abbrev rOne  : Fin 7 := ⟨6, by decide⟩

private def suffix (bits : Nat) : List (Instr bits 7) :=
  [ .branchLt rKey rTmp 7 9,
    .mov rHi rMid,
    .goto 0,
    .add rLo rMid rOne,
    .goto 0,
    .halt ]

/-- PC 0 tests the interval, PCs 1–3 compute the midpoint, PCs 4–5
read the input, and PCs 6–10 select and install the new bound. -/
def worker {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) :
    Program (layout bits cap hcap) :=
  ([Instr.branchLt rLo rHi 1 11] ++
    (ramMidpoint (L := layout bits cap hcap) rMid rLo rHi ++
      (indexedInputRead (w := bits) rTmp rBase rMid ++ suffix bits))).toArray

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}

local notation "SL" => layout bits cap hcap
local notation "WorkerCode" => worker (bits := bits) (cap := cap) hcap

@[simp] theorem worker_size : (WorkerCode).size = 12 := by
  simp [worker, ramMidpoint, indexedInputRead, suffix]

-- `Program L` is `Array (Instr bits L.registerCount)`. The array fetch
-- therefore reads the same position in the list used to build the program.
private theorem worker_fetch (i : Nat) :
    WorkerCode[i]? =
      ([Instr.branchLt rLo rHi 1 11] ++
        (ramMidpoint (L := SL) rMid rLo rHi ++
          (indexedInputRead (w := bits) rTmp rBase rMid ++ suffix bits)))[i]? := by
  let ops : List (Instr bits 7) :=
    [Instr.branchLt rLo rHi 1 11] ++
      (ramMidpoint (L := SL) rMid rLo rHi ++
        (indexedInputRead (w := bits) rTmp rBase rMid ++ suffix bits))
  calc
    WorkerCode[i]? = (ops.toArray)[i]? := rfl
    _ = ops[i]? := by simp

private theorem fetch_zero :
    WorkerCode[0]? = some (Instr.branchLt rLo rHi 1 11) := by
  rfl

private theorem midpoint_placed :
    Placed (L := SL) WorkerCode 1 (ramMidpoint (L := SL) rMid rLo rHi) := by
  simpa only [worker, List.length_cons, List.length_nil] using
    (placed_link (L := SL) [Instr.branchLt rLo rHi 1 11]
      (ramMidpoint (L := SL) rMid rLo rHi)
      (indexedInputRead (w := bits) rTmp rBase rMid ++ suffix bits))

private theorem read_placed :
    Placed (L := SL) WorkerCode 4 (indexedInputRead (w := bits) rTmp rBase rMid) := by
  exact
    (placed_link (L := SL)
      ([Instr.branchLt rLo rHi 1 11] ++ ramMidpoint (L := SL) rMid rLo rHi)
      (indexedInputRead (w := bits) rTmp rBase rMid) (suffix bits))

structure Slice (input : Input SL) where
  base : Word bits
  len : Nat
  fits : base.val + len < 2 ^ bits
  within : base.val + len ≤ cap

private theorem physical_position {input : Input SL}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    {i : Nat} (hi : i < p.len) :
    p.base.val + i < cap :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi p.base.val) p.within

def Slice.get {input : Input SL}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (i : Nat) (hi : i < p.len) : Word bits :=
  input.words[p.base.val + i]'(by
    -- `Input` declares `size_eq : words.size = L.inputCap`.
    have hsize : input.words.size = cap := input.size_eq
    rw [hsize]
    exact physical_position p hi)

def Slice.Sorted {input : Input SL}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input) : Prop :=
  ∀ (i j : Nat) (hi : i < p.len) (hj : j < p.len), i ≤ j →
    (Slice.get (bits := bits) (cap := cap) (hcap := hcap) p i hi).val ≤
    (Slice.get (bits := bits) (cap := cap) (hcap := hcap) p j hj).val

private def zeroWord (x : Word bits) : Word bits :=
  ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt⟩

-- At width zero a live interval is impossible, so this register is not used.
private def oneWord (x : Word bits) : Word bits :=
  if h : 1 < 2 ^ bits then ⟨1, h⟩ else zeroWord x

/-- The calling convention: lo = 0, hi = len, with two scratch registers. -/
def init {input : Input SL}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (key : Word bits) : State SL where
  regs := #[zeroWord p.base,
    ⟨p.len, by have h := p.fits; omega⟩,
    p.base, key, zeroWord p.base, zeroWord p.base, oneWord p.base]
  data := #[]
  pc := 0
  regs_size := rfl
  data_size := rfl

def lower (s : State SL) : Nat := (reg s rLo).val
def upper (s : State SL) : Nat := (reg s rHi).val
def midpoint (s : State SL) : Nat := lower s + (upper s - lower s) / 2

theorem midpoint_lt_upper {s : State SL} (h : lower s < upper s) :
    midpoint s < upper s := by
  unfold midpoint
  omega

structure Head {input : Input SL}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (key : Word bits) (s : State SL) : Prop where
  pc_zero : s.pc = 0
  base_reg : reg s rBase = p.base
  key_reg : reg s rKey = key
  one_reg : reg s rOne = oneWord p.base
  ordered : lower s ≤ upper s
  inSlice : upper s ≤ p.len

private def put (s : State SL) (dst : Fin 7) (w : Word bits) : State SL :=
  let h : dst.val < s.regs.size := by simpa only [s.regs_size] using dst.isLt
  { s with
    regs := s.regs.set dst.val w h
    regs_size := by simp only [Array.size_set, s.regs_size]
    pc := s.pc + 1 }

private def read (s : State SL) (r : Fin 7) : Word bits :=
  s.regs[r.val]'(by simpa only [s.regs_size] using r.isLt)

private theorem put_same (s : State SL) (dst : Fin 7) (w : Word bits) :
    reg (put s dst w) dst = w := by
  change read (put s dst w) dst = w
  simp [read, put]

private theorem put_other (s : State SL) (dst r : Fin 7) (w : Word bits)
    (h : r ≠ dst) : reg (put s dst w) r = reg s r := by
  have hv : r.val ≠ dst.val := fun e => h (Fin.ext e)
  change read (put s dst w) r = read s r
  simp [read, put, Array.getElem_set, Ne.symm hv]

private theorem mov_step {input : Input SL} {s : State SL} {dst src : Fin 7}
    (hf : WorkerCode[s.pc]? = some (Instr.mov dst src))
    (hn : s.pc + 1 < (WorkerCode).size) :
    step WorkerCode input s = some (Transition.next (put s dst (reg s src))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < (WorkerCode).size then
    some (Transition.next (put s dst (reg s src))) else none) = _
  rw [if_pos hn]

private theorem add_step {input : Input SL} {s : State SL} {dst x y : Fin 7}
    (hf : WorkerCode[s.pc]? = some (Instr.add dst x y))
    (hn : s.pc + 1 < (WorkerCode).size) :
    step WorkerCode input s =
      some (Transition.next (put s dst (add (reg s x) (reg s y)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < (WorkerCode).size then
    some (Transition.next (put s dst (add (reg s x) (reg s y)))) else none) = _
  rw [if_pos hn]

private theorem branch_step {input : Input SL} {s : State SL}
    {x y : Fin 7} {yes no dst : Nat}
    (hf : WorkerCode[s.pc]? = some (Instr.branchLt x y yes no))
    (hs : (if ltb (reg s x) (reg s y) then yes else no) = dst)
    (hd : dst < (WorkerCode).size) :
    step WorkerCode input s = some (Transition.next { s with pc := dst }) := by
  have ht : (if ltb (reg s x) (reg s y) then yes else no) < (WorkerCode).size := by
    rw [hs]
    exact hd
  have h := step_branchLt_at (L := SL) (code := WorkerCode) (input := input) hf ht
  rw [hs] at h
  exact h

private theorem cmp_true {x y : Word bits} (h : x.val < y.val) :
    ltb x y = true := by
  simpa only [PaperB.WordOps.ltb_eq_true] using h

private theorem cmp_false {x y : Word bits} (h : ¬ x.val < y.val) :
    ltb x y = false := by
  cases hb : ltb x y with
  | false => rfl
  | true =>
    exact (h (by simpa only [PaperB.WordOps.ltb_eq_true] using hb)).elim

/-- A live iteration executes exactly nine instructions and returns to PC 0.
The comparison is against the entry at the mathematical midpoint. -/
theorem worker_iteration {input : Input SL}
    {p : Slice (bits := bits) (cap := cap) (hcap := hcap) input}
    {key : Word bits} {s : State SL}
    (H : Head p key s) (live : lower s < upper s) :
    ∃ t, Steps WorkerCode input 9 s t ∧ Head p key t ∧ t.data = s.data ∧
      let m := midpoint s
      let e := Slice.get (bits := bits) (cap := cap) (hcap := hcap) p m
        (Nat.lt_of_lt_of_le (midpoint_lt_upper live) H.inSlice)
      (key.val < e.val ∧ lower t = lower s ∧ upper t = m) ∨
      (e.val ≤ key.val ∧ lower t = m + 1 ∧ upper t = upper s) := by
  let m := midpoint s
  have hml : lower s ≤ m := by
    change lower s ≤ lower s + (upper s - lower s) / 2
    omega
  have hmh : m < upper s := midpoint_lt_upper live
  have hmn : m < p.len := Nat.lt_of_lt_of_le hmh H.inSlice
  let e := Slice.get (bits := bits) (cap := cap) (hcap := hcap) p m hmn
  let a : State SL := { s with pc := 1 }
  have h0 : step WorkerCode input s = some (Transition.next a) := by
    have hf : WorkerCode[s.pc]? = some (Instr.branchLt rLo rHi 1 11) := by
      rw [H.pc_zero]
      exact fetch_zero (bits := bits) (cap := cap) (hcap := hcap)
    have hb : ltb (reg s rLo) (reg s rHi) = true := cmp_true live
    exact branch_step (input := input) (dst := 1) hf
      (by rw [hb]; rfl) (by rw [worker_size]; decide)
  obtain ⟨b, hb, bpc, bmid, bkeep, bdata⟩ :=
    ramMidpoint_steps (L := SL) (code := WorkerCode) (input := input)
      (s := a) (entry := 1)
      (midpoint_placed (bits := bits) (cap := cap) (hcap := hcap)) rfl
      (by rw [worker_size]; decide) (by change (4 : Fin 7) ≠ 0; decide) (Nat.le_of_lt live)
  have bm : (reg b rMid).val = m := bmid
  have bb : reg b rBase = p.base :=
    (bkeep rBase (by change (2 : Fin 7) ≠ 4; decide)).trans H.base_reg
  have haddr : p.base.val + m < cap := physical_position p hmn
  obtain ⟨c, hc, cpc, cread, ckeep, cdata⟩ :=
    indexedInputRead_steps (L := SL) (code := WorkerCode) (input := input)
      (s := b) (entry := 4)
      (read_placed (bits := bits) (cap := cap) (hcap := hcap)) bpc
      (by rw [worker_size]; decide) (by rw [bb, bm]; exact haddr)
  have ce : reg c rTmp = e := by
    have hsize : input.words.size = cap := input.size_eq
    have hpos : p.base.val + m < input.words.size := by
      rw [hsize]
      exact haddr
    apply Option.some.inj
    calc
      -- `indexedInputRead_steps` returns `some (reg t dst) =
      -- input.words[(reg s base).val + (reg s index).val]?`.
      some (reg c rTmp) =
          input.words[(reg b rBase).val + (reg b rMid).val]? := cread
      _ = input.words[p.base.val + m]? := by rw [bb, bm]
      _ = some (input.words[p.base.val + m]'hpos) := by
        simp [getElem?_def, hpos]
      _ = some e := rfl
  have cb : reg c rBase = p.base := (ckeep rBase (by change (2 : Fin 7) ≠ 5; decide)).trans bb
  have ck : reg c rKey = key :=
    (ckeep rKey (by change (3 : Fin 7) ≠ 5; decide)).trans ((bkeep rKey (by change (3 : Fin 7) ≠ 4; decide)).trans H.key_reg)
  have co : reg c rOne = oneWord p.base :=
    (ckeep rOne (by change (6 : Fin 7) ≠ 5; decide)).trans ((bkeep rOne (by change (6 : Fin 7) ≠ 4; decide)).trans H.one_reg)
  have cl : lower c = lower s :=
    congrArg Fin.val ((ckeep rLo (by change (0 : Fin 7) ≠ 5; decide)).trans (bkeep rLo (by change (0 : Fin 7) ≠ 4; decide)))
  have ch : upper c = upper s :=
    congrArg Fin.val ((ckeep rHi (by change (1 : Fin 7) ≠ 5; decide)).trans (bkeep rHi (by change (1 : Fin 7) ≠ 4; decide)))
  have cm : (reg c rMid).val = m :=
    (congrArg Fin.val (ckeep rMid (by change (4 : Fin 7) ≠ 5; decide))).trans bm
  have walked : Steps WorkerCode input 6 s c :=
    Steps.cons h0 (hb.append hc)
  have cpc6 : c.pc = 6 := cpc
  have hf6 : WorkerCode[c.pc]? = some (Instr.branchLt rKey rTmp 7 9) := by
    rw [cpc6]
    rfl
  by_cases hcmp : key.val < e.val
  · let d : State SL := { c with pc := 7 }
    have hd : step WorkerCode input c = some (Transition.next d) := by
      have ht : ltb (reg c rKey) (reg c rTmp) = true := by
        rw [ck, ce]
        exact cmp_true hcmp
      exact branch_step (input := input) (dst := 7) hf6
        (by simp [ht]) (by rw [worker_size]; decide)
    let w := reg d rMid
    let v := put d rHi w
    have hf7 : WorkerCode[d.pc]? = some (Instr.mov rHi rMid) := by
      change WorkerCode[7]? = some (Instr.mov rHi rMid)
      rfl
    have hv : step WorkerCode input d = some (Transition.next v) :=
      mov_step (input := input) hf7
        (by rw [worker_size]; change 8 < 12; decide)
    let t : State SL := { v with pc := 0 }
    have hf8 : WorkerCode[v.pc]? = some (Instr.goto 0) := by
      change WorkerCode[8]? = some (Instr.goto 0)
      rfl
    have ht : step WorkerCode input v = some (Transition.next t) :=
      step_goto_at (L := SL) (code := WorkerCode) (input := input) hf8
        (by rw [worker_size]; decide)
    have tl : lower t = lower s :=
      (congrArg Fin.val (put_other d rHi rLo w (by change (0 : Fin 7) ≠ 1; decide))).trans cl
    have th : upper t = m :=
      (congrArg Fin.val (put_same d rHi w)).trans cm
    have hhead : Head p key t := {
      pc_zero := rfl
      base_reg := (put_other d rHi rBase w (by change (2 : Fin 7) ≠ 1; decide)).trans cb
      key_reg := (put_other d rHi rKey w (by change (3 : Fin 7) ≠ 1; decide)).trans ck
      one_reg := (put_other d rHi rOne w (by change (6 : Fin 7) ≠ 1; decide)).trans co
      ordered := by rw [tl, th]; exact hml
      inSlice := by rw [th]; exact Nat.le_of_lt hmn }
    have tailSteps : Steps WorkerCode input 3 c t :=
      Steps.cons hd (Steps.cons hv (Steps.cons ht (Steps.zero t)))
    exact ⟨t, walked.append tailSteps, hhead,
      (show t.data = c.data from rfl).trans (cdata.trans bdata),
      Or.inl ⟨hcmp, tl, th⟩⟩
  · let d : State SL := { c with pc := 9 }
    have hd : step WorkerCode input c = some (Transition.next d) := by
      have ht : ltb (reg c rKey) (reg c rTmp) = false := by
        rw [ck, ce]
        exact cmp_false hcmp
      exact branch_step (input := input) (dst := 9) hf6
        (by simp [ht]) (by rw [worker_size]; decide)
    have hh : upper s < 2 ^ bits := (reg s rHi).isLt
    have h1 : 1 < 2 ^ bits := by omega
    have dOne : (reg d rOne).val = 1 := by
      change (reg c rOne).val = 1
      rw [co]
      simp [oneWord, h1]
    have dMid : (reg d rMid).val = m := cm
    have hadd : (reg d rMid).val + (reg d rOne).val < 2 ^ bits := by
      rw [dMid, dOne]
      omega
    let w := add (reg d rMid) (reg d rOne)
    let v := put d rLo w
    have hf9 : WorkerCode[d.pc]? = some (Instr.add rLo rMid rOne) := by
      change WorkerCode[9]? = some (Instr.add rLo rMid rOne)
      rfl
    have hv : step WorkerCode input d = some (Transition.next v) :=
      add_step (input := input) hf9
        (by rw [worker_size]; change 10 < 12; decide)
    let t : State SL := { v with pc := 0 }
    have hf10 : WorkerCode[v.pc]? = some (Instr.goto 0) := by
      change WorkerCode[10]? = some (Instr.goto 0)
      rfl
    have ht : step WorkerCode input v = some (Transition.next t) :=
      step_goto_at (L := SL) (code := WorkerCode) (input := input) hf10
        (by rw [worker_size]; decide)
    have tl : lower t = m + 1 := by
      calc
        lower t = w.val := congrArg Fin.val (put_same d rLo w)
        _ = (reg d rMid).val + (reg d rOne).val :=
          PaperB.WordOps.add_no_wrap (reg d rMid) (reg d rOne) hadd
        _ = m + 1 := by rw [dMid, dOne]
    have th : upper t = upper s :=
      (congrArg Fin.val (put_other d rLo rHi w (by change (1 : Fin 7) ≠ 0; decide))).trans ch
    have hhead : Head p key t := {
      pc_zero := rfl
      base_reg := (put_other d rLo rBase w (by change (2 : Fin 7) ≠ 0; decide)).trans cb
      key_reg := (put_other d rLo rKey w (by change (3 : Fin 7) ≠ 0; decide)).trans ck
      one_reg := (put_other d rLo rOne w (by change (6 : Fin 7) ≠ 0; decide)).trans co
      ordered := by rw [tl, th]; omega
      inSlice := by rw [th]; exact H.inSlice }
    have tailSteps : Steps WorkerCode input 3 c t :=
      Steps.cons hd (Steps.cons hv (Steps.cons ht (Steps.zero t)))
    exact ⟨t, walked.append tailSteps, hhead,
      (show t.data = c.data from rfl).trans (cdata.trans bdata),
      Or.inr ⟨Nat.le_of_not_gt hcmp, tl, th⟩⟩

/-- On a crossed interval the test and halt are the only instructions.
In particular the output register and work array do not change. -/
theorem worker_crossed {input : Input SL} {s : State SL} (hpc : s.pc = 0)
    (cross : upper s ≤ lower s) :
    run WorkerCode input 2 s = some ⟨{ s with pc := 11 }, 2⟩ := by
  let t : State SL := { s with pc := 11 }
  have hf : WorkerCode[s.pc]? = some (Instr.branchLt rLo rHi 1 11) := by
    rw [hpc]
    exact fetch_zero (bits := bits) (cap := cap) (hcap := hcap)
  have hb : ltb (reg s rLo) (reg s rHi) = false :=
    cmp_false (Nat.not_lt_of_ge cross)
  have hn : step WorkerCode input s = some (Transition.next t) :=
    branch_step (input := input) (dst := 11) hf
      (by rw [hb]; rfl) (by rw [worker_size]; decide)
  have hf11 : WorkerCode[t.pc]? = some (Instr.halt : Instr bits 7) := by
    change WorkerCode[11]? = some (Instr.halt : Instr bits 7)
    rfl
  have hh : step WorkerCode input t = some (Transition.halted t) :=
    step_halt_at (L := SL) (code := WorkerCode) (input := input) hf11
  exact (Steps.cons hn (Steps.zero t)).halts hh

end PaperB.RamProgram.Predecessor
