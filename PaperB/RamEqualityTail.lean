module

public import PaperB.RamConcreteSetup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PaperB.RamProgram.ThreeCalls.EqualityTail

open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)

private def wzero {bits : Nat} (hb : 1 < 2 ^ bits) : Word bits :=
  ⟨0, by omega⟩

def wone {bits : Nat} (hb : 1 < 2 ^ bits) : Word bits :=
  ⟨1, hb⟩

def flag {bits : Nat} (hb : 1 < 2 ^ bits) (b : Bool) : Word bits :=
  if b then wone hb else wzero hb

/-- Instruction offsets are relative to PC 60. The two loads use the
original, read-only input array. -/
def tailCell {bits : Nat} (hb : 1 < 2 ^ bits) : Nat → Instr bits 16
  | 0  => .imm 1 (wzero hb)
  | 1  => .branchLt 1 0 62 75
  | 2  => .imm 2 (wone hb)
  | 3  => .sub 3 0 2
  | 4  => .add 3 13 3
  | 5  => .add 4 7 3
  | 6  => .loadInput 5 4
  | 7  => .add 4 9 3
  | 8  => .loadInput 6 4
  | 9  => .branchLt 5 11 75 70
  | 10 => .branchLt 11 5 75 71
  | 11 => .branchLt 6 12 75 72
  | 12 => .branchLt 12 6 75 73
  | 13 => .imm 0 (wone hb)
  | 14 => .halt
  | 15 => .imm 0 (wzero hb)
  | _  => .halt

variable {bits cap : Nat}

private def linkedCell (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits)
    (setup : Setup bits) (p : Fin 77) : Instr bits 16 :=
  if hp : p.val < 60 then
    (program hcap setup)[p.val]'(by
      rw [program_size]
      omega)
  else
    tailCell hb (p.val - 60)

/-- Keep exactly the old instructions at PCs 0–59, replacing the old halt
at PC 60 with the validation tail. The layout is unchanged. -/
def checkedProgram (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits)
    (setup : Setup bits) : Program (layout bits cap hcap) :=
  Array.ofFn (linkedCell hcap hb setup)

variable (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits) (setup : Setup bits)

@[simp] theorem checkedProgram_size : (checkedProgram hcap hb setup).size = 77 := by
  simp only [checkedProgram, Array.size_ofFn]

theorem fetch_prefix {p : Nat} (hp : p < 60) :
    (checkedProgram hcap hb setup)[p]? = (program hcap setup)[p]? := by
  have h77 : p < 77 := by omega
  have hOld : p < (program hcap setup).size := by
    rw [program_size]
    omega
  simp only [checkedProgram, getElem?_def, Array.size_ofFn, h77, hOld,
    dif_pos, Array.getElem_ofFn, linkedCell, Fin.val_mk, hp]

theorem fetch_tail {p : Nat} (hl : 60 ≤ p) (hh : p < 77) :
    (checkedProgram hcap hb setup)[p]? = some (tailCell hb (p - 60)) := by
  have hn : ¬ p < 60 := by omega
  simp only [checkedProgram, getElem?_def, Array.size_ofFn, hh, dif_pos,
    Array.getElem_ofFn, linkedCell, Fin.val_mk, hn, dite_false]

attribute [local irreducible] checkedProgram

section StepLemmas

variable {L : Layout bits} {code : Program L} {input : Input L}
    {s : State L}

private def put (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private def jump (s : State L) (p : Nat) : State L :=
  { s with pc := p }

private theorem reg_jump (s : State L) (p : Nat) (r : Fin L.registerCount) :
    reg (jump s p) r = reg s r := rfl

private theorem reg_put (s : State L) (d r : Fin L.registerCount)
    (w : Word bits) :
    reg (put s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp [Array.getElem_set]
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, hv, Ne.symm hv]

private theorem imm_at {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then some (Transition.next (put s d w))
    else none) = _
  rw [if_pos hn]

private theorem add_at {d x y : Fin L.registerCount}
    (hf : code[s.pc]? = some (.add d x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d (add (reg s x) (reg s y)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d (add (reg s x) (reg s y)))) else none) = _
  rw [if_pos hn]

private theorem sub_at {d x y : Fin L.registerCount}
    (hf : code[s.pc]? = some (.sub d x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d (sub (reg s x) (reg s y)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d (sub (reg s x) (reg s y)))) else none) = _
  rw [if_pos hn]

private theorem load_at {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw : input.words[(reg s a).val]? = some w) :
    step code input s = some (.next (put s d w)) := by
  unfold step
  rw [hf]
  change (input.words[(reg s a).val]? >>= fun v =>
    if s.pc + 1 < code.size then some (Transition.next (put s d v))
    else none) = _
  rw [hw]
  change (if s.pc + 1 < code.size then some (Transition.next (put s d w))
    else none) = _
  rw [if_pos hn]

private theorem branch_to {x y : Fin L.registerCount} {yes no target : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yes no))
    (hc : (if ltb (reg s x) (reg s y) then yes else no) = target)
    (ht : target < code.size) :
    step code input s = some (.next (jump s target)) := by
  have hbound : (if ltb (reg s x) (reg s y) then yes else no) < code.size := by
    rw [hc]
    exact ht
  simpa only [hc, jump] using step_branchLt_at (input := input) hf hbound

end StepLemmas

private theorem ltb_true {a b : Word bits} (h : a.val < b.val) :
    ltb a b = true := by
  change decide (a.val < b.val) = true
  simp [h]

private theorem ltb_false {a b : Word bits} (h : ¬ a.val < b.val) :
    ltb a b = false := by
  change decide (a.val < b.val) = false
  simp [h]

private theorem add_value {a b : Word bits} (h : a.val + b.val < 2 ^ bits) :
    (add a b).val = a.val + b.val := by
  change (a.val + b.val) % (2 ^ bits) = a.val + b.val
  exact Nat.mod_eq_of_lt h

private theorem sub_value {a b : Word bits} (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  have ha := a.isLt
  have hd : a.val - b.val < 2 ^ bits := by omega
  have hm : ((a.val - b.val) + 2 ^ bits) % (2 ^ bits) = a.val - b.val := by
    calc
      _ = ((a.val - b.val) % (2 ^ bits) + (2 ^ bits) % (2 ^ bits)) %
          (2 ^ bits) := Nat.add_mod _ _ _
      _ = _ := by simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hd]
  first
  | change (a.val + 2 ^ bits - b.val) % (2 ^ bits) = _
    rw [show a.val + 2 ^ bits - b.val = (a.val - b.val) + 2 ^ bits by omega]
    exact hm
  | change (2 ^ bits + a.val - b.val) % (2 ^ bits) = _
    rw [show 2 ^ bits + a.val - b.val = (a.val - b.val) + 2 ^ bits by omega]
    exact hm
  | change (a.val + (2 ^ bits - b.val)) % (2 ^ bits) = _
    have hb' := b.isLt
    rw [show a.val + (2 ^ bits - b.val) = (a.val - b.val) + 2 ^ bits by omega]
    exact hm
  | change (a.val - b.val) % (2 ^ bits) = _
    exact Nat.mod_eq_of_lt hd
  | rfl
  | unfold sub
    simp [h, show ¬ a.val < b.val by omega, Nat.mod_eq_of_lt hd]

/-- The two unsigned branches either fall through together or jump to
rejection at the first strict inequality. -/
private theorem compare_pair {L : Layout bits} {code : Program L}
    {input : Input L} {s : State L} {x y : Fin L.registerCount} {p bad : Nat}
    (hf₁ : code[s.pc]? = some (.branchLt x y bad (p + 1)))
    (hf₂ : code[p + 1]? = some (.branchLt y x bad (p + 2)))
    (h₁ : p + 1 < code.size) (h₂ : p + 2 < code.size) (hr : bad < code.size) :
    (reg s x = reg s y ∧ Steps code input 2 s (jump s (p + 2))) ∨
      (reg s x ≠ reg s y ∧
        ∃ n : Nat, n ≤ 2 ∧ Steps code input n s (jump s bad)) := by
  by_cases hxy : (reg s x).val < (reg s y).val
  · have e : step code input s = some (.next (jump s bad)) :=
      branch_to hf₁ (by simp [ltb_true hxy]) hr
    refine Or.inr ⟨?_, 1, by decide, .cons e (.zero _)⟩
    intro he
    exact (Nat.lt_irrefl (reg s x).val) (by simpa only [← he] using hxy)
  · have e₁ : step code input s = some (.next (jump s (p + 1))) :=
      branch_to hf₁ (by simp [ltb_false hxy]) h₁
    by_cases hyx : (reg s y).val < (reg s x).val
    · have e₂ : step code input (jump s (p + 1)) =
          some (.next (jump s bad)) := by
        apply branch_to (s := jump s (p + 1)) hf₂ _ hr
        simp [reg_jump, ltb_true hyx]
      refine Or.inr ⟨?_, 2, by decide, .cons e₁ (.cons e₂ (.zero _))⟩
      intro he
      exact (Nat.lt_irrefl (reg s x).val) (by simpa only [← he] using hyx)
    · have e₂ : step code input (jump s (p + 1)) =
          some (.next (jump s (p + 2))) := by
        apply branch_to (s := jump s (p + 1)) hf₂ _ h₂
        simp [reg_jump, ltb_false hyx]
      exact Or.inl ⟨Fin.ext (by omega), .cons e₁ (.cons e₂ (.zero _))⟩

def chosenIndex {hcap : cap ≤ 2 ^ bits} (s : State (layout bits cap hcap)) : Nat :=
  (reg s 13).val + (reg s 0).val - 1

/-- Specification on the actual input words and the saved target words.
The two columns use the same zero-based index. -/
def selectedPairMatches {hcap : cap ≤ 2 ^ bits} (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) : Prop :=
  0 < (reg s 0).val ∧
    i.words[(reg s 7).val + chosenIndex s]? = some (reg s 11) ∧
    i.words[(reg s 9).val + chosenIndex s]? = some (reg s 12)

private theorem finish
    {i : Input (layout bits cap hcap)} {t : State (layout bits cap hcap)}
    (b : Bool) (hp : t.pc = if b then 73 else 75) :
    ∃ v, step (checkedProgram hcap hb setup) i t = some (.next v) ∧
      step (checkedProgram hcap hb setup) i v = some (.halted v) ∧
      reg v 0 = flag hb b ∧ reg v 3 = reg t 3 := by
  let v := put t 0 (flag hb b)
  have hf : (checkedProgram hcap hb setup)[t.pc]? = some (.imm 0 (flag hb b)) := by
    rw [hp]
    cases b with
    | false => exact fetch_tail hcap hb setup (p := 75) (by decide) (by decide)
    | true => exact fetch_tail hcap hb setup (p := 73) (by decide) (by decide)
  have hn : t.pc + 1 < (checkedProgram hcap hb setup).size := by
    rw [hp, checkedProgram_size]
    cases b <;> decide
  have hv : v.pc = (if b then 73 else 75) + 1 := by
    change t.pc + 1 = _
    rw [hp]
  have hh : (checkedProgram hcap hb setup)[v.pc]? = some .halt := by
    rw [hv]
    cases b with
    | false => exact fetch_tail hcap hb setup (p := 76) (by decide) (by decide)
    | true => exact fetch_tail hcap hb setup (p := 74) (by decide) (by decide)
  refine ⟨v, imm_at hf hn, step_halt_at hh, ?_, ?_⟩
  · simp [v, reg_put]
  · simp (disch := decide) [v, reg_put]

def TailTrace (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) : Prop :=
  ∃ (n : Nat) (t : State (layout bits cap hcap)) (b : Bool),
    n ≤ 14 ∧
    Steps (checkedProgram hcap hb setup) i n s t ∧
    step (checkedProgram hcap hb setup) i t = some (.halted t) ∧
    reg t 0 = flag hb b ∧ (b = true ↔ selectedPairMatches i s)

/-- `hi` is exclusive. Each column must contain the prefix ending at `hi`,
and the worker's one-based result must lie in the saved interval. -/
def TailTraceWithIndex (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) : Prop :=
  ∃ (n : Nat) (t : State (layout bits cap hcap)) (b : Bool),
    n ≤ 14 ∧
    Steps (checkedProgram hcap hb setup) i n s t ∧
    step (checkedProgram hcap hb setup) i t = some (.halted t) ∧
    reg t 0 = flag hb b ∧
    (b = true ↔ selectedPairMatches i s) ∧
    (b = true → (reg t 3).val = chosenIndex s)

theorem validation_trace_with_index (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 60)
    (hk : (reg s 0).val ≤ (reg s 14).val - (reg s 13).val)
    (hcol₁ : (reg s 7).val + (reg s 14).val ≤ cap)
    (hcol₂ : (reg s 9).val + (reg s 14).val ≤ cap) :
    TailTraceWithIndex hcap hb setup i s := by
  let code := checkedProgram hcap hb setup
  have F (p : Nat) (hl : 60 ≤ p) (hh : p < 77) :
      code[p]? = some (tailCell hb (p - 60)) :=
    fetch_tail hcap hb setup hl hh
  have B (p : Nat) (hp : p < 77) : p < code.size := by
    change p < (checkedProgram hcap hb setup).size
    rw [checkedProgram_size hcap hb setup]
    exact hp
  have close (b : Bool) (m : Nat) (t : State (layout bits cap hcap))
      (hm : m ≤ 13) (ht : Steps code i m s t)
      (hp : t.pc = if b then 73 else 75)
      (hc : b = true ↔ selectedPairMatches i s)
      (hindex : b = true → (reg t 3).val = chosenIndex s) :
      TailTraceWithIndex hcap hb setup i s := by
    obtain ⟨v, en, eh, er, er₃⟩ := finish hcap hb setup (i := i) b hp
    refine ⟨m + 1, v, b, by omega, ht.append (.cons en (.zero v)), eh, er, hc, ?_⟩
    intro htrue
    rw [er₃]
    exact hindex htrue

  let s61 := put s 1 (wzero hb)
  have f60 : code[s.pc]? = some (.imm 1 (wzero hb)) := by
    rw [hpc]
    exact F 60 (by decide) (by decide)
  have e60 : step code i s = some (.next s61) :=
    imm_at f60 (by rw [hpc]; exact B 61 (by decide))
  have f61 : code[s61.pc]? = some (.branchLt 1 0 62 75) := by
    have hp : s61.pc = 61 := by
      change s.pc + 1 = 61
      rw [hpc]
    rw [hp]
    exact F 61 (by decide) (by decide)
  have r61z : reg s61 1 = wzero hb := by simp [s61, reg_put]
  have r61k : reg s61 0 = reg s 0 := by
    simp (disch := decide) [s61, reg_put]
  by_cases hpos : 0 < (reg s 0).val
  · let s62 := jump s61 62
    have q61 : ltb (reg s61 1) (reg s61 0) = true := by
      apply ltb_true
      rw [r61z, r61k]
      exact hpos
    have e61 : step code i s61 = some (.next s62) :=
      branch_to f61 (by simp [q61]) (B 62 (by decide))
    -- The decrement is exact, and the index lies strictly below hi.
    let dm := sub (reg s 0) (wone hb)
    let ix := add (reg s 13) dm
    have hdm : dm.val = (reg s 0).val - 1 :=
      sub_value (show 1 ≤ (reg s 0).val by omega)
    have hixBound : chosenIndex s < (reg s 14).val := by
      unfold chosenIndex
      omega
    have hixFit : (reg s 13).val + dm.val < 2 ^ bits := by
      have hh := (reg s 14).isLt
      unfold chosenIndex at hixBound
      omega
    have hix : ix.val = chosenIndex s := by
      change (add (reg s 13) dm).val = _
      rw [add_value hixFit, hdm]
      unfold chosenIndex
      omega
    -- The mathematical addresses are in the input array and below the modulus.
    let a := add (reg s 7) ix
    let b := add (reg s 9) ix
    have haCap : (reg s 7).val + chosenIndex s < cap := by omega
    have hbCap : (reg s 9).val + chosenIndex s < cap := by omega
    have haFit : (reg s 7).val + ix.val < 2 ^ bits := by
      rw [hix]
      exact Nat.lt_of_lt_of_le haCap hcap
    have hbFit : (reg s 9).val + ix.val < 2 ^ bits := by
      rw [hix]
      exact Nat.lt_of_lt_of_le hbCap hcap
    have ha : a.val = (reg s 7).val + chosenIndex s := by
      change (add (reg s 7) ix).val = _
      rw [add_value haFit, hix]
    have hbAddr : b.val = (reg s 9).val + chosenIndex s := by
      change (add (reg s 9) ix).val = _
      rw [add_value hbFit, hix]
    have haRead : a.val < i.words.size := by
      rw [ha, i.size_eq]
      exact haCap
    have hbRead : b.val < i.words.size := by
      rw [hbAddr, i.size_eq]
      exact hbCap
    let u := i.words[a.val]'haRead
    let v := i.words[b.val]'hbRead
    have hu : i.words[a.val]? = some u := by
      simp only [getElem?_def, haRead, dif_pos, u]
    have hv : i.words[b.val]? = some v := by
      simp only [getElem?_def, hbRead, dif_pos, v]
    have match_iff : selectedPairMatches i s ↔ u = reg s 11 ∧ v = reg s 12 := by
      unfold selectedPairMatches
      rw [← ha, ← hbAddr, hu, hv]
      simp [hpos]
    let s63 := put s62 2 (wone hb)
    let s64 := put s63 3 dm
    let s65 := put s64 3 ix
    let s66 := put s65 4 a
    let s67 := put s66 5 u
    let s68 := put s67 4 b
    let s69 := put s68 6 v
    have e62 : step code i s62 = some (.next s63) :=
      imm_at (F 62 (by decide) (by decide)) (B 63 (by decide))
    have e63 : step code i s63 = some (.next s64) := by
      have he : sub (reg s63 0) (reg s63 2) = dm := by
        simp (disch := decide) [s63, s62, s61, reg_put, reg_jump, dm]
      have hf : code[s63.pc]? = some (.sub 3 0 2) :=
        F 63 (by decide) (by decide)
      simpa only [he, s64] using sub_at (input := i) hf (B 64 (by decide))
    have e64 : step code i s64 = some (.next s65) := by
      have he : add (reg s64 13) (reg s64 3) = ix := by
        simp (disch := decide) [s64, s63, s62, s61, reg_put, reg_jump, ix]
      have hf : code[s64.pc]? = some (.add 3 13 3) :=
        F 64 (by decide) (by decide)
      simpa only [he, s65] using add_at (input := i) hf (B 65 (by decide))
    have e65 : step code i s65 = some (.next s66) := by
      have he : add (reg s65 7) (reg s65 3) = a := by
        simp (disch := decide)
          [s65, s64, s63, s62, s61, reg_put, reg_jump, a]
      have hf : code[s65.pc]? = some (.add 4 7 3) :=
        F 65 (by decide) (by decide)
      simpa only [he, s66] using add_at (input := i) hf (B 66 (by decide))
    have e66 : step code i s66 = some (.next s67) := by
      have ha' : reg s66 4 = a := by simp [s66, reg_put]
      have hread : i.words[(reg s66 4).val]? = some u := by
        simpa only [ha'] using hu
      exact load_at (F 66 (by decide) (by decide)) (B 67 (by decide)) hread
    have e67 : step code i s67 = some (.next s68) := by
      have he : add (reg s67 9) (reg s67 3) = b := by
        simp (disch := decide)
          [s67, s66, s65, s64, s63, s62, s61, reg_put, reg_jump, b]
      have hf : code[s67.pc]? = some (.add 4 9 3) :=
        F 67 (by decide) (by decide)
      simpa only [he, s68] using add_at (input := i) hf (B 68 (by decide))
    have e68 : step code i s68 = some (.next s69) := by
      have hb' : reg s68 4 = b := by simp [s68, reg_put]
      have hread : i.words[(reg s68 4).val]? = some v := by
        simpa only [hb'] using hv
      exact load_at (F 68 (by decide) (by decide)) (B 69 (by decide)) hread
    have pre : Steps code i 9 s s69 :=
      .cons e60 (.cons e61 (.cons e62 (.cons e63 (.cons e64
        (.cons e65 (.cons e66 (.cons e67 (.cons e68 (.zero s69)))))))))
    have ru : reg s69 5 = u := by
      simp (disch := decide) [s69, s68, s67, reg_put]
    have rv : reg s69 6 = v := by simp [s69, reg_put]
    have rt₁ : reg s69 11 = reg s 11 := by
      simp (disch := decide)
        [s69, s68, s67, s66, s65, s64, s63, s62, s61, reg_put, reg_jump]
    have rt₂ : reg s69 12 = reg s 12 := by
      simp (disch := decide)
        [s69, s68, s67, s66, s65, s64, s63, s62, s61, reg_put, reg_jump]
    have r69ix : (reg s69 3).val = chosenIndex s := by
      calc
        (reg s69 3).val = ix.val := by
          simp (disch := decide) [s69, s68, s67, s66, s65, reg_put]
        _ = chosenIndex s := hix
    rcases compare_pair (input := i) (s := s69) (x := 5) (y := 11)
        (p := 69) (bad := 75)
        (F 69 (by decide) (by decide)) (F 70 (by decide) (by decide))
        (B 70 (by decide)) (B 71 (by decide)) (B 75 (by decide)) with
      ⟨eq₁, path₁⟩ | ⟨ne₁, n, hn, path₁⟩
    · rw [ru, rt₁] at eq₁
      rcases compare_pair (input := i) (s := jump s69 71) (x := 6) (y := 12)
          (p := 71) (bad := 75)
          (F 71 (by decide) (by decide)) (F 72 (by decide) (by decide))
          (B 72 (by decide)) (B 73 (by decide)) (B 75 (by decide)) with
        ⟨eq₂, path₂⟩ | ⟨ne₂, n, hn, path₂⟩
      · simp only [reg_jump, rv, rt₂] at eq₂
        refine close true 13 _ (by decide) ((pre.append path₁).append path₂)
          rfl (by simp [match_iff, eq₁, eq₂]) ?_
        intro _
        change (reg (jump (jump s69 71) 73) 3).val = chosenIndex s
        simpa only [reg_jump] using r69ix
      · simp only [reg_jump, rv, rt₂] at ne₂
        have hno : ¬ selectedPairMatches i s := fun hm => ne₂ (match_iff.mp hm).2
        exact close false ((9 + 2) + n) _ (by omega)
          ((pre.append path₁).append path₂) rfl (by simp [hno])
          (by intro h; cases h)
    · rw [ru, rt₁] at ne₁
      have hno : ¬ selectedPairMatches i s := fun hm => ne₁ (match_iff.mp hm).1
      exact close false (9 + n) _ (by omega) (pre.append path₁)
        rfl (by simp [hno]) (by intro h; cases h)
  · have q61 : ltb (reg s61 1) (reg s61 0) = false := by
      apply ltb_false
      rw [r61z, r61k]
      exact hpos
    have e61 : step code i s61 = some (.next (jump s61 75)) :=
      branch_to f61 (by simp [q61]) (B 75 (by decide))
    have hno : ¬ selectedPairMatches i s := fun hm => hpos hm.1
    exact close false 2 _ (by decide) (.cons e60 (.cons e61 (.zero _)))
      rfl (by simp [hno]) (by intro h; cases h)

theorem validation_trace (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 60)
    (hk : (reg s 0).val ≤ (reg s 14).val - (reg s 13).val)
    (hcol₁ : (reg s 7).val + (reg s 14).val ≤ cap)
    (hcol₂ : (reg s 9).val + (reg s 14).val ≤ cap) :
    TailTrace hcap hb setup i s := by
  obtain ⟨n, t, b, hn, hsteps, hhalt, hout, hmatch, _hindex⟩ :=
    validation_trace_with_index hcap hb setup i s hpc hk hcol₁ hcol₂
  exact ⟨n, t, b, hn, hsteps, hhalt, hout, hmatch⟩

theorem validation_correct_with_index (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 60)
    (hk : (reg s 0).val ≤ (reg s 14).val - (reg s 13).val)
    (hcol₁ : (reg s 7).val + (reg s 14).val ≤ cap)
    (hcol₂ : (reg s 9).val + (reg s 14).val ≤ cap) :
    ∃ r : Result (layout bits cap hcap),
      run (checkedProgram hcap hb setup) i 15 s = some r ∧
      (reg r.finalState 0 = wone hb ↔ selectedPairMatches i s) ∧
      (reg r.finalState 0 = wone hb →
        (reg r.finalState 3).val = chosenIndex s) := by
  obtain ⟨n, t, b, hn, hsteps, hhalt, hout, hmatch, hindex⟩ :=
    validation_trace_with_index hcap hb setup i s hpc hk hcol₁ hcol₂
  have last : run (checkedProgram hcap hb setup) i (15 - n) t =
      some (⟨t, 1⟩ : Result (layout bits cap hcap)) := by
    cases he : 15 - n with
    | zero => omega
    | succ m => simp only [run, hhalt]
  have hrun := hsteps.thenRun last
  have hfuel : n + (15 - n) = 15 := by omega
  rw [hfuel] at hrun
  refine ⟨⟨t, n + 1⟩, hrun, ?_⟩
  change (reg t 0 = wone hb ↔ selectedPairMatches i s) ∧
    (reg t 0 = wone hb → (reg t 3).val = chosenIndex s)
  rw [hout]
  cases b with
  | false =>
    have hz : wzero hb ≠ wone hb := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = 1 at hv
      omega
    constructor
    · simpa [flag, hz] using hmatch
    · intro hone
      change wzero hb = wone hb at hone
      exact (hz hone).elim
  | true =>
    exact ⟨by simpa [flag] using hmatch, fun _ => hindex rfl⟩

/-- Fifteen instructions of fuel suffice. The returned Boolean word is one
exactly when the nonzero result selects both saved targets in the input. -/
theorem validation_correct (i : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 60)
    (hk : (reg s 0).val ≤ (reg s 14).val - (reg s 13).val)
    (hcol₁ : (reg s 7).val + (reg s 14).val ≤ cap)
    (hcol₂ : (reg s 9).val + (reg s 14).val ≤ cap) :
    ∃ r : Result (layout bits cap hcap),
      run (checkedProgram hcap hb setup) i 15 s = some r ∧
      (reg r.finalState 0 = wone hb ↔ selectedPairMatches i s) := by
  obtain ⟨n, t, b, hn, hsteps, hhalt, hout, hmatch⟩ :=
    validation_trace hcap hb setup i s hpc hk hcol₁ hcol₂
  have last : run (checkedProgram hcap hb setup) i (15 - n) t =
      some (⟨t, 1⟩ : Result (layout bits cap hcap)) := by
    cases he : 15 - n with
    | zero => omega
    | succ m => simp only [run, hhalt]
  have hrun := hsteps.thenRun last
  have hfuel : n + (15 - n) = 15 := by omega
  rw [hfuel] at hrun
  refine ⟨⟨t, n + 1⟩, hrun, ?_⟩
  change reg t 0 = wone hb ↔ selectedPairMatches i s
  rw [hout]
  cases b with
  | false =>
    have hz : wzero hb ≠ wone hb := by
      intro h
      have hv := congrArg Fin.val h
      change 0 = 1 at hv
      omega
    simpa [flag, hz] using hmatch
  | true =>
    simpa [flag] using hmatch

end PaperB.RamProgram.ThreeCalls.EqualityTail
