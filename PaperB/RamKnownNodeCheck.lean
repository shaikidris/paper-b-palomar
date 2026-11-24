module

public import PaperB.RamProgram
public import PaperB.RamForestPackedFinish
public import PaperB.ForestSlimIndex

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Fixed 16-register read-only word-RAM kernel (`workCap = 0`) for `O(1)`
known-node proper-loss membership (`WordColumns.known` / `Columns.known`),
performing 4 `loadInput` reads and an interval test `entry[a] ≤ entry[label[y]] < stop[a]`
in at most 12 (`≤ 16`) RAM steps.
-/

namespace PaperB.RamProgram.KnownNodeCheck

open PaperB.Machine (Word)
open PaperB.WordOps (add ltb)
open PaperB.LabelledQuotient (CutPair)
open PaperB.RamForestProgram.Finish (packedPrefix packedPayload)
open PaperB.RetainedProperLoss (WordColumns packWordColumns packWordColumns_known ofOrderedReader)
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount)
open _root_.EX24.PreparedSweep (orderedConfig)

/-- Read-only 16-register layout (`workCap = 0`) for `O(1)` known-node queries. -/
abbrev knownCheckLayout (bits inputCap : Nat) (fits : inputCap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, inputCap, 0, fits, Nat.zero_le _⟩

/-- Fixed 14-instruction read-only program computing `entry[a] ≤ entry[label[y]] < stop[a]`.
Input registers at `pc = 0`:
`r1 = a`, `r2 = y`, `r3 = labelsBase`, `r4 = entryBase`, `r5 = stopBase`,
`r6 = 0` (`zero`), `r7 = 1` (`one`).
Output at halt: `r0 = 1` iff `entry[a] ≤ entry[label[y]] < stop[a]`, else `0`. -/
def knownNodeProgram {bits inputCap : Nat} (fits : inputCap ≤ 2 ^ bits) :
    Program (knownCheckLayout bits inputCap fits) :=
  #[.add 8 3 2,
    .loadInput 8 8,
    .add 8 4 8,
    .loadInput 8 8,
    .add 9 4 1,
    .loadInput 9 9,
    .add 10 5 1,
    .loadInput 10 10,
    .branchLt 8 9 12 9,
    .branchLt 8 10 10 12,
    .mov 0 7,
    .halt,
    .mov 0 6,
    .halt]

section Execution

variable {bits inputCap : Nat} {fits : inputCap ≤ 2 ^ bits}
local notation "L" => knownCheckLayout bits inputCap fits

private def putReg (s : State L) (d : Fin 16) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_putReg (s : State L) (d j : Fin 16) (w : Word bits) :
    reg (putReg s d w) j = if j = d then w else reg s j := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hj : j.val < s.regs.size := by simpa only [s.regs_size] using j.isLt
  change (s.regs.set d.val w hd)[j.val]'(by simpa only [Array.size_set] using hj) =
    if j = d then w else s.regs[j.val]'hj
  by_cases he : j = d
  · subst j; simp
  · have hv : j.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, Ne.symm hv]

private theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {dst src : Fin 16} (hf : code[s.pc]? = some (.mov dst src)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst (reg s src))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg s dst (reg s src))) else none) = _
  rw [ite_eq_left hn]

private theorem step_add_put {code : Program L} {input : Input L} {s : State L}
    {dst x y : Fin 16} (hf : code[s.pc]? = some (.add dst x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst (add (reg s x) (reg s y)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg s dst (add (reg s x) (reg s y)))) else none) = _
  rw [ite_eq_left hn]

private theorem step_loadInput_put {code : Program L} {input : Input L} {s : State L}
    {dst addr : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput dst addr))
    (hread : input.words[(reg s addr).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst w)) := by
  have h1 : step code input s =
      (input.words[(reg s addr).val]? >>= fun v =>
        if s.pc + 1 < code.size then some (Transition.next (putReg s dst v)) else none) := by
    unfold step; rw [hf]; rfl
  rw [h1, hread]
  change (if s.pc + 1 < code.size then some (Transition.next (putReg s dst w)) else none) = _
  rw [ite_eq_left hn]

private theorem add_no_wrap (a b : Word bits) (h : a.val + b.val < 2 ^ bits) :
    (add a b).val = a.val + b.val := by
  change (a.val + b.val) % (2 ^ bits) = a.val + b.val
  exact Nat.mod_eq_of_lt h

/-- Exact execution of `knownNodeProgram`: 4 `loadInput` reads followed by the
interval check `entry[a] ≤ entry[label[y]] < stop[a]`, halting in 11 or 12
(`≤ 16`) steps with `r0 = 1` iff inside `[lo, hi)`, leaving `t.data = s.data`. -/
theorem knownNodeProgram_spec
    (input : Input L) (s : State L) (hpc : s.pc = 0)
    {wLabel wKey wLo wHi zeroW oneW : Word bits}
    (hZero : zeroW.val = 0) (hOne : oneW.val = 1)
    (hr6 : reg s 6 = zeroW) (hr7 : reg s 7 = oneW)
    (hLAddr : (reg s 3).val + (reg s 2).val < inputCap)
    (hLRead : input.words[(reg s 3).val + (reg s 2).val]? = some wLabel)
    (hKAddr : (reg s 4).val + wLabel.val < inputCap)
    (hKRead : input.words[(reg s 4).val + wLabel.val]? = some wKey)
    (hLoAddr : (reg s 4).val + (reg s 1).val < inputCap)
    (hLoRead : input.words[(reg s 4).val + (reg s 1).val]? = some wLo)
    (hHiAddr : (reg s 5).val + (reg s 1).val < inputCap)
    (hHiRead : input.words[(reg s 5).val + (reg s 1).val]? = some wHi) :
    let ok := wLo.val ≤ wKey.val ∧ wKey.val < wHi.val
    let steps := if wKey.val < wLo.val then 11 else 12
    ∃ (t : State L) (trace : List (State L)),
      steps ≤ 16 ∧
      run (knownNodeProgram fits) input steps s = some ⟨t, steps⟩ ∧
      SuccessfulTrace (knownNodeProgram fits) input s trace ⟨t, steps⟩ ∧
      tracePeakWords input trace = inputCap + 16 ∧
      reg t 0 = (if ok then oneW else zeroW) ∧
      ((reg t 0).val = 1 ↔ ok) ∧
      t.data = s.data := by
  intro ok steps
  let code := knownNodeProgram fits
  have hsz : code.size = 14 := rfl
  let aL := add (reg s 3) (reg s 2)
  let s1 := putReg s 8 aL
  let s2 := putReg s1 8 wLabel
  let aK := add (reg s 4) wLabel
  let s3 := putReg s2 8 aK
  let s4 := putReg s3 8 wKey
  let aLo := add (reg s 4) (reg s 1)
  let s5 := putReg s4 9 aLo
  let s6 := putReg s5 9 wLo
  let aHi := add (reg s 5) (reg s 1)
  let s7 := putReg s6 10 aHi
  let s8 := putReg s7 10 wHi
  have pc1 : s1.pc = 1 := by change s.pc + 1 = 1; rw [hpc]
  have pc2 : s2.pc = 2 := by change s1.pc + 1 = 2; rw [pc1]
  have pc3 : s3.pc = 3 := by change s2.pc + 1 = 3; rw [pc2]
  have pc4 : s4.pc = 4 := by change s3.pc + 1 = 4; rw [pc3]
  have pc5 : s5.pc = 5 := by change s4.pc + 1 = 5; rw [pc4]
  have pc6 : s6.pc = 6 := by change s5.pc + 1 = 6; rw [pc5]
  have pc7 : s7.pc = 7 := by change s6.pc + 1 = 7; rw [pc6]
  have pc8 : s8.pc = 8 := by change s7.pc + 1 = 8; rw [pc7]
  have k2 (r : Fin 16) (hr : r ≠ 8) : reg s2 r = reg s r := by
    change reg (putReg (putReg s 8 aL) 8 wLabel) r = reg s r
    rw [reg_putReg, ite_eq_right hr, reg_putReg, ite_eq_right hr]
  have k4 (r : Fin 16) (hr : r ≠ 8) : reg s4 r = reg s r := by
    change reg (putReg (putReg s2 8 aK) 8 wKey) r = reg s r
    rw [reg_putReg, ite_eq_right hr, reg_putReg, ite_eq_right hr, k2 r hr]
  have k6 (r : Fin 16) (hr8 : r ≠ 8) (hr9 : r ≠ 9) : reg s6 r = reg s r := by
    change reg (putReg (putReg s4 9 aLo) 9 wLo) r = reg s r
    rw [reg_putReg, ite_eq_right hr9, reg_putReg, ite_eq_right hr9, k4 r hr8]
  have k8 (r : Fin 16) (hr8 : r ≠ 8) (hr9 : r ≠ 9) (hr10 : r ≠ 10) : reg s8 r = reg s r := by
    change reg (putReg (putReg s6 10 aHi) 10 wHi) r = reg s r
    rw [reg_putReg, ite_eq_right hr10, reg_putReg, ite_eq_right hr10, k6 r hr8 hr9]
  have r8_2 : reg s2 8 = wLabel := by
    change reg (putReg s1 8 wLabel) 8 = wLabel; rw [reg_putReg, ite_eq_left rfl]
  have r8_4 : reg s4 8 = wKey := by
    change reg (putReg s3 8 wKey) 8 = wKey; rw [reg_putReg, ite_eq_left rfl]
  have r8_6 : reg s6 8 = wKey := by
    change reg (putReg (putReg s4 9 aLo) 9 wLo) 8 = wKey
    rw [reg_putReg, ite_eq_right (show (8 : Fin 16) ≠ 9 by decide),
      reg_putReg, ite_eq_right (show (8 : Fin 16) ≠ 9 by decide), r8_4]
  have r8_8 : reg s8 8 = wKey := by
    change reg (putReg (putReg s6 10 aHi) 10 wHi) 8 = wKey
    rw [reg_putReg, ite_eq_right (show (8 : Fin 16) ≠ 10 by decide),
      reg_putReg, ite_eq_right (show (8 : Fin 16) ≠ 10 by decide), r8_6]
  have r9_6 : reg s6 9 = wLo := by
    change reg (putReg s5 9 wLo) 9 = wLo; rw [reg_putReg, ite_eq_left rfl]
  have r9_8 : reg s8 9 = wLo := by
    change reg (putReg (putReg s6 10 aHi) 10 wHi) 9 = wLo
    rw [reg_putReg, ite_eq_right (show (9 : Fin 16) ≠ 10 by decide),
      reg_putReg, ite_eq_right (show (9 : Fin 16) ≠ 10 by decide), r9_6]
  have r10_8 : reg s8 10 = wHi := by
    change reg (putReg s7 10 wHi) 10 = wHi; rw [reg_putReg, ite_eq_left rfl]
  have st0 : step code input s = some (.next s1) :=
    step_add_put (by rw [hpc]; rfl) (by rw [hpc, hsz]; exact (show 0 + 1 < 14 by decide))
  have st1 : step code input s1 = some (.next s2) := by
    refine step_loadInput_put (by rw [pc1]; rfl) ?_ (by rw [pc1, hsz]; exact (show 1 + 1 < 14 by decide))
    have hr8_1 : reg s1 8 = aL := by
      change reg (putReg s 8 aL) 8 = aL; rw [reg_putReg, ite_eq_left rfl]
    rw [hr8_1, add_no_wrap _ _ (Nat.lt_of_lt_of_le hLAddr fits)]
    exact hLRead
  have st2 : step code input s2 = some (.next s3) := by
    have h := step_add_put (code := code) (input := input) (s := s2) (dst := 8) (x := 4) (y := 8)
      (by rw [pc2]; rfl) (by rw [pc2, hsz]; exact (show 2 + 1 < 14 by decide))
    simpa only [s3, aK, k2 4 (show (4 : Fin 16) ≠ 8 by decide), r8_2] using h
  have st3 : step code input s3 = some (.next s4) := by
    refine step_loadInput_put (by rw [pc3]; rfl) ?_ (by rw [pc3, hsz]; exact (show 3 + 1 < 14 by decide))
    have hr8_3 : reg s3 8 = aK := by
      change reg (putReg s2 8 aK) 8 = aK; rw [reg_putReg, ite_eq_left rfl]
    rw [hr8_3, add_no_wrap _ _ (Nat.lt_of_lt_of_le hKAddr fits)]
    exact hKRead
  have st4 : step code input s4 = some (.next s5) := by
    have h := step_add_put (code := code) (input := input) (s := s4) (dst := 9) (x := 4) (y := 1)
      (by rw [pc4]; rfl) (by rw [pc4, hsz]; exact (show 4 + 1 < 14 by decide))
    simpa only [s5, aLo, k4 4 (show (4 : Fin 16) ≠ 8 by decide),
      k4 1 (show (1 : Fin 16) ≠ 8 by decide)] using h
  have st5 : step code input s5 = some (.next s6) := by
    refine step_loadInput_put (by rw [pc5]; rfl) ?_ (by rw [pc5, hsz]; exact (show 5 + 1 < 14 by decide))
    have hr9_5 : reg s5 9 = aLo := by
      change reg (putReg s4 9 aLo) 9 = aLo; rw [reg_putReg, ite_eq_left rfl]
    rw [hr9_5, add_no_wrap _ _ (Nat.lt_of_lt_of_le hLoAddr fits)]
    exact hLoRead
  have st6 : step code input s6 = some (.next s7) := by
    have h := step_add_put (code := code) (input := input) (s := s6) (dst := 10) (x := 5) (y := 1)
      (by rw [pc6]; rfl) (by rw [pc6, hsz]; exact (show 6 + 1 < 14 by decide))
    simpa only [s7, aHi, k6 5 (show (5 : Fin 16) ≠ 8 by decide) (show (5 : Fin 16) ≠ 9 by decide),
      k6 1 (show (1 : Fin 16) ≠ 8 by decide) (show (1 : Fin 16) ≠ 9 by decide)] using h
  have st7 : step code input s7 = some (.next s8) := by
    refine step_loadInput_put (by rw [pc7]; rfl) ?_ (by rw [pc7, hsz]; exact (show 7 + 1 < 14 by decide))
    have hr10_7 : reg s7 10 = aHi := by
      change reg (putReg s6 10 aHi) 10 = aHi; rw [reg_putReg, ite_eq_left rfl]
    rw [hr10_7, add_no_wrap _ _ (Nat.lt_of_lt_of_le hHiAddr fits)]
    exact hHiRead
  have p08 : Steps code input 8 s s8 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
      Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <| Steps.zero s8
  have d8 : s8.data = s.data := rfl
  have c8 : ltb (reg s8 8) (reg s8 9) = decide (wKey.val < wLo.val) := by
    rw [r8_8, r9_8]
    change decide (wKey.val < wLo.val) = _
    rfl
  by_cases hlt : wKey.val < wLo.val
  · have hnot : ¬ ok := fun h => (Nat.not_lt_of_ge h.1) hlt
    have f8 : code[s8.pc]? = some (.branchLt 8 9 12 9) := by rw [pc8]; rfl
    have st8 : step code input s8 = some (.next { s8 with pc := 12 }) := by
      simpa [c8, hlt] using
        step_branchLt_at (input := input) f8 (by simp [c8, hlt, hsz])
    let s9 : State L := { s8 with pc := 12 }
    have f9 : code[s9.pc]? = some (.mov 0 6) := rfl
    have st9 := step_mov_at (input := input) f9 (by rw [hsz]; exact (show 12 + 1 < 14 by decide))
    let t := putReg s9 0 (reg s9 6)
    have f10 : code[t.pc]? = some .halt := rfl
    have hh : step code input t = some (.halted t) := step_halt_at f10
    have pAll : Steps code input 10 s t :=
      p08.append (Steps.cons st8 (Steps.cons st9 (Steps.zero t)))
    have exec := pAll.halts hh
    obtain ⟨trace, htr⟩ := run_has_successfulTrace exec
    have hr0 : reg t 0 = zeroW := by
      change reg (putReg s9 0 (reg s9 6)) 0 = zeroW
      rw [reg_putReg, ite_eq_left rfl]
      change reg s8 6 = zeroW
      rw [k8 6 (show (6 : Fin 16) ≠ 8 by decide) (show (6 : Fin 16) ≠ 9 by decide)
        (show (6 : Fin 16) ≠ 10 by decide), hr6]
    have hiff : (reg t 0).val = 1 ↔ ok := by
      rw [hr0, hZero]
      exact ⟨fun h => by omega, fun h => absurd h hnot⟩
    refine ⟨t, trace, ?_, ?_, ?_, ?_, ?_, hiff, rfl⟩
    · simp only [steps, ite_eq_left hlt]; exact (show 11 ≤ 16 by decide)
    · simpa only [steps, ite_eq_left hlt] using exec
    · simpa only [steps, ite_eq_left hlt] using htr
    · simpa only [footprint] using htr.peak_eq
    · simpa only [ok, ite_eq_right hnot] using hr0
  · have hge : wLo.val ≤ wKey.val := Nat.le_of_not_gt hlt
    have f8 : code[s8.pc]? = some (.branchLt 8 9 12 9) := by rw [pc8]; rfl
    have st8 : step code input s8 = some (.next { s8 with pc := 9 }) := by
      simpa [c8, hlt] using
        step_branchLt_at (input := input) f8 (by simp [c8, hlt, hsz])
    let s9 : State L := { s8 with pc := 9 }
    have f9 : code[s9.pc]? = some (.branchLt 8 10 10 12) := rfl
    have c9 : ltb (reg s9 8) (reg s9 10) = decide (wKey.val < wHi.val) := by
      change ltb (reg s8 8) (reg s8 10) = _
      rw [r8_8, r10_8]
      rfl
    by_cases hhi : wKey.val < wHi.val
    · have hok : ok := ⟨hge, hhi⟩
      have st9 : step code input s9 = some (.next { s9 with pc := 10 }) := by
        simpa [c9, hhi] using
          step_branchLt_at (input := input) f9 (by simp [c9, hhi, hsz])
      let s10 : State L := { s9 with pc := 10 }
      have f10 : code[s10.pc]? = some (.mov 0 7) := rfl
      have st10 := step_mov_at (input := input) f10 (by rw [hsz]; exact (show 10 + 1 < 14 by decide))
      let t := putReg s10 0 (reg s10 7)
      have f11 : code[t.pc]? = some .halt := rfl
      have hh : step code input t = some (.halted t) := step_halt_at f11
      have pAll : Steps code input 11 s t :=
        p08.append (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.zero t))))
      have exec := pAll.halts hh
      obtain ⟨trace, htr⟩ := run_has_successfulTrace exec
      have hr0 : reg t 0 = oneW := by
        change reg (putReg s10 0 (reg s10 7)) 0 = oneW
        rw [reg_putReg, ite_eq_left rfl]
        change reg s8 7 = oneW
        rw [k8 7 (show (7 : Fin 16) ≠ 8 by decide) (show (7 : Fin 16) ≠ 9 by decide)
          (show (7 : Fin 16) ≠ 10 by decide), hr7]
      have hiff : (reg t 0).val = 1 ↔ ok := by
        rw [hr0, hOne]
        exact ⟨fun _ => hok, fun _ => rfl⟩
      refine ⟨t, trace, ?_, ?_, ?_, ?_, ?_, hiff, rfl⟩
      · simp only [steps, ite_eq_right hlt]; exact (show 12 ≤ 16 by decide)
      · simpa only [steps, ite_eq_right hlt] using exec
      · simpa only [steps, ite_eq_right hlt] using htr
      · simpa only [footprint] using htr.peak_eq
      · simpa only [ok, ite_eq_left hok] using hr0
    · have hnot : ¬ ok := fun h => hhi h.2
      have st9 : step code input s9 = some (.next { s9 with pc := 12 }) := by
        simpa [c9, hhi] using
          step_branchLt_at (input := input) f9 (by simp [c9, hhi, hsz])
      let s10 : State L := { s9 with pc := 12 }
      have f10 : code[s10.pc]? = some (.mov 0 6) := rfl
      have st10 := step_mov_at (input := input) f10 (by rw [hsz]; exact (show 12 + 1 < 14 by decide))
      let t := putReg s10 0 (reg s10 6)
      have f11 : code[t.pc]? = some .halt := rfl
      have hh : step code input t = some (.halted t) := step_halt_at f11
      have pAll : Steps code input 11 s t :=
        p08.append (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.zero t))))
      have exec := pAll.halts hh
      obtain ⟨trace, htr⟩ := run_has_successfulTrace exec
      have hr0 : reg t 0 = zeroW := by
        change reg (putReg s10 0 (reg s10 6)) 0 = zeroW
        rw [reg_putReg, ite_eq_left rfl]
        change reg s8 6 = zeroW
        rw [k8 6 (show (6 : Fin 16) ≠ 8 by decide) (show (6 : Fin 16) ≠ 9 by decide)
          (show (6 : Fin 16) ≠ 10 by decide), hr6]
      have hiff : (reg t 0).val = 1 ↔ ok := by
        rw [hr0, hZero]
        exact ⟨fun h => by omega, fun h => absurd h hnot⟩
      refine ⟨t, trace, ?_, ?_, ?_, ?_, ?_, hiff, rfl⟩
      · simp only [steps, ite_eq_right hlt]; exact (show 12 ≤ 16 by decide)
      · simpa only [steps, ite_eq_right hlt] using exec
      · simpa only [steps, ite_eq_right hlt] using htr
      · simpa only [footprint] using htr.peak_eq
      · simpa only [ok, ite_eq_right hnot] using hr0

/-- Exact equivalence between `knownNodeProgram` and `WordColumns.known`
when `w.labels`, `w.entry`, and `w.stop` are placed at `labelsBase`,
`entryBase`, `stopBase` in `input.words`. -/
theorem knownNodeProgram_wordColumns_spec
    (w : WordColumns bits) (input : Input L) (s : State L) (hpc : s.pc = 0)
    (labelsBase entryBase stopBase a y : Nat) (zeroW oneW : Word bits)
    (hZero : zeroW.val = 0) (hOne : oneW.val = 1)
    (haE : a < w.entry.size) (haS : a < w.stop.size) (hy : y < w.labels.size)
    (hlE : w.labelAt y < w.entry.size)
    (hr1 : (reg s 1).val = a) (hr2 : (reg s 2).val = y)
    (hr3 : (reg s 3).val = labelsBase) (hr4 : (reg s 4).val = entryBase)
    (hr5 : (reg s 5).val = stopBase) (hr6 : reg s 6 = zeroW) (hr7 : reg s 7 = oneW)
    (hLFit : labelsBase + w.labels.size ≤ inputCap)
    (hEFit : entryBase + w.entry.size ≤ inputCap)
    (hSFit : stopBase + w.stop.size ≤ inputCap)
    (hLabels : ∀ j (hj : j < w.labels.size),
      input.words[labelsBase + j]? = some (w.labels[j]'hj))
    (hEntry : ∀ j (hj : j < w.entry.size),
      input.words[entryBase + j]? = some (w.entry[j]'hj))
    (hStop : ∀ j (hj : j < w.stop.size),
      input.words[stopBase + j]? = some (w.stop[j]'hj)) :
    ∃ (steps : Nat) (t : State L) (trace : List (State L)),
      steps ≤ 16 ∧
      run (knownNodeProgram fits) input steps s = some ⟨t, steps⟩ ∧
      SuccessfulTrace (knownNodeProgram fits) input s trace ⟨t, steps⟩ ∧
      tracePeakWords input trace = inputCap + 16 ∧
      reg t 0 = (if w.known a y then oneW else zeroW) ∧
      ((reg t 0).val = 1 ↔ w.known a y = true) ∧
      t.data = s.data := by
  have hLabVal : w.labelAt y = (w.labels[y]'hy).val := by
    unfold WordColumns.labelAt
    rw [getElem?_pos w.labels y hy, Option.map_some, Option.getD_some]
  have hLAddr : (reg s 3).val + (reg s 2).val < inputCap := by rw [hr3, hr2]; omega
  have hLRead : input.words[(reg s 3).val + (reg s 2).val]? = some (w.labels[y]'hy) := by
    rw [hr3, hr2]; exact hLabels y hy
  have hKAddr : (reg s 4).val + (w.labels[y]'hy).val < inputCap := by
    rw [hr4, ← hLabVal]; omega
  have hKRead : input.words[(reg s 4).val + (w.labels[y]'hy).val]? =
      some (w.entry[w.labelAt y]'hlE) := by
    rw [hr4, ← hLabVal]; exact hEntry (w.labelAt y) hlE
  have hLoAddr : (reg s 4).val + (reg s 1).val < inputCap := by rw [hr4, hr1]; omega
  have hLoRead : input.words[(reg s 4).val + (reg s 1).val]? = some (w.entry[a]'haE) := by
    rw [hr4, hr1]; exact hEntry a haE
  have hHiAddr : (reg s 5).val + (reg s 1).val < inputCap := by rw [hr5, hr1]; omega
  have hHiRead : input.words[(reg s 5).val + (reg s 1).val]? = some (w.stop[a]'haS) := by
    rw [hr5, hr1]; exact hStop a haS
  obtain ⟨t, trace, h16, hrun, htr, hpeak, hr0, hiff, hdata⟩ :=
    knownNodeProgram_spec input s hpc hZero hOne hr6 hr7
      hLAddr hLRead hKAddr hKRead hLoAddr hLoRead hHiAddr hHiRead
  have hKnownEq :
      (w.entry[a]'haE).val ≤ (w.entry[w.labelAt y]'hlE).val ∧
      (w.entry[w.labelAt y]'hlE).val < (w.stop[a]'haS).val ↔
        w.known a y = true := by
    unfold WordColumns.known
    rw [getElem?_pos w.entry (w.labelAt y) hlE, getElem?_pos w.entry a haE,
      getElem?_pos w.stop a haS]
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq]
  have hBoolEq :
      ((w.entry[a]'haE).val ≤ (w.entry[w.labelAt y]'hlE).val ∧
       (w.entry[w.labelAt y]'hlE).val < (w.stop[a]'haS).val) =
      (w.known a y = true) := propext hKnownEq
  refine ⟨_, t, trace, h16, hrun, htr, hpeak, ?_, hiff.trans hKnownEq, hdata⟩
  by_cases hk : w.known a y = true
  · have hok : (w.entry[a]'haE).val ≤ (w.entry[w.labelAt y]'hlE).val ∧
        (w.entry[w.labelAt y]'hlE).val < (w.stop[a]'haS).val := hKnownEq.mpr hk
    simp only [hk, ite_true]
    simp only [hok] at hr0
    exact hr0
  · have hnok : ¬ ((w.entry[a]'haE).val ≤ (w.entry[w.labelAt y]'hlE).val ∧
        (w.entry[w.labelAt y]'hlE).val < (w.stop[a]'haS).val) := fun h => hk (hKnownEq.mp h)
    have hfk : w.known a y = false := Bool.eq_false_iff.mpr hk
    simp only [hfk, Bool.false_eq_true, ite_false]
    simp only [hnok, ite_false] at hr0
    exact hr0

/-- Specialization to `packedPayload w` at offset `0` of `input.words`, linking
directly to `Columns.known` via `packWordColumns_known`. -/
theorem knownNodeProgram_packedPayload_spec
    {H : LabelledQuotient} {p : PaperB.ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount} [DecidableEq (CutPair H)]
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits)
    (input : Input L) (s : State L) (hpc : s.pc = 0)
    (a y : Nat) (zeroW oneW : Word bits)
    (hZero : zeroW.val = 0) (hOne : oneW.val = 1)
    (ha : a < (ofOrderedReader r).entry.size) (hy : y < H.vertexCount)
    (hlab : ((ofOrderedReader r).labels[y]?).getD 0 < (ofOrderedReader r).entry.size)
    (hPayFit : (packWordColumns r cap).wordCount ≤ inputCap)
    (hPayload : ∀ j, j < (packWordColumns r cap).wordCount →
      input.words[j]? = (packedPayload (packWordColumns r cap))[j]?)
    (hr1 : (reg s 1).val = a) (hr2 : (reg s 2).val = y)
    (hr3 : (reg s 3).val = (packWordColumns r cap).dictionary.size +
      (packWordColumns r cap).back.tagAndFirst.size +
      (packWordColumns r cap).back.second.size)
    (hr4 : (reg s 4).val = (packedPrefix (packWordColumns r cap)).size)
    (hr5 : (reg s 5).val = (packedPrefix (packWordColumns r cap)).size +
      (packWordColumns r cap).entry.size)
    (hr6 : reg s 6 = zeroW) (hr7 : reg s 7 = oneW) :
    ∃ (steps : Nat) (t : State L) (trace : List (State L)),
      steps ≤ 16 ∧
      run (knownNodeProgram fits) input steps s = some ⟨t, steps⟩ ∧
      SuccessfulTrace (knownNodeProgram fits) input s trace ⟨t, steps⟩ ∧
      tracePeakWords input trace = inputCap + 16 ∧
      reg t 0 = (if (ofOrderedReader r).known a y then oneW else zeroW) ∧
      ((reg t 0).val = 1 ↔ (ofOrderedReader r).known a y = true) ∧
      t.data = s.data := by
  let w := packWordColumns r cap
  have hLabelsSz : w.labels.size = H.vertexCount := by
    change (BoundedScalarArray.pack (ofOrderedReader r).labels _ _).size = H.vertexCount
    rw [_root_.BoundedScalarArray.size_pack]
    exact r.index.ok.1
  have hEntrySz : w.entry.size = (ofOrderedReader r).entry.size := by
    change (BoundedScalarArray.pack (ofOrderedReader r).entry _ _).size = _
    exact _root_.BoundedScalarArray.size_pack _ _ _
  have hStopSz : w.stop.size = (ofOrderedReader r).stop.size := by
    change (BoundedScalarArray.pack (ofOrderedReader r).stop _ _).size = _
    exact _root_.BoundedScalarArray.size_pack _ _ _
  have he : (ofOrderedReader r).entry.size = nodeCount (orderedConfig p large) r.out :=
    r.index.reader.layout.endpoints.entry.len
  have ht : (ofOrderedReader r).stop.size = nodeCount (orderedConfig p large) r.out :=
    r.index.reader.layout.endpoints.stop.len
  have hESeq : (ofOrderedReader r).stop.size = (ofOrderedReader r).entry.size :=
    ht.trans he.symm
  have hLabAt : w.labelAt y = ((ofOrderedReader r).labels[y]?).getD 0 := by
    change ((BoundedScalarArray.pack (ofOrderedReader r).labels _ _)[y]?.map Fin.val).getD 0 = _
    rw [_root_.BoundedScalarArray.getElem?_pack_map_val]
  have hlE : w.labelAt y < w.entry.size := by rw [hLabAt, hEntrySz]; exact hlab
  have hWC : w.wordCount =
      (packedPrefix w).size + w.entry.size + w.stop.size := by
    simp only [WordColumns.wordCount, packedPrefix, Array.size_append]
  have hPre : (packedPrefix w).size =
      w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size := by
    simp only [packedPrefix, Array.size_append]
  dsimp only [w] at hLabelsSz hEntrySz hStopSz hLabAt hlE hWC hPre
  have hWStopSz : (packWordColumns r cap).stop.size = (packWordColumns r cap).entry.size :=
    hStopSz.trans (hESeq.trans hEntrySz.symm)
  have hLabels : ∀ j (hj : j < (packWordColumns r cap).labels.size),
      input.words[((packWordColumns r cap).dictionary.size +
        (packWordColumns r cap).back.tagAndFirst.size +
        (packWordColumns r cap).back.second.size) + j]? =
        some ((packWordColumns r cap).labels[j]'hj) := by
    intro j hj
    have hlt : ((packWordColumns r cap).dictionary.size +
        (packWordColumns r cap).back.tagAndFirst.size +
        (packWordColumns r cap).back.second.size) + j <
        (packWordColumns r cap).wordCount := by omega
    rw [hPayload _ hlt]
    unfold packedPayload packedPrefix
    rw [Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_right (by simp [Array.size_append]; omega)]
    rw [Array.size_append, Array.size_append, Nat.add_sub_cancel_left]
    exact getElem?_pos (packWordColumns r cap).labels j hj
  have hEntry : ∀ j (hj : j < (packWordColumns r cap).entry.size),
      input.words[(packedPrefix (packWordColumns r cap)).size + j]? =
        some ((packWordColumns r cap).entry[j]'hj) := by
    intro j hj
    have hlt : (packedPrefix (packWordColumns r cap)).size + j <
        (packWordColumns r cap).wordCount := by omega
    rw [hPayload _ hlt]
    unfold packedPayload
    rw [Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact getElem?_pos (packWordColumns r cap).entry j hj
  have hStop : ∀ j (hj : j < (packWordColumns r cap).stop.size),
      input.words[((packedPrefix (packWordColumns r cap)).size +
        (packWordColumns r cap).entry.size) + j]? =
        some ((packWordColumns r cap).stop[j]'hj) := by
    intro j hj
    have hlt : ((packedPrefix (packWordColumns r cap)).size +
        (packWordColumns r cap).entry.size) + j <
        (packWordColumns r cap).wordCount := by omega
    rw [hPayload _ hlt]
    unfold packedPayload
    rw [Array.getElem?_append_right (by rw [Array.size_append]; omega),
      Array.size_append, Nat.add_sub_cancel_left]
    exact getElem?_pos (packWordColumns r cap).stop j hj
  obtain ⟨steps, t, trace, h16, hrun, htr, hpeak, hr0, hiff, hdata⟩ :=
    knownNodeProgram_wordColumns_spec (packWordColumns r cap) input s hpc
      ((packWordColumns r cap).dictionary.size + (packWordColumns r cap).back.tagAndFirst.size +
        (packWordColumns r cap).back.second.size)
      (packedPrefix (packWordColumns r cap)).size
      ((packedPrefix (packWordColumns r cap)).size + (packWordColumns r cap).entry.size)
      a y zeroW oneW hZero hOne (hEntrySz ▸ ha) (hStopSz ▸ hESeq ▸ ha)
      (hLabelsSz ▸ hy) hlE
      hr1 hr2 hr3 hr4 hr5 hr6 hr7 (by omega) (by omega) (by omega)
      hLabels hEntry hStop
  rw [packWordColumns_known r cap a y] at hr0 hiff
  exact ⟨steps, t, trace, h16, hrun, htr, hpeak, hr0, hiff, hdata⟩

end Execution

end PaperB.RamProgram.KnownNodeCheck
