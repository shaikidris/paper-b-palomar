module

public import PaperB.RamForestPhaseLink
public import PaperB.ExitPriorBase
public import PaperB.ExitSealedBase
public import PaperB.OracleContract

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Fixed 16-register read-only word-RAM kernel (`workCap = 0`) compiling
`PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase.run` over contiguous
`depth[u]`, 18-word `storedCodec`-encoded `Stored` records, and 6-word
`ExitSealedBase`-serialized `Values` prior entries.

Loops at most `depth[u] - d` (`≤ 3 * ceilLog2 (n + 2) ≤ 3 * L`) skew-binary
hops via `ExitWordArrayQuery.foldStored_steps_le`, evaluates `Map.eval`
coordinate-wise (`min`/`max`/`.empty`) in registers, and halts in `O(L)` RAM
steps (`≤ 360 * (L n + 1)`) with `r0..r5` holding the exact 6 `Word bits`
encoding `PriorBase.run` via `intervalCodec`.
-/

namespace PaperB.RamProgram.ExitEval

open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute (selectAtDepth foldFused foldFusedAux)
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase

private theorem coordCodec_word_base {bits : Nat} (hTag : TagsFit bits) (c : Coord)
    (hC : (coordCodec hTag).valid c) (i : Fin 3) :
    (coordCodec hTag).encode c hC ⟨i.val, by omega⟩ =
      (intervalCodec hTag).encode c.base hC.1 i := by
  rcases c with ⟨b, s⟩
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

private theorem mapCodec_word_x0 {bits : Nat} (hTag : TagsFit bits) (m : Map)
    (hM : (mapCodec hTag).valid m) (i : Fin 4) :
    (mapCodec hTag).encode m hM ⟨i.val, by omega⟩ =
      (coordCodec hTag).encode m.x0 hM.1 i := by
  rcases m with ⟨c0, c1⟩
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

private theorem mapCodec_word_x1 {bits : Nat} (hTag : TagsFit bits) (m : Map)
    (hM : (mapCodec hTag).valid m) (i : Fin 4) :
    (mapCodec hTag).encode m hM ⟨4 + i.val, by omega⟩ =
      (coordCodec hTag).encode m.x1 hM.2 i := by
  rcases m with ⟨c0, c1⟩
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

private theorem storedCodec_word0 {bits : Nat} (hTag : TagsFit bits) (rec : Stored)
    (hRec : (storedCodec hTag).valid rec) :
    ((storedCodec hTag).encode rec hRec ⟨0, by decide⟩).val = rec.parent := by
  rcases rec with ⟨p, j, pm, jm⟩
  change (word p hRec.1.1).val = p
  simp [Retention.word]

private theorem storedCodec_word1 {bits : Nat} (hTag : TagsFit bits) (rec : Stored)
    (hRec : (storedCodec hTag).valid rec) :
    ((storedCodec hTag).encode rec hRec ⟨1, by decide⟩).val = rec.jump := by
  rcases rec with ⟨p, j, pm, jm⟩
  change (word j hRec.1.2).val = j
  simp [Retention.word]

private theorem storedCodec_word_parentMap {bits : Nat} (hTag : TagsFit bits) (rec : Stored)
    (hRec : (storedCodec hTag).valid rec) (i : Fin 8) :
    (storedCodec hTag).encode rec hRec ⟨2 + i.val, by omega⟩ =
      (mapCodec hTag).encode rec.parentMap hRec.2.1 i := by
  rcases rec with ⟨p, j, pm, jm⟩
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl

private theorem storedCodec_word_jumpMap {bits : Nat} (hTag : TagsFit bits) (rec : Stored)
    (hRec : (storedCodec hTag).valid rec) (i : Fin 8) :
    (storedCodec hTag).encode rec hRec ⟨10 + i.val, by omega⟩ =
      (mapCodec hTag).encode rec.jumpMap hRec.2.2 i := by
  rcases rec with ⟨p, j, pm, jm⟩
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl

/-- Read-only 16-register layout (`workCap = 0`) for `O(L)` exit evaluation. -/
abbrev exitEvalLayout (bits inputCap : Nat) (fits : inputCap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, inputCap, 0, fits, Nat.zero_le _⟩

/-- Exact canonical 3-word `intervalCodec` representation of `x : Interval`
in `(w0, w1, w2)`. -/
def IntervalWords {bits : Nat} (hTag : TagsFit bits) (x : Interval)
    (w0 w1 w2 : Word bits) : Prop :=
  ∃ hx : RankBound (2 ^ bits) x,
    w0 = (intervalCodec hTag).encode x hx 0 ∧
    w1 = (intervalCodec hTag).encode x hx 1 ∧
    w2 = (intervalCodec hTag).encode x hx 2

/-- Exact canonical 6-word representation of `xs : Values` in `r0..r5`. -/
def ValuesRegs {bits inputCap : Nat} {fits : inputCap ≤ 2 ^ bits}
    (hTag : TagsFit bits) (xs : Values)
    (s : State (exitEvalLayout bits inputCap fits)) : Prop :=
  IntervalWords hTag xs.x0 (reg s 0) (reg s 1) (reg s 2) ∧
  IntervalWords hTag xs.x1 (reg s 3) (reg s 4) (reg s 5)

section Helpers

variable {bits inputCap : Nat} {fits : inputCap ≤ 2 ^ bits}
local notation "L" => exitEvalLayout bits inputCap fits

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

private theorem step_imm_put {code : Program L} {input : Input L} {s : State L}
    {dst : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.imm dst w)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst w)) := by
  unfold step; rw [hf]
  change (if s.pc + 1 < code.size then some (Transition.next (putReg s dst w)) else none) = _
  rw [ite_eq_left hn]

private theorem step_mov_put {code : Program L} {input : Input L} {s : State L}
    {dst src : Fin 16} (hf : code[s.pc]? = some (.mov dst src)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst (reg s src))) := by
  unfold step; rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg s dst (reg s src))) else none) = _
  rw [ite_eq_left hn]

private theorem step_add_put {code : Program L} {input : Input L} {s : State L}
    {dst x y : Fin 16} (hf : code[s.pc]? = some (.add dst x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst (add (reg s x) (reg s y)))) := by
  unfold step; rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg s dst (add (reg s x) (reg s y)))) else none) = _
  rw [ite_eq_left hn]

private theorem step_sub_put {code : Program L} {input : Input L} {s : State L}
    {dst x y : Fin 16} (hf : code[s.pc]? = some (.sub dst x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg s dst (sub (reg s x) (reg s y)))) := by
  unfold step; rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (putReg s dst (sub (reg s x) (reg s y)))) else none) = _
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

private theorem sub_no_wrap (a b : Word bits) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  change (2 ^ bits + a.val - b.val) % (2 ^ bits) = a.val - b.val
  have ha := a.isLt
  have hMod : 2 ^ bits + (a.val - b.val) = 2 ^ bits + a.val - b.val := by omega
  rw [← hMod, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

private theorem intervalWords_empty_iff {hTag : TagsFit bits} {x : Interval}
    {w0 w1 w2 : Word bits} (hw : IntervalWords hTag x w0 w1 w2) :
    (x = .empty ↔ w0.val < 1) := by
  rcases hw with ⟨hx, h0, _, _⟩
  cases x with
  | empty =>
    have hv : w0.val = 0 := by rw [h0]; rfl
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  | span lo hi =>
    have hv : w0.val = 1 := by rw [h0]; rfl
    exact ⟨fun h => False.elim (by cases h), fun h => False.elim (by omega)⟩

private theorem intervalWords_span_vals {hTag : TagsFit bits} {lo hi : Nat}
    {w0 w1 w2 : Word bits} (hw : IntervalWords hTag (.span lo hi) w0 w1 w2) :
    w0.val = 1 ∧ w1.val = lo ∧ w2.val = hi := by
  rcases hw with ⟨hx, h0, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl

private theorem intervalWords_mk_empty {hTag : TagsFit bits} {w0 w1 w2 : Word bits}
    (h0 : w0.val = 0) (h1 : w1.val = 0) (h2 : w2.val = 0) :
    IntervalWords hTag .empty w0 w1 w2 := by
  refine ⟨True.intro, ?_, ?_, ?_⟩ <;> apply Fin.ext
  · exact h0
  · exact h1
  · exact h2

private theorem intervalWords_mk_span {hTag : TagsFit bits} {w0 w1 w2 : Word bits}
    (h0 : w0.val = 1) :
    IntervalWords hTag (.span w1.val w2.val) w0 w1 w2 := by
  refine ⟨⟨w1.isLt, w2.isLt⟩, ?_, ?_, ?_⟩ <;> apply Fin.ext
  · exact h0
  · rfl
  · rfl

private theorem intervalWords_join {hTag : TagsFit bits}
    {x y : Interval} {ax0 ax1 ax2 ay0 ay1 ay2 : Word bits}
    (hx : IntervalWords hTag x ax0 ax1 ax2) (hy : IntervalWords hTag y ay0 ay1 ay2) :
    IntervalWords hTag (Interval.join x y)
      (match x with | .empty => ay0 | .span _ _ => ax0)
      (match x, y with
        | .empty, _ => ay1
        | .span _ _, .empty => ax1
        | .span _ _, .span _ _ => if ax1.val < ay1.val then ax1 else ay1)
      (match x, y with
        | .empty, _ => ay2
        | .span _ _, .empty => ax2
        | .span _ _, .span _ _ => if ay2.val < ax2.val then ax2 else ay2) := by
  cases x with
  | empty =>
    simpa [Interval.join] using hy
  | span xlo xhi =>
    obtain ⟨hx0, hx1, hx2⟩ := intervalWords_span_vals hx
    cases y with
    | empty =>
      simpa [Interval.join] using hx
    | span ylo yhi =>
      obtain ⟨hy0, hy1, hy2⟩ := intervalWords_span_vals hy
      simp only [Interval.join]
      have hmin : (if ax1.val < ay1.val then ax1 else ay1).val = min xlo ylo := by
        rw [← hx1, ← hy1]; split <;> omega
      have hmax : (if ay2.val < ax2.val then ax2 else ay2).val = max xhi yhi := by
        rw [← hx2, ← hy2]; split <;> omega
      rw [← hmin, ← hmax]
      exact intervalWords_mk_span hx0

/-! ### Phase Combinator: 3-way Dispatch (`branch3Phase`) -/

private def patchHalt (p : Phase L) (base target : Nat) : Program L :=
  (p.code.map (relocateInstr base)).set p.haltPC (.goto target)
    (by simpa only [Array.size_map] using p.haltFits)

private theorem patchHalt_size (p : Phase L) (base target : Nat) :
    (patchHalt p base target).size = p.code.size := by
  simp [patchHalt, Array.size_set, Array.size_map]

private theorem patchHalt_nonhalt (p : Phase L) (base target : Nat) :
    ∀ (i : Nat) (op : Instr bits 16),
      (patchHalt p base target)[i]? = some op → op ≠ .halt := by
  intro i op hop heq
  subst heq
  by_cases hi : i < p.code.size
  · by_cases hpc : i = p.haltPC
    · have hget : (patchHalt p base target)[i]? = some (.goto target) := by
        rw [hpc]; unfold patchHalt
        exact Array.getElem?_set_self _
      rw [hget] at hop; cases hop
    · unfold patchHalt at hop
      rw [Array.getElem?_set_ne _ (Ne.symm hpc), Array.getElem?_map] at hop
      cases hc : p.code[i]? with
      | none => simp [hc] at hop
      | some orig =>
        rw [hc, Option.map_some] at hop
        have hop' := Option.some.inj hop
        have horig : orig = .halt := by cases orig <;> cases hop' <;> rfl
        exact hpc (p.uniqueHalt i (horig ▸ hc))
  · have hnone : (patchHalt p base target)[i]? = none :=
      Array.getElem?_eq_none (by rw [patchHalt_size]; omega)
    rw [hnone] at hop; cases hop

private theorem patchHalt_exec (p : Phase L) (base target : Nat)
    (code : Program L)
    (hSlice : ∀ j, j < p.code.size →
      code[base + j]? = (patchHalt p base target)[j]?)
    (hTarget : target < code.size)
    {input : Input L} {s u : State L} {steps : Nat}
    (hRun : run p.code input steps (Phase.initial s) = some ⟨u, steps⟩) :
    Steps code input steps (relocateStatePC base (Phase.initial s)) { u with pc := target } := by
  have hSteps := linked_return_of_run_multi (linked := code) (base := base)
    (ret := fun _ => target) hRun
    (fun i op hi hne => by
      have hiLt : i < p.code.size := by
        by_cases h : i < p.code.size; · exact h
        · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hi; cases hi
      have hneHalt : i ≠ p.haltPC := fun e => hne (Option.some.inj (hi.symm.trans (e ▸ p.haltAt)))
      rw [hSlice i hiLt]
      unfold patchHalt
      rw [Array.getElem?_set_ne _ (Ne.symm hneHalt), Array.getElem?_map, hi]
      rfl)
    (fun i hi => by
      have heq := p.uniqueHalt i hi
      rw [heq]
      refine ⟨?_, hTarget⟩
      rw [hSlice p.haltPC p.haltFits]
      unfold patchHalt
      exact Array.getElem?_set_self _)
  exact hSteps

private def branch3Code (hdr : Program L) (p0 p1 p2 : Phase L) : Program L :=
  let b0 := hdr.size
  let b1 := b0 + p0.code.size
  let b2 := b1 + p1.code.size
  let tgt := b2 + p2.code.size
  hdr ++ patchHalt p0 b0 tgt ++ patchHalt p1 b1 tgt ++ patchHalt p2 b2 tgt ++ #[.halt]

private theorem branch3Code_size (hdr : Program L) (p0 p1 p2 : Phase L) :
    (branch3Code hdr p0 p1 p2).size =
      hdr.size + p0.code.size + p1.code.size + p2.code.size + 1 := by
  rw [branch3Code]
  dsimp only
  simp only [Array.size_append, Array.size_singleton]
  rw [patchHalt_size, patchHalt_size, patchHalt_size]

private def branch3Phase (hdr : Program L)
    (hHdr : hdr.toList.all (@nonHalt bits L) = true)
    (p0 p1 p2 : Phase L) : Phase L :=
  let code := branch3Code hdr p0 p1 p2
  let last := hdr.size + p0.code.size + p1.code.size + p2.code.size
  Phase.ofLast code last (branch3Code_size hdr p0 p1 p2)
    (by
      rw [show code = branch3Code hdr p0 p1 p2 from rfl, branch3Code]
      dsimp only
      have hSz : (hdr ++
          patchHalt p0 hdr.size (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
          patchHalt p1 (hdr.size + p0.code.size)
            (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
          patchHalt p2 (hdr.size + p0.code.size + p1.code.size)
            (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size = last := by
        simp only [Array.size_append]
        rw [patchHalt_size, patchHalt_size, patchHalt_size]
      rw [Array.getElem?_append_right (by omega), hSz, Nat.sub_self]
      rfl)
    (by
      have hEq : (hdr ++ patchHalt p0 hdr.size last ++
          patchHalt p1 (hdr.size + p0.code.size) last ++
          patchHalt p2 (hdr.size + p0.code.size + p1.code.size) last).size = last := by
        simp only [Array.size_append]
        rw [patchHalt_size, patchHalt_size, patchHalt_size]
      have htake : (code.toList.take last) =
          hdr.toList ++ (patchHalt p0 hdr.size last).toList ++
            (patchHalt p1 (hdr.size + p0.code.size) last).toList ++
            (patchHalt p2 (hdr.size + p0.code.size + p1.code.size) last).toList := by
        dsimp only [last]
        rw [show code = branch3Code hdr p0 p1 p2 from rfl, branch3Code]
        dsimp only
        rw [Array.toList_append,
          List.take_append_of_le_length (by
            simp only [Array.length_toList]
            exact Nat.le_of_eq (by dsimp only [last] at hEq; exact hEq.symm)),
          List.take_of_length_le (by
            simp only [Array.length_toList]
            exact Nat.le_of_eq (by dsimp only [last] at hEq; exact hEq))]
        simp only [Array.toList_append]
      rw [htake]
      simp only [List.all_append, hHdr, Bool.true_and, Bool.and_eq_true]
      have mkAll : ∀ (p : Phase L) (base : Nat),
          (patchHalt p base last).toList.all (@nonHalt bits L) = true := by
        intro p base
        rw [List.all_eq_true]
        intro op hmem
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
        have hget : (patchHalt p base last)[i]? = some op := by
          rw [← heq]
          exact getElem?_pos _ i (by simpa using hi)
        have hne := patchHalt_nonhalt p base last i op hget
        cases op <;> simp [nonHalt] at hne ⊢
      exact ⟨⟨mkAll p0 _, mkAll p1 _⟩, mkAll p2 _⟩)

/-! ### Phase 1: `baseNonePhase` (reads 3-word interval at `r11` -> `dst`, `r11 += 4`) -/

private def baseNoneCode (hTag : TagsFit bits) (dstTag dstLo dstHi : Fin 16) : Program L :=
  #[.loadInput dstTag 11,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 11 11 15,
    .loadInput dstLo 11,
    .add 11 11 15,
    .loadInput dstHi 11,
    .imm 15 ⟨2, hTag⟩,
    .add 11 11 15,
    .halt]

private def baseNonePhase (hTag : TagsFit bits) (dstTag dstLo dstHi : Fin 16) : Phase L :=
  Phase.ofLast (baseNoneCode hTag dstTag dstLo dstHi) 8 rfl rfl (by
    simp [baseNoneCode, nonHalt])

private theorem baseNonePhase_spec (hTag : TagsFit bits)
    (dstTag dstLo dstHi : Fin 16)
    (hd01 : dstTag ≠ dstLo) (hd02 : dstTag ≠ dstHi) (hd12 : dstLo ≠ dstHi)
    (hd11 : dstTag ≠ 11 ∧ dstLo ≠ 11 ∧ dstHi ≠ 11)
    (hd15 : dstTag ≠ 15 ∧ dstLo ≠ 15 ∧ dstHi ≠ 15)
    (input : Input L) (s : State L) (x : Interval)
    (hx : RankBound (2 ^ bits) x)
    (hAddr : (reg s 11).val + 4 ≤ inputCap)
    (hW0 : input.words[(reg s 11).val]? = some ((intervalCodec hTag).encode x hx 0))
    (hW1 : input.words[(reg s 11).val + 1]? = some ((intervalCodec hTag).encode x hx 1))
    (hW2 : input.words[(reg s 11).val + 2]? = some ((intervalCodec hTag).encode x hx 2)) :
    ∃ t : State L,
      run (baseNonePhase (fits := fits) hTag dstTag dstLo dstHi).code input 9 (Phase.initial s) =
        some ⟨t, 9⟩ ∧
      IntervalWords hTag x (reg t dstTag) (reg t dstLo) (reg t dstHi) ∧
      ((reg s 11).val + 4 < 2 ^ bits → (reg t 11).val = (reg s 11).val + 4) ∧
      (∀ r : Fin 16, r ≠ dstTag → r ≠ dstLo → r ≠ dstHi → r ≠ 11 → r ≠ 15 →
        reg t r = reg s r) ∧
      t.data = s.data := by
  let code := (baseNonePhase (fits := fits) hTag dstTag dstLo dstHi).code
  have hsz : code.size = 9 := rfl
  let s0 := Phase.initial s
  let w0 := (intervalCodec hTag).encode x hx 0
  let w1 := (intervalCodec hTag).encode x hx 1
  let w2 := (intervalCodec hTag).encode x hx 2
  have h4Lt : (reg s 11).val + 4 ≤ 2 ^ bits := Nat.le_trans hAddr fits
  have h15_11 : (15 : Fin 16) ≠ 11 := by decide
  let s1 := putReg s0 dstTag w0
  let s2 := putReg s1 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s3 := putReg s2 11 (add (reg s2 11) (reg s2 15))
  let s4 := putReg s3 dstLo w1
  let s5 := putReg s4 11 (add (reg s4 11) (reg s4 15))
  let s6 := putReg s5 dstHi w2
  let s7 := putReg s6 15 ⟨2, hTag⟩
  let s8 := putReg s7 11 (add (reg s7 11) (reg s7 15))
  have st0 : step code input s0 = some (.next s1) :=
    step_loadInput_put rfl hW0 (by rw [hsz]; exact (show 0 + 1 < 9 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_imm_put rfl (by rw [hsz]; exact (show 1 + 1 < 9 by decide))
  have r11_2 : reg s2 11 = reg s 11 := by
    change reg (putReg (putReg s0 dstTag w0) 15 _) 11 = _
    rw [reg_putReg, ite_eq_right h15_11.symm, reg_putReg, ite_eq_right hd11.1.symm]
    rfl
  have r15_2 : (reg s2 15).val = 1 := by
    change (reg (putReg s1 15 _) 15).val = 1
    rw [reg_putReg, ite_eq_left rfl]
  have r11_3val : (reg s3 11).val = (reg s 11).val + 1 := by
    change (reg (putReg s2 11 (add (reg s2 11) (reg s2 15))) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_2, r15_2]; omega), r11_2, r15_2]
  have st2 : step code input s2 = some (.next s3) :=
    step_add_put rfl (by rw [hsz]; exact (show 2 + 1 < 9 by decide))
  have st3 : step code input s3 = some (.next s4) :=
    step_loadInput_put rfl (by rw [r11_3val]; exact hW1) (by rw [hsz]; exact (show 3 + 1 < 9 by decide))
  have r15_4 : (reg s4 15).val = 1 := by
    change (reg (putReg (putReg s2 11 _) dstLo w1) 15).val = 1
    rw [reg_putReg, ite_eq_right hd15.2.1.symm, reg_putReg, ite_eq_right h15_11, r15_2]
  have r11_4val : (reg s4 11).val = (reg s 11).val + 1 := by
    change (reg (putReg s3 dstLo w1) 11).val = _
    rw [reg_putReg, ite_eq_right hd11.2.1.symm, r11_3val]
  have r11_5val : (reg s5 11).val = (reg s 11).val + 2 := by
    change (reg (putReg s4 11 (add (reg s4 11) (reg s4 15))) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_4val, r15_4]; omega),
      r11_4val, r15_4]
  have st4 : step code input s4 = some (.next s5) :=
    step_add_put rfl (by rw [hsz]; exact (show 4 + 1 < 9 by decide))
  have st5 : step code input s5 = some (.next s6) :=
    step_loadInput_put rfl (by rw [r11_5val]; exact hW2) (by rw [hsz]; exact (show 5 + 1 < 9 by decide))
  have st6 : step code input s6 = some (.next s7) :=
    step_imm_put rfl (by rw [hsz]; exact (show 6 + 1 < 9 by decide))
  have r11_7val : (reg s7 11).val = (reg s 11).val + 2 := by
    change (reg (putReg (putReg s5 dstHi w2) 15 _) 11).val = _
    rw [reg_putReg, ite_eq_right h15_11.symm, reg_putReg, ite_eq_right hd11.2.2.symm, r11_5val]
  have r15_7 : (reg s7 15).val = 2 := by
    change (reg (putReg s6 15 ⟨2, hTag⟩) 15).val = 2
    rw [reg_putReg, ite_eq_left rfl]
  have r11_8val : (reg s 11).val + 4 < 2 ^ bits → (reg s8 11).val = (reg s 11).val + 4 := by
    intro h4LtStrict
    change (reg (putReg s7 11 (add (reg s7 11) (reg s7 15))) 11).val = _
    have h7lt : (reg s7 11).val + (reg s7 15).val < 2 ^ bits := by
      rw [r11_7val, r15_7]
      exact h4LtStrict
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ h7lt, r11_7val, r15_7]
  have st7 : step code input s7 = some (.next s8) :=
    step_add_put rfl (by rw [hsz]; exact (show 7 + 1 < 9 by decide))
  have hh : step code input s8 = some (.halted s8) := step_halt_at rfl
  have exec := (Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <| Steps.zero s8).halts hh
  have hd0_8 : reg s8 dstTag = w0 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right hd11.1,
      ite_eq_right hd15.1, ite_eq_right hd02, ite_eq_right hd01, ite_true]
  have hd1_8 : reg s8 dstLo = w1 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right hd11.2.1,
      ite_eq_right hd15.2.1, ite_eq_right hd12, ite_true]
  have hd2_8 : reg s8 dstHi = w2 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right hd11.2.2,
      ite_eq_right hd15.2.2, ite_true]
  refine ⟨s8, exec, ⟨hx, hd0_8, hd1_8, hd2_8⟩, r11_8val, ?_, rfl⟩
  intro r h0 h1 h2 h11 h15
  simp only [s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
    ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h11, ite_eq_right h15]
  rfl

/-! ### `branch3Phase` Execution Helpers -/

private theorem branch3Code_slice_hdr (hdr : Program L) (p0 p1 p2 : Phase L)
    {j : Nat} (hj : j < hdr.size) :
    (branch3Code hdr p0 p1 p2)[j]? = hdr[j]? := by
  rw [branch3Code]
  dsimp only
  have s0 : hdr.size ≤ (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    simp only [Array.size_append]; omega
  have s1 : hdr.size ≤ (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    simp only [Array.size_append]; omega
  have s2 : hdr.size ≤ (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p2 (hdr.size + p0.code.size + p1.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    simp only [Array.size_append]; omega
  rw [Array.getElem?_append_left (by omega),
    Array.getElem?_append_left (by omega),
    Array.getElem?_append_left (by omega),
    Array.getElem?_append_left hj]

private theorem branch3Code_slice_p0 (hdr : Program L) (p0 p1 p2 : Phase L)
    {j : Nat} (hj : j < p0.code.size) :
    (branch3Code hdr p0 p1 p2)[hdr.size + j]? =
      (patchHalt p0 hdr.size (hdr.size + p0.code.size + p1.code.size + p2.code.size))[j]? := by
  rw [branch3Code]
  dsimp only
  have hp0 := patchHalt_size p0 hdr.size (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp1 := patchHalt_size p1 (hdr.size + p0.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp2 := patchHalt_size p2 (hdr.size + p0.code.size + p1.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hL : hdr.size + j < (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    rw [Array.size_append, hp0]; omega
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
    Array.getElem?_append_left (by rw [Array.size_append, hp1]; omega),
    Array.getElem?_append_left hL,
    Array.getElem?_append_right (Nat.le_add_right _ _)]
  simp [Nat.add_sub_cancel_left]

private theorem branch3Code_slice_p1 (hdr : Program L) (p0 p1 p2 : Phase L)
    {j : Nat} (hj : j < p1.code.size) :
    (branch3Code hdr p0 p1 p2)[hdr.size + p0.code.size + j]? =
      (patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size))[j]? := by
  rw [branch3Code]
  dsimp only
  have hp0 := patchHalt_size p0 hdr.size (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp1 := patchHalt_size p1 (hdr.size + p0.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp2 := patchHalt_size p2 (hdr.size + p0.code.size + p1.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hPrev : (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size = hdr.size + p0.code.size := by
    rw [Array.size_append, hp0]
  have hL : hdr.size + p0.code.size + j < (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    rw [Array.size_append, hPrev, hp1]; omega
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
    Array.getElem?_append_left hL,
    Array.getElem?_append_right (by rw [hPrev]; omega),
    hPrev]
  simp [Nat.add_sub_cancel_left]

private theorem branch3Code_slice_p2 (hdr : Program L) (p0 p1 p2 : Phase L)
    {j : Nat} (hj : j < p2.code.size) :
    (branch3Code hdr p0 p1 p2)[hdr.size + p0.code.size + p1.code.size + j]? =
      (patchHalt p2 (hdr.size + p0.code.size + p1.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size))[j]? := by
  rw [branch3Code]
  dsimp only
  have hp0 := patchHalt_size p0 hdr.size (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp1 := patchHalt_size p1 (hdr.size + p0.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hp2 := patchHalt_size p2 (hdr.size + p0.code.size + p1.code.size)
    (hdr.size + p0.code.size + p1.code.size + p2.code.size)
  have hPrev : (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size =
      hdr.size + p0.code.size + p1.code.size := by
    rw [Array.size_append, Array.size_append, hp0, hp1]
  have hL : hdr.size + p0.code.size + p1.code.size + j < (hdr ++ patchHalt p0 hdr.size
      (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p1 (hdr.size + p0.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size) ++
      patchHalt p2 (hdr.size + p0.code.size + p1.code.size)
        (hdr.size + p0.code.size + p1.code.size + p2.code.size)).size := by
    rw [Array.size_append, hPrev, hp2]; omega
  rw [Array.getElem?_append_left hL,
    Array.getElem?_append_right (by rw [hPrev]; omega),
    hPrev]
  simp [Nat.add_sub_cancel_left]

private theorem steps_trans {code : Program L} {input : Input L}
    {k1 k2 : Nat} {s1 s2 s3 : State L}
    (h1 : Steps code input k1 s1 s2) (h2 : Steps code input k2 s2 s3) :
    Steps code input (k1 + k2) s1 s3 := by
  induction h1 with
  | zero _ => simpa only [Nat.zero_add] using h2
  | cons hstep _ ih => simpa only [Nat.succ_add] using Steps.cons hstep (ih h2)

private theorem branch3Phase_exec_0 (hdr : Program L)
    (hHdr : hdr.toList.all (@nonHalt bits L) = true) (p0 p1 p2 : Phase L)
    {input : Input L} {s sMid u : State L} {kHdr kP : Nat}
    (h1 : Steps (branch3Phase hdr hHdr p0 p1 p2).code input kHdr (Phase.initial s)
      (relocateStatePC hdr.size (Phase.initial sMid)))
    (h2 : run p0.code input kP (Phase.initial sMid) = some ⟨u, kP⟩) :
    run (branch3Phase hdr hHdr p0 p1 p2).code input (kHdr + kP + 1) (Phase.initial s) =
      some ⟨{ u with pc := (branch3Phase hdr hHdr p0 p1 p2).haltPC }, kHdr + kP + 1⟩ := by
  let ph := branch3Phase hdr hHdr p0 p1 p2
  have hMid := patchHalt_exec p0 hdr.size ph.haltPC ph.code
    (fun j hj => branch3Code_slice_p0 hdr p0 p1 p2 hj) ph.haltFits h2
  exact (steps_trans h1 hMid).halts (step_halt_at ph.haltAt)

private theorem branch3Phase_exec_1 (hdr : Program L)
    (hHdr : hdr.toList.all (@nonHalt bits L) = true) (p0 p1 p2 : Phase L)
    {input : Input L} {s sMid u : State L} {kHdr kP : Nat}
    (h1 : Steps (branch3Phase hdr hHdr p0 p1 p2).code input kHdr (Phase.initial s)
      (relocateStatePC (hdr.size + p0.code.size) (Phase.initial sMid)))
    (h2 : run p1.code input kP (Phase.initial sMid) = some ⟨u, kP⟩) :
    run (branch3Phase hdr hHdr p0 p1 p2).code input (kHdr + kP + 1) (Phase.initial s) =
      some ⟨{ u with pc := (branch3Phase hdr hHdr p0 p1 p2).haltPC }, kHdr + kP + 1⟩ := by
  let ph := branch3Phase hdr hHdr p0 p1 p2
  have hMid := patchHalt_exec p1 (hdr.size + p0.code.size) ph.haltPC ph.code
    (fun j hj => branch3Code_slice_p1 hdr p0 p1 p2 hj) ph.haltFits h2
  exact (steps_trans h1 hMid).halts (step_halt_at ph.haltAt)

private theorem branch3Phase_exec_2 (hdr : Program L)
    (hHdr : hdr.toList.all (@nonHalt bits L) = true) (p0 p1 p2 : Phase L)
    {input : Input L} {s sMid u : State L} {kHdr kP : Nat}
    (h1 : Steps (branch3Phase hdr hHdr p0 p1 p2).code input kHdr (Phase.initial s)
      (relocateStatePC (hdr.size + p0.code.size + p1.code.size) (Phase.initial sMid)))
    (h2 : run p2.code input kP (Phase.initial sMid) = some ⟨u, kP⟩) :
    run (branch3Phase hdr hHdr p0 p1 p2).code input (kHdr + kP + 1) (Phase.initial s) =
      some ⟨{ u with pc := (branch3Phase hdr hHdr p0 p1 p2).haltPC }, kHdr + kP + 1⟩ := by
  let ph := branch3Phase hdr hHdr p0 p1 p2
  have hMid := patchHalt_exec p2 (hdr.size + p0.code.size + p1.code.size) ph.haltPC ph.code
    (fun j hj => branch3Code_slice_p2 hdr p0 p1 p2 hj) ph.haltFits h2
  exact (steps_trans h1 hMid).halts (step_halt_at ph.haltAt)

/-! ### Phase 2: `baseJoinPhase` (`dst := Interval.join base src`, `r11 += 4`) -/

private def baseJoinCode (hTag : TagsFit bits)
    (dstTag dstLo dstHi srcTag srcLo srcHi tmpTag tmpLo tmpHi : Fin 16) : Program L :=
  #[.loadInput tmpTag 11,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 11 11 15,
    .loadInput tmpLo 11,
    .add 11 11 15,
    .loadInput tmpHi 11,
    .imm 15 ⟨2, hTag⟩,
    .add 11 11 15,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .branchLt tmpTag 15 21 10,
    .branchLt srcTag 15 25 11,
    .mov dstTag tmpTag,
    .branchLt tmpLo srcLo 13 15,
    .mov dstLo tmpLo,
    .goto 16,
    .mov dstLo srcLo,
    .branchLt srcHi tmpHi 17 19,
    .mov dstHi tmpHi,
    .goto 20,
    .mov dstHi srcHi,
    .goto 28,
    .mov dstTag srcTag,
    .mov dstLo srcLo,
    .mov dstHi srcHi,
    .goto 28,
    .mov dstTag tmpTag,
    .mov dstLo tmpLo,
    .mov dstHi tmpHi,
    .halt]

private def baseJoinPhase (hTag : TagsFit bits)
    (dstTag dstLo dstHi srcTag srcLo srcHi tmpTag tmpLo tmpHi : Fin 16) : Phase L :=
  Phase.ofLast (baseJoinCode hTag dstTag dstLo dstHi srcTag srcLo srcHi tmpTag tmpLo tmpHi)
    28 rfl rfl (by simp [baseJoinCode, nonHalt])

private theorem step_branchLt_at' {code : Program L} {input : Input L} {s : State L}
    {a b : Fin 16} {t e : Nat}
    (hf : code[s.pc]? = some (.branchLt a b t e))
    (ht : (if (reg s a).val < (reg s b).val then t else e) < code.size) :
    step code input s =
      some (Transition.next { s with pc := if (reg s a).val < (reg s b).val then t else e }) := by
  have hiff : ltb (reg s a) (reg s b) = true ↔ (reg s a).val < (reg s b).val :=
    WordOps.ltb_eq_true _ _
  by_cases hlt : (reg s a).val < (reg s b).val
  · have htb : ltb (reg s a) (reg s b) = true := hiff.mpr hlt
    have ht' : (if ltb (reg s a) (reg s b) then t else e) < code.size := by
      simpa only [htb, ite_true] using (by simpa only [ite_eq_left hlt] using ht)
    have hs := step_branchLt_at (input := input) hf ht'
    simpa only [htb, ite_true, ite_eq_left hlt] using hs
  · have hfb : ltb (reg s a) (reg s b) = false := by
      cases hc : ltb (reg s a) (reg s b)
      · rfl
      · exact False.elim (hlt (hiff.mp hc))
    have ht' : (if ltb (reg s a) (reg s b) then t else e) < code.size := by
      simpa only [hfb, Bool.false_eq_true, ite_false] using (by simpa only [ite_eq_right hlt] using ht)
    have hs := step_branchLt_at (input := input) hf ht'
    simpa only [hfb, Bool.false_eq_true, ite_false, ite_eq_right hlt] using hs

private theorem step_goto_at' {code : Program L} {input : Input L} {s : State L} {tgt : Nat}
    (hf : code[s.pc]? = some (.goto tgt)) (ht : tgt < code.size) :
    step code input s = some (Transition.next { s with pc := tgt }) :=
  step_goto_at hf ht

private theorem baseJoinPhase_spec (hTag : TagsFit bits)
    (dstTag dstLo dstHi srcTag srcLo srcHi tmpTag tmpLo tmpHi : Fin 16)
    (hd01 : dstTag ≠ dstLo) (hd02 : dstTag ≠ dstHi) (hd12 : dstLo ≠ dstHi)
    (hd11 : dstTag ≠ 11 ∧ dstLo ≠ 11 ∧ dstHi ≠ 11)
    (_hd15 : dstTag ≠ 15 ∧ dstLo ≠ 15 ∧ dstHi ≠ 15)
    (hs11 : srcTag ≠ 11 ∧ srcLo ≠ 11 ∧ srcHi ≠ 11)
    (hs15 : srcTag ≠ 15 ∧ srcLo ≠ 15 ∧ srcHi ≠ 15)
    (ht01 : tmpTag ≠ tmpLo) (ht02 : tmpTag ≠ tmpHi) (ht12 : tmpLo ≠ tmpHi)
    (ht11 : tmpTag ≠ 11 ∧ tmpLo ≠ 11 ∧ tmpHi ≠ 11)
    (ht15 : tmpTag ≠ 15 ∧ tmpLo ≠ 15 ∧ tmpHi ≠ 15)
    (hts0 : tmpTag ≠ srcTag ∧ tmpTag ≠ srcLo ∧ tmpTag ≠ srcHi)
    (hts1 : tmpLo ≠ srcTag ∧ tmpLo ≠ srcLo ∧ tmpLo ≠ srcHi)
    (hts2 : tmpHi ≠ srcTag ∧ tmpHi ≠ srcLo ∧ tmpHi ≠ srcHi)
    (hAlias : (dstTag = tmpTag ∧ dstLo = tmpLo ∧ dstHi = tmpHi) ∨
      ((dstTag ≠ tmpTag ∧ dstTag ≠ tmpLo ∧ dstTag ≠ tmpHi) ∧
       (dstLo ≠ tmpTag ∧ dstLo ≠ tmpLo ∧ dstLo ≠ tmpHi) ∧
       (dstHi ≠ tmpTag ∧ dstHi ≠ tmpLo ∧ dstHi ≠ tmpHi)))
    (hds : (dstTag = srcTag ∧ dstLo = srcLo ∧ dstHi = srcHi) ∨
      ((dstTag ≠ srcTag ∧ dstTag ≠ srcLo ∧ dstTag ≠ srcHi) ∧
       (dstLo ≠ srcTag ∧ dstLo ≠ srcLo ∧ dstLo ≠ srcHi) ∧
       (dstHi ≠ srcTag ∧ dstHi ≠ srcLo ∧ dstHi ≠ srcHi)))
    (input : Input L) (s : State L) (base y : Interval)
    (hBase : RankBound (2 ^ bits) base)
    (hSrc : IntervalWords hTag y (reg s srcTag) (reg s srcLo) (reg s srcHi))
    (hAddr : (reg s 11).val + 4 ≤ inputCap)
    (hW0 : input.words[(reg s 11).val]? = some ((intervalCodec hTag).encode base hBase 0))
    (hW1 : input.words[(reg s 11).val + 1]? = some ((intervalCodec hTag).encode base hBase 1))
    (hW2 : input.words[(reg s 11).val + 2]? = some ((intervalCodec hTag).encode base hBase 2)) :
    ∃ (t : State L) (k : Nat),
      k ≤ 21 ∧
      run (baseJoinPhase (fits := fits) hTag dstTag dstLo dstHi srcTag srcLo srcHi
        tmpTag tmpLo tmpHi).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      IntervalWords hTag (Interval.join base y) (reg t dstTag) (reg t dstLo) (reg t dstHi) ∧
      ((reg s 11).val + 4 < 2 ^ bits → (reg t 11).val = (reg s 11).val + 4) ∧
      (∀ r : Fin 16, r ≠ dstTag → r ≠ dstLo → r ≠ dstHi →
        r ≠ tmpTag → r ≠ tmpLo → r ≠ tmpHi → r ≠ 11 → r ≠ 15 →
        reg t r = reg s r) ∧
      t.data = s.data := by
  let code := (baseJoinPhase (fits := fits) hTag dstTag dstLo dstHi srcTag srcLo srcHi
    tmpTag tmpLo tmpHi).code
  have hsz : code.size = 29 := rfl
  let s0 := Phase.initial s
  let w0 := (intervalCodec hTag).encode base hBase 0
  let w1 := (intervalCodec hTag).encode base hBase 1
  let w2 := (intervalCodec hTag).encode base hBase 2
  have h4Lt : (reg s 11).val + 4 ≤ 2 ^ bits := Nat.le_trans hAddr fits
  have h15_11 : (15 : Fin 16) ≠ 11 := by decide
  let s1 := putReg s0 tmpTag w0
  let s2 := putReg s1 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s3 := putReg s2 11 (add (reg s2 11) (reg s2 15))
  let s4 := putReg s3 tmpLo w1
  let s5 := putReg s4 11 (add (reg s4 11) (reg s4 15))
  let s6 := putReg s5 tmpHi w2
  let s7 := putReg s6 15 ⟨2, hTag⟩
  let s8 := putReg s7 11 (add (reg s7 11) (reg s7 15))
  let s9 := putReg s8 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  have st0 : step code input s0 = some (.next s1) :=
    step_loadInput_put rfl hW0 (by rw [hsz]; exact (show 0 + 1 < 29 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_imm_put rfl (by rw [hsz]; exact (show 1 + 1 < 29 by decide))
  have r11_2 : reg s2 11 = reg s 11 := by
    change reg (putReg (putReg s0 tmpTag w0) 15 _) 11 = _
    rw [reg_putReg, ite_eq_right h15_11.symm, reg_putReg, ite_eq_right ht11.1.symm]
    rfl
  have r15_2 : (reg s2 15).val = 1 := by
    change (reg (putReg s1 15 _) 15).val = 1
    rw [reg_putReg, ite_eq_left rfl]
  have r11_3val : (reg s3 11).val = (reg s 11).val + 1 := by
    change (reg (putReg s2 11 (add (reg s2 11) (reg s2 15))) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_2, r15_2]; omega), r11_2, r15_2]
  have st2 : step code input s2 = some (.next s3) :=
    step_add_put rfl (by rw [hsz]; exact (show 2 + 1 < 29 by decide))
  have st3 : step code input s3 = some (.next s4) :=
    step_loadInput_put rfl (by rw [r11_3val]; exact hW1) (by rw [hsz]; exact (show 3 + 1 < 29 by decide))
  have r15_4 : (reg s4 15).val = 1 := by
    change (reg (putReg (putReg s2 11 _) tmpLo w1) 15).val = 1
    rw [reg_putReg, ite_eq_right ht15.2.1.symm, reg_putReg, ite_eq_right h15_11, r15_2]
  have r11_4val : (reg s4 11).val = (reg s 11).val + 1 := by
    change (reg (putReg s3 tmpLo w1) 11).val = _
    rw [reg_putReg, ite_eq_right ht11.2.1.symm, r11_3val]
  have r11_5val : (reg s5 11).val = (reg s 11).val + 2 := by
    change (reg (putReg s4 11 (add (reg s4 11) (reg s4 15))) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_4val, r15_4]; omega),
      r11_4val, r15_4]
  have st4 : step code input s4 = some (.next s5) :=
    step_add_put rfl (by rw [hsz]; exact (show 4 + 1 < 29 by decide))
  have st5 : step code input s5 = some (.next s6) :=
    step_loadInput_put rfl (by rw [r11_5val]; exact hW2) (by rw [hsz]; exact (show 5 + 1 < 29 by decide))
  have st6 : step code input s6 = some (.next s7) :=
    step_imm_put rfl (by rw [hsz]; exact (show 6 + 1 < 29 by decide))
  have r11_7val : (reg s7 11).val = (reg s 11).val + 2 := by
    change (reg (putReg (putReg s5 tmpHi w2) 15 _) 11).val = _
    rw [reg_putReg, ite_eq_right h15_11.symm, reg_putReg, ite_eq_right ht11.2.2.symm, r11_5val]
  have r15_7 : (reg s7 15).val = 2 := by
    change (reg (putReg s6 15 ⟨2, hTag⟩) 15).val = 2
    rw [reg_putReg, ite_eq_left rfl]
  have r11_8val : (reg s 11).val + 4 < 2 ^ bits → (reg s8 11).val = (reg s 11).val + 4 := by
    intro h4LtStrict
    change (reg (putReg s7 11 (add (reg s7 11) (reg s7 15))) 11).val = _
    have h7lt : (reg s7 11).val + (reg s7 15).val < 2 ^ bits := by
      rw [r11_7val, r15_7]; exact h4LtStrict
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ h7lt, r11_7val, r15_7]
  have st7 : step code input s7 = some (.next s8) :=
    step_add_put rfl (by rw [hsz]; exact (show 7 + 1 < 29 by decide))
  have st8 : step code input s8 = some (.next s9) :=
    step_imm_put rfl (by rw [hsz]; exact (show 8 + 1 < 29 by decide))
  have preSteps : Steps code input 9 s0 s9 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <|
    Steps.cons st8 <| Steps.zero s9
  have hBaseW : IntervalWords hTag base (reg s9 tmpTag) (reg s9 tmpLo) (reg s9 tmpHi) := by
    refine ⟨hBase, ?_, ?_, ?_⟩
    · simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
        ite_eq_right ht15.1, ite_eq_right ht11.1, ite_eq_right ht02,
        ite_eq_right ht01, ite_true]
      rfl
    · simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
        ite_eq_right ht15.2.1, ite_eq_right ht11.2.1, ite_eq_right ht12,
        ite_true]
      rfl
    · simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
        ite_eq_right ht15.2.2, ite_eq_right ht11.2.2, ite_true]
      rfl
  have h15_9 : (reg s9 15).val = 1 := by
    simp only [s9, reg_putReg, ite_true]
  have h11_9 : (reg s 11).val + 4 < 2 ^ bits → (reg s9 11).val = (reg s 11).val + 4 := by
    intro hlt
    change (reg (putReg s8 15 _) 11).val = _
    rw [reg_putReg, ite_eq_right h15_11.symm]
    exact r11_8val hlt
  have hPres9 : ∀ r : Fin 16, r ≠ tmpTag → r ≠ tmpLo → r ≠ tmpHi → r ≠ 11 → r ≠ 15 →
      reg s9 r = reg s r := by
    intro r hr0 hr1 hr2 hr11 hr15
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
      ite_eq_right hr15, ite_eq_right hr11, ite_eq_right hr2, ite_eq_right hr1, ite_eq_right hr0]
    rfl
  have hSrc9 : reg s9 srcTag = reg s srcTag ∧ reg s9 srcLo = reg s srcLo ∧
      reg s9 srcHi = reg s srcHi :=
    ⟨hPres9 srcTag hts0.1.symm hts1.1.symm hts2.1.symm hs11.1 hs15.1,
     hPres9 srcLo hts0.2.1.symm hts1.2.1.symm hts2.2.1.symm hs11.2.1 hs15.2.1,
     hPres9 srcHi hts0.2.2.symm hts1.2.2.symm hts2.2.2.symm hs11.2.2 hs15.2.2⟩
  have hpc9 : s9.pc = 9 := rfl
  have hd_src_cross : dstTag ≠ srcLo ∧ dstTag ≠ srcHi ∧ dstLo ≠ srcHi := by
    rcases hds with ⟨rfl, rfl, rfl⟩ | ⟨hA, hB, _⟩
    · exact ⟨hd01, hd02, hd12⟩
    · exact ⟨hA.2.1, hA.2.2, hB.2.2⟩
  have hd_tmp_cross : dstTag ≠ tmpLo ∧ dstTag ≠ tmpHi ∧ dstLo ≠ tmpHi := by
    rcases hAlias with ⟨rfl, rfl, rfl⟩ | ⟨hA, hB, _⟩
    · exact ⟨ht01, ht02, ht12⟩
    · exact ⟨hA.2.1, hA.2.2, hB.2.2⟩
  cases base with
  | empty =>
    have htmpTag0 : (reg s9 tmpTag).val = 0 := by
      rcases hBaseW with ⟨_, h0, _, _⟩; rw [h0]; rfl
    have st9 : step code input s9 = some (.next { s9 with pc := 21 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s9)
        (a := tmpTag) (b := 15) (t := 21) (e := 10)
        (by rw [hpc9]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [htmpTag0, h15_9, ite_eq_left (by decide : (0 : Nat) < 1)] using hst
    let s10 := { s9 with pc := 21 }
    let s11 := putReg s10 dstTag (reg s10 srcTag)
    let s12 := putReg s11 dstLo (reg s11 srcLo)
    let s13 := putReg s12 dstHi (reg s12 srcHi)
    let s14 := { s13 with pc := 28 }
    have st10 : step code input s10 = some (.next s11) :=
      step_mov_put rfl (by rw [hsz]; exact (show 21 + 1 < 29 by decide))
    have st11 : step code input s11 = some (.next s12) :=
      step_mov_put rfl (by rw [hsz]; exact (show 22 + 1 < 29 by decide))
    have st12 : step code input s12 = some (.next s13) :=
      step_mov_put rfl (by rw [hsz]; exact (show 23 + 1 < 29 by decide))
    have st13 : step code input s13 = some (.next s14) :=
      step_goto_at' rfl (by rw [hsz]; exact (show 28 < 29 by decide))
    have hh : step code input s14 = some (.halted s14) := step_halt_at rfl
    have exec := (steps_trans preSteps (Steps.cons st9 <| Steps.cons st10 <| Steps.cons st11 <|
      Steps.cons st12 <| Steps.cons st13 <| Steps.zero s14)).halts hh
    refine ⟨s14, 15, by decide, exec, ?_, ?_, ?_, rfl⟩
    · have hdt : reg s14 dstTag = reg s srcTag := by
        change reg s13 dstTag = _
        simp only [s13, s12, s11, s10, reg_putReg, ite_eq_right hd02,
          ite_eq_right hd01, ite_true]
        exact hSrc9.1
      have hdl : reg s14 dstLo = reg s srcLo := by
        change reg s13 dstLo = _
        simp only [s13, s12, s11, s10, reg_putReg, ite_eq_right hd12, ite_true,
          ite_eq_right hd_src_cross.1.symm]
        exact hSrc9.2.1
      have hdh : reg s14 dstHi = reg s srcHi := by
        change reg s13 dstHi = _
        simp only [s13, s12, s11, s10, reg_putReg, ite_true,
          ite_eq_right hd_src_cross.2.2.symm, ite_eq_right hd_src_cross.2.1.symm]
        exact hSrc9.2.2
      rw [hdt, hdl, hdh]
      simpa [Interval.join] using hSrc
    · intro hlt
      change (reg s13 11).val = _
      simp only [s13, s12, s11, s10, reg_putReg, ite_eq_right hd11.2.2.symm,
        ite_eq_right hd11.2.1.symm, ite_eq_right hd11.1.symm]
      exact h11_9 hlt
    · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr11 hr15
      change reg s13 r = _
      simp only [s13, s12, s11, s10, reg_putReg, ite_eq_right hr2, ite_eq_right hr1,
        ite_eq_right hr0]
      exact hPres9 r hr3 hr4 hr5 hr11 hr15
  | span blo bhi =>
    have htmpTag1 : (reg s9 tmpTag).val = 1 :=
      (intervalWords_span_vals hBaseW).1
    have st9 : step code input s9 = some (.next { s9 with pc := 10 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s9)
        (a := tmpTag) (b := 15) (t := 21) (e := 10)
        (by rw [hpc9]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [htmpTag1, h15_9, ite_eq_right (by decide : ¬ (1 : Nat) < 1)] using hst
    let s10 := { s9 with pc := 10 }
    cases y with
    | empty =>
      have hsrcTag0 : (reg s10 srcTag).val = 0 := by
        rcases hSrc with ⟨_, h0, _, _⟩
        change (reg s9 srcTag).val = 0
        rw [hSrc9.1, h0]; rfl
      have st10 : step code input s10 = some (.next { s10 with pc := 25 }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s10)
          (a := srcTag) (b := 15) (t := 25) (e := 11)
          rfl (by split <;> rw [hsz] <;> decide)
        simpa only [hsrcTag0, show (reg s10 15).val = 1 from h15_9,
          ite_eq_left (by decide : (0 : Nat) < 1)] using hst
      let s11 := { s10 with pc := 25 }
      let s12 := putReg s11 dstTag (reg s11 tmpTag)
      let s13 := putReg s12 dstLo (reg s12 tmpLo)
      let s14 := putReg s13 dstHi (reg s13 tmpHi)
      have st11 : step code input s11 = some (.next s12) :=
        step_mov_put rfl (by rw [hsz]; exact (show 25 + 1 < 29 by decide))
      have st12 : step code input s12 = some (.next s13) :=
        step_mov_put rfl (by rw [hsz]; exact (show 26 + 1 < 29 by decide))
      have st13 : step code input s13 = some (.next s14) :=
        step_mov_put rfl (by rw [hsz]; exact (show 27 + 1 < 29 by decide))
      have hh : step code input s14 = some (.halted s14) := step_halt_at rfl
      have exec := (steps_trans preSteps (Steps.cons st9 <| Steps.cons st10 <| Steps.cons st11 <|
        Steps.cons st12 <| Steps.cons st13 <| Steps.zero s14)).halts hh
      refine ⟨s14, 15, by decide, exec, ?_, ?_, ?_, rfl⟩
      · have hdt : reg s14 dstTag = reg s9 tmpTag := by
          simp only [s14, s13, s12, s11, s10, reg_putReg, ite_eq_right hd02,
            ite_eq_right hd01, ite_true]
          rfl
        have hdl : reg s14 dstLo = reg s9 tmpLo := by
          simp only [s14, s13, s12, s11, s10, reg_putReg, ite_eq_right hd12, ite_true,
            ite_eq_right hd_tmp_cross.1.symm]
          rfl
        have hdh : reg s14 dstHi = reg s9 tmpHi := by
          simp only [s14, s13, s12, s11, s10, reg_putReg, ite_true,
            ite_eq_right hd_tmp_cross.2.2.symm, ite_eq_right hd_tmp_cross.2.1.symm]
          rfl
        rw [hdt, hdl, hdh]
        simpa [Interval.join] using hBaseW
      · intro hlt
        simp only [s14, s13, s12, s11, s10, reg_putReg, ite_eq_right hd11.2.2.symm,
          ite_eq_right hd11.2.1.symm, ite_eq_right hd11.1.symm]
        exact h11_9 hlt
      · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr11 hr15
        simp only [s14, s13, s12, s11, s10, reg_putReg, ite_eq_right hr2, ite_eq_right hr1,
          ite_eq_right hr0]
        exact hPres9 r hr3 hr4 hr5 hr11 hr15
    | span slo shi =>
      have hSrcW9 : IntervalWords hTag (.span slo shi)
          (reg s9 srcTag) (reg s9 srcLo) (reg s9 srcHi) := by
        rw [hSrc9.1, hSrc9.2.1, hSrc9.2.2]; exact hSrc
      have hsrcTag1 : (reg s10 srcTag).val = 1 :=
        (intervalWords_span_vals hSrcW9).1
      have st10 : step code input s10 = some (.next { s10 with pc := 11 }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s10)
          (a := srcTag) (b := 15) (t := 25) (e := 11)
          rfl (by split <;> rw [hsz] <;> decide)
        simpa only [hsrcTag1, show (reg s10 15).val = 1 from h15_9,
          ite_eq_right (by decide : ¬ (1 : Nat) < 1)] using hst
      let s11 := { s10 with pc := 11 }
      let s12 := putReg s11 dstTag (reg s11 tmpTag)
      have st11 : step code input s11 = some (.next s12) :=
        step_mov_put rfl (by rw [hsz]; exact (show 11 + 1 < 29 by decide))
      have hdt_12 : reg s12 dstTag = reg s9 tmpTag := by
        simp only [s12, s11, s10, reg_putReg, ite_true]; rfl
      have hd_ne_srcLo : dstTag ≠ srcLo := hd_src_cross.1
      have hd_ne_srcHi : dstTag ≠ srcHi := hd_src_cross.2.1
      have htmpLo_12 : reg s12 tmpLo = reg s9 tmpLo := by
        simp only [s12, s11, s10, reg_putReg, ite_eq_right hd_tmp_cross.1.symm]; rfl
      have htmpHi_12 : reg s12 tmpHi = reg s9 tmpHi := by
        simp only [s12, s11, s10, reg_putReg, ite_eq_right hd_tmp_cross.2.1.symm]; rfl
      have hsrcLo_12 : reg s12 srcLo = reg s9 srcLo := by
        simp only [s12, s11, s10, reg_putReg, ite_eq_right hd_ne_srcLo.symm]; rfl
      have hsrcHi_12 : reg s12 srcHi = reg s9 srcHi := by
        simp only [s12, s11, s10, reg_putReg, ite_eq_right hd_ne_srcHi.symm]; rfl
      have hLoBlk : ∃ (s15 : State L) (kLo : Nat),
          kLo ≤ 3 ∧ Steps code input kLo s12 s15 ∧ s15.pc = 16 ∧
          reg s15 dstTag = reg s9 tmpTag ∧
          reg s15 dstLo =
            (if (reg s9 tmpLo).val < (reg s9 srcLo).val then reg s9 tmpLo else reg s9 srcLo) ∧
          reg s15 tmpHi = reg s9 tmpHi ∧ reg s15 srcHi = reg s9 srcHi ∧
          (∀ r : Fin 16, r ≠ dstTag → r ≠ dstLo → reg s15 r = reg s9 r) ∧
          s15.data = s9.data := by
        by_cases hlt : (reg s9 tmpLo).val < (reg s9 srcLo).val
        · have hlt12 : (reg s12 tmpLo).val < (reg s12 srcLo).val := by
            rw [htmpLo_12, hsrcLo_12]; exact hlt
          have st12 : step code input s12 = some (.next { s12 with pc := 13 }) := by
            have hst := step_branchLt_at' (code := code) (input := input) (s := s12)
              (a := tmpLo) (b := srcLo) (t := 13) (e := 15)
              rfl (by split <;> rw [hsz] <;> decide)
            simpa only [ite_eq_left hlt12] using hst
          let s13 := putReg { s12 with pc := 13 } dstLo (reg { s12 with pc := 13 } tmpLo)
          let s14 := { s13 with pc := 16 }
          have st13 : step code input { s12 with pc := 13 } = some (.next s13) :=
            step_mov_put rfl (by rw [hsz]; exact (show 13 + 1 < 29 by decide))
          have st14 : step code input s13 = some (.next s14) :=
            step_goto_at' rfl (by rw [hsz]; exact (show 16 < 29 by decide))
          refine ⟨s14, 3, by decide,
            Steps.cons st12 <| Steps.cons st13 <| Steps.cons st14 <| Steps.zero s14,
            rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          · change reg s13 dstTag = _; rw [reg_putReg, ite_eq_right hd01]; exact hdt_12
          · change reg s13 dstLo = _; rw [reg_putReg, ite_eq_left rfl, ite_eq_left hlt]; exact htmpLo_12
          · change reg s13 tmpHi = _; rw [reg_putReg, ite_eq_right hd_tmp_cross.2.2.symm]; exact htmpHi_12
          · change reg s13 srcHi = _; rw [reg_putReg, ite_eq_right hd_src_cross.2.2.symm]; exact hsrcHi_12
          · intro r hr0 hr1
            change reg s13 r = _
            rw [reg_putReg, ite_eq_right hr1]
            change reg s12 r = _
            rw [reg_putReg, ite_eq_right hr0]
            rfl
        · have hlt12 : ¬ ((reg s12 tmpLo).val < (reg s12 srcLo).val) := by
            rw [htmpLo_12, hsrcLo_12]; exact hlt
          have st12 : step code input s12 = some (.next { s12 with pc := 15 }) := by
            have hst := step_branchLt_at' (code := code) (input := input) (s := s12)
              (a := tmpLo) (b := srcLo) (t := 13) (e := 15)
              rfl (by split <;> rw [hsz] <;> decide)
            simpa only [ite_eq_right hlt12] using hst
          let s13 := putReg { s12 with pc := 15 } dstLo (reg { s12 with pc := 15 } srcLo)
          have st13 : step code input { s12 with pc := 15 } = some (.next s13) :=
            step_mov_put rfl (by rw [hsz]; exact (show 15 + 1 < 29 by decide))
          refine ⟨s13, 2, by decide,
            Steps.cons st12 <| Steps.cons st13 <| Steps.zero s13,
            rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
          · rw [reg_putReg, ite_eq_right hd01]; exact hdt_12
          · rw [reg_putReg, ite_eq_left rfl, ite_eq_right hlt]; exact hsrcLo_12
          · rw [reg_putReg, ite_eq_right hd_tmp_cross.2.2.symm]; exact htmpHi_12
          · rw [reg_putReg, ite_eq_right hd_src_cross.2.2.symm]; exact hsrcHi_12
          · intro r hr0 hr1
            rw [reg_putReg, ite_eq_right hr1]
            change reg s12 r = _
            rw [reg_putReg, ite_eq_right hr0]
            rfl
      rcases hLoBlk with ⟨s15, kLo, hkLo, hStepsLo, hpc15, hdt15, hdl15, hth15, hsh15, hPres15, hD15⟩
      have hHiBlk : ∃ (s19 : State L) (kHi : Nat),
          kHi ≤ 3 ∧ Steps code input kHi s15 s19 ∧ s19.pc = 20 ∧
          reg s19 dstTag = reg s9 tmpTag ∧ reg s19 dstLo = reg s15 dstLo ∧
          reg s19 dstHi =
            (if (reg s9 srcHi).val < (reg s9 tmpHi).val then reg s9 tmpHi else reg s9 srcHi) ∧
          (∀ r : Fin 16, r ≠ dstTag → r ≠ dstLo → r ≠ dstHi → reg s19 r = reg s9 r) ∧
          s19.data = s9.data := by
        by_cases hlt : (reg s9 srcHi).val < (reg s9 tmpHi).val
        · have hlt15 : (reg s15 srcHi).val < (reg s15 tmpHi).val := by
            rw [hsh15, hth15]; exact hlt
          have st15 : step code input s15 = some (.next { s15 with pc := 17 }) := by
            have hst := step_branchLt_at' (code := code) (input := input) (s := s15)
              (a := srcHi) (b := tmpHi) (t := 17) (e := 19)
              (by rw [hpc15]; rfl) (by split <;> rw [hsz] <;> decide)
            simpa only [ite_eq_left hlt15] using hst
          let s16 := putReg { s15 with pc := 17 } dstHi (reg { s15 with pc := 17 } tmpHi)
          let s17 := { s16 with pc := 20 }
          have st16 : step code input { s15 with pc := 17 } = some (.next s16) :=
            step_mov_put rfl (by rw [hsz]; exact (show 17 + 1 < 29 by decide))
          have st17 : step code input s16 = some (.next s17) :=
            step_goto_at' rfl (by rw [hsz]; exact (show 20 < 29 by decide))
          refine ⟨s17, 3, by decide,
            Steps.cons st15 <| Steps.cons st16 <| Steps.cons st17 <| Steps.zero s17,
            rfl, ?_, ?_, ?_, ?_, hD15⟩
          · change reg s16 dstTag = _; rw [reg_putReg, ite_eq_right hd02]; exact hdt15
          · change reg s16 dstLo = _; rw [reg_putReg, ite_eq_right hd12]; rfl
          · change reg s16 dstHi = _; rw [reg_putReg, ite_eq_left rfl, ite_eq_left hlt]; exact hth15
          · intro r hr0 hr1 hr2
            change reg s16 r = _; rw [reg_putReg, ite_eq_right hr2]; exact hPres15 r hr0 hr1
        · have hlt15 : ¬ ((reg s15 srcHi).val < (reg s15 tmpHi).val) := by
            rw [hsh15, hth15]; exact hlt
          have st15 : step code input s15 = some (.next { s15 with pc := 19 }) := by
            have hst := step_branchLt_at' (code := code) (input := input) (s := s15)
              (a := srcHi) (b := tmpHi) (t := 17) (e := 19)
              (by rw [hpc15]; rfl) (by split <;> rw [hsz] <;> decide)
            simpa only [ite_eq_right hlt15] using hst
          let s16 := putReg { s15 with pc := 19 } dstHi (reg { s15 with pc := 19 } srcHi)
          have st16 : step code input { s15 with pc := 19 } = some (.next s16) :=
            step_mov_put rfl (by rw [hsz]; exact (show 19 + 1 < 29 by decide))
          refine ⟨s16, 2, by decide,
            Steps.cons st15 <| Steps.cons st16 <| Steps.zero s16,
            rfl, ?_, ?_, ?_, ?_, hD15⟩
          · rw [reg_putReg, ite_eq_right hd02]; exact hdt15
          · rw [reg_putReg, ite_eq_right hd12]; rfl
          · rw [reg_putReg, ite_eq_left rfl, ite_eq_right hlt]; exact hsh15
          · intro r hr0 hr1 hr2; rw [reg_putReg, ite_eq_right hr2]; exact hPres15 r hr0 hr1
      rcases hHiBlk with ⟨s19, kHi, hkHi, hStepsHi, hpc19, hdt19, hdl19, hdh19, hPres19, hD19⟩
      let s20 := { s19 with pc := 28 }
      have st19 : step code input s19 = some (.next s20) :=
        step_goto_at' (by rw [hpc19]; rfl) (by rw [hsz]; exact (show 28 < 29 by decide))
      have hh : step code input s20 = some (.halted s20) := step_halt_at rfl
      have hMid : Steps code input (3 + kLo + kHi + 1) s9 s20 := by
        have h1 := Steps.cons st9 <| Steps.cons st10 <| Steps.cons st11 hStepsLo
        have h2 := steps_trans h1 hStepsHi
        have h3 := steps_trans h2 (Steps.cons st19 (Steps.zero s20))
        rw [show 3 + kLo + kHi + 1 = kLo.succ.succ.succ + (kHi + Nat.succ 0) by omega]
        exact h3
      have exec := (steps_trans preSteps hMid).halts hh
      refine ⟨s20, 9 + (3 + kLo + kHi + 1) + 1, by omega, exec, ?_, ?_, ?_, hD19⟩
      · have hJ := intervalWords_join hBaseW hSrcW9
        change IntervalWords hTag (Interval.join (.span blo bhi) (.span slo shi))
          (reg s19 dstTag) (reg s19 dstLo) (reg s19 dstHi)
        rw [hdt19, hdl19, hdl15, hdh19]
        exact hJ
      · intro hlt
        change (reg s19 11).val = _
        rw [hPres19 11 hd11.1.symm hd11.2.1.symm hd11.2.2.symm]
        exact h11_9 hlt
      · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr11 hr15
        change reg s19 r = _
        rw [hPres19 r hr0 hr1 hr2]
        exact hPres9 r hr3 hr4 hr5 hr11 hr15

/-! ### Phase 3: `coord0Phase` (`r12..r14 := Coord.eval c0 xs`, `r11 += 4`) -/

private def coord0Header (hTag : TagsFit bits) (b0 b1 b2 : Nat) : Program L :=
  #[.imm 15 ⟨2, hTag⟩,
    .add 12 11 15,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 12 12 15,
    .loadInput 12 12,
    .branchLt 12 15 b0 6,
    .imm 15 ⟨2, hTag⟩,
    .branchLt 12 15 b1 b2]

private def coord0P0 (hTag : TagsFit bits) : Phase L :=
  baseNonePhase hTag 12 13 14

private def coord0P1 (hTag : TagsFit bits) : Phase L :=
  baseJoinPhase hTag 12 13 14 0 1 2 12 13 14

private def coord0P2 (hTag : TagsFit bits) : Phase L :=
  baseJoinPhase hTag 12 13 14 3 4 5 12 13 14

private theorem coord0Header_nonhalt (hTag : TagsFit bits) (b0 b1 b2 : Nat) :
    (coord0Header (fits := fits) hTag b0 b1 b2).toList.all (@nonHalt bits L) = true := by
  simp [coord0Header, nonHalt]

private def coord0Phase (hTag : TagsFit bits) : Phase L :=
  let p0 : Phase L := coord0P0 hTag
  let p1 : Phase L := coord0P1 hTag
  let p2 : Phase L := coord0P2 hTag
  let hdr := coord0Header hTag 8 (8 + p0.code.size) (8 + p0.code.size + p1.code.size)
  branch3Phase hdr (coord0Header_nonhalt hTag _ _ _) p0 p1 p2

private theorem coordCodec_word3_val (hTag : TagsFit bits) (c : Coord)
    (hC : (coordCodec hTag).valid c) :
    ((coordCodec hTag).encode c hC 3).val =
      match c.slot with
      | none => 0
      | some ⟨0, _⟩ => 1
      | some ⟨1, _⟩ => 2 := by
  rcases c with ⟨b, s⟩
  cases s with
  | none => rfl
  | some j =>
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

private theorem coord0Phase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (c : Coord) (xs : Values)
    (hC : (coordCodec hTag).valid c)
    (hXs : ValuesRegs hTag xs s)
    (hAddr : (reg s 11).val + 4 ≤ inputCap)
    (hW0 : input.words[(reg s 11).val]? = some ((coordCodec hTag).encode c hC 0))
    (hW1 : input.words[(reg s 11).val + 1]? = some ((coordCodec hTag).encode c hC 1))
    (hW2 : input.words[(reg s 11).val + 2]? = some ((coordCodec hTag).encode c hC 2))
    (hW3 : input.words[(reg s 11).val + 3]? = some ((coordCodec hTag).encode c hC 3)) :
    ∃ (t : State L) (k : Nat),
      k ≤ 30 ∧
      run (coord0Phase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      IntervalWords hTag (Coord.eval c xs) (reg t 12) (reg t 13) (reg t 14) ∧
      ((reg s 11).val + 4 < 2 ^ bits → (reg t 11).val = (reg s 11).val + 4) ∧
      (∀ r : Fin 16, r < 11 → reg t r = reg s r) ∧
      t.data = s.data := by
  let p0 : Phase L := coord0P0 hTag
  let p1 : Phase L := coord0P1 hTag
  let p2 : Phase L := coord0P2 hTag
  let hdr := coord0Header (fits := fits) hTag 8 (8 + p0.code.size) (8 + p0.code.size + p1.code.size)
  have hHdr := coord0Header_nonhalt (fits := fits) hTag 8 (8 + p0.code.size)
    (8 + p0.code.size + p1.code.size)
  let ph := branch3Phase hdr hHdr p0 p1 p2
  let code := ph.code
  have hHdrSz : hdr.size = 8 := rfl
  have hCodeSz : code.size = 8 + p0.code.size + p1.code.size + p2.code.size + 1 := by
    have hSz := branch3Code_size hdr p0 p1 p2
    change code.size = hdr.size + p0.code.size + p1.code.size + p2.code.size + 1 at hSz
    rw [hHdrSz] at hSz
    exact hSz
  have hFetch : ∀ j, j < 8 → code[j]? = hdr[j]? := fun j hj =>
    branch3Code_slice_hdr hdr p0 p1 p2 hj
  have h4Lt : (reg s 11).val + 4 ≤ 2 ^ bits := Nat.le_trans hAddr fits
  let s0 := Phase.initial s
  let s1 := putReg s0 15 ⟨2, hTag⟩
  let s2 := putReg s1 12 (add (reg s1 11) (reg s1 15))
  let s3 := putReg s2 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s4 := putReg s3 12 (add (reg s3 12) (reg s3 15))
  let w3 := (coordCodec hTag).encode c hC 3
  let s5 := putReg s4 12 w3
  have st0 : step code input s0 = some (.next s1) :=
    step_imm_put (by change code[0]? = _; rw [hFetch 0 (by decide)]; rfl)
      (by change 0 + 1 < code.size; rw [hCodeSz]; omega)
  have st1 : step code input s1 = some (.next s2) :=
    step_add_put (by change code[1]? = _; rw [hFetch 1 (by decide)]; rfl)
      (by change 1 + 1 < code.size; rw [hCodeSz]; omega)
  have st2 : step code input s2 = some (.next s3) :=
    step_imm_put (by change code[2]? = _; rw [hFetch 2 (by decide)]; rfl)
      (by change 2 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_3val : (reg s3 12).val = (reg s 11).val + 2 := by
    change (reg (putReg (putReg (putReg s0 15 ⟨2, hTag⟩) 12 _) 15 _) 12).val = _
    have r11_1 : (reg s1 11).val = (reg s 11).val := by
      simp only [s1, s0, reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 15)]; rfl
    have r15_1 : (reg s1 15).val = 2 := by
      simp only [s1, reg_putReg, ite_true]
    have hlt2 : (reg s1 11).val + (reg s1 15).val < 2 ^ bits := by
      rw [r11_1, r15_1]; omega
    simp only [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15), ite_true,
      add_no_wrap _ _ hlt2, r11_1, r15_1]
  have r15_3val : (reg s3 15).val = 1 := by
    simp only [s3, reg_putReg, ite_true]
  have st3 : step code input s3 = some (.next s4) :=
    step_add_put (by change code[3]? = _; rw [hFetch 3 (by decide)]; rfl)
      (by change 3 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_4val : (reg s4 12).val = (reg s 11).val + 3 := by
    change (reg (putReg s3 12 _) 12).val = _
    have hlt3 : (reg s3 12).val + (reg s3 15).val < 2 ^ bits := by
      rw [r12_3val, r15_3val]; omega
    simp only [reg_putReg, ite_true, add_no_wrap _ _ hlt3, r12_3val, r15_3val]
  have st4 : step code input s4 = some (.next s5) :=
    step_loadInput_put (by change code[4]? = _; rw [hFetch 4 (by decide)]; rfl)
      (by rw [r12_4val]; exact hW3) (by change 4 + 1 < code.size; rw [hCodeSz]; omega)
  have pre5 : Steps code input 5 s0 s5 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.zero s5
  have h12_5 : reg s5 12 = w3 := by simp only [s5, reg_putReg, ite_true]
  have h15_5 : (reg s5 15).val = 1 := by
    simp only [s5, s4, reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 12), r15_3val]
  have hPres5 : ∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg s5 r = reg s r := by
    intro r hr12 hr15
    simp only [s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right hr12, ite_eq_right hr15]
    rfl
  have hBaseW0 : input.words[(reg s5 11).val]? = some ((intervalCodec hTag).encode c.base hC.1 0) := by
    rw [hPres5 11 (by decide) (by decide)]; exact hW0
  have hBaseW1 : input.words[(reg s5 11).val + 1]? = some ((intervalCodec hTag).encode c.base hC.1 1) := by
    rw [hPres5 11 (by decide) (by decide)]; exact hW1
  have hBaseW2 : input.words[(reg s5 11).val + 2]? = some ((intervalCodec hTag).encode c.base hC.1 2) := by
    rw [hPres5 11 (by decide) (by decide)]; exact hW2
  have hAddr5 : (reg s5 11).val + 4 ≤ inputCap := by
    rw [hPres5 11 (by decide) (by decide)]; exact hAddr
  cases hslot : c.slot with
  | none =>
    have hw3_0 : (reg s5 12).val = 0 := by
      rw [h12_5]; exact (coordCodec_word3_val hTag c hC).trans (by rw [hslot])
    have st5 : step code input s5 = some (.next { s5 with pc := 8 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s5)
        (a := 12) (b := 15) (t := 8) (e := 6)
        (by change code[5]? = _; rw [hFetch 5 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
      simpa only [hw3_0, h15_5, ite_eq_left (by decide : (0 : Nat) < 1)] using hst
    have hHdrSteps : Steps ph.code input 6 (Phase.initial s)
        (relocateStatePC hdr.size (Phase.initial s5)) :=
      steps_trans pre5 (Steps.cons st5 (Steps.zero _))
    obtain ⟨u, hRun0, hUInt, hUr11, hUPres, hUData⟩ :=
      baseNonePhase_spec (fits := fits) hTag 12 13 14 (by decide) (by decide) (by decide)
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
        input s5 c.base hC.1 hAddr5 hBaseW0 hBaseW1 hBaseW2
    have hExec := branch3Phase_exec_0 hdr hHdr p0 p1 p2 hHdrSteps hRun0
    refine ⟨{ u with pc := ph.haltPC }, 6 + 9 + 1, by decide, hExec, ?_, ?_, ?_, hUData⟩
    · change IntervalWords hTag (Coord.eval c xs) (reg u 12) (reg u 13) (reg u 14)
      rw [Coord.eval, hslot]
      exact hUInt
    · intro hlt
      change (reg u 11).val = _
      rw [hUr11 (by rw [hPres5 11 (by decide) (by decide)]; exact hlt),
        hPres5 11 (by decide) (by decide)]
    · intro r hr
      change reg u r = _
      rw [hUPres r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
      exact hPres5 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
  | some j =>
    match j with
    | ⟨0, _⟩ =>
      have hw3_1 : (reg s5 12).val = 1 := by
        rw [h12_5]; exact (coordCodec_word3_val hTag c hC).trans (by rw [hslot])
      have st5 : step code input s5 = some (.next { s5 with pc := 6 }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s5)
          (a := 12) (b := 15) (t := 8) (e := 6)
          (by change code[5]? = _; rw [hFetch 5 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [hw3_1, h15_5, ite_eq_right (by decide : ¬ (1 : Nat) < 1)] using hst
      let s6 := putReg { s5 with pc := 6 } 15 ⟨2, hTag⟩
      have st6 : step code input { s5 with pc := 6 } = some (.next s6) :=
        step_imm_put (by change code[6]? = _; rw [hFetch 6 (by decide)]; rfl)
          (by change 6 + 1 < code.size; rw [hCodeSz]; omega)
      have h12_6 : (reg s6 12).val = 1 := by
        rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15)]; exact hw3_1
      have h15_6 : (reg s6 15).val = 2 := by
        rw [reg_putReg, ite_eq_left rfl]
      have st7 : step code input s6 = some (.next { s6 with pc := 8 + p0.code.size }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s6)
          (a := 12) (b := 15) (t := 8 + p0.code.size) (e := 8 + p0.code.size + p1.code.size)
          (by change code[7]? = _; rw [hFetch 7 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [h12_6, h15_6, ite_eq_left (by decide : (1 : Nat) < 2)] using hst
      have hHdrSteps : Steps ph.code input 8 (Phase.initial s)
          (relocateStatePC (hdr.size + p0.code.size) (Phase.initial s6)) :=
        steps_trans pre5 (Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <| Steps.zero _)
      have hPres6 : ∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg s6 r = reg s r := by
        intro r hr12 hr15
        change reg (putReg { s5 with pc := 6 } 15 _) r = _
        rw [reg_putReg, ite_eq_right hr15]
        exact hPres5 r hr12 hr15
      have hSrc0 : IntervalWords hTag xs.x0 (reg s6 0) (reg s6 1) (reg s6 2) := by
        rw [hPres6 0 (by decide) (by decide), hPres6 1 (by decide) (by decide),
          hPres6 2 (by decide) (by decide)]
        exact hXs.1
      have h6W0 : input.words[(reg s6 11).val]? = some ((intervalCodec hTag).encode c.base hC.1 0) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW0
      have h6W1 : input.words[(reg s6 11).val + 1]? = some ((intervalCodec hTag).encode c.base hC.1 1) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW1
      have h6W2 : input.words[(reg s6 11).val + 2]? = some ((intervalCodec hTag).encode c.base hC.1 2) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW2
      have hAddr6 : (reg s6 11).val + 4 ≤ inputCap := by
        rw [hPres6 11 (by decide) (by decide)]; exact hAddr
      obtain ⟨u, kP, hkP, hRun1, hUInt, hUr11, hUPres, hUData⟩ :=
        baseJoinPhase_spec (fits := fits) hTag 12 13 14 0 1 2 12 13 14
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (Or.inr ⟨⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩)
          input s6 c.base xs.x0 hC.1 hSrc0 hAddr6 h6W0 h6W1 h6W2
      have hExec := branch3Phase_exec_1 hdr hHdr p0 p1 p2 hHdrSteps hRun1
      refine ⟨{ u with pc := ph.haltPC }, 8 + kP + 1, by omega, hExec, ?_, ?_, ?_, hUData⟩
      · change IntervalWords hTag (Coord.eval c xs) (reg u 12) (reg u 13) (reg u 14)
        rw [Coord.eval, hslot]
        simpa [Two.get] using hUInt
      · intro hlt
        change (reg u 11).val = _
        rw [hUr11 (by rw [hPres6 11 (by decide) (by decide)]; exact hlt),
          hPres6 11 (by decide) (by decide)]
      · intro r hr
        change reg u r = _
        rw [hUPres r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
        exact hPres6 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    | ⟨1, _⟩ =>
      have hw3_2 : (reg s5 12).val = 2 := by
        rw [h12_5]; exact (coordCodec_word3_val hTag c hC).trans (by rw [hslot])
      have st5 : step code input s5 = some (.next { s5 with pc := 6 }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s5)
          (a := 12) (b := 15) (t := 8) (e := 6)
          (by change code[5]? = _; rw [hFetch 5 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [hw3_2, h15_5, ite_eq_right (by decide : ¬ (2 : Nat) < 1)] using hst
      let s6 := putReg { s5 with pc := 6 } 15 ⟨2, hTag⟩
      have st6 : step code input { s5 with pc := 6 } = some (.next s6) :=
        step_imm_put (by change code[6]? = _; rw [hFetch 6 (by decide)]; rfl)
          (by change 6 + 1 < code.size; rw [hCodeSz]; omega)
      have h12_6 : (reg s6 12).val = 2 := by
        rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15)]; exact hw3_2
      have h15_6 : (reg s6 15).val = 2 := by
        rw [reg_putReg, ite_eq_left rfl]
      have st7 : step code input s6 = some (.next { s6 with pc := 8 + p0.code.size + p1.code.size }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s6)
          (a := 12) (b := 15) (t := 8 + p0.code.size) (e := 8 + p0.code.size + p1.code.size)
          (by change code[7]? = _; rw [hFetch 7 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [h12_6, h15_6, ite_eq_right (by decide : ¬ (2 : Nat) < 2)] using hst
      have hHdrSteps : Steps ph.code input 8 (Phase.initial s)
          (relocateStatePC (hdr.size + p0.code.size + p1.code.size) (Phase.initial s6)) :=
        steps_trans pre5 (Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <| Steps.zero _)
      have hPres6 : ∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg s6 r = reg s r := by
        intro r hr12 hr15
        change reg (putReg { s5 with pc := 6 } 15 _) r = _
        rw [reg_putReg, ite_eq_right hr15]
        exact hPres5 r hr12 hr15
      have hSrc1 : IntervalWords hTag xs.x1 (reg s6 3) (reg s6 4) (reg s6 5) := by
        rw [hPres6 3 (by decide) (by decide), hPres6 4 (by decide) (by decide),
          hPres6 5 (by decide) (by decide)]
        exact hXs.2
      have h6W0 : input.words[(reg s6 11).val]? = some ((intervalCodec hTag).encode c.base hC.1 0) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW0
      have h6W1 : input.words[(reg s6 11).val + 1]? = some ((intervalCodec hTag).encode c.base hC.1 1) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW1
      have h6W2 : input.words[(reg s6 11).val + 2]? = some ((intervalCodec hTag).encode c.base hC.1 2) := by
        rw [hPres6 11 (by decide) (by decide)]; exact hW2
      have hAddr6 : (reg s6 11).val + 4 ≤ inputCap := by
        rw [hPres6 11 (by decide) (by decide)]; exact hAddr
      obtain ⟨u, kP, hkP, hRun2, hUInt, hUr11, hUPres, hUData⟩ :=
        baseJoinPhase_spec (fits := fits) hTag 12 13 14 3 4 5 12 13 14
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (Or.inr ⟨⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩)
          input s6 c.base xs.x1 hC.1 hSrc1 hAddr6 h6W0 h6W1 h6W2
      have hExec := branch3Phase_exec_2 hdr hHdr p0 p1 p2 hHdrSteps hRun2
      refine ⟨{ u with pc := ph.haltPC }, 8 + kP + 1, by omega, hExec, ?_, ?_, ?_, hUData⟩
      · change IntervalWords hTag (Coord.eval c xs) (reg u 12) (reg u 13) (reg u 14)
        rw [Coord.eval, hslot]
        simpa [Two.get] using hUInt
      · intro hlt
        change (reg u 11).val = _
        rw [hUr11 (by rw [hPres6 11 (by decide) (by decide)]; exact hlt),
          hPres6 11 (by decide) (by decide)]
      · intro r hr
        change reg u r = _
        rw [hUPres r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))]
        exact hPres6 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))

/-! ### Phase 4: `copy0Phase`, `applyMapPhase`, `selectRecordPhase`, `decRemPhase`, `hopBodyPhase` -/

private theorem phase_link_run (p q : Phase L)
    {input : Input L} {s m u : State L} {a b : Nat}
    (hp : run p.code input a (Phase.initial s) = some ⟨m, a⟩)
    (hq : run q.code input b (Phase.initial m) = some ⟨u, b⟩) :
    ∃ v : State L, (∀ r : Fin 16, reg v r = reg u r) ∧ v.data = u.data ∧
      run (p.link q).code input (a + b) (Phase.initial s) = some ⟨v, a + b⟩ := by
  obtain ⟨v, _, hvRegs, hvData, hRun, _, _⟩ :=
    run_linked_pair p q.code (Nat.zero_lt_of_lt q.haltFits) hp hq
  refine ⟨v, ?_, hvData, hRun⟩
  intro r
  cases v
  cases u
  simp only at hvRegs
  cases hvRegs
  rfl

private def copy0Code : Program L :=
  #[.mov 0 12, .mov 1 13, .mov 2 14, .halt]

private def copy0Phase : Phase L :=
  Phase.ofLast copy0Code 3 rfl rfl (by simp [copy0Code, nonHalt])

private theorem copy0Phase_spec (input : Input L) (s : State L) :
    ∃ t : State L,
      run (copy0Phase (fits := fits)).code input 4 (Phase.initial s) = some ⟨t, 4⟩ ∧
      reg t 0 = reg s 12 ∧ reg t 1 = reg s 13 ∧ reg t 2 = reg s 14 ∧
      (∀ r : Fin 16, 3 ≤ r.val → reg t r = reg s r) ∧
      t.data = s.data := by
  let code := (copy0Phase (fits := fits)).code
  have hsz : code.size = 4 := rfl
  let s0 := Phase.initial s
  let s1 := putReg s0 0 (reg s0 12)
  let s2 := putReg s1 1 (reg s1 13)
  let s3 := putReg s2 2 (reg s2 14)
  have st0 : step code input s0 = some (.next s1) :=
    step_mov_put rfl (by rw [hsz]; exact (show 0 + 1 < 4 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_mov_put rfl (by rw [hsz]; exact (show 1 + 1 < 4 by decide))
  have st2 : step code input s2 = some (.next s3) :=
    step_mov_put rfl (by rw [hsz]; exact (show 2 + 1 < 4 by decide))
  have hh : step code input s3 = some (.halted s3) := step_halt_at rfl
  have exec := (Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.zero s3).halts hh
  refine ⟨s3, exec, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (0 : Fin 16) ≠ 2),
      ite_eq_right (by decide : (0 : Fin 16) ≠ 1), ite_true]; rfl
  · simp only [s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (1 : Fin 16) ≠ 2),
      ite_eq_right (by decide : (13 : Fin 16) ≠ 0), ite_true]; rfl
  · simp only [s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (14 : Fin 16) ≠ 1),
      ite_eq_right (by decide : (14 : Fin 16) ≠ 0), ite_true]; rfl
  · intro r hr
    simp only [s3, s2, s1, s0, reg_putReg,
      ite_eq_right (Fin.ne_of_val_ne (by omega) : r ≠ 2),
      ite_eq_right (Fin.ne_of_val_ne (by omega) : r ≠ 1),
      ite_eq_right (Fin.ne_of_val_ne (by omega) : r ≠ 0)]
    rfl

private def applyMapHeader (hTag : TagsFit bits) (b0 b1 b2 : Nat) : Program L :=
  #[.imm 15 ⟨2, hTag⟩,
    .add 12 11 15,
    .add 12 12 15,
    .add 12 12 15,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 12 12 15,
    .loadInput 12 12,
    .branchLt 12 15 b0 8,
    .imm 15 ⟨2, hTag⟩,
    .branchLt 12 15 b1 b2]

private theorem applyMapHeader_nonhalt (hTag : TagsFit bits) (b0 b1 b2 : Nat) :
    (applyMapHeader (fits := fits) hTag b0 b1 b2).toList.all (@nonHalt bits L) = true := by
  simp [applyMapHeader, nonHalt]

private def applyMapP0 (hTag : TagsFit bits) : Phase L :=
  (coord0Phase hTag).link ((baseNonePhase hTag 3 4 5).link copy0Phase)

private def applyMapP1 (hTag : TagsFit bits) : Phase L :=
  (coord0Phase hTag).link ((baseJoinPhase hTag 3 4 5 0 1 2 3 4 5).link copy0Phase)

private def applyMapP2 (hTag : TagsFit bits) : Phase L :=
  (coord0Phase hTag).link (copy0Phase.link (baseJoinPhase hTag 3 4 5 3 4 5 12 13 14))

private def applyMapPhase (hTag : TagsFit bits) : Phase L :=
  let p0 : Phase L := applyMapP0 hTag
  let p1 : Phase L := applyMapP1 hTag
  let p2 : Phase L := applyMapP2 hTag
  let hdr := applyMapHeader hTag 10 (10 + p0.code.size) (10 + p0.code.size + p1.code.size)
  branch3Phase hdr (applyMapHeader_nonhalt hTag _ _ _) p0 p1 p2

private theorem applyMapPhase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (m : Map) (xs : Values)
    (hM : (mapCodec hTag).valid m)
    (hXs : ValuesRegs hTag xs s)
    (hAddr : (reg s 11).val + 8 ≤ inputCap)
    (hW : ∀ idx : Fin 8,
      input.words[(reg s 11).val + idx.val]? = some ((mapCodec hTag).encode m hM idx)) :
    ∃ (t : State L) (k : Nat),
      k ≤ 66 ∧
      run (applyMapPhase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      ValuesRegs hTag (Map.eval m xs) t ∧
      (∀ r : Fin 16, 6 ≤ r.val → r.val ≤ 10 → reg t r = reg s r) ∧
      t.data = s.data := by
  let p0 : Phase L := applyMapP0 hTag
  let p1 : Phase L := applyMapP1 hTag
  let p2 : Phase L := applyMapP2 hTag
  let hdr := applyMapHeader (fits := fits) hTag 10 (10 + p0.code.size) (10 + p0.code.size + p1.code.size)
  have hHdr := applyMapHeader_nonhalt (fits := fits) hTag 10 (10 + p0.code.size)
    (10 + p0.code.size + p1.code.size)
  let ph := branch3Phase hdr hHdr p0 p1 p2
  let code := ph.code
  have hHdrSz : hdr.size = 10 := rfl
  have hCodeSz : code.size = 10 + p0.code.size + p1.code.size + p2.code.size + 1 := by
    have hSz := branch3Code_size hdr p0 p1 p2
    change code.size = hdr.size + p0.code.size + p1.code.size + p2.code.size + 1 at hSz
    rw [hHdrSz] at hSz
    exact hSz
  have hFetch : ∀ j, j < 10 → code[j]? = hdr[j]? := fun j hj =>
    branch3Code_slice_hdr hdr p0 p1 p2 hj
  have h8Lt : (reg s 11).val + 8 ≤ 2 ^ bits := Nat.le_trans hAddr fits
  let s0 := Phase.initial s
  let s1 := putReg s0 15 ⟨2, hTag⟩
  let s2 := putReg s1 12 (add (reg s1 11) (reg s1 15))
  let s3 := putReg s2 12 (add (reg s2 12) (reg s2 15))
  let s4 := putReg s3 12 (add (reg s3 12) (reg s3 15))
  let s5 := putReg s4 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s6 := putReg s5 12 (add (reg s5 12) (reg s5 15))
  let w7 := (mapCodec hTag).encode m hM ⟨7, by decide⟩
  let s7 := putReg s6 12 w7
  have st0 : step code input s0 = some (.next s1) :=
    step_imm_put (by change code[0]? = _; rw [hFetch 0 (by decide)]; rfl)
      (by change 0 + 1 < code.size; rw [hCodeSz]; omega)
  have st1 : step code input s1 = some (.next s2) :=
    step_add_put (by change code[1]? = _; rw [hFetch 1 (by decide)]; rfl)
      (by change 1 + 1 < code.size; rw [hCodeSz]; omega)
  have r15_1 : (reg s1 15).val = 2 := by simp only [s1, reg_putReg, ite_true]
  have r11_1 : (reg s1 11).val = (reg s 11).val := by
    simp only [s1, s0, reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 15)]; rfl
  have r12_2 : (reg s2 12).val = (reg s 11).val + 2 := by
    change (reg (putReg s1 12 _) 12).val = _
    have hlt : (reg s1 11).val + (reg s1 15).val < 2 ^ bits := by rw [r11_1, r15_1]; omega
    simp only [reg_putReg, ite_true, add_no_wrap _ _ hlt, r11_1, r15_1]
  have r15_2 : (reg s2 15).val = 2 := by
    change (reg (putReg s1 12 _) 15).val = 2
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 12), r15_1]
  have st2 : step code input s2 = some (.next s3) :=
    step_add_put (by change code[2]? = _; rw [hFetch 2 (by decide)]; rfl)
      (by change 2 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_3 : (reg s3 12).val = (reg s 11).val + 4 := by
    change (reg (putReg s2 12 _) 12).val = _
    have hlt : (reg s2 12).val + (reg s2 15).val < 2 ^ bits := by rw [r12_2, r15_2]; omega
    simp only [reg_putReg, ite_true, add_no_wrap _ _ hlt, r12_2, r15_2]
  have r15_3 : (reg s3 15).val = 2 := by
    change (reg (putReg s2 12 _) 15).val = 2
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 12), r15_2]
  have st3 : step code input s3 = some (.next s4) :=
    step_add_put (by change code[3]? = _; rw [hFetch 3 (by decide)]; rfl)
      (by change 3 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_4 : (reg s4 12).val = (reg s 11).val + 6 := by
    change (reg (putReg s3 12 _) 12).val = _
    have hlt : (reg s3 12).val + (reg s3 15).val < 2 ^ bits := by rw [r12_3, r15_3]; omega
    simp only [reg_putReg, ite_true, add_no_wrap _ _ hlt, r12_3, r15_3]
  have st4 : step code input s4 = some (.next s5) :=
    step_imm_put (by change code[4]? = _; rw [hFetch 4 (by decide)]; rfl)
      (by change 4 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_5 : (reg s5 12).val = (reg s 11).val + 6 := by
    change (reg (putReg s4 15 _) 12).val = _
    rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15), r12_4]
  have r15_5 : (reg s5 15).val = 1 := by simp only [s5, reg_putReg, ite_true]
  have st5 : step code input s5 = some (.next s6) :=
    step_add_put (by change code[5]? = _; rw [hFetch 5 (by decide)]; rfl)
      (by change 5 + 1 < code.size; rw [hCodeSz]; omega)
  have r12_6 : (reg s6 12).val = (reg s 11).val + 7 := by
    change (reg (putReg s5 12 _) 12).val = _
    have hlt : (reg s5 12).val + (reg s5 15).val < 2 ^ bits := by rw [r12_5, r15_5]; omega
    simp only [reg_putReg, ite_true, add_no_wrap _ _ hlt, r12_5, r15_5]
  have st6 : step code input s6 = some (.next s7) :=
    step_loadInput_put (by change code[6]? = _; rw [hFetch 6 (by decide)]; rfl)
      (by rw [r12_6]; exact hW ⟨7, by decide⟩)
      (by change 6 + 1 < code.size; rw [hCodeSz]; omega)
  have pre7 : Steps code input 7 s0 s7 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.zero s7
  have h12_7 : reg s7 12 = w7 := by simp only [s7, reg_putReg, ite_true]
  have h15_7 : (reg s7 15).val = 1 := by
    change (reg (putReg s6 12 w7) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 12)]
    change (reg (putReg s5 12 _) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 12), r15_5]
  have hPres7 : ∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg s7 r = reg s r := by
    intro r hr12 hr15
    simp only [s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right hr12, ite_eq_right hr15]
    rfl
  have hw7_eq : w7 = (coordCodec hTag).encode m.x1 hM.2 3 :=
    mapCodec_word_x1 hTag m hM 3
  have runCoord0 : ∀ sStart : State L,
      (∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg sStart r = reg s r) →
      sStart.data = s.data →
      ∃ (u1 : State L) (k1 : Nat),
        k1 ≤ 30 ∧
        run (coord0Phase (fits := fits) hTag).code input k1 (Phase.initial sStart) = some ⟨u1, k1⟩ ∧
        IntervalWords hTag (Coord.eval m.x0 xs) (reg u1 12) (reg u1 13) (reg u1 14) ∧
        (reg u1 11).val = (reg s 11).val + 4 ∧
        (∀ r : Fin 16, r < 11 → reg u1 r = reg s r) ∧
        u1.data = s.data := by
    intro sStart hPr hD
    have hXsS : ValuesRegs hTag xs sStart := by
      refine ⟨?_, ?_⟩
      · rw [hPr 0 (by decide) (by decide), hPr 1 (by decide) (by decide),
          hPr 2 (by decide) (by decide)]
        exact hXs.1
      · rw [hPr 3 (by decide) (by decide), hPr 4 (by decide) (by decide),
          hPr 5 (by decide) (by decide)]
        exact hXs.2
    have hAddrS : (reg sStart 11).val + 4 ≤ inputCap := by
      rw [hPr 11 (by decide) (by decide)]; omega
    have hS0 : input.words[(reg sStart 11).val]? = some ((coordCodec hTag).encode m.x0 hM.1 0) := by
      rw [hPr 11 (by decide) (by decide), ← mapCodec_word_x0 hTag m hM 0]
      exact hW 0
    have hS1 : input.words[(reg sStart 11).val + 1]? = some ((coordCodec hTag).encode m.x0 hM.1 1) := by
      rw [hPr 11 (by decide) (by decide), ← mapCodec_word_x0 hTag m hM 1]
      exact hW 1
    have hS2 : input.words[(reg sStart 11).val + 2]? = some ((coordCodec hTag).encode m.x0 hM.1 2) := by
      rw [hPr 11 (by decide) (by decide), ← mapCodec_word_x0 hTag m hM 2]
      exact hW 2
    have hS3 : input.words[(reg sStart 11).val + 3]? = some ((coordCodec hTag).encode m.x0 hM.1 3) := by
      rw [hPr 11 (by decide) (by decide), ← mapCodec_word_x0 hTag m hM 3]
      exact hW 3
    obtain ⟨u1, k1, hk1, hR1, hI1, hr11, hP1, hD1⟩ :=
      coord0Phase_spec hTag input sStart m.x0 xs hM.1 hXsS hAddrS hS0 hS1 hS2 hS3
    refine ⟨u1, k1, hk1, hR1, hI1, ?_, ?_, hD1.trans hD⟩
    · rw [hr11 (by rw [hPr 11 (by decide) (by decide)]; omega), hPr 11 (by decide) (by decide)]
    · intro r hr
      rw [hP1 r hr]
      exact hPr r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
  have hBaseX1W0 : ∀ r11 : Word bits, r11.val = (reg s 11).val + 4 →
      input.words[r11.val]? = some ((intervalCodec hTag).encode m.x1.base hM.2.1 0) := by
    intro r11 hr11
    rw [hr11]
    exact (hW ⟨4, by decide⟩).trans (congrArg some
      ((mapCodec_word_x1 hTag m hM 0).trans (coordCodec_word_base hTag m.x1 hM.2 0)))
  have hBaseX1W1 : ∀ r11 : Word bits, r11.val = (reg s 11).val + 4 →
      input.words[r11.val + 1]? = some ((intervalCodec hTag).encode m.x1.base hM.2.1 1) := by
    intro r11 hr11
    rw [hr11, Nat.add_assoc]
    exact (hW ⟨5, by decide⟩).trans (congrArg some
      ((mapCodec_word_x1 hTag m hM 1).trans (coordCodec_word_base hTag m.x1 hM.2 1)))
  have hBaseX1W2 : ∀ r11 : Word bits, r11.val = (reg s 11).val + 4 →
      input.words[r11.val + 2]? = some ((intervalCodec hTag).encode m.x1.base hM.2.1 2) := by
    intro r11 hr11
    rw [hr11, Nat.add_assoc]
    exact (hW ⟨6, by decide⟩).trans (congrArg some
      ((mapCodec_word_x1 hTag m hM 2).trans (coordCodec_word_base hTag m.x1 hM.2 2)))
  cases hslot : m.x1.slot with
  | none =>
    have hw7_0 : (reg s7 12).val = 0 := by
      rw [h12_7, hw7_eq]; exact (coordCodec_word3_val hTag m.x1 hM.2).trans (by rw [hslot])
    have st7 : step code input s7 = some (.next { s7 with pc := 10 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s7)
        (a := 12) (b := 15) (t := 10) (e := 8)
        (by change code[7]? = _; rw [hFetch 7 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
      simpa only [hw7_0, h15_7, ite_eq_left (by decide : (0 : Nat) < 1)] using hst
    have hHdrSteps : Steps ph.code input 8 (Phase.initial s)
        (relocateStatePC hdr.size (Phase.initial s7)) :=
      steps_trans pre7 (Steps.cons st7 (Steps.zero _))
    obtain ⟨u1, k1, hk1, hR1, hI1, hu11, hP1, hD1⟩ := runCoord0 s7 hPres7 rfl
    obtain ⟨u2, hR2, hI2, _, hP2, hD2⟩ :=
      baseNonePhase_spec (fits := fits) hTag 3 4 5 (by decide) (by decide) (by decide)
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
        input u1 m.x1.base hM.2.1 (by rw [hu11]; omega)
        (hBaseX1W0 (reg u1 11) hu11) (hBaseX1W1 (reg u1 11) hu11) (hBaseX1W2 (reg u1 11) hu11)
    obtain ⟨u3, hR3, hr0, hr1, hr2, hP3, hD3⟩ := copy0Phase_spec input u2
    obtain ⟨m23, hm23Reg, hm23Data, hLink23⟩ := phase_link_run _ _ hR2 hR3
    obtain ⟨uAll, huAllReg, huAllData, hLinkAll⟩ := phase_link_run _ _ hR1 hLink23
    have hExec := branch3Phase_exec_0 hdr hHdr p0 p1 p2 hHdrSteps hLinkAll
    refine ⟨{ uAll with pc := ph.haltPC }, 8 + (k1 + (9 + 4)) + 1, by omega, hExec, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change IntervalWords hTag (Map.eval m xs).x0 (reg uAll 0) (reg uAll 1) (reg uAll 2)
        rw [huAllReg 0, huAllReg 1, huAllReg 2, hm23Reg 0, hm23Reg 1, hm23Reg 2, hr0, hr1, hr2,
          hP2 12 (by decide) (by decide) (by decide) (by decide) (by decide),
          hP2 13 (by decide) (by decide) (by decide) (by decide) (by decide),
          hP2 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hI1
      · change IntervalWords hTag (Map.eval m xs).x1 (reg uAll 3) (reg uAll 4) (reg uAll 5)
        rw [huAllReg 3, huAllReg 4, huAllReg 5, hm23Reg 3, hm23Reg 4, hm23Reg 5,
          hP3 3 (by decide), hP3 4 (by decide), hP3 5 (by decide)]
        change IntervalWords hTag (Coord.eval m.x1 xs) _ _ _
        rw [Coord.eval, hslot]
        exact hI2
    · intro r hr6 hr10
      change reg uAll r = _
      rw [huAllReg r, hm23Reg r, hP3 r (by omega),
        hP2 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)),
        hP1 r (by change r.val < 11; omega)]
    · exact huAllData.trans (hm23Data.trans (hD3.trans (hD2.trans hD1)))
  | some j =>
    have hw7_ge1 : (reg s7 12).val = if j = 0 then 1 else 2 := by
      rw [h12_7, hw7_eq, coordCodec_word3_val hTag m.x1 hM.2, hslot]
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    have hNotLt1 : ¬ ((reg s7 12).val < (reg s7 15).val) := by
      rw [hw7_ge1, h15_7]
      split <;> decide
    have st7 : step code input s7 = some (.next { s7 with pc := 8 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s7)
        (a := 12) (b := 15) (t := 10) (e := 8)
        (by change code[7]? = _; rw [hFetch 7 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
      simpa only [ite_eq_right hNotLt1] using hst
    let s8 := putReg { s7 with pc := 8 } 15 ⟨2, hTag⟩
    have st8 : step code input { s7 with pc := 8 } = some (.next s8) :=
      step_imm_put (by change code[8]? = _; rw [hFetch 8 (by decide)]; rfl)
        (by change 8 + 1 < code.size; rw [hCodeSz]; omega)
    have h15_8 : (reg s8 15).val = 2 := by simp only [s8, reg_putReg, ite_true]
    have hPres8 : ∀ r : Fin 16, r ≠ 12 → r ≠ 15 → reg s8 r = reg s r := by
      intro r hr12 hr15
      change reg (putReg { s7 with pc := 8 } 15 _) r = _
      rw [reg_putReg, ite_eq_right hr15]
      exact hPres7 r hr12 hr15
    match j with
    | ⟨0, _⟩ =>
      have h12_8 : (reg s8 12).val = 1 := by
        change (reg (putReg { s7 with pc := 8 } 15 _) 12).val = 1
        rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15)]
        exact hw7_ge1
      have st9 : step code input s8 = some (.next { s8 with pc := 10 + p0.code.size }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s8)
          (a := 12) (b := 15) (t := 10 + p0.code.size) (e := 10 + p0.code.size + p1.code.size)
          (by change code[9]? = _; rw [hFetch 9 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [h12_8, h15_8, ite_eq_left (by decide : (1 : Nat) < 2)] using hst
      have hHdrSteps : Steps ph.code input 10 (Phase.initial s)
          (relocateStatePC (hdr.size + p0.code.size) (Phase.initial s8)) :=
        steps_trans pre7 (Steps.cons st7 <| Steps.cons st8 <| Steps.cons st9 <| Steps.zero _)
      obtain ⟨u1, k1, hk1, hR1, hI1, hu11, hP1, hD1⟩ := runCoord0 s8 hPres8 rfl
      have hSrc0 : IntervalWords hTag xs.x0 (reg u1 0) (reg u1 1) (reg u1 2) := by
        rw [hP1 0 (by decide), hP1 1 (by decide), hP1 2 (by decide)]
        exact hXs.1
      obtain ⟨u2, k2, hk2, hR2, hI2, _, hP2, hD2⟩ :=
        baseJoinPhase_spec (fits := fits) hTag 3 4 5 0 1 2 3 4 5
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (Or.inr ⟨⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩)
          input u1 m.x1.base xs.x0 hM.2.1 hSrc0 (by rw [hu11]; omega)
          (hBaseX1W0 (reg u1 11) hu11) (hBaseX1W1 (reg u1 11) hu11) (hBaseX1W2 (reg u1 11) hu11)
      obtain ⟨u3, hR3, hr0, hr1, hr2, hP3, hD3⟩ := copy0Phase_spec input u2
      obtain ⟨m23, hm23Reg, hm23Data, hLink23⟩ := phase_link_run _ _ hR2 hR3
      obtain ⟨uAll, huAllReg, huAllData, hLinkAll⟩ := phase_link_run _ _ hR1 hLink23
      have hExec := branch3Phase_exec_1 hdr hHdr p0 p1 p2 hHdrSteps hLinkAll
      refine ⟨{ uAll with pc := ph.haltPC }, 10 + (k1 + (k2 + 4)) + 1, by omega, hExec, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · change IntervalWords hTag (Map.eval m xs).x0 (reg uAll 0) (reg uAll 1) (reg uAll 2)
          rw [huAllReg 0, huAllReg 1, huAllReg 2, hm23Reg 0, hm23Reg 1, hm23Reg 2, hr0, hr1, hr2,
            hP2 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hP2 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hP2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hI1
        · change IntervalWords hTag (Map.eval m xs).x1 (reg uAll 3) (reg uAll 4) (reg uAll 5)
          rw [huAllReg 3, huAllReg 4, huAllReg 5, hm23Reg 3, hm23Reg 4, hm23Reg 5,
            hP3 3 (by decide), hP3 4 (by decide), hP3 5 (by decide)]
          change IntervalWords hTag (Coord.eval m.x1 xs) _ _ _
          rw [Coord.eval, hslot]
          simpa [Two.get] using hI2
      · intro r hr6 hr10
        change reg uAll r = _
        rw [huAllReg r, hm23Reg r, hP3 r (by omega),
          hP2 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)),
          hP1 r (by change r.val < 11; omega)]
      · exact huAllData.trans (hm23Data.trans (hD3.trans (hD2.trans hD1)))
    | ⟨1, _⟩ =>
      have h12_8 : (reg s8 12).val = 2 := by
        change (reg (putReg { s7 with pc := 8 } 15 _) 12).val = 2
        rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 15)]
        exact hw7_ge1
      have st9 : step code input s8 = some (.next { s8 with pc := 10 + p0.code.size + p1.code.size }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s8)
          (a := 12) (b := 15) (t := 10 + p0.code.size) (e := 10 + p0.code.size + p1.code.size)
          (by change code[9]? = _; rw [hFetch 9 (by decide)]; rfl) (by split <;> rw [hCodeSz] <;> omega)
        simpa only [h12_8, h15_8, ite_eq_right (by decide : ¬ (2 : Nat) < 2)] using hst
      have hHdrSteps : Steps ph.code input 10 (Phase.initial s)
          (relocateStatePC (hdr.size + p0.code.size + p1.code.size) (Phase.initial s8)) :=
        steps_trans pre7 (Steps.cons st7 <| Steps.cons st8 <| Steps.cons st9 <| Steps.zero _)
      obtain ⟨u1, k1, hk1, hR1, hI1, hu11, hP1, hD1⟩ := runCoord0 s8 hPres8 rfl
      obtain ⟨u2, hR2, hr0, hr1, hr2, hP2, hD2⟩ := copy0Phase_spec input u1
      have hSrc1 : IntervalWords hTag xs.x1 (reg u2 3) (reg u2 4) (reg u2 5) := by
        rw [hP2 3 (by decide), hP2 4 (by decide), hP2 5 (by decide),
          hP1 3 (by decide), hP1 4 (by decide), hP1 5 (by decide)]
        exact hXs.2
      have hu2_11 : (reg u2 11).val = (reg s 11).val + 4 := by
        rw [hP2 11 (by decide), hu11]
      obtain ⟨u3, k3, hk3, hR3, hI3, _, hP3, hD3⟩ :=
        baseJoinPhase_spec (fits := fits) hTag 3 4 5 3 4 5 12 13 14
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (by decide) (by decide) (by decide)
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
          (Or.inr ⟨⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩)
          (Or.inl ⟨rfl, rfl, rfl⟩)
          input u2 m.x1.base xs.x1 hM.2.1 hSrc1 (by rw [hu2_11]; omega)
          (hBaseX1W0 (reg u2 11) hu2_11) (hBaseX1W1 (reg u2 11) hu2_11) (hBaseX1W2 (reg u2 11) hu2_11)
      obtain ⟨m23, hm23Reg, hm23Data, hLink23⟩ := phase_link_run _ _ hR2 hR3
      obtain ⟨uAll, huAllReg, huAllData, hLinkAll⟩ := phase_link_run _ _ hR1 hLink23
      have hExec := branch3Phase_exec_2 hdr hHdr p0 p1 p2 hHdrSteps hLinkAll
      refine ⟨{ uAll with pc := ph.haltPC }, 10 + (k1 + (4 + k3)) + 1, by omega, hExec, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · change IntervalWords hTag (Map.eval m xs).x0 (reg uAll 0) (reg uAll 1) (reg uAll 2)
          rw [huAllReg 0, huAllReg 1, huAllReg 2, hm23Reg 0, hm23Reg 1, hm23Reg 2,
            hP3 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hP3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hP3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hr0, hr1, hr2]
          exact hI1
        · change IntervalWords hTag (Map.eval m xs).x1 (reg uAll 3) (reg uAll 4) (reg uAll 5)
          rw [huAllReg 3, huAllReg 4, huAllReg 5, hm23Reg 3, hm23Reg 4, hm23Reg 5]
          change IntervalWords hTag (Coord.eval m.x1 xs) _ _ _
          rw [Coord.eval, hslot]
          simpa [Two.get] using hI3
      · intro r hr6 hr10
        change reg uAll r = _
        rw [huAllReg r, hm23Reg r,
          hP3 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
            (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)),
          hP2 r (by omega),
          hP1 r (by change r.val < 11; omega)]
      · exact huAllData.trans (hm23Data.trans (hD3.trans (hD2.trans hD1)))

private def selectRecordCode (hTag : TagsFit bits) : Program L :=
  #[.add 12 6 6,
    .add 12 12 12,
    .add 12 12 12,
    .add 12 12 6,
    .add 12 12 12,
    .add 11 10 12,
    .loadInput 12 11,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 11 11 15,
    .loadInput 13 11,
    .add 11 11 15,
    .add 14 9 13,
    .loadInput 14 14,
    .branchLt 14 7 14 16,
    .mov 6 12,
    .goto 22,
    .mov 6 13,
    .imm 15 ⟨2, hTag⟩,
    .add 11 11 15,
    .add 11 11 15,
    .add 11 11 15,
    .add 11 11 15,
    .halt]

private def selectRecordPhase (hTag : TagsFit bits) : Phase L :=
  Phase.ofLast (selectRecordCode hTag) 22 rfl rfl (by simp [selectRecordCode, nonHalt])

private theorem selectRecord_pre13 (hTag : TagsFit bits)
    (input : Input L) (s : State L) (rec : Stored) (depthJump : Nat)
    (hRec : (storedCodec hTag).valid rec)
    (hDepthJumpLt : depthJump < 2 ^ bits)
    (hRecAddr : (reg s 10).val + 18 * (reg s 6).val + 18 ≤ inputCap)
    (hJumpDepthAddr : (reg s 9).val + rec.jump < inputCap)
    (hRecW : ∀ i : Fin 18,
      input.words[(reg s 10).val + 18 * (reg s 6).val + i.val]? =
        some ((storedCodec hTag).encode rec hRec i))
    (hDepthJumpW : input.words[(reg s 9).val + rec.jump]? =
      some ⟨depthJump, hDepthJumpLt⟩) :
    ∃ s13 : State L,
      Steps (selectRecordPhase (fits := fits) hTag).code input 13 (Phase.initial s) s13 ∧
      s13.pc = 13 ∧
      reg s13 7 = reg s 7 ∧
      (reg s13 14).val = depthJump ∧
      (reg s13 12).val = rec.parent ∧
      (reg s13 13).val = rec.jump ∧
      (reg s13 11).val = (reg s 10).val + 18 * (reg s 6).val + 2 ∧
      (∀ r : Fin 16, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → reg s13 r = reg s r) ∧
      s13.data = s.data := by
  let code := (selectRecordPhase (fits := fits) hTag).code
  have hsz : code.size = 23 := rfl
  have h18Lt : (reg s 10).val + 18 * (reg s 6).val + 18 ≤ 2 ^ bits := Nat.le_trans hRecAddr fits
  have hJD2 : (reg s 9).val + rec.jump < 2 ^ bits := Nat.lt_of_lt_of_le hJumpDepthAddr fits
  let u := (reg s 6).val
  let sb := (reg s 10).val
  let s0 := Phase.initial s
  let s1 := putReg s0 12 (add (reg s0 6) (reg s0 6))
  let s2 := putReg s1 12 (add (reg s1 12) (reg s1 12))
  let s3 := putReg s2 12 (add (reg s2 12) (reg s2 12))
  let s4 := putReg s3 12 (add (reg s3 12) (reg s3 6))
  let s5 := putReg s4 12 (add (reg s4 12) (reg s4 12))
  let s6 := putReg s5 11 (add (reg s5 10) (reg s5 12))
  let wP := (storedCodec hTag).encode rec hRec ⟨0, by decide⟩
  let s7 := putReg s6 12 wP
  let s8 := putReg s7 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s9 := putReg s8 11 (add (reg s8 11) (reg s8 15))
  let wJ := (storedCodec hTag).encode rec hRec ⟨1, by decide⟩
  let s10 := putReg s9 13 wJ
  let s11 := putReg s10 11 (add (reg s10 11) (reg s10 15))
  let s12 := putReg s11 14 (add (reg s11 9) (reg s11 13))
  let s13 := putReg s12 14 ⟨depthJump, hDepthJumpLt⟩
  have r12_1 : (reg s1 12).val = 2 * u := by
    change (reg (putReg s0 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by change u + u < 2 ^ bits; omega)]
    change u + u = 2 * u; omega
  have r12_2 : (reg s2 12).val = 4 * u := by
    change (reg (putReg s1 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_1]; omega), r12_1]; omega
  have r12_3 : (reg s3 12).val = 8 * u := by
    change (reg (putReg s2 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_2]; omega), r12_2]; omega
  have r6_3 : (reg s3 6).val = u := by
    simp only [s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (6 : Fin 16) ≠ 12)]; rfl
  have r12_4 : (reg s4 12).val = 9 * u := by
    change (reg (putReg s3 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_3, r6_3]; omega), r12_3, r6_3]; omega
  have r12_5 : (reg s5 12).val = 18 * u := by
    change (reg (putReg s4 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_4]; omega), r12_4]; omega
  have r10_5 : (reg s5 10).val = sb := by
    simp only [s5, s4, s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (10 : Fin 16) ≠ 12)]; rfl
  have r11_6 : (reg s6 11).val = sb + 18 * u := by
    change (reg (putReg s5 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r10_5, r12_5]; omega), r10_5, r12_5]
  have r11_8 : (reg s8 11).val = sb + 18 * u := by
    change (reg (putReg (putReg s6 12 wP) 15 _) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 15),
      reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 12), r11_6]
  have r15_8 : (reg s8 15).val = 1 := by simp only [s8, reg_putReg, ite_true]
  have r11_9 : (reg s9 11).val = sb + 18 * u + 1 := by
    change (reg (putReg s8 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_8, r15_8]; omega), r11_8, r15_8]
  have r11_10 : (reg s10 11).val = sb + 18 * u + 1 := by
    change (reg (putReg s9 13 wJ) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 13), r11_9]
  have r15_10 : (reg s10 15).val = 1 := by
    change (reg (putReg (putReg s8 11 _) 13 wJ) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 13),
      reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_8]
  have r11_11 : (reg s11 11).val = sb + 18 * u + 2 := by
    change (reg (putReg s10 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_10, r15_10]; omega), r11_10, r15_10]
  have r9_11 : (reg s11 9).val = (reg s 9).val := by
    simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
      ite_eq_right (by decide : (9 : Fin 16) ≠ 11),
      ite_eq_right (by decide : (9 : Fin 16) ≠ 13),
      ite_eq_right (by decide : (9 : Fin 16) ≠ 15),
      ite_eq_right (by decide : (9 : Fin 16) ≠ 12)]
    rfl
  have r13_11 : (reg s11 13).val = rec.jump := by
    change (reg (putReg s10 11 _) 13).val = _
    rw [reg_putReg, ite_eq_right (by decide : (13 : Fin 16) ≠ 11)]
    change (reg (putReg s9 13 wJ) 13).val = _
    rw [reg_putReg, ite_eq_left rfl]
    exact storedCodec_word1 hTag rec hRec
  have r14_12 : (reg s12 14).val = (reg s 9).val + rec.jump := by
    change (reg (putReg s11 14 _) 14).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r9_11, r13_11]; exact hJD2), r9_11, r13_11]
  have st0 : step code input s0 = some (.next s1) :=
    step_add_put rfl (by rw [hsz]; exact (show 0 + 1 < 23 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_add_put rfl (by rw [hsz]; exact (show 1 + 1 < 23 by decide))
  have st2 : step code input s2 = some (.next s3) :=
    step_add_put rfl (by rw [hsz]; exact (show 2 + 1 < 23 by decide))
  have st3 : step code input s3 = some (.next s4) :=
    step_add_put rfl (by rw [hsz]; exact (show 3 + 1 < 23 by decide))
  have st4 : step code input s4 = some (.next s5) :=
    step_add_put rfl (by rw [hsz]; exact (show 4 + 1 < 23 by decide))
  have st5 : step code input s5 = some (.next s6) :=
    step_add_put rfl (by rw [hsz]; exact (show 5 + 1 < 23 by decide))
  have st6 : step code input s6 = some (.next s7) :=
    step_loadInput_put rfl (by rw [r11_6]; exact hRecW ⟨0, by decide⟩)
      (by rw [hsz]; exact (show 6 + 1 < 23 by decide))
  have st7 : step code input s7 = some (.next s8) :=
    step_imm_put rfl (by rw [hsz]; exact (show 7 + 1 < 23 by decide))
  have st8 : step code input s8 = some (.next s9) :=
    step_add_put rfl (by rw [hsz]; exact (show 8 + 1 < 23 by decide))
  have st9 : step code input s9 = some (.next s10) :=
    step_loadInput_put rfl (by rw [r11_9]; exact hRecW ⟨1, by decide⟩)
      (by rw [hsz]; exact (show 9 + 1 < 23 by decide))
  have st10 : step code input s10 = some (.next s11) :=
    step_add_put rfl (by rw [hsz]; exact (show 10 + 1 < 23 by decide))
  have st11 : step code input s11 = some (.next s12) :=
    step_add_put rfl (by rw [hsz]; exact (show 11 + 1 < 23 by decide))
  have st12 : step code input s12 = some (.next s13) :=
    step_loadInput_put rfl (by rw [r14_12]; exact hDepthJumpW)
      (by rw [hsz]; exact (show 12 + 1 < 23 by decide))
  have pre13 : Steps code input 13 s0 s13 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <|
    Steps.cons st8 <| Steps.cons st9 <| Steps.cons st10 <| Steps.cons st11 <|
    Steps.cons st12 <| Steps.zero s13
  have hPres13 : ∀ r : Fin 16, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
      reg s13 r = reg s r := by
    intro r hr11 hr12 hr13 hr14 hr15
    simp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
      ite_eq_right hr14, ite_eq_right hr11, ite_eq_right hr13, ite_eq_right hr15, ite_eq_right hr12]
    rfl
  refine ⟨s13, pre13, rfl,
    hPres13 7 (by decide) (by decide) (by decide) (by decide) (by decide),
    by simp only [s13, reg_putReg, ite_true], ?_, ?_, ?_, hPres13, rfl⟩
  · change (reg (putReg s12 14 _) 12).val = _
    simp only [s12, s11, s10, s9, s8, s7, reg_putReg,
      ite_eq_right (by decide : (12 : Fin 16) ≠ 14),
      ite_eq_right (by decide : (12 : Fin 16) ≠ 11),
      ite_eq_right (by decide : (12 : Fin 16) ≠ 13),
      ite_eq_right (by decide : (12 : Fin 16) ≠ 15),
      ite_true]
    exact storedCodec_word0 hTag rec hRec
  · change (reg (putReg s12 14 _) 13).val = _
    rw [reg_putReg, ite_eq_right (by decide : (13 : Fin 16) ≠ 14)]
    change (reg (putReg s11 14 _) 13).val = _
    rw [reg_putReg, ite_eq_right (by decide : (13 : Fin 16) ≠ 14)]
    exact r13_11
  · change (reg (putReg s12 14 _) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 14)]
    change (reg (putReg s11 14 _) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 14)]
    exact r11_11

private theorem selectRecordPhase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (rec : Stored) (depthJump : Nat)
    (hRec : (storedCodec hTag).valid rec)
    (hDepthJumpLt : depthJump < 2 ^ bits)
    (hRecAddr : (reg s 10).val + 18 * (reg s 6).val + 18 ≤ inputCap)
    (hJumpDepthAddr : (reg s 9).val + rec.jump < inputCap)
    (hRecW : ∀ i : Fin 18,
      input.words[(reg s 10).val + 18 * (reg s 6).val + i.val]? =
        some ((storedCodec hTag).encode rec hRec i))
    (hDepthJumpW : input.words[(reg s 9).val + rec.jump]? =
      some ⟨depthJump, hDepthJumpLt⟩) :
    ∃ (t : State L) (k : Nat),
      k ≤ 21 ∧
      run (selectRecordPhase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      (reg t 6).val = (if (reg s 7).val ≤ depthJump then rec.jump else rec.parent) ∧
      (reg t 11).val =
        (reg s 10).val + 18 * (reg s 6).val + (if (reg s 7).val ≤ depthJump then 10 else 2) ∧
      (∀ r : Fin 16, r ≤ 5 → reg t r = reg s r) ∧
      reg t 7 = reg s 7 ∧ reg t 8 = reg s 8 ∧ reg t 9 = reg s 9 ∧ reg t 10 = reg s 10 ∧
      t.data = s.data := by
  let code := (selectRecordPhase (fits := fits) hTag).code
  have hsz : code.size = 23 := rfl
  have h18Lt : (reg s 10).val + 18 * (reg s 6).val + 18 ≤ 2 ^ bits := Nat.le_trans hRecAddr fits
  let u := (reg s 6).val
  let sb := (reg s 10).val
  obtain ⟨s13, pre13, hpc13, r7_13, r14_13, r12_13val, r13_13val, r11_13val, hPres13, hD13⟩ :=
    selectRecord_pre13 hTag input s rec depthJump hRec hDepthJumpLt hRecAddr hJumpDepthAddr
      hRecW hDepthJumpW
  by_cases hle : (reg s 7).val ≤ depthJump
  · have hNotLt : ¬ ((reg s13 14).val < (reg s13 7).val) := by
      rw [r14_13, r7_13]; omega
    have st13 : step code input s13 = some (.next { s13 with pc := 16 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s13)
        (a := 14) (b := 7) (t := 14) (e := 16)
        (by rw [hpc13]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [ite_eq_right hNotLt] using hst
    let s14 := { s13 with pc := 16 }
    let s15 := putReg s14 6 (reg s14 13)
    let s16 := putReg s15 15 ⟨2, hTag⟩
    let s17 := putReg s16 11 (add (reg s16 11) (reg s16 15))
    let s18 := putReg s17 11 (add (reg s17 11) (reg s17 15))
    let s19 := putReg s18 11 (add (reg s18 11) (reg s18 15))
    let s20 := putReg s19 11 (add (reg s19 11) (reg s19 15))
    have st14 : step code input s14 = some (.next s15) :=
      step_mov_put rfl (by rw [hsz]; exact (show 16 + 1 < 23 by decide))
    have st15 : step code input s15 = some (.next s16) :=
      step_imm_put rfl (by rw [hsz]; exact (show 17 + 1 < 23 by decide))
    have r15_16 : (reg s16 15).val = 2 := by simp only [s16, reg_putReg, ite_true]
    have r11_16 : (reg s16 11).val = sb + 18 * u + 2 := by
      change (reg (putReg (putReg s14 6 _) 15 _) 11).val = _
      rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 15),
        reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 6)]
      exact r11_13val
    have r11_17 : (reg s17 11).val = sb + 18 * u + 4 := by
      change (reg (putReg s16 11 _) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_16, r15_16]; omega), r11_16, r15_16]
    have r15_17 : (reg s17 15).val = 2 := by
      change (reg (putReg s16 11 _) 15).val = 2
      rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_16]
    have r11_18 : (reg s18 11).val = sb + 18 * u + 6 := by
      change (reg (putReg s17 11 _) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_17, r15_17]; omega), r11_17, r15_17]
    have r15_18 : (reg s18 15).val = 2 := by
      change (reg (putReg s17 11 _) 15).val = 2
      rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_17]
    have r11_19 : (reg s19 11).val = sb + 18 * u + 8 := by
      change (reg (putReg s18 11 _) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_18, r15_18]; omega), r11_18, r15_18]
    have r15_19 : (reg s19 15).val = 2 := by
      change (reg (putReg s18 11 _) 15).val = 2
      rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_18]
    have r11_20 : (reg s20 11).val = sb + 18 * u + 10 := by
      change (reg (putReg s19 11 _) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_19, r15_19]; omega), r11_19, r15_19]
    have st16 : step code input s16 = some (.next s17) :=
      step_add_put rfl (by rw [hsz]; exact (show 18 + 1 < 23 by decide))
    have st17 : step code input s17 = some (.next s18) :=
      step_add_put rfl (by rw [hsz]; exact (show 19 + 1 < 23 by decide))
    have st18 : step code input s18 = some (.next s19) :=
      step_add_put rfl (by rw [hsz]; exact (show 20 + 1 < 23 by decide))
    have st19 : step code input s19 = some (.next s20) :=
      step_add_put rfl (by rw [hsz]; exact (show 21 + 1 < 23 by decide))
    have hh : step code input s20 = some (.halted s20) := step_halt_at rfl
    have exec := (steps_trans pre13 (Steps.cons st13 <| Steps.cons st14 <| Steps.cons st15 <|
      Steps.cons st16 <| Steps.cons st17 <| Steps.cons st18 <| Steps.cons st19 <|
      Steps.zero s20)).halts hh
    have hPres20 : ∀ r : Fin 16, r ≠ 6 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg s20 r = reg s r := by
      intro r hr6 hr11 hr12 hr13 hr14 hr15
      simp only [s20, s19, s18, s17, s16, s15, s14, reg_putReg,
        ite_eq_right hr11, ite_eq_right hr15, ite_eq_right hr6]
      exact hPres13 r hr11 hr12 hr13 hr14 hr15
    refine ⟨s20, 13 + 8, by decide, exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hD13⟩
    · rw [ite_eq_left hle]
      simp only [s20, s19, s18, s17, s16, s15, s14, reg_putReg,
        ite_eq_right (by decide : (6 : Fin 16) ≠ 11),
        ite_eq_right (by decide : (6 : Fin 16) ≠ 15), ite_true]
      exact r13_13val
    · rw [ite_eq_left hle, r11_20]
    · intro r hr5
      exact hPres20 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    · exact hPres20 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres20 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres20 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres20 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hLt : (reg s13 14).val < (reg s13 7).val := by
      rw [r14_13, r7_13]; omega
    have st13 : step code input s13 = some (.next { s13 with pc := 14 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s13)
        (a := 14) (b := 7) (t := 14) (e := 16)
        (by rw [hpc13]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [ite_eq_left hLt] using hst
    let s14 := { s13 with pc := 14 }
    let s15 := putReg s14 6 (reg s14 12)
    let s16 := { s15 with pc := 22 }
    have st14 : step code input s14 = some (.next s15) :=
      step_mov_put rfl (by rw [hsz]; exact (show 14 + 1 < 23 by decide))
    have st15 : step code input s15 = some (.next s16) :=
      step_goto_at' rfl (by rw [hsz]; exact (show 22 < 23 by decide))
    have hh : step code input s16 = some (.halted s16) := step_halt_at rfl
    have exec := (steps_trans pre13 (Steps.cons st13 <| Steps.cons st14 <| Steps.cons st15 <|
      Steps.zero s16)).halts hh
    have hPres16 : ∀ r : Fin 16, r ≠ 6 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        reg s16 r = reg s r := by
      intro r hr6 hr11 hr12 hr13 hr14 hr15
      change reg s15 r = _
      rw [reg_putReg, ite_eq_right hr6]
      exact hPres13 r hr11 hr12 hr13 hr14 hr15
    refine ⟨s16, 13 + 4, by decide, exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hD13⟩
    · rw [ite_eq_right hle]
      change (reg s15 6).val = _
      rw [reg_putReg, ite_eq_left rfl]
      exact r12_13val
    · rw [ite_eq_right hle]
      change (reg s15 11).val = _
      rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 6)]
      exact r11_13val
    · intro r hr5
      exact hPres16 r (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    · exact hPres16 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres16 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres16 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hPres16 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def decRemCode (hTag : TagsFit bits) : Program L :=
  #[.imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩, .sub 8 8 15, .halt]

private def decRemPhase (hTag : TagsFit bits) : Phase L :=
  Phase.ofLast (decRemCode hTag) 2 rfl rfl (by simp [decRemCode, nonHalt])

private theorem decRemPhase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (hRemPos : 1 ≤ (reg s 8).val) :
    ∃ t : State L,
      run (decRemPhase (fits := fits) hTag).code input 3 (Phase.initial s) = some ⟨t, 3⟩ ∧
      (reg t 8).val = (reg s 8).val - 1 ∧
      (∀ r : Fin 16, r ≠ 8 → r ≠ 15 → reg t r = reg s r) ∧
      t.data = s.data := by
  let code := (decRemPhase (fits := fits) hTag).code
  have hsz : code.size = 3 := rfl
  let s0 := Phase.initial s
  let s1 := putReg s0 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s2 := putReg s1 8 (sub (reg s1 8) (reg s1 15))
  have st0 : step code input s0 = some (.next s1) :=
    step_imm_put rfl (by rw [hsz]; exact (show 0 + 1 < 3 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_sub_put rfl (by rw [hsz]; exact (show 1 + 1 < 3 by decide))
  have hh : step code input s2 = some (.halted s2) := step_halt_at rfl
  have exec := (Steps.cons st0 <| Steps.cons st1 <| Steps.zero s2).halts hh
  have r8_1 : (reg s1 8).val = (reg s 8).val := by
    simp only [s1, s0, reg_putReg, ite_eq_right (by decide : (8 : Fin 16) ≠ 15)]; rfl
  have r15_1 : (reg s1 15).val = 1 := by simp only [s1, reg_putReg, ite_true]
  refine ⟨s2, exec, ?_, ?_, rfl⟩
  · change (reg (putReg s1 8 _) 8).val = _
    rw [reg_putReg, ite_eq_left rfl, sub_no_wrap _ _ (by rw [r15_1, r8_1]; exact hRemPos), r8_1, r15_1]
  · intro r hr8 hr15
    simp only [s2, s1, s0, reg_putReg, ite_eq_right hr8, ite_eq_right hr15]
    rfl

private def hopBodyPhase (hTag : TagsFit bits) : Phase L :=
  (selectRecordPhase hTag).link ((applyMapPhase hTag).link (decRemPhase hTag))

private theorem hopBodyPhase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (rec : Stored) (depthJump : Nat) (xs : Values)
    (hRec : (storedCodec hTag).valid rec)
    (hDepthJumpLt : depthJump < 2 ^ bits)
    (hXs : ValuesRegs hTag xs s)
    (hRemPos : 1 ≤ (reg s 8).val)
    (hRecAddr : (reg s 10).val + 18 * (reg s 6).val + 18 ≤ inputCap)
    (hJumpDepthAddr : (reg s 9).val + rec.jump < inputCap)
    (hRecW : ∀ i : Fin 18,
      input.words[(reg s 10).val + 18 * (reg s 6).val + i.val]? =
        some ((storedCodec hTag).encode rec hRec i))
    (hDepthJumpW : input.words[(reg s 9).val + rec.jump]? =
      some ⟨depthJump, hDepthJumpLt⟩) :
    let sel := selectAtDepth (fun _ => depthJump) (reg s 7).val rec
    ∃ (t : State L) (k : Nat),
      k ≤ 90 ∧
      run (hopBodyPhase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      ValuesRegs hTag (Map.eval sel.map xs) t ∧
      (reg t 6).val = sel.dst ∧
      (reg t 8).val = (reg s 8).val - 1 ∧
      reg t 7 = reg s 7 ∧ reg t 9 = reg s 9 ∧ reg t 10 = reg s 10 ∧
      t.data = s.data := by
  intro sel
  obtain ⟨u1, k1, hk1, hR1, h1r6, h1r11, h1r05, h1r7, h1r8, h1r9, h1r10, hD1⟩ :=
    selectRecordPhase_spec hTag input s rec depthJump hRec hDepthJumpLt hRecAddr hJumpDepthAddr
      hRecW hDepthJumpW
  have hXs1 : ValuesRegs hTag xs u1 := by
    refine ⟨?_, ?_⟩
    · rw [h1r05 0 (by decide), h1r05 1 (by decide), h1r05 2 (by decide)]; exact hXs.1
    · rw [h1r05 3 (by decide), h1r05 4 (by decide), h1r05 5 (by decide)]; exact hXs.2
  have hApply : ∃ (u2 : State L) (k2 : Nat),
      k2 ≤ 66 ∧
      run (applyMapPhase (fits := fits) hTag).code input k2 (Phase.initial u1) = some ⟨u2, k2⟩ ∧
      ValuesRegs hTag (Map.eval sel.map xs) u2 ∧
      (reg u2 6).val = sel.dst ∧
      reg u2 7 = reg s 7 ∧ reg u2 8 = reg s 8 ∧ reg u2 9 = reg s 9 ∧ reg u2 10 = reg s 10 ∧
      u2.data = s.data := by
    by_cases hle : (reg s 7).val ≤ depthJump
    · have h11 : (reg u1 11).val = (reg s 10).val + 18 * (reg s 6).val + 10 := by
        rw [h1r11, ite_eq_left hle]
      have h6 : (reg u1 6).val = rec.jump := by rw [h1r6, ite_eq_left hle]
      have hSel : sel = ⟨rec.jump, rec.jumpMap⟩ := by
        simp [sel, selectAtDepth, CheckedFold.Stored.select, hle]
      obtain ⟨u2, k2, hk2, hR2, hXs2, h2P, hD2⟩ :=
        applyMapPhase_spec hTag input u1 rec.jumpMap xs hRec.2.2 hXs1
          (by rw [h11]; omega)
          (fun idx => by
            rw [h11, Nat.add_assoc, ← storedCodec_word_jumpMap hTag rec hRec idx]
            exact hRecW ⟨10 + idx.val, by omega⟩)
      refine ⟨u2, k2, hk2, hR2, ?_, ?_, ?_, ?_, ?_, ?_, hD2.trans hD1⟩
      · rw [hSel]; exact hXs2
      · rw [h2P 6 (by decide) (by decide), h6, hSel]
      · rw [h2P 7 (by decide) (by decide), h1r7]
      · rw [h2P 8 (by decide) (by decide), h1r8]
      · rw [h2P 9 (by decide) (by decide), h1r9]
      · rw [h2P 10 (by decide) (by decide), h1r10]
    · have h11 : (reg u1 11).val = (reg s 10).val + 18 * (reg s 6).val + 2 := by
        rw [h1r11, ite_eq_right hle]
      have h6 : (reg u1 6).val = rec.parent := by rw [h1r6, ite_eq_right hle]
      have hSel : sel = ⟨rec.parent, rec.parentMap⟩ := by
        simp [sel, selectAtDepth, CheckedFold.Stored.select, hle]
      obtain ⟨u2, k2, hk2, hR2, hXs2, h2P, hD2⟩ :=
        applyMapPhase_spec hTag input u1 rec.parentMap xs hRec.2.1 hXs1
          (by rw [h11]; omega)
          (fun idx => by
            rw [h11, Nat.add_assoc, ← storedCodec_word_parentMap hTag rec hRec idx]
            exact hRecW ⟨2 + idx.val, by omega⟩)
      refine ⟨u2, k2, hk2, hR2, ?_, ?_, ?_, ?_, ?_, ?_, hD2.trans hD1⟩
      · rw [hSel]; exact hXs2
      · rw [h2P 6 (by decide) (by decide), h6, hSel]
      · rw [h2P 7 (by decide) (by decide), h1r7]
      · rw [h2P 8 (by decide) (by decide), h1r8]
      · rw [h2P 9 (by decide) (by decide), h1r9]
      · rw [h2P 10 (by decide) (by decide), h1r10]
  rcases hApply with ⟨u2, k2, hk2, hR2, hXs2, h2r6, h2r7, h2r8, h2r9, h2r10, hD2⟩
  obtain ⟨u3, hR3, h3r8, h3P, hD3⟩ := decRemPhase_spec hTag input u2 (by rw [h2r8]; exact hRemPos)
  obtain ⟨m23, hm23Reg, hm23Data, hLink23⟩ := phase_link_run _ _ hR2 hR3
  obtain ⟨uAll, huAllReg, huAllData, hLinkAll⟩ := phase_link_run _ _ hR1 hLink23
  refine ⟨uAll, k1 + (k2 + 3), by omega, hLinkAll, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [huAllReg 0, huAllReg 1, huAllReg 2, hm23Reg 0, hm23Reg 1, hm23Reg 2,
        h3P 0 (by decide) (by decide), h3P 1 (by decide) (by decide), h3P 2 (by decide) (by decide)]
      exact hXs2.1
    · rw [huAllReg 3, huAllReg 4, huAllReg 5, hm23Reg 3, hm23Reg 4, hm23Reg 5,
        h3P 3 (by decide) (by decide), h3P 4 (by decide) (by decide), h3P 5 (by decide) (by decide)]
      exact hXs2.2
  · rw [huAllReg 6, hm23Reg 6, h3P 6 (by decide) (by decide), h2r6]
  · rw [huAllReg 8, hm23Reg 8, h3r8, h2r8]
  · rw [huAllReg 7, hm23Reg 7, h3P 7 (by decide) (by decide), h2r7]
  · rw [huAllReg 9, hm23Reg 9, h3P 9 (by decide) (by decide), h2r9]
  · rw [huAllReg 10, hm23Reg 10, h3P 10 (by decide) (by decide), h2r10]
  · exact huAllData.trans (hm23Data.trans (hD3.trans hD2))

/-! ### Phase 5: `initPhase` (load 6-word seed from `priorBase + 6*v`, `rem := depth[u] - d`) -/

private def initCode (hTag : TagsFit bits) : Program L :=
  #[.add 12 8 8,
    .add 13 12 12,
    .add 12 12 13,
    .add 11 11 12,
    .loadInput 0 11,
    .imm 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .add 11 11 15,
    .loadInput 1 11,
    .add 11 11 15,
    .loadInput 2 11,
    .add 11 11 15,
    .loadInput 3 11,
    .add 11 11 15,
    .loadInput 4 11,
    .add 11 11 15,
    .loadInput 5 11,
    .add 12 9 6,
    .loadInput 12 12,
    .branchLt 12 7 19 21,
    .imm 8 ⟨0, by change 2 < 2 ^ bits at hTag; omega⟩,
    .goto 22,
    .sub 8 12 7,
    .halt]

private def initPhase (hTag : TagsFit bits) : Phase L :=
  Phase.ofLast (initCode hTag) 22 rfl rfl (by simp [initCode, nonHalt])

private theorem init_pre10 (hTag : TagsFit bits)
    (input : Input L) (s : State L) (w0 w1 w2 : Word bits)
    (hSeedAddr : (reg s 11).val + 6 * (reg s 8).val + 6 ≤ inputCap)
    (hW0 : input.words[(reg s 11).val + 6 * (reg s 8).val]? = some w0)
    (hW1 : input.words[(reg s 11).val + 6 * (reg s 8).val + 1]? = some w1)
    (hW2 : input.words[(reg s 11).val + 6 * (reg s 8).val + 2]? = some w2) :
    ∃ s10 : State L,
      Steps (initPhase (fits := fits) hTag).code input 10 (Phase.initial s) s10 ∧
      s10.pc = 10 ∧
      reg s10 0 = w0 ∧ reg s10 1 = w1 ∧ reg s10 2 = w2 ∧
      (reg s10 11).val = (reg s 11).val + 6 * (reg s 8).val + 2 ∧
      (reg s10 15).val = 1 ∧
      reg s10 6 = reg s 6 ∧ reg s10 7 = reg s 7 ∧ reg s10 9 = reg s 9 ∧
      reg s10 10 = reg s 10 ∧
      s10.data = s.data := by
  let code := (initPhase (fits := fits) hTag).code
  have hsz : code.size = 23 := rfl
  have h6Lt : (reg s 11).val + 6 * (reg s 8).val + 6 ≤ 2 ^ bits := Nat.le_trans hSeedAddr fits
  let v := (reg s 8).val
  let pb := (reg s 11).val
  let s0 := Phase.initial s
  let s1 := putReg s0 12 (add (reg s0 8) (reg s0 8))
  let s2 := putReg s1 13 (add (reg s1 12) (reg s1 12))
  let s3 := putReg s2 12 (add (reg s2 12) (reg s2 13))
  let s4 := putReg s3 11 (add (reg s3 11) (reg s3 12))
  let s5 := putReg s4 0 w0
  let s6 := putReg s5 15 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩
  let s7 := putReg s6 11 (add (reg s6 11) (reg s6 15))
  let s8 := putReg s7 1 w1
  let s9 := putReg s8 11 (add (reg s8 11) (reg s8 15))
  let s10 := putReg s9 2 w2
  have r12_1 : (reg s1 12).val = 2 * v := by
    change (reg (putReg s0 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by change v + v < 2 ^ bits; omega)]
    change v + v = 2 * v; omega
  have r13_2 : (reg s2 13).val = 4 * v := by
    change (reg (putReg s1 13 _) 13).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_1]; omega), r12_1]; omega
  have r12_2 : (reg s2 12).val = 2 * v := by
    change (reg (putReg s1 13 _) 12).val = _
    rw [reg_putReg, ite_eq_right (by decide : (12 : Fin 16) ≠ 13), r12_1]
  have r12_3 : (reg s3 12).val = 6 * v := by
    change (reg (putReg s2 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r12_2, r13_2]; omega), r12_2, r13_2]; omega
  have r11_3 : (reg s3 11).val = pb := by
    simp only [s3, s2, s1, s0, reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 12),
      ite_eq_right (by decide : (11 : Fin 16) ≠ 13)]; rfl
  have r11_4 : (reg s4 11).val = pb + 6 * v := by
    change (reg (putReg s3 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_3, r12_3]; omega), r11_3, r12_3]
  have r11_6 : (reg s6 11).val = pb + 6 * v := by
    change (reg (putReg (putReg s4 0 w0) 15 _) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 15),
      reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 0), r11_4]
  have r15_6 : (reg s6 15).val = 1 := by simp only [s6, reg_putReg, ite_true]
  have r11_7 : (reg s7 11).val = pb + 6 * v + 1 := by
    change (reg (putReg s6 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_6, r15_6]; omega), r11_6, r15_6]
  have r15_8 : (reg s8 15).val = 1 := by
    change (reg (putReg (putReg s6 11 _) 1 w1) 15).val = _
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 1),
      reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_6]
  have r11_8 : (reg s8 11).val = pb + 6 * v + 1 := by
    change (reg (putReg s7 1 w1) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 1), r11_7]
  have r11_9 : (reg s9 11).val = pb + 6 * v + 2 := by
    change (reg (putReg s8 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [r11_8, r15_8]; omega), r11_8, r15_8]
  have st0 : step code input s0 = some (.next s1) :=
    step_add_put rfl (by rw [hsz]; exact (show 0 + 1 < 23 by decide))
  have st1 : step code input s1 = some (.next s2) :=
    step_add_put rfl (by rw [hsz]; exact (show 1 + 1 < 23 by decide))
  have st2 : step code input s2 = some (.next s3) :=
    step_add_put rfl (by rw [hsz]; exact (show 2 + 1 < 23 by decide))
  have st3 : step code input s3 = some (.next s4) :=
    step_add_put rfl (by rw [hsz]; exact (show 3 + 1 < 23 by decide))
  have st4 : step code input s4 = some (.next s5) :=
    step_loadInput_put rfl (by rw [r11_4]; exact hW0) (by rw [hsz]; exact (show 4 + 1 < 23 by decide))
  have st5 : step code input s5 = some (.next s6) :=
    step_imm_put rfl (by rw [hsz]; exact (show 5 + 1 < 23 by decide))
  have st6 : step code input s6 = some (.next s7) :=
    step_add_put rfl (by rw [hsz]; exact (show 6 + 1 < 23 by decide))
  have st7 : step code input s7 = some (.next s8) :=
    step_loadInput_put rfl (by rw [r11_7]; exact hW1) (by rw [hsz]; exact (show 7 + 1 < 23 by decide))
  have st8 : step code input s8 = some (.next s9) :=
    step_add_put rfl (by rw [hsz]; exact (show 8 + 1 < 23 by decide))
  have st9 : step code input s9 = some (.next s10) :=
    step_loadInput_put rfl (by rw [r11_9]; exact hW2) (by rw [hsz]; exact (show 9 + 1 < 23 by decide))
  have pre10 : Steps code input 10 s0 s10 :=
    Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
    Steps.cons st4 <| Steps.cons st5 <| Steps.cons st6 <| Steps.cons st7 <|
    Steps.cons st8 <| Steps.cons st9 <| Steps.zero s10
  have hPres10 : ∀ r : Fin 16, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 15 →
      reg s10 r = reg s r := by
    intro r hr0 hr1 hr2 hr11 hr12 hr13 hr15
    simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, reg_putReg,
      ite_eq_right hr2, ite_eq_right hr11, ite_eq_right hr1, ite_eq_right hr15,
      ite_eq_right hr0, ite_eq_right hr12, ite_eq_right hr13]
    rfl
  refine ⟨s10, pre10, rfl, ?_, ?_, ?_, ?_, ?_,
    hPres10 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hPres10 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hPres10 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hPres10 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    rfl⟩
  · simp only [s10, s9, s8, s7, s6, s5, reg_putReg,
      ite_eq_right (by decide : (0 : Fin 16) ≠ 2),
      ite_eq_right (by decide : (0 : Fin 16) ≠ 11),
      ite_eq_right (by decide : (0 : Fin 16) ≠ 1),
      ite_eq_right (by decide : (0 : Fin 16) ≠ 15),
      ite_true]
  · simp only [s10, s9, s8, reg_putReg,
      ite_eq_right (by decide : (1 : Fin 16) ≠ 2),
      ite_eq_right (by decide : (1 : Fin 16) ≠ 11),
      ite_true]
  · simp only [s10, reg_putReg, ite_true]
  · change (reg (putReg s9 2 w2) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 2), r11_9]
  · change (reg (putReg s9 2 w2) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 2)]
    change (reg (putReg s8 11 _) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), r15_8]

private theorem initPhase_spec (hTag : TagsFit bits)
    (input : Input L) (s : State L) (seed : Values) (hSeed : RankBound (2 ^ bits) seed.x0 ∧ RankBound (2 ^ bits) seed.x1)
    (depthU : Nat) (hDepthULt : depthU < 2 ^ bits)
    (hSeedAddr : (reg s 11).val + 6 * (reg s 8).val + 6 ≤ inputCap)
    (hDepthUAddr : (reg s 9).val + (reg s 6).val < inputCap)
    (hSeedW0 : input.words[(reg s 11).val + 6 * (reg s 8).val]? = some ((intervalCodec hTag).encode seed.x0 hSeed.1 0))
    (hSeedW1 : input.words[(reg s 11).val + 6 * (reg s 8).val + 1]? = some ((intervalCodec hTag).encode seed.x0 hSeed.1 1))
    (hSeedW2 : input.words[(reg s 11).val + 6 * (reg s 8).val + 2]? = some ((intervalCodec hTag).encode seed.x0 hSeed.1 2))
    (hSeedW3 : input.words[(reg s 11).val + 6 * (reg s 8).val + 3]? = some ((intervalCodec hTag).encode seed.x1 hSeed.2 0))
    (hSeedW4 : input.words[(reg s 11).val + 6 * (reg s 8).val + 4]? = some ((intervalCodec hTag).encode seed.x1 hSeed.2 1))
    (hSeedW5 : input.words[(reg s 11).val + 6 * (reg s 8).val + 5]? = some ((intervalCodec hTag).encode seed.x1 hSeed.2 2))
    (hDepthUW : input.words[(reg s 9).val + (reg s 6).val]? = some ⟨depthU, hDepthULt⟩) :
    ∃ (t : State L) (k : Nat),
      k ≤ 22 ∧
      run (initPhase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
      ValuesRegs hTag seed t ∧
      (reg t 8).val = depthU - (reg s 7).val ∧
      reg t 6 = reg s 6 ∧ reg t 7 = reg s 7 ∧ reg t 9 = reg s 9 ∧ reg t 10 = reg s 10 ∧
      t.data = s.data := by
  let code := (initPhase (fits := fits) hTag).code
  have hsz : code.size = 23 := rfl
  have h6Lt : (reg s 11).val + 6 * (reg s 8).val + 6 ≤ 2 ^ bits := Nat.le_trans hSeedAddr fits
  have hDU2 : (reg s 9).val + (reg s 6).val < 2 ^ bits := Nat.lt_of_lt_of_le hDepthUAddr fits
  let w0 := (intervalCodec hTag).encode seed.x0 hSeed.1 0
  let w1 := (intervalCodec hTag).encode seed.x0 hSeed.1 1
  let w2 := (intervalCodec hTag).encode seed.x0 hSeed.1 2
  let w3 := (intervalCodec hTag).encode seed.x1 hSeed.2 0
  let w4 := (intervalCodec hTag).encode seed.x1 hSeed.2 1
  let w5 := (intervalCodec hTag).encode seed.x1 hSeed.2 2
  obtain ⟨s10, pre10, hpc10, h0_10, h1_10, h2_10, h11_10, h15_10, h6_10, h7_10, h9_10, h10_10, hD10⟩ :=
    init_pre10 hTag input s w0 w1 w2 hSeedAddr hSeedW0 hSeedW1 hSeedW2
  let s11 := putReg s10 11 (add (reg s10 11) (reg s10 15))
  let s12 := putReg s11 3 w3
  let s13 := putReg s12 11 (add (reg s12 11) (reg s12 15))
  let s14 := putReg s13 4 w4
  let s15 := putReg s14 11 (add (reg s14 11) (reg s14 15))
  let s16 := putReg s15 5 w5
  let s17 := putReg s16 12 (add (reg s16 9) (reg s16 6))
  let s18 := putReg s17 12 ⟨depthU, hDepthULt⟩
  have h11_11 : (reg s11 11).val = (reg s 11).val + 6 * (reg s 8).val + 3 := by
    change (reg (putReg s10 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [h11_10, h15_10]; omega), h11_10, h15_10]
  have h15_12 : (reg s12 15).val = 1 := by
    change (reg (putReg (putReg s10 11 _) 3 w3) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 3),
      reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), h15_10]
  have h11_12 : (reg s12 11).val = (reg s 11).val + 6 * (reg s 8).val + 3 := by
    change (reg (putReg s11 3 w3) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 3), h11_11]
  have h11_13 : (reg s13 11).val = (reg s 11).val + 6 * (reg s 8).val + 4 := by
    change (reg (putReg s12 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [h11_12, h15_12]; omega), h11_12, h15_12]
  have h15_14 : (reg s14 15).val = 1 := by
    change (reg (putReg (putReg s12 11 _) 4 w4) 15).val = 1
    rw [reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 4),
      reg_putReg, ite_eq_right (by decide : (15 : Fin 16) ≠ 11), h15_12]
  have h11_14 : (reg s14 11).val = (reg s 11).val + 6 * (reg s 8).val + 4 := by
    change (reg (putReg s13 4 w4) 11).val = _
    rw [reg_putReg, ite_eq_right (by decide : (11 : Fin 16) ≠ 4), h11_13]
  have h11_15 : (reg s15 11).val = (reg s 11).val + 6 * (reg s 8).val + 5 := by
    change (reg (putReg s14 11 _) 11).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [h11_14, h15_14]; omega), h11_14, h15_14]
  have hPres16 : ∀ r : Fin 16, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 11 → reg s16 r = reg s10 r := by
    intro r hr3 hr4 hr5 hr11
    simp only [s16, s15, s14, s13, s12, s11, reg_putReg,
      ite_eq_right hr5, ite_eq_right hr11, ite_eq_right hr4, ite_eq_right hr3]
  have h9_16 : reg s16 9 = reg s 9 :=
    (hPres16 9 (by decide) (by decide) (by decide) (by decide)).trans h9_10
  have h6_16 : reg s16 6 = reg s 6 :=
    (hPres16 6 (by decide) (by decide) (by decide) (by decide)).trans h6_10
  have h12_17 : (reg s17 12).val = (reg s 9).val + (reg s 6).val := by
    change (reg (putReg s16 12 _) 12).val = _
    rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [h9_16, h6_16]; exact hDU2), h9_16, h6_16]
  have hpc11 : s11.pc = 11 := by change s10.pc + 1 = 11; omega
  have hpc12 : s12.pc = 12 := by change s11.pc + 1 = 12; omega
  have hpc13 : s13.pc = 13 := by change s12.pc + 1 = 13; omega
  have hpc14 : s14.pc = 14 := by change s13.pc + 1 = 14; omega
  have hpc15 : s15.pc = 15 := by change s14.pc + 1 = 15; omega
  have hpc16 : s16.pc = 16 := by change s15.pc + 1 = 16; omega
  have hpc17 : s17.pc = 17 := by change s16.pc + 1 = 17; omega
  have hpc18 : s18.pc = 18 := by change s17.pc + 1 = 18; omega
  have st10 : step code input s10 = some (.next s11) :=
    step_add_put (by rw [hpc10]; rfl) (by rw [hpc10, hsz]; exact (show 10 + 1 < 23 by decide))
  have st11 : step code input s11 = some (.next s12) :=
    step_loadInput_put (by rw [hpc11]; rfl) (by rw [h11_11]; exact hSeedW3)
      (by rw [hpc11, hsz]; exact (show 11 + 1 < 23 by decide))
  have st12 : step code input s12 = some (.next s13) :=
    step_add_put (by rw [hpc12]; rfl) (by rw [hpc12, hsz]; exact (show 12 + 1 < 23 by decide))
  have st13 : step code input s13 = some (.next s14) :=
    step_loadInput_put (by rw [hpc13]; rfl) (by rw [h11_13]; exact hSeedW4)
      (by rw [hpc13, hsz]; exact (show 13 + 1 < 23 by decide))
  have st14 : step code input s14 = some (.next s15) :=
    step_add_put (by rw [hpc14]; rfl) (by rw [hpc14, hsz]; exact (show 14 + 1 < 23 by decide))
  have st15 : step code input s15 = some (.next s16) :=
    step_loadInput_put (by rw [hpc15]; rfl) (by rw [h11_15]; exact hSeedW5)
      (by rw [hpc15, hsz]; exact (show 15 + 1 < 23 by decide))
  have st16 : step code input s16 = some (.next s17) :=
    step_add_put (by rw [hpc16]; rfl) (by rw [hpc16, hsz]; exact (show 16 + 1 < 23 by decide))
  have st17 : step code input s17 = some (.next s18) :=
    step_loadInput_put (by rw [hpc17]; rfl) (by rw [h12_17]; exact hDepthUW)
      (by rw [hpc17, hsz]; exact (show 17 + 1 < 23 by decide))
  have pre18 : Steps code input 18 (Phase.initial s) s18 :=
    steps_trans pre10 (Steps.cons st10 <| Steps.cons st11 <| Steps.cons st12 <|
      Steps.cons st13 <| Steps.cons st14 <| Steps.cons st15 <| Steps.cons st16 <|
      Steps.cons st17 <| Steps.zero s18)
  have hPres18 : ∀ r : Fin 16, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 11 → r ≠ 12 →
      reg s18 r = reg s10 r := by
    intro r hr3 hr4 hr5 hr11 hr12
    change reg (putReg (putReg s16 12 _) 12 _) r = _
    rw [reg_putReg, ite_eq_right hr12, reg_putReg, ite_eq_right hr12]
    exact hPres16 r hr3 hr4 hr5 hr11
  have h12_18 : (reg s18 12).val = depthU := by simp only [s18, reg_putReg, ite_true]
  have h7_18 : reg s18 7 = reg s 7 :=
    (hPres18 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7_10
  have hSeed18 : ValuesRegs hTag seed s18 := by
    refine ⟨⟨hSeed.1, ?_, ?_, ?_⟩, ⟨hSeed.2, ?_, ?_, ?_⟩⟩
    · rw [hPres18 0 (by decide) (by decide) (by decide) (by decide) (by decide), h0_10]
    · rw [hPres18 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1_10]
    · rw [hPres18 2 (by decide) (by decide) (by decide) (by decide) (by decide), h2_10]
    · change reg (putReg (putReg s16 12 _) 12 _) 3 = w3
      rw [reg_putReg, ite_eq_right (by decide : (3 : Fin 16) ≠ 12),
        reg_putReg, ite_eq_right (by decide : (3 : Fin 16) ≠ 12)]
      simp only [s16, s15, s14, s13, s12, reg_putReg,
        ite_eq_right (by decide : (3 : Fin 16) ≠ 5),
        ite_eq_right (by decide : (3 : Fin 16) ≠ 11),
        ite_eq_right (by decide : (3 : Fin 16) ≠ 4), ite_true]
    · change reg (putReg (putReg s16 12 _) 12 _) 4 = w4
      rw [reg_putReg, ite_eq_right (by decide : (4 : Fin 16) ≠ 12),
        reg_putReg, ite_eq_right (by decide : (4 : Fin 16) ≠ 12)]
      simp only [s16, s15, s14, reg_putReg,
        ite_eq_right (by decide : (4 : Fin 16) ≠ 5),
        ite_eq_right (by decide : (4 : Fin 16) ≠ 11), ite_true]
    · change reg (putReg (putReg s16 12 _) 12 _) 5 = w5
      rw [reg_putReg, ite_eq_right (by decide : (5 : Fin 16) ≠ 12),
        reg_putReg, ite_eq_right (by decide : (5 : Fin 16) ≠ 12)]
      simp only [s16, reg_putReg, ite_true]
  by_cases hlt : depthU < (reg s 7).val
  · have hlt18 : (reg s18 12).val < (reg s18 7).val := by rw [h12_18, h7_18]; exact hlt
    have st18 : step code input s18 = some (.next { s18 with pc := 19 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s18)
        (a := 12) (b := 7) (t := 19) (e := 21)
        (by rw [hpc18]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [ite_eq_left hlt18] using hst
    let s19 := { s18 with pc := 19 }
    let s20 := putReg s19 8 ⟨0, by omega⟩
    let s21 := { s20 with pc := 22 }
    have st19 : step code input s19 = some (.next s20) :=
      step_imm_put rfl (by rw [hsz]; exact (show 19 + 1 < 23 by decide))
    have st20 : step code input s20 = some (.next s21) :=
      step_goto_at' rfl (by rw [hsz]; exact (show 22 < 23 by decide))
    have hh : step code input s21 = some (.halted s21) := step_halt_at rfl
    have exec := (steps_trans pre18 (Steps.cons st18 <| Steps.cons st19 <| Steps.cons st20 <|
      Steps.zero s21)).halts hh
    have hPres21 : ∀ r : Fin 16, r ≠ 8 → reg s21 r = reg s18 r := by
      intro r hr8; change reg s20 r = _; rw [reg_putReg, ite_eq_right hr8]; rfl
    refine ⟨s21, 18 + 4, by decide, exec, ?_, ?_, ?_, ?_, ?_, ?_, hD10⟩
    · refine ⟨⟨hSeed18.1.1, ?_, ?_, ?_⟩, ⟨hSeed18.2.1, ?_, ?_, ?_⟩⟩
      · rw [hPres21 0 (by decide)]; exact hSeed18.1.2.1
      · rw [hPres21 1 (by decide)]; exact hSeed18.1.2.2.1
      · rw [hPres21 2 (by decide)]; exact hSeed18.1.2.2.2
      · rw [hPres21 3 (by decide)]; exact hSeed18.2.2.1
      · rw [hPres21 4 (by decide)]; exact hSeed18.2.2.2.1
      · rw [hPres21 5 (by decide)]; exact hSeed18.2.2.2.2
    · change (reg s20 8).val = _; rw [reg_putReg, ite_eq_left rfl]; change 0 = _; omega
    · rw [hPres21 6 (by decide), hPres18 6 (by decide) (by decide) (by decide) (by decide) (by decide), h6_10]
    · rw [hPres21 7 (by decide), h7_18]
    · rw [hPres21 9 (by decide), hPres18 9 (by decide) (by decide) (by decide) (by decide) (by decide), h9_10]
    · rw [hPres21 10 (by decide), hPres18 10 (by decide) (by decide) (by decide) (by decide) (by decide), h10_10]
  · have hNotLt18 : ¬ ((reg s18 12).val < (reg s18 7).val) := by rw [h12_18, h7_18]; exact hlt
    have st18 : step code input s18 = some (.next { s18 with pc := 21 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s18)
        (a := 12) (b := 7) (t := 19) (e := 21)
        (by rw [hpc18]; rfl) (by split <;> rw [hsz] <;> decide)
      simpa only [ite_eq_right hNotLt18] using hst
    let s19 := { s18 with pc := 21 }
    let s20 := putReg s19 8 (sub (reg s19 12) (reg s19 7))
    have st19 : step code input s19 = some (.next s20) :=
      step_sub_put rfl (by rw [hsz]; exact (show 21 + 1 < 23 by decide))
    have hh : step code input s20 = some (.halted s20) := step_halt_at rfl
    have exec := (steps_trans pre18 (Steps.cons st18 <| Steps.cons st19 <| Steps.zero s20)).halts hh
    have hPres20 : ∀ r : Fin 16, r ≠ 8 → reg s20 r = reg s18 r := by
      intro r hr8; rw [reg_putReg, ite_eq_right hr8]; rfl
    refine ⟨s20, 18 + 3, by decide, exec, ?_, ?_, ?_, ?_, ?_, ?_, hD10⟩
    · refine ⟨⟨hSeed18.1.1, ?_, ?_, ?_⟩, ⟨hSeed18.2.1, ?_, ?_, ?_⟩⟩
      · rw [hPres20 0 (by decide)]; exact hSeed18.1.2.1
      · rw [hPres20 1 (by decide)]; exact hSeed18.1.2.2.1
      · rw [hPres20 2 (by decide)]; exact hSeed18.1.2.2.2
      · rw [hPres20 3 (by decide)]; exact hSeed18.2.2.1
      · rw [hPres20 4 (by decide)]; exact hSeed18.2.2.2.1
      · rw [hPres20 5 (by decide)]; exact hSeed18.2.2.2.2
    · rw [reg_putReg, ite_eq_left rfl]
      change (sub (reg s18 12) (reg s18 7)).val = _
      rw [sub_no_wrap _ _ (by rw [h12_18, h7_18]; omega), h12_18, h7_18]
    · rw [hPres20 6 (by decide), hPres18 6 (by decide) (by decide) (by decide) (by decide) (by decide), h6_10]
    · rw [hPres20 7 (by decide), h7_18]
    · rw [hPres20 9 (by decide), hPres18 9 (by decide) (by decide) (by decide) (by decide) (by decide), h9_10]
    · rw [hPres20 10 (by decide), hPres18 10 (by decide) (by decide) (by decide) (by decide) (by decide), h10_10]

/-! ### Phase 6: `loopPart` and `exitEvalProgram` -/

private def loopHeader (hTag : TagsFit bits) (exitPC : Nat) : Program L :=
  #[.imm 11 ⟨1, by change 2 < 2 ^ bits at hTag; omega⟩,
    .branchLt 8 11 exitPC 2,
    .add 11 9 6,
    .loadInput 11 11,
    .branchLt 7 11 5 exitPC]

private theorem loopHeader_nonhalt (hTag : TagsFit bits) (exitPC : Nat) :
    (loopHeader (fits := fits) hTag exitPC).toList.all (@nonHalt bits L) = true := by
  simp [loopHeader, nonHalt]

private def loopPartCode (hTag : TagsFit bits) : Program L :=
  let hop := hopBodyPhase (fits := fits) hTag
  let exitPC := 5 + hop.code.size
  loopHeader hTag exitPC ++
    ((hop.code.map (relocateInstr 5)).set hop.haltPC (.goto 0)
      (by simpa only [Array.size_map] using hop.haltFits)) ++
    #[.halt]

private theorem loopPartCode_size (hTag : TagsFit bits) :
    (loopPartCode (fits := fits) hTag).size = 5 + (hopBodyPhase (fits := fits) hTag).code.size + 1 := by
  unfold loopPartCode
  dsimp only
  simp only [Array.size_append, Array.size_singleton, Array.size_set, Array.size_map]
  rfl

private def loopPart (hTag : TagsFit bits) : Phase L :=
  let hop := hopBodyPhase (fits := fits) hTag
  let exitPC := 5 + hop.code.size
  Phase.ofLast (loopPartCode hTag) exitPC (loopPartCode_size hTag)
    (by
      unfold loopPartCode
      dsimp only [hop, exitPC]
      have hPrev : (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size) ++
          (((hopBodyPhase (fits := fits) hTag).code.map (relocateInstr 5)).set
            (hopBodyPhase (fits := fits) hTag).haltPC (.goto 0)
            (by simpa only [Array.size_map] using (hopBodyPhase (fits := fits) hTag).haltFits))).size =
          5 + (hopBodyPhase (fits := fits) hTag).code.size := by
        simp only [Array.size_append, Array.size_set, Array.size_map]; rfl
      rw [Array.getElem?_append_right (Nat.le_of_eq hPrev), hPrev, Nat.sub_self]
      rfl)
    (by
      let hdr := loopHeader (fits := fits) hTag exitPC
      let body := (hop.code.map (relocateInstr 5)).set hop.haltPC (.goto 0)
        (by simpa only [Array.size_map] using hop.haltFits)
      have hPrev : (hdr ++ body).size = exitPC := by
        simp only [hdr, body, Array.size_append, Array.size_set, Array.size_map, exitPC]; rfl
      have htake : (loopPartCode (fits := fits) hTag).toList.take exitPC = hdr.toList ++ body.toList := by
        change (hdr ++ body ++ #[Instr.halt]).toList.take exitPC = hdr.toList ++ body.toList
        rw [Array.toList_append,
          List.take_append_of_le_length (by simp only [Array.length_toList]; exact Nat.le_of_eq hPrev.symm),
          List.take_of_length_le (by simp only [Array.length_toList]; exact Nat.le_of_eq hPrev)]
        exact Array.toList_append
      rw [htake, List.all_append, loopHeader_nonhalt, Bool.true_and, List.all_eq_true]
      intro op hmem
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
      have hget : body[i]? = some op := by
        rw [← heq]; exact getElem?_pos _ i (by simpa using hi)
      by_cases hpc : i = hop.haltPC
      · have hs : body[i]? = some (.goto 0) := by
          rw [hpc]; exact Array.getElem?_set_self _
        rw [hs] at hget; cases hget; rfl
      · have hne : body[i]? = (hop.code.map (relocateInstr 5))[i]? :=
          Array.getElem?_set_ne _ (Ne.symm hpc)
        rw [hne, Array.getElem?_map] at hget
        cases hc : hop.code[i]? with
        | none => simp [hc] at hget
        | some orig =>
          rw [hc, Option.map_some] at hget
          have hop' := Option.some.inj hget
          cases orig <;> simp [relocateInstr] at hop' <;> subst hop' <;> try rfl
          exact False.elim (hpc (hop.uniqueHalt i hc)))

private theorem loopPart_slice_hdr (hTag : TagsFit bits) {j : Nat} (hj : j < 5) :
    (loopPart (fits := fits) hTag).code[j]? =
      (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size))[j]? := by
  change (loopPartCode (fits := fits) hTag)[j]? = _
  unfold loopPartCode
  dsimp only
  have hHdr : (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size)).size = 5 := rfl
  have s0 : j < (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size)).size := by
    rw [hHdr]; exact hj
  have s1 : j < (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size) ++
      (((hopBodyPhase (fits := fits) hTag).code.map (relocateInstr 5)).set
        (hopBodyPhase (fits := fits) hTag).haltPC (.goto 0)
        (by simpa only [Array.size_map] using (hopBodyPhase (fits := fits) hTag).haltFits))).size := by
    rw [Array.size_append, hHdr]; omega
  rw [Array.getElem?_append_left s1, Array.getElem?_append_left s0]

private theorem loopPart_slice_hop (hTag : TagsFit bits)
    {j : Nat} (hj : j < (hopBodyPhase (fits := fits) hTag).code.size) :
    (loopPart (fits := fits) hTag).code[5 + j]? =
      (((hopBodyPhase (fits := fits) hTag).code.map (relocateInstr 5)).set
        (hopBodyPhase (fits := fits) hTag).haltPC (.goto 0)
        (by simpa only [Array.size_map] using (hopBodyPhase (fits := fits) hTag).haltFits))[j]? := by
  change (loopPartCode (fits := fits) hTag)[5 + j]? = _
  unfold loopPartCode
  dsimp only
  have hHdr : (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size)).size = 5 := rfl
  have hL : 5 + j < (loopHeader (fits := fits) hTag (5 + (hopBodyPhase (fits := fits) hTag).code.size) ++
      (((hopBodyPhase (fits := fits) hTag).code.map (relocateInstr 5)).set
        (hopBodyPhase (fits := fits) hTag).haltPC (.goto 0)
        (by simpa only [Array.size_map] using (hopBodyPhase (fits := fits) hTag).haltFits))).size := by
    simp only [Array.size_append, Array.size_set, Array.size_map, hHdr]; omega
  rw [Array.getElem?_append_left hL, Array.getElem?_append_right (by rw [hHdr]; omega), hHdr]
  simp [Nat.add_sub_cancel_left]

private theorem loopPart_hop_step (hTag : TagsFit bits)
    {input : Input L} {s u : State L} {k : Nat}
    (hRun : run (hopBodyPhase (fits := fits) hTag).code input k (Phase.initial s) = some ⟨u, k⟩) :
    Steps (loopPart (fits := fits) hTag).code input k
      (relocateStatePC 5 (Phase.initial s)) (Phase.initial u) := by
  let hop := hopBodyPhase (fits := fits) hTag
  have hSteps := linked_return_of_run_multi (linked := (loopPart (fits := fits) hTag).code)
    (base := 5) (ret := fun _ => 0) hRun
    (fun i op hi hne => by
      have hiLt : i < hop.code.size := by
        by_cases h : i < hop.code.size; · exact h
        · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hi; cases hi
      have hneHalt : i ≠ hop.haltPC := fun e => hne (Option.some.inj (hi.symm.trans (e ▸ hop.haltAt)))
      rw [loopPart_slice_hop hTag hiLt, Array.getElem?_set_ne _ (Ne.symm hneHalt),
        Array.getElem?_map, hi]
      rfl)
    (fun i hi => by
      rw [hop.uniqueHalt i hi]
      refine ⟨?_, ?_⟩
      · rw [loopPart_slice_hop hTag hop.haltFits, Array.getElem?_set_self _]
      · change 0 < (loopPart (fits := fits) hTag).code.size
        rw [show (loopPart (fits := fits) hTag).code.size = 5 + hop.code.size + 1 from
          loopPartCode_size hTag]
        omega)
  exact hSteps

private theorem map_eval_compose (inner outer : Map) (xs : Values) :
    Map.eval (Map.compose inner outer) xs = Map.eval outer (Map.eval inner xs) := by
  have h0 := Map.eval_compose_get inner outer xs 0
  have h1 := Map.eval_compose_get inner outer xs 1
  change (Map.eval (Map.compose inner outer) xs).x0 = (Map.eval outer (Map.eval inner xs)).x0 at h0
  change (Map.eval (Map.compose inner outer) xs).x1 = (Map.eval outer (Map.eval inner xs)).x1 at h1
  cases hL : Map.eval (Map.compose inner outer) xs
  cases hR : Map.eval outer (Map.eval inner xs)
  rw [hL] at h0 h1; rw [hR] at h0 h1
  exact (congrArg (fun a => Two.mk a _) h0).trans (congrArg (Two.mk _) h1)

private def evalAux (depth : Nat → Nat) (rec : Nat → Stored) (d budget u : Nat)
    (xs : Values) (steps : Nat) : Values :=
  if _h : steps < budget ∧ d < depth u then
    let r := rec u
    let sel := selectAtDepth depth d r
    evalAux depth rec d budget sel.dst (Map.eval sel.map xs) (steps + 1)
  else xs
termination_by budget - steps
decreasing_by omega

private theorem evalAux_eq_foldFusedAux (depth : Nat → Nat) (rec : Nat → Stored)
    (d budget u : Nat) (acc : Map) (xs : Values) (steps : Nat) :
    evalAux depth rec d budget u (Map.eval acc xs) steps =
      Map.eval (accumulated (foldFusedAux depth rec d budget u acc steps)) xs := by
  conv => lhs; rw [evalAux]
  conv => rhs; rw [foldFusedAux]
  by_cases h : steps < budget ∧ d < depth u
  · simp only [dite_eq_left h]
    rw [← map_eval_compose]
    exact evalAux_eq_foldFusedAux depth rec d budget _ (Map.compose acc _) xs (steps + 1)
  · simp only [dite_eq_right h]
    rfl
termination_by budget - steps
decreasing_by omega

private theorem serialize_word_eq {n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (v : Fin prior.size) (k : Fin 6) :
    (serialize w prior hb)[6 * v.val + k.val]'(by
      rw [seal_size]; have hv := v.isLt; have hk := k.isLt; omega) =
      (if hk : k.val < 3 then
        (intervalCodec w.tags).encode ((prior[v.val]'(v.isLt)).getD PaperB.BuiltExit.zero).x0
          (rankBound_mono w.ranks (hb v).1) ⟨k.val, hk⟩
       else
        (intervalCodec w.tags).encode ((prior[v.val]'(v.isLt)).getD PaperB.BuiltExit.zero).x1
          (rankBound_mono w.ranks (hb v).2) ⟨k.val - 3, by have := k.isLt; omega⟩) := by
  have hv : (6 * v.val + k.val) / 6 = v.val := by have hk := k.isLt; omega
  have hk : (6 * v.val + k.val) % 6 = k.val := by have hk := k.isLt; omega
  have hfe : (⟨(6 * v.val + k.val) / 6, by have hv' := v.isLt; have hk' := k.isLt; omega⟩ :
      Fin prior.size) = v := Fin.ext hv
  have hke : (⟨(6 * v.val + k.val) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) = k := Fin.ext hk
  simp only [serialize, Array.getElem_ofFn, hfe, hke]
  rfl

private theorem foldFusedAux_steps_indep (depth : Nat → Nat) (rec : Nat → Stored)
    (d budget u : Nat) (a b : Map) (steps : Nat) :
    (foldFusedAux depth rec d budget u a steps).steps =
      (foldFusedAux depth rec d budget u b steps).steps := by
  conv => lhs; rw [foldFusedAux]
  conv => rhs; rw [foldFusedAux]
  by_cases h : steps < budget ∧ d < depth u
  · simp only [dite_eq_left h]
    exact foldFusedAux_steps_indep depth rec d budget _ _ _ (steps + 1)
  · simp only [dite_eq_right h]
termination_by budget - steps
decreasing_by omega

private theorem foldFusedAux_steps_ge (depth : Nat → Nat) (rec : Nat → Stored)
    (d budget u : Nat) (acc : Map) (steps : Nat) :
    steps ≤ (foldFusedAux depth rec d budget u acc steps).steps := by
  conv => rhs; rw [foldFusedAux]
  by_cases h : steps < budget ∧ d < depth u
  · simp only [dite_eq_left h]
    exact Nat.le_trans (Nat.le_succ _)
      (foldFusedAux_steps_ge depth rec d budget _ _ (steps + 1))
  · simp only [dite_eq_right h]
    exact Nat.le_refl _
termination_by budget - steps
decreasing_by omega

private theorem array_getElem_eq {α : Type} {a : Array α} {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (h : i = j) : a[i]'hi = a[j]'hj := by
  subst h
  rfl

private theorem loopPart_run
    {endpoints : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {F : JumpForest} {ref : Nat → Stored}
    {w : Width bits (max R.slots endpoints)}
    (ok : Occupied mem R F ref w)
    (input : Input L) (hWords : input.words = mem)
    (depthBase : Nat)
    (hDepthContig : ∀ v : Fin R.slots, (R.depthAddr v).val = depthBase + v.val)
    (d budget steps rem : Nat) (hRemEq : rem = budget - steps) :
    ∀ (u : Nat) (xs : Values) (s : State L),
      u < F.size →
      (reg s 6).val = u →
      (reg s 7).val = d →
      (reg s 8).val = rem →
      (reg s 9).val = depthBase →
      (reg s 10).val = R.base.val →
      ValuesRegs w.tags xs s →
      ∃ (t : State L) (k : Nat),
        k ≤ 96 * ((foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget u Map.identity steps).steps - steps) + 6 ∧
        run (loopPart (fits := fits) w.tags).code input k (Phase.initial s) = some ⟨t, k⟩ ∧
        ValuesRegs w.tags (evalAux (depthAt mem R) (recordAt mem R w.tags) d budget u xs steps) t ∧
        t.data = s.data := by
  induction rem generalizing steps with
  | zero =>
    intro u xs s hu _ _ hr8 _ _ hXs
    have hNotLt : ¬ (steps < budget) := by omega
    have hNeg : ¬ (steps < budget ∧ d < depthAt mem R u) := fun h => hNotLt h.1
    have hTw : 2 < 2 ^ bits := w.tags
    let ph := loopPart (fits := fits) w.tags
    let code := ph.code
    have hSz : code.size = 5 + (hopBodyPhase (fits := fits) w.tags).code.size + 1 :=
      loopPartCode_size w.tags
    have hHaltEq : ph.haltPC = 5 + (hopBodyPhase (fits := fits) w.tags).code.size := rfl
    have hFetch : ∀ j, j < 5 → code[j]? =
        (loopHeader (fits := fits) w.tags (5 + (hopBodyPhase (fits := fits) w.tags).code.size))[j]? :=
      fun j hj => loopPart_slice_hdr w.tags hj
    let s0 := Phase.initial s
    let s1 := putReg s0 11 ⟨1, by omega⟩
    have st0 : step code input s0 = some (.next s1) :=
      step_imm_put (by change code[0]? = _; rw [hFetch 0 (by decide)]; rfl)
        (by change 0 + 1 < code.size; rw [hSz]; omega)
    have hr8_1 : (reg s1 8).val = 0 := by
      change (reg (putReg s0 11 _) 8).val = 0
      rw [reg_putReg, ite_eq_right (by decide : (8 : Fin 16) ≠ 11)]
      exact hr8
    have hr11_1 : (reg s1 11).val = 1 := by simp only [s1, reg_putReg, ite_true]
    have st1 : step code input s1 = some (.next { s1 with pc := ph.haltPC }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s1)
        (a := 8) (b := 11) (t := ph.haltPC) (e := 2)
        (by change code[1]? = _; rw [hFetch 1 (by decide)]; rfl)
        (by
          split
          · rw [hHaltEq, hSz]; omega
          · rw [hSz]; omega)
      simpa only [hr8_1, hr11_1, ite_eq_left (by decide : (0 : Nat) < 1)] using hst
    have hh : step code input { s1 with pc := ph.haltPC } = some (.halted { s1 with pc := ph.haltPC }) :=
      step_halt_at ph.haltAt
    have exec := (Steps.cons st0 <| Steps.cons st1 <| Steps.zero { s1 with pc := ph.haltPC }).halts hh
    refine ⟨{ s1 with pc := ph.haltPC }, 3, by omega, exec, ?_, rfl⟩
    · conv => arg 2; rw [evalAux, dite_eq_right hNeg]
      have hPres1 : ∀ r : Fin 16, r ≠ 11 → reg { s1 with pc := ph.haltPC } r = reg s r := by
        intro r hr11; change reg (putReg s0 11 _) r = _; rw [reg_putReg, ite_eq_right hr11]; rfl
      refine ⟨⟨hXs.1.1, (hPres1 0 (by decide)).trans hXs.1.2.1,
          (hPres1 1 (by decide)).trans hXs.1.2.2.1, (hPres1 2 (by decide)).trans hXs.1.2.2.2⟩,
        ⟨hXs.2.1, (hPres1 3 (by decide)).trans hXs.2.2.1,
          (hPres1 4 (by decide)).trans hXs.2.2.2.1, (hPres1 5 (by decide)).trans hXs.2.2.2.2⟩⟩
  | succ rem' ih =>
    intro u xs s hu hr6 hr7 hr8 hr9 hr10 hXs
    have hTw : 2 < 2 ^ bits := w.tags
    have hGet : ∀ i (hi : i < mem.size), input.words[i]? = some (mem[i]'hi) :=
      fun i hi => by rw [hWords]; exact getElem?_pos mem i hi
    have hSzEq : mem.size = inputCap := by rw [← hWords, input.size_eq]
    have hLtBudget : steps < budget := by omega
    have huSlots : u < R.slots := ok.size_eq.symm ▸ hu
    let uFin : Fin R.slots := ⟨u, huSlots⟩
    have hDepthULtMem : depthBase + u < mem.size := by
      rw [← hDepthContig uFin]; exact R.depthMem uFin
    have hDepthULtBits : depthBase + u < 2 ^ bits :=
      Nat.lt_of_lt_of_le (hSzEq ▸ hDepthULtMem) fits
    let wDU := mem[depthBase + u]'hDepthULtMem
    have hDUVal : wDU.val = depthAt mem R u := by
      simp only [depthAt, dite_eq_left huSlots, wDU]
      exact congrArg Fin.val (array_getElem_eq hDepthULtMem (R.depthMem uFin) (hDepthContig uFin).symm)
    have hWDU : input.words[depthBase + u]? = some wDU := hGet _ hDepthULtMem
    let ph := loopPart (fits := fits) w.tags
    let code := ph.code
    have hSz : code.size = 5 + (hopBodyPhase (fits := fits) w.tags).code.size + 1 :=
      loopPartCode_size w.tags
    have hHaltEq : ph.haltPC = 5 + (hopBodyPhase (fits := fits) w.tags).code.size := rfl
    have hFetch : ∀ j, j < 5 → code[j]? =
        (loopHeader (fits := fits) w.tags (5 + (hopBodyPhase (fits := fits) w.tags).code.size))[j]? :=
      fun j hj => loopPart_slice_hdr w.tags hj
    let s0 := Phase.initial s
    let s1 := putReg s0 11 ⟨1, by omega⟩
    have st0 : step code input s0 = some (.next s1) :=
      step_imm_put (by change code[0]? = _; rw [hFetch 0 (by decide)]; rfl)
        (by change 0 + 1 < code.size; rw [hSz]; omega)
    have hr8_1 : (reg s1 8).val = rem' + 1 := by
      change (reg (putReg s0 11 _) 8).val = _
      rw [reg_putReg, ite_eq_right (by decide : (8 : Fin 16) ≠ 11)]
      exact hr8
    have hr11_1 : (reg s1 11).val = 1 := by simp only [s1, reg_putReg, ite_true]
    have hNotLt1 : ¬ ((reg s1 8).val < (reg s1 11).val) := by rw [hr8_1, hr11_1]; omega
    have st1 : step code input s1 = some (.next { s1 with pc := 2 }) := by
      have hst := step_branchLt_at' (code := code) (input := input) (s := s1)
        (a := 8) (b := 11) (t := ph.haltPC) (e := 2)
        (by change code[1]? = _; rw [hFetch 1 (by decide)]; rfl)
        (by split <;> rw [hSz] <;> change _ < 5 + _ + 1 <;> omega)
      simpa only [ite_eq_right hNotLt1] using hst
    let s2 := { s1 with pc := 2 }
    have h9_2 : (reg s2 9).val = depthBase := by
      change (reg (putReg s0 11 _) 9).val = _
      rw [reg_putReg, ite_eq_right (by decide : (9 : Fin 16) ≠ 11)]; exact hr9
    have h6_2 : (reg s2 6).val = u := by
      change (reg (putReg s0 11 _) 6).val = _
      rw [reg_putReg, ite_eq_right (by decide : (6 : Fin 16) ≠ 11)]; exact hr6
    let s3 := putReg s2 11 (add (reg s2 9) (reg s2 6))
    have st2 : step code input s2 = some (.next s3) :=
      step_add_put (by change code[2]? = _; rw [hFetch 2 (by decide)]; rfl)
        (by change 2 + 1 < code.size; rw [hSz]; omega)
    have hr11_3 : (reg s3 11).val = depthBase + u := by
      change (reg (putReg s2 11 _) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, add_no_wrap _ _ (by rw [h9_2, h6_2]; exact hDepthULtBits),
        h9_2, h6_2]
    let s4 := putReg s3 11 wDU
    have st3 : step code input s3 = some (.next s4) :=
      step_loadInput_put (by change code[3]? = _; rw [hFetch 3 (by decide)]; rfl)
        (by rw [hr11_3]; exact hWDU)
        (by change 3 + 1 < code.size; rw [hSz]; omega)
    have hPres4 : ∀ r : Fin 16, r ≠ 11 → reg s4 r = reg s r := by
      intro r hr11
      change reg (putReg (putReg s2 11 _) 11 wDU) r = _
      rw [reg_putReg, ite_eq_right hr11, reg_putReg, ite_eq_right hr11]
      change reg (putReg s0 11 _) r = _
      rw [reg_putReg, ite_eq_right hr11]
      rfl
    have h7_4 : (reg s4 7).val = d := by rw [hPres4 7 (by decide), hr7]
    have h11_4 : (reg s4 11).val = depthAt mem R u := by
      change (reg (putReg s3 11 wDU) 11).val = _
      rw [reg_putReg, ite_eq_left rfl, hDUVal]
    by_cases hltD : d < depthAt mem R u
    · have hCond4 : (reg s4 7).val < (reg s4 11).val := by rw [h7_4, h11_4]; exact hltD
      have st4 : step code input s4 = some (.next { s4 with pc := 5 }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s4)
          (a := 7) (b := 11) (t := 5) (e := ph.haltPC)
          (by change code[4]? = _; rw [hFetch 4 (by decide)]; rfl)
          (by split <;> rw [hSz] <;> change _ < 5 + _ + 1 <;> omega)
        simpa only [ite_eq_left hCond4] using hst
      have pre5 : Steps code input 5 (Phase.initial s) (relocateStatePC 5 (Phase.initial s4)) :=
        Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
        Steps.cons st4 <| Steps.zero _
      let recU := ref u
      have hp : recU.parent < R.slots := by
        change (ref u).parent < R.slots
        rw [ok.parent_eq u hu, ok.size_eq]
        exact ok.valid.parentOf_lt_size hu
      have hj : recU.jump < R.slots := by
        change (ref u).jump < R.slots
        rw [ok.jump_eq u hu, ok.size_eq]
        exact ok.valid.jumpOf_lt_size hu
      have hRec : (storedCodec w.tags).valid recU :=
        stored_fits w recU hp hj (ok.maps uFin).1 (ok.maps uFin).2
      have hRecExact : recordAt mem R w.tags u = recU := by
        rw [recordAt, dite_eq_left huSlots]
        exact readStoredAt_exact w.tags mem R.base u (R.recordAddr uFin) (R.recordMem uFin)
          recU hRec (ok.packed uFin hRec)
      let jFin : Fin R.slots := ⟨recU.jump, hj⟩
      have hDepthJLtMem : depthBase + recU.jump < mem.size := by
        rw [← hDepthContig jFin]; exact R.depthMem jFin
      let wDJ := mem[depthBase + recU.jump]'hDepthJLtMem
      have hDJVal : wDJ.val = depthAt mem R recU.jump := by
        simp only [depthAt, dite_eq_left hj, wDJ]
        exact congrArg Fin.val (array_getElem_eq hDepthJLtMem (R.depthMem jFin) (hDepthContig jFin).symm)
      have hWDJ : input.words[depthBase + recU.jump]? = some wDJ := hGet _ hDepthJLtMem
      have hXs4 : ValuesRegs w.tags xs s4 := by
        refine ⟨⟨hXs.1.1, (hPres4 0 (by decide)).trans hXs.1.2.1,
            (hPres4 1 (by decide)).trans hXs.1.2.2.1, (hPres4 2 (by decide)).trans hXs.1.2.2.2⟩,
          ⟨hXs.2.1, (hPres4 3 (by decide)).trans hXs.2.2.1,
            (hPres4 4 (by decide)).trans hXs.2.2.2.1, (hPres4 5 (by decide)).trans hXs.2.2.2.2⟩⟩
      have h4_6 : (reg s4 6).val = u := by rw [hPres4 6 (by decide), hr6]
      have h4_8 : (reg s4 8).val = rem' + 1 := by rw [hPres4 8 (by decide), hr8]
      have h4_9 : (reg s4 9).val = depthBase := by rw [hPres4 9 (by decide), hr9]
      have h4_10 : (reg s4 10).val = R.base.val := by rw [hPres4 10 (by decide), hr10]
      have hRecAddr4 : (reg s4 10).val + 18 * (reg s4 6).val + 18 ≤ inputCap := by
        rw [h4_10, h4_6, ← hSzEq]; exact R.recordMem uFin
      have hRecW4 : ∀ i : Fin 18,
          input.words[(reg s4 10).val + 18 * (reg s4 6).val + i.val]? =
            some ((storedCodec w.tags).encode recU hRec i) := by
        intro i
        rw [h4_10, h4_6]
        have hm := R.recordMem uFin
        have hi := i.isLt
        have hidx : R.base.val + 18 * u + i.val < mem.size := by omega
        exact (hGet _ hidx).trans (congrArg some (ok.packed uFin hRec i))
      obtain ⟨uHop, kHop, hkHop, hHopRun, hHopXs, hHop6, hHop8, hHop7, hHop9, hHop10, hHopData⟩ :=
        hopBodyPhase_spec w.tags input s4 recU wDJ.val xs hRec wDJ.isLt hXs4 (by omega)
          hRecAddr4 (by rw [h4_9, ← hSzEq]; exact hDepthJLtMem) hRecW4
          (by rw [h4_9]; exact hWDJ)
      have hHopSteps := loopPart_hop_step w.tags hHopRun
      let sel := selectAtDepth (depthAt mem R) d recU
      have hSelEq : selectAtDepth (fun _ => wDJ.val) (reg s4 7).val recU = sel := by
        rw [h7_4, hDJVal]
        rfl
      have hDstLt : sel.dst < F.size := by
        by_cases hc : d ≤ depthAt mem R recU.jump
        · simpa [sel, selectAtDepth, Stored.select, hc] using (ok.size_eq ▸ hj)
        · simpa [sel, selectAtDepth, Stored.select, hc] using (ok.size_eq ▸ hp)
      have hHop8' : (reg uHop 8).val = rem' := by rw [hHop8, h4_8]; omega
      obtain ⟨t, kTail, hkTail, hTailRun, hTailXs, hTailData⟩ :=
        ih (steps + 1) (by omega) sel.dst (Map.eval sel.map xs) uHop hDstLt
          (by rw [hHop6, hSelEq]) (by rw [hHop7, h7_4]) hHop8' (by rw [hHop9, h4_9])
          (by rw [hHop10, h4_10]) (by rw [hSelEq] at hHopXs; exact hHopXs)
      obtain ⟨lTail, tTail, hTailSteps, hTailHalt, hTailCost⟩ := run_has_steps_then_halt hTailRun
      have hAllSteps := steps_trans (steps_trans pre5 hHopSteps) hTailSteps
      have hAllRun := hAllSteps.halts hTailHalt
      have hSameT : t = tTail := (halted_fetch_and_state hTailHalt).2
      have hTotalEq : 5 + kHop + kTail = (5 + kHop + lTail) + 1 := by
        change kTail = lTail + 1 at hTailCost
        omega
      have hAllRun' : run code input (5 + kHop + kTail) (Phase.initial s) =
          some ⟨t, 5 + kHop + kTail⟩ := by
        rw [hTotalEq]
        simpa only [hSameT] using hAllRun
      have hFusedEq : foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget u Map.identity steps =
          foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget sel.dst
            (Map.compose Map.identity sel.map) (steps + 1) := by
        conv => lhs; rw [foldFusedAux, dite_eq_left ⟨hLtBudget, hltD⟩]
        simp only [hRecExact, sel]
      have hStepsInd := foldFusedAux_steps_indep (depthAt mem R) (recordAt mem R w.tags)
        d budget sel.dst (Map.compose Map.identity sel.map) Map.identity (steps + 1)
      have hStepsGe := foldFusedAux_steps_ge (depthAt mem R) (recordAt mem R w.tags)
        d budget sel.dst Map.identity (steps + 1)
      let finalSteps := (foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget
        sel.dst Map.identity (steps + 1)).steps
      have hBound : 5 + kHop + kTail ≤
          96 * ((foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget u Map.identity steps).steps - steps) + 6 := by
        rw [hFusedEq, hStepsInd]
        have hDiff : finalSteps - steps = (finalSteps - (steps + 1)) + 1 := by
          change steps + 1 ≤ finalSteps at hStepsGe
          omega
        rw [hDiff, Nat.mul_succ]
        change kTail ≤ 96 * (finalSteps - (steps + 1)) + 6 at hkTail
        omega
      refine ⟨t, 5 + kHop + kTail, hBound, hAllRun', ?_, hTailData.trans hHopData⟩
      conv => arg 2; rw [evalAux, dite_eq_left ⟨hLtBudget, hltD⟩]
      simpa only [hRecExact, sel] using hTailXs
    · have hCond4 : ¬ ((reg s4 7).val < (reg s4 11).val) := by rw [h7_4, h11_4]; exact hltD
      have hNeg : ¬ (steps < budget ∧ d < depthAt mem R u) := fun h => hltD h.2
      have st4 : step code input s4 = some (.next { s4 with pc := ph.haltPC }) := by
        have hst := step_branchLt_at' (code := code) (input := input) (s := s4)
          (a := 7) (b := 11) (t := 5) (e := ph.haltPC)
          (by change code[4]? = _; rw [hFetch 4 (by decide)]; rfl)
          (by
            split
            · rw [hSz]; omega
            · rw [hHaltEq, hSz]; omega)
        simpa only [ite_eq_right hCond4] using hst
      have hh : step code input { s4 with pc := ph.haltPC } =
          some (.halted { s4 with pc := ph.haltPC }) :=
        step_halt_at ph.haltAt
      have exec := (Steps.cons st0 <| Steps.cons st1 <| Steps.cons st2 <| Steps.cons st3 <|
        Steps.cons st4 <| Steps.zero { s4 with pc := ph.haltPC }).halts hh
      refine ⟨{ s4 with pc := ph.haltPC }, 6, by omega, exec, ?_, rfl⟩
      conv => arg 2; rw [evalAux, dite_eq_right hNeg]
      refine ⟨⟨hXs.1.1, (hPres4 0 (by decide)).trans hXs.1.2.1,
          (hPres4 1 (by decide)).trans hXs.1.2.2.1, (hPres4 2 (by decide)).trans hXs.1.2.2.2⟩,
        ⟨hXs.2.1, (hPres4 3 (by decide)).trans hXs.2.2.1,
          (hPres4 4 (by decide)).trans hXs.2.2.2.1, (hPres4 5 (by decide)).trans hXs.2.2.2.2⟩⟩

end Helpers

/-! ### Public Word-RAM Exit Evaluation Program and Specifications -/

private def exitEvalPhase {bits inputCap : Nat} {fits : inputCap ≤ 2 ^ bits}
    (hTag : TagsFit bits) : Phase (exitEvalLayout bits inputCap fits) :=
  (initPhase hTag).link (loopPart hTag)

/-- Fixed 16-register read-only word-RAM program (`workCap = 0`) compiling
`ExitPriorBase.run` over contiguous `depth`, 18-word `storedCodec` records, and
6-word `intervalCodec` serialized prior entries.

Input registers at `pc = 0`:
`r6 = u`, `r7 = d`, `r8 = v`, `r9 = depthBase`, `r10 = storedBase`, `r11 = priorBase`.
Output at halt: `r0..r5` holds the exact 6-word `intervalCodec` representation of
`PriorBase.run mem R w.tags prior v u d` (`ValuesRegs`). -/
def exitEvalProgram {bits inputCap : Nat} {fits : inputCap ≤ 2 ^ bits}
    (hTag : TagsFit bits) : Program (exitEvalLayout bits inputCap fits) :=
  (exitEvalPhase hTag).code

theorem ceilLog2_le_oracleL (n : Nat) :
    PaperB.ceilLog2 (n + 2) ≤ PaperB.OracleContract.L n := by
  apply PaperB.ceilLog2_le_of_pow2_ge
  have hlt : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) :=
    (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self (Nat.log2 (n + 1)))
  change n + 2 ≤ 2 ^ PaperB.OracleContract.L n
  exact hlt

/-- Exact execution and `O(foldStored.steps)` work proof for `exitEvalProgram`
against `ExitPriorBase.run`. -/
theorem exitEvalProgram_spec {bits endpoints : Nat} {mem : Array (Word bits)}
    {fits : mem.size ≤ 2 ^ bits}
    {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
    {w : Width bits (max R.slots endpoints)}
    (ok : Occupied mem R F ref w)
    (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
    (B : BaseView prior.size mem.size)
    (hPlaced : SealedPriorBase.Placed w prior hb mem B)
    (input : Input (exitEvalLayout bits mem.size fits))
    (hWords : input.words = mem)
    (depthBase : Nat)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = depthBase + x.val)
    {u : Nat} (hu : u < F.size) (v : Fin prior.size) (d : Nat)
    (s : State (exitEvalLayout bits mem.size fits))
    (hpc : s.pc = 0)
    (hr6 : (reg s 6).val = u) (hr7 : (reg s 7).val = d) (hr8 : (reg s 8).val = v.val)
    (hr9 : (reg s 9).val = depthBase) (hr10 : (reg s 10).val = R.base.val)
    (hr11 : (reg s 11).val = B.start) :
    ∃ (t : State (exitEvalLayout bits mem.size fits))
      (trace : List (State (exitEvalLayout bits mem.size fits))) (k : Nat),
      k ≤ 96 * (foldStored mem R w.tags u d).steps + 28 ∧
      run (exitEvalProgram (fits := fits) w.tags) input k s = some ⟨t, k⟩ ∧
      SuccessfulTrace (exitEvalProgram (fits := fits) w.tags) input s trace ⟨t, k⟩ ∧
      tracePeakWords input trace = footprint (exitEvalLayout bits mem.size fits) ∧
      ValuesRegs w.tags (PriorBase.run mem R w.tags prior v u d) t ∧
      t.data = s.data := by
  have hGet : ∀ i (hi : i < mem.size), input.words[i]? = some (mem[i]'hi) :=
    fun i hi => by rw [hWords]; exact getElem?_pos mem i hi
  have huSlots : u < R.slots := ok.size_eq.symm ▸ hu
  let uFin : Fin R.slots := ⟨u, huSlots⟩
  let seed : Values := (prior[v.val]'(v.isLt)).getD PaperB.BuiltExit.zero
  have hSeedBound : RankBound (2 ^ bits) seed.x0 ∧ RankBound (2 ^ bits) seed.x1 :=
    ⟨rankBound_mono w.ranks (hb v).1, rankBound_mono w.ranks (hb v).2⟩
  have hSeedAddr : (reg s 11).val + 6 * (reg s 8).val + 6 ≤ mem.size := by
    rw [hr11, hr8]
    have hv := v.isLt
    have hB := B.fits
    omega
  have hSeedWord_x0 : ∀ k : Fin 3,
      input.words[(reg s 11).val + 6 * (reg s 8).val + k.val]? =
        some ((intervalCodec w.tags).encode seed.x0 hSeedBound.1 k) := by
    intro k
    have hk := k.isLt
    have hv := v.isLt
    have hB := B.fits
    have hIdxMem : B.start + (6 * v.val + k.val) < mem.size := by omega
    have hAddrEq : (reg s 11).val + 6 * (reg s 8).val + k.val = B.start + (6 * v.val + k.val) := by
      rw [hr11, hr8]; omega
    rw [hAddrEq]
    refine (hGet _ hIdxMem).trans (congrArg some ?_)
    let k6 : Fin 6 := ⟨k.val, by omega⟩
    let j : Fin (6 * prior.size) := ⟨6 * v.val + k6.val, by omega⟩
    have hSer := (hPlaced j).trans (serialize_word_eq (inputCap := mem.size) w prior hb v k6)
    simpa only [k6, dite_eq_left hk] using hSer
  have hSeedWord_x1 : ∀ k : Fin 3,
      input.words[(reg s 11).val + 6 * (reg s 8).val + (3 + k.val)]? =
        some ((intervalCodec w.tags).encode seed.x1 hSeedBound.2 k) := by
    intro k
    have hk := k.isLt
    have hv := v.isLt
    have hB := B.fits
    have hIdxMem : B.start + (6 * v.val + (3 + k.val)) < mem.size := by omega
    have hAddrEq : (reg s 11).val + 6 * (reg s 8).val + (3 + k.val) =
        B.start + (6 * v.val + (3 + k.val)) := by
      rw [hr11, hr8]; omega
    rw [hAddrEq]
    refine (hGet _ hIdxMem).trans (congrArg some ?_)
    let k6 : Fin 6 := ⟨3 + k.val, by omega⟩
    let j : Fin (6 * prior.size) := ⟨6 * v.val + k6.val, by omega⟩
    have hSer := (hPlaced j).trans (serialize_word_eq (inputCap := mem.size) w prior hb v k6)
    have hNotLt : ¬ (k6.val < 3) := by dsimp only [k6]; omega
    have hSub : (⟨k6.val - 3, by have := k6.isLt; omega⟩ : Fin 3) = k := by
      ext; dsimp only [k6]; omega
    simpa only [k6, dite_eq_right hNotLt, hSub] using hSer
  have hDepthUAddr : (reg s 9).val + (reg s 6).val < mem.size := by
    rw [hr9, hr6, ← hDepthContig uFin]
    exact R.depthMem uFin
  let wDU := mem[(reg s 9).val + (reg s 6).val]'hDepthUAddr
  have hDUVal : wDU.val = depthAt mem R u := by
    simp only [depthAt, dite_eq_left huSlots, wDU]
    have hEq : (reg s 9).val + (reg s 6).val = (R.depthAddr uFin).val := by
      rw [hr9, hr6, hDepthContig uFin]
    exact congrArg Fin.val (array_getElem_eq hDepthUAddr (R.depthMem uFin) hEq)
  have hWDU : input.words[(reg s 9).val + (reg s 6).val]? = some wDU := hGet _ hDepthUAddr
  have hSW0 : input.words[(reg s 11).val + 6 * (reg s 8).val]? =
      some ((intervalCodec w.tags).encode seed.x0 hSeedBound.1 0) := by
    simpa only [Fin.val_zero, Nat.add_zero] using hSeedWord_x0 0
  have hSW1 : input.words[(reg s 11).val + 6 * (reg s 8).val + 1]? =
      some ((intervalCodec w.tags).encode seed.x0 hSeedBound.1 1) :=
    hSeedWord_x0 1
  have hSW2 : input.words[(reg s 11).val + 6 * (reg s 8).val + 2]? =
      some ((intervalCodec w.tags).encode seed.x0 hSeedBound.1 2) :=
    hSeedWord_x0 2
  have hSW3 : input.words[(reg s 11).val + 6 * (reg s 8).val + 3]? =
      some ((intervalCodec w.tags).encode seed.x1 hSeedBound.2 0) :=
    hSeedWord_x1 0
  have hSW4 : input.words[(reg s 11).val + 6 * (reg s 8).val + 4]? =
      some ((intervalCodec w.tags).encode seed.x1 hSeedBound.2 1) :=
    hSeedWord_x1 1
  have hSW5 : input.words[(reg s 11).val + 6 * (reg s 8).val + 5]? =
      some ((intervalCodec w.tags).encode seed.x1 hSeedBound.2 2) :=
    hSeedWord_x1 2
  obtain ⟨u1, k1, hk1, hInitRun, hInitXs, hInit8, hInit6, hInit7, hInit9, hInit10, hInitData⟩ :=
    initPhase_spec w.tags input s seed hSeedBound wDU.val wDU.isLt hSeedAddr hDepthUAddr
      hSW0 hSW1 hSW2 hSW3 hSW4 hSW5 hWDU
  have hBudgetEq : wDU.val - (reg s 7).val = depthAt mem R u - d := by rw [hDUVal, hr7]
  obtain ⟨u2, k2, hk2, hLoopRun, hLoopXs, hLoopData⟩ :=
    loopPart_run ok input hWords depthBase hDepthContig d (depthAt mem R u - d) 0
      (depthAt mem R u - d) (Nat.sub_zero _).symm u seed u1 hu
      (by rw [hInit6, hr6]) (by rw [hInit7, hr7]) (by rw [hInit8, hBudgetEq])
      (by rw [hInit9, hr9]) (by rw [hInit10, hr10]) hInitXs
  obtain ⟨t, trace, htRegs, htData, hAllRun, hTrace, hPeak⟩ :=
    run_linked_pair (initPhase (fits := fits) w.tags) (loopPart (fits := fits) w.tags).code
      (Nat.zero_lt_of_lt (loopPart (fits := fits) w.tags).haltFits) hInitRun hLoopRun
  have hsEq : Phase.initial s = s := by cases s; cases hpc; rfl
  rw [hsEq] at hAllRun hTrace
  have hValsEq : evalAux (depthAt mem R) (recordAt mem R w.tags) d (depthAt mem R u - d) u seed 0 =
      PriorBase.run mem R w.tags prior v u d := by
    rw [← Map.eval_identity seed]
    exact evalAux_eq_foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d
      (depthAt mem R u - d) u Map.identity seed 0
  have htXs : ValuesRegs w.tags (PriorBase.run mem R w.tags prior v u d) t := by
    rw [← hValsEq]
    have hRegEq : ∀ r : Fin 16, reg t r = reg u2 r := by
      intro r; cases t; cases u2; simp only at htRegs; cases htRegs; rfl
    refine ⟨⟨hLoopXs.1.1, ?_, ?_, ?_⟩, ⟨hLoopXs.2.1, ?_, ?_, ?_⟩⟩
    · rw [hRegEq 0]; exact hLoopXs.1.2.1
    · rw [hRegEq 1]; exact hLoopXs.1.2.2.1
    · rw [hRegEq 2]; exact hLoopXs.1.2.2.2
    · rw [hRegEq 3]; exact hLoopXs.2.2.1
    · rw [hRegEq 4]; exact hLoopXs.2.2.2.1
    · rw [hRegEq 5]; exact hLoopXs.2.2.2.2
  have hkBound : k1 + k2 ≤ 96 * (foldStored mem R w.tags u d).steps + 28 := by
    change k1 + k2 ≤ 96 * (foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d
      (depthAt mem R u - d) u Map.identity 0).steps + 28
    omega
  exact ⟨t, trace, k1 + k2, hkBound, hAllRun, hTrace, hPeak, htXs, htData.trans (hLoopData.trans hInitData)⟩

/-- `O(L)` RAM step bound (`≤ 288 * L n + 28 ≤ 316 * (L n + 1)`) and exact equivalence
to `ExitSealedBase.SealedPriorBase.run`. -/
theorem exitEvalProgram_sealed_spec {bits endpoints n : Nat} {mem : Array (Word bits)}
    {fits : mem.size ≤ 2 ^ bits}
    {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
    {w : Width bits (max R.slots endpoints)}
    (ok : Occupied mem R F ref w)
    (route : JumpMapRoute.StoreOK F ref)
    (hn : F.numInserted ≤ n)
    (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
    (B : BaseView prior.size mem.size)
    (hPlaced : SealedPriorBase.Placed w prior hb mem B)
    (input : Input (exitEvalLayout bits mem.size fits))
    (hWords : input.words = mem)
    (depthBase : Nat)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = depthBase + x.val)
    {u : Nat} (hu : u < F.size) (v : Fin prior.size) (d : Nat)
    (s : State (exitEvalLayout bits mem.size fits))
    (hpc : s.pc = 0)
    (hr6 : (reg s 6).val = u) (hr7 : (reg s 7).val = d) (hr8 : (reg s 8).val = v.val)
    (hr9 : (reg s 9).val = depthBase) (hr10 : (reg s 10).val = R.base.val)
    (hr11 : (reg s 11).val = B.start) :
    ∃ (t : State (exitEvalLayout bits mem.size fits))
      (trace : List (State (exitEvalLayout bits mem.size fits))) (k : Nat),
      k ≤ 288 * PaperB.OracleContract.L n + 28 ∧
      run (exitEvalProgram (fits := fits) w.tags) input k s = some ⟨t, k⟩ ∧
      SuccessfulTrace (exitEvalProgram (fits := fits) w.tags) input s trace ⟨t, k⟩ ∧
      tracePeakWords input trace = footprint (exitEvalLayout bits mem.size fits) ∧
      ValuesRegs w.tags (SealedPriorBase.run mem R w.tags mem B v u d) t ∧
      t.data = s.data := by
  obtain ⟨t, trace, k, hk, hRun, hTrace, hPeak, hVals, hData⟩ :=
    exitEvalProgram_spec ok prior hb B hPlaced input hWords depthBase hDepthContig
      hu v d s hpc hr6 hr7 hr8 hr9 hr10 hr11
  have hFoldSteps := foldStored_steps_le ok route hu hn d
  have hLog := ceilLog2_le_oracleL n
  have hkL : k ≤ 288 * PaperB.OracleContract.L n + 28 := by omega
  have hEq : SealedPriorBase.run mem R w.tags mem B v u d =
      PriorBase.run mem R w.tags prior v u d :=
    SealedPriorBase.run_eq_priorBase mem R w prior hb mem B hPlaced v u d
  rw [← hEq] at hVals
  exact ⟨t, trace, k, hkL, hRun, hTrace, hPeak, hVals, hData⟩

/-- End-to-end `O(L)` word-RAM bridge to `BuiltExit.Query.run`. -/
theorem exitEvalProgram_query_spec
    {H : PaperB.LabelledQuotient} {m : Nat}
    {W : PaperB.BuiltExit.Model H m} {Bp : PaperB.LabelledQuotient.CutPair H}
    {z : Fin H.vertexCount}
    {P : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    (q : PaperB.BuiltExit.Query W P S Bp z)
    (rb : PaperB.BuiltExit.BaseReader P) (rm : PaperB.BuiltExit.MapReader S)
    {bits endpoints n : Nat} {mem : Array (Word bits)}
    {fits : mem.size ≤ 2 ^ bits}
    {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
    {w : Width bits (max R.slots endpoints)}
    (ok : Occupied mem R F ref w)
    (route : JumpMapRoute.StoreOK F ref)
    (hn : F.numInserted ≤ n)
    (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
    (B : BaseView prior.size mem.size)
    (hPlaced : SealedPriorBase.Placed w prior hb mem B)
    (input : Input (exitEvalLayout bits mem.size fits))
    (hWords : input.words = mem)
    (depthBase : Nat)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = depthBase + x.val)
    {u : Nat} (hu : u < F.size) (v : Fin prior.size) (d : Nat)
    (hbase : (prior[v.val]'(v.isLt)) = rb z q.readOK)
    (hmap : PriorBase.accumulated (foldFused F ref u d) = q.route.actual rm)
    (s : State (exitEvalLayout bits mem.size fits))
    (hpc : s.pc = 0)
    (hr6 : (reg s 6).val = u) (hr7 : (reg s 7).val = d) (hr8 : (reg s 8).val = v.val)
    (hr9 : (reg s 9).val = depthBase) (hr10 : (reg s 10).val = R.base.val)
    (hr11 : (reg s 11).val = B.start) :
    ∃ (t : State (exitEvalLayout bits mem.size fits))
      (trace : List (State (exitEvalLayout bits mem.size fits))) (k : Nat),
      k ≤ 288 * PaperB.OracleContract.L n + 28 ∧
      run (exitEvalProgram (fits := fits) w.tags) input k s = some ⟨t, k⟩ ∧
      SuccessfulTrace (exitEvalProgram (fits := fits) w.tags) input s trace ⟨t, k⟩ ∧
      tracePeakWords input trace = footprint (exitEvalLayout bits mem.size fits) ∧
      ValuesRegs w.tags (q.run rb rm) t ∧
      t.data = s.data := by
  obtain ⟨t, trace, k, hk, hRun, hTrace, hPeak, hVals, hData⟩ :=
    exitEvalProgram_sealed_spec ok route hn prior hb B hPlaced input hWords
      depthBase hDepthContig hu v d s hpc hr6 hr7 hr8 hr9 hr10 hr11
  have hEq : SealedPriorBase.run mem R w.tags mem B v u d = q.run rb rm := by
    rw [SealedPriorBase.run_eq_priorBase mem R w prior hb mem B hPlaced v u d]
    exact PriorBase.run_eq_query q rb rm ok hu d prior v hbase hmap
  rw [← hEq]
  exact ⟨t, trace, k, hk, hRun, hTrace, hPeak, hVals, hData⟩

end PaperB.RamProgram.ExitEval
