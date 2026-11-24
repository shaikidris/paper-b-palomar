module

public import PaperB.RamForestFinish
public import PaperB.RamAppendLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamForestStack (StackAt commandWord pushCode push_steps)
open PaperB.ForestLayout (ChildLists)
open PaperB.WordOps (add ltb)
open PaperB.LabelledQuotient (ValidDepthTree)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def zeroCell : List (Instr bits 15) :=
  pushCode registers.ptr tinBase registers.zero registers.one registers.tmp

private def seedRoot : List (Instr bits 15) :=
  pushCode registers.ptr registers.stackBase cmd registers.one registers.tmp

/-- Zero both adjacent time columns, reset the cursor and clock, then push
the root command. The parent-derived CSR banks are already in the arena. -/
def seedCode (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  let branch : Instr bits 15 := .branchLt registers.ptr registers.remain 1 5
  let resets : List (Instr bits 15) :=
    [.goto 0, .add registers.ptr registers.zero registers.zero,
      .add clk registers.zero registers.zero]
  ([branch] ++ zeroCell ++ resets ++ seedRoot ++ [Instr.halt]).toArray

/-- Scalar parameters for the seed phase. The time columns and stack bank
can initially contain arbitrary words. -/
structure SeedInput (a : Arena bits workCap n) (g : ChildLists n) (root : Fin n)
    (s : State L) : Prop where
  pc : s.pc = 0
  regs : Control a s
  length_eq : (reg s registers.remain).val = 2 * n
  empty : (reg s registers.ptr).val = 0
  root_eq : reg s cmd = commandWord a.tags (.enter root)
  rows : ChildImage a g s.data

private theorem stack_repeat_iff {data : Array (Word bits)} {base i : Nat}
    {w : Word bits} :
    StackAt data base (List.replicate i w) ↔ ∀ j < i, data[base + j]? = some w := by
  induction i with
  | zero => simp [StackAt]
  | succ i ih =>
    simp only [List.replicate_succ, StackAt, List.length_replicate, ih]
    constructor
    · rintro ⟨last, other⟩ j hj
      by_cases e : j = i
      · subst j; exact last
      · exact other j (by omega)
    · intro h
      exact ⟨h i (by omega), fun j hj => h j (by omega)⟩

private structure Clear (a : Arena bits workCap n) (orig : State L) (i : Nat)
    (s : State L) : Prop where
  pc : s.pc = 0
  ptr : (reg s registers.ptr).val = i
  fixed : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → reg s r = reg orig r
  cleared : StackAt s.data a.tin (List.replicate i (reg orig registers.zero))
  untouched : ∀ j, (j < a.tin ∨ a.tin + i ≤ j) → s.data[j]? = orig.data[j]?

private theorem clear_step (input : Input L) {a : Arena bits workCap n}
    {g : ChildLists n} {root : Fin n} {orig : State L} {i : Nat}
    (initial : SeedInput a g root orig) (below : i < 2 * n) :
    BlockSpec (seedCode hi hw) input 5 (Clear a orig i) (Clear a orig (i + 1)) := by
  intro s h
  have remain : (reg s registers.remain).val = 2 * n :=
    (congrArg Fin.val (h.fixed registers.remain (by decide +revert) (by decide +revert))).trans
      initial.length_eq
  have cmp : ltb (reg s registers.ptr) (reg s registers.remain) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [h.ptr, remain]; exact below)
  let u : State L := {s with pc := 1}
  have fetch : (seedCode hi hw)[s.pc]? = some (.branchLt registers.ptr registers.remain 1 5) := by
    rw [h.pc]; rfl
  have su : step (seedCode hi hw) input s = some (.next u) := by
    simpa only [u, cmp, ite_true] using
      step_branchLt_at (input := input) fetch (by rw [cmp]; exact (show 1 < 11 by decide))
  have place : Placed (seedCode hi hw) 1 (zeroCell (bits := bits)) := by
    intro k op hk
    cases k with
    | zero => exact hk
    | succ k =>
      cases k with
      | zero => exact hk
      | succ k =>
        cases k with
        | zero => exact hk
        | succ k =>
          change ([] : List (Instr bits 15))[k]? = some op at hk
          simp at hk
  have base : (reg u tinBase).val = a.tin :=
    (congrArg Fin.val (h.fixed tinBase (by decide +revert) (by decide +revert))).trans initial.regs.tin_eq
  have room := a.room
  have wide := a.wordFits
  have fit : (reg u tinBase).val + (List.replicate i (reg orig registers.zero)).length <
      (layout bits inputCap workCap hi hw).workCap := by
    change (reg u tinBase).val + (List.replicate i (reg orig registers.zero)).length < workCap
    rw [base, List.length_replicate]
    unfold Arena.tin
    omega
  have stack : StackAt u.data (reg u tinBase).val (List.replicate i (reg orig registers.zero)) := by
    rw [base]; exact h.cleared
  obtain ⟨v, uv, vpc, vp, vs, vr, vm⟩ := push_steps (input := input) (s := u) place rfl
    (show 4 < 11 by decide) (by change (reg s registers.ptr).val = _; simpa only [List.length_replicate] using h.ptr)
    ((congrArg Fin.val (h.fixed registers.one (by decide +revert) (by decide +revert))).trans
      initial.regs.one) fit (by rw [List.length_replicate]; omega)
    (show registers.zero ≠ registers.tmp by decide)
    (show registers.ptr ≠ registers.tmp by decide)
    (show registers.one ≠ registers.tmp by decide) stack
  have back : (seedCode hi hw)[v.pc]? = some (.goto 0) := by rw [vpc]; rfl
  let t : State L := {v with pc := 0}
  have vt : step (seedCode hi hw) input v = some (.next t) :=
    step_goto_at back (show 0 < 11 by decide)
  refine ⟨t, (Steps.cons su uv).append (.cons vt (.zero _)), rfl, ?_, ?_, ?_, ?_⟩
  · change (reg v registers.ptr).val = i + 1
    simpa only [List.length_replicate] using vp
  · intro r first second
    exact (vr r first second).trans (h.fixed r first second)
  · have eq : reg u registers.zero = reg orig registers.zero :=
      h.fixed registers.zero (by decide +revert) (by decide +revert)
    rw [base, eq, ← List.replicate_succ] at vs
    exact vs
  · intro j hj
    rw [base, List.length_replicate] at vm
    exact (vm j (by omega)).trans (h.untouched j (by omega))

private theorem five_iterations (k : Nat) : iterationCost (fun _ => 5) k = 5 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterationCost, ih, Nat.mul_succ]

private theorem control_frame {a : Arena bits workCap n} {s t : State L}
    (c : Control a s)
    (f : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → r ≠ clk →
      reg t r = reg s r) : Control a t :=
  ⟨(congrArg Fin.val (f count (by decide +revert) (by decide +revert) (by decide +revert))).trans c.count_eq,
    (congrArg Fin.val (f registers.one (by decide +revert) (by decide +revert) (by decide +revert))).trans c.one,
    (congrArg Fin.val (f registers.zero (by decide +revert) (by decide +revert) (by decide +revert))).trans c.zero,
    (congrArg Fin.val (f registers.stackBase (by decide +revert) (by decide +revert) (by decide +revert))).trans c.stackBase_eq,
    (congrArg Fin.val (f tinBase (by decide +revert) (by decide +revert) (by decide +revert))).trans c.tin_eq,
    (congrArg Fin.val (f toutBase (by decide +revert) (by decide +revert) (by decide +revert))).trans c.tout_eq,
    (congrArg Fin.val (f offsetBase (by decide +revert) (by decide +revert) (by decide +revert))).trans c.offset_eq,
    (congrArg Fin.val (f childrenBase (by decide +revert) (by decide +revert) (by decide +revert))).trans c.child_eq⟩

/-- The seed instructions write the two timestamp columns and initial
stack. Existing CSR cells remain unchanged. -/
theorem seed_steps (input : Input L) {a : Arena bits workCap n}
    {g : ChildLists n} {root : Fin n} {s : State L} (ready : SeedInput a g root s) :
    ∃ t, Steps (seedCode hi hw) input (10 * n + 6) s t ∧ t.pc = 10 ∧
      AtGuard a g (PaperB.ForestLayout.initial root) {t with pc := 0} ∧
      (∀ j < a.base, t.data[j]? = s.data[j]?) := by
  have start : Clear a s 0 s := ⟨ready.pc, ready.empty, fun _ _ _ => rfl, trivial, fun _ _ => rfl⟩
  obtain ⟨v, clear, h⟩ := loop_steps (code := seedCode hi hw) (input := input)
    (2 * n) (fun _ => 5) (Clear a s) (fun _ hk => clear_step input ready hk) s start
  rw [five_iterations] at clear
  have rem := h.fixed registers.remain (show registers.remain ≠ registers.ptr by decide)
    (show registers.remain ≠ registers.tmp by decide)
  have compare : ltb (reg v registers.ptr) (reg v registers.remain) = false := by
    cases e : ltb (reg v registers.ptr) (reg v registers.remain) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp e
      rw [h.ptr, rem, ready.length_eq] at lt
      omega
  let b : State L := {v with pc := 5}
  have guardFetch : (seedCode hi hw)[v.pc]? = some (.branchLt registers.ptr registers.remain 1 5) := by
    rw [h.pc]; rfl
  have vb : step (seedCode hi hw) input v = some (.next b) := by
    simpa only [b, compare, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) guardFetch (by rw [compare]; exact (show 5 < 11 by decide))
  have pFetch : (seedCode hi hw)[b.pc]? = some (.add registers.ptr registers.zero registers.zero) := rfl
  obtain ⟨c, bc, cpc, cPtr, cRegs, cMem⟩ := step_add_at (input := input) pFetch (show 6 < 11 by decide)
  have cFetch : (seedCode hi hw)[c.pc]? = some (.add clk registers.zero registers.zero) := by
    rw [cpc]; rfl
  have continuation : c.pc + 1 < (seedCode hi hw).size := by rw [cpc]; exact (show 7 < 11 by decide)
  obtain ⟨d, cd, dpc, dClk, dRegs, dMem⟩ := step_add_at (input := input) cFetch continuation
  have dPos : d.pc = 7 := by rw [dpc, cpc]
  have zeroVal : (reg b registers.zero).val = 0 :=
    (congrArg Fin.val (h.fixed registers.zero (by decide +revert) (by decide +revert))).trans ready.regs.zero
  have zfit : (reg b registers.zero).val + (reg b registers.zero).val < 2 ^ bits := by
    rw [zeroVal]; exact Nat.two_pow_pos bits
  have dPtr : (reg d registers.ptr).val = ([] : List (Word bits)).length := by
    rw [dRegs registers.ptr (show registers.ptr ≠ clk by decide), cPtr,
      PaperB.WordOps.add_no_wrap _ _ zfit, zeroVal]
    rfl
  have dClock : (reg d clk).val = 0 := by
    rw [dClk, cRegs _ (show registers.zero ≠ registers.ptr by decide),
      PaperB.WordOps.add_no_wrap _ _ zfit, zeroVal]
  have carry (r : Fin 15) (notPtr : r ≠ registers.ptr)
      (notTmp : r ≠ registers.tmp) (notClk : r ≠ clk) :
      reg d r = reg s r :=
    (dRegs r notClk).trans ((cRegs r notPtr).trans (h.fixed r notPtr notTmp))
  have control := control_frame ready.regs carry
  have dData : d.data = v.data := dMem.trans cMem
  have rootWord : reg d cmd = commandWord a.tags (.enter root) :=
    (carry cmd (by decide +revert) (by decide +revert) (by decide +revert)).trans ready.root_eq
  have place : Placed (seedCode hi hw) 7 (seedRoot (bits := bits)) := by
    intro k op hk
    cases k with
    | zero => exact hk
    | succ k =>
      cases k with
      | zero => exact hk
      | succ k =>
        cases k with
        | zero => exact hk
        | succ k =>
          change ([] : List (Instr bits 15))[k]? = some op at hk
          simp at hk
  have room := a.room
  have width := a.wordFits
  have nonempty := root.isLt
  have bound : (reg d registers.stackBase).val + ([] : List (Word bits)).length < (layout bits inputCap workCap hi hw).workCap := by
    change (reg d registers.stackBase).val + 0 < workCap
    rw [control.stackBase_eq]; omega
  obtain ⟨t, dt, tpc, tPtr, stack, tRegs, tMem⟩ := push_steps (input := input) place dPos
    (show 10 < 11 by decide) dPtr control.one bound (by simp only [List.length_nil, Nat.zero_add]; omega)
    (show cmd ≠ registers.tmp by decide) (show registers.ptr ≠ registers.tmp by decide)
    (show registers.one ≠ registers.tmp by decide) trivial
  have after := control_frame control (fun r p q _ => tRegs r p q)
  have outside (j : Nat) (neq : j ≠ a.base) : t.data[j]? = v.data[j]? := by
    rw [dData] at tMem
    apply tMem
    simpa only [control.stackBase_eq, List.length_nil, Nat.add_zero] using neq
  have cleared := stack_repeat_iff.mp h.cleared
  have zeros (i : Nat) (hi : i < 2 * n) :
      t.data[a.tin + i]? = some (reg s registers.zero) := by
    rw [outside]
    · exact cleared i hi
    · have hn := root.isLt
      unfold Arena.tin
      omega
  have kept (vtx : Fin n) : (t.data[a.offsets + vtx.val]?) = s.data[a.offsets + vtx.val]? := by
    have bound : a.tin + 2 * n ≤ a.offsets + vtx.val := by
      unfold Arena.tin Arena.offsets; omega
    rw [outside _ (by unfold Arena.offsets; omega), h.untouched _ (Or.inr bound)]
  have whole :=  (((clear.append (.cons vb (.cons bc (.cons cd (.zero _))))).append dt))
  have steps : Steps (seedCode hi hw) input (10 * n + 6) s t := by
    have cost : 5 * (2 * n) + (1 + (1 + (1 + 0))) + 3 = 10 * n + 6 := by omega
    rw [← cost]
    exact whole
  have resetControl : Control a {t with pc := 0} :=
    ⟨after.count_eq, after.one, after.zero, after.stackBase_eq, after.tin_eq, after.tout_eq,
      after.offset_eq, after.child_eq⟩
  refine ⟨t, steps, tpc, ⟨rfl, resetControl, tPtr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (reg t clk).val = 0
    rw [tRegs clk (show clk ≠ registers.ptr by decide) (show clk ≠ registers.tmp by decide), dClock]
  · rw [control.stackBase_eq, rootWord] at stack
    exact stack
  · intro i
    obtain ⟨lo, stop, lread, rread, hlen, hm, rdata⟩ := ready.rows i
    have keep (j : Nat) (hj : a.offsets ≤ j) : t.data[j]? = s.data[j]? := by
      have q : a.tin + 2 * n ≤ j := by unfold Arena.offsets Arena.tin at *; omega
      rw [outside _ (by unfold Arena.offsets at hj; omega), h.untouched _ (Or.inr q)]
    refine ⟨lo, stop, (kept i).trans lread, ?_, hlen, hm, ?_⟩
    · rw [keep _ (by omega)]; exact rread
    · intro j hj
      rw [keep _ (by unfold Arena.payload Arena.offsets; omega)]
      exact rdata j hj
  · intro i
    change (t.data[a.tin + i.val]?).map Fin.val = (Array.replicate n 0)[i.val]?
    rw [zeros _ (by have := i.isLt; omega), Option.map_some, ready.regs.zero]
    simp [i.isLt]
  · intro i
    change (t.data[a.tout + i.val]?).map Fin.val = (Array.replicate n 0)[i.val]?
    have addr : a.tout + i.val = a.tin + (n + i.val) := by
      unfold Arena.tin Arena.tout
      omega
    rw [addr, zeros _ (by have := i.isLt; omega), Option.map_some, ready.regs.zero]
    simp [i.isLt]
  · intro j hj
    rw [outside _ (by omega), h.untouched _ (Or.inl (by unfold Arena.tin; omega))]

/-- Fixed ROM linking the small seed program and the DFS. The seed's
terminal instruction becomes the jump to the DFS entry point. -/
def seededProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  FixedROM.join (seedCode hi hw) (program hi hw) 10 (show 10 < 11 by decide)

private theorem seed_halt_index {i : Nat}
    (h : (seedCode hi hw)[i]? = some .halt) : i = 10 := by
  have bound : i < 11 := by
    by_cases e : i < 11
    · exact e
    · have hn : (seedCode hi hw)[i]? = none := getElem?_neg _ _ e
      rw [hn] at h
      cases h
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases h

/-- One machine run initializes the stack and timestamps and computes the
two interval columns. Its trace includes initialization, linking, and the
final halt. All data stays in the original arena. -/
theorem run_seeded_tree (input : Input L) {a : Arena bits workCap n}
    {g : ChildLists n} {root : Fin n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (tree : ValidDepthTree root parent depth)
    (rows : g = PaperB.ForestLayout.bucketChildLists root parent)
    (mass : a.children ≤ n) (s : State L) (ready : SeedInput a g root s) :
    let final := PaperB.ForestLayout.layout g root (2 * n)
    ∃ (u : State L) (trace : List (State L)) (work : Nat),
      ColumnAt (n := n) a.tin final.entries u.data ∧
      ColumnAt (n := n) a.tout final.ends u.data ∧ work ≤ 50 * n + 9 ∧
      run (seededProgram hi hw) input work s = some ⟨u, work⟩ ∧
      SuccessfulTrace (seededProgram hi hw) input s trace ⟨u, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      Control a u ∧ (reg u registers.ptr).val = 0 ∧ u.pc = 42 ∧
      (∀ j < a.base, u.data[j]? = s.data[j]?) := by
  let rom := seededProgram hi hw
  have haltSlot : 10 < (seedCode hi hw).size := show 10 < 11 by decide
  obtain ⟨seeded, seed, pc, guard, seedFrame⟩ := seed_steps input ready
  have seedHalt : step (seedCode hi hw) input seeded = some (.halted seeded) :=
    step_halt_at (by rw [pc]; rfl)
  have prefixTrace : Steps rom input (10 * n + 7) s {seeded with pc := 11} := by
    have start : relocateStatePC 0 s = s := by cases s; simp [relocateStatePC]
    rw [← start]
    apply linked_return_of_trace_multi (base := 0) (ret := fun _ => 11)
      (n := 10 * n + 6) _ _ seed seedHalt
    · intro i op h nonhalt
      have neq : i ≠ 10 := by
        intro eq
        subst i
        have halt : (seedCode hi hw)[10]? = some .halt := rfl
        exact nonhalt (Option.some.inj (h.symm.trans halt))
      have fetch := FixedROM.fetch_left (seedCode hi hw) (program hi hw) haltSlot neq h
      have same : relocateInstr 0 op = op := by cases op <;> simp [relocateInstr]
      simpa only [rom, seededProgram, Nat.zero_add, same] using fetch
    · intro i h
      have eq := seed_halt_index h
      subst i
      have fetch := FixedROM.fetch_halt (seedCode hi hw) (program hi hw) haltSlot
      exact ⟨fetch.1, fetch.2 (by rw [program_size]; decide)⟩
  let atEntry : State L := {seeded with pc := 0}
  obtain ⟨u, _, work, final, bound, hr, _, _, dfsFrame⟩ :=
    run_prepared_tree input tree rows mass atEntry guard
  obtain ⟨k, h, dfs, halt, counts⟩ := run_has_steps_then_halt hr
  let placed : RelocatedSlice (program hi hw) rom 11 :=
    FixedROM.relocated_right (seedCode hi hw) (program hi hw) haltSlot
  have execute := prefixTrace.append (dfs.relocate placed)
  obtain ⟨fetch, stopped⟩ := halted_fetch_and_state halt
  have stop : step rom input (relocateStatePC 11 h) =
      some (.halted (relocateStatePC 11 ({u with pc := 31} : State L))) := by
    have whereHalt := placed h.pc .halt fetch
    have hstep := step_halt_at (input := input) (s := relocateStatePC 11 h) whereHalt
    change ({u with pc := 31} : State L) = h at stopped
    rw [stopped]
    exact hstep
  have total := execute.halts stop
  obtain ⟨trace, success⟩ := run_has_successfulTrace total
  change work = k + 1 at counts
  refine ⟨relocateStatePC 11 {u with pc := 31}, trace, (10 * n + 7) + k + 1, final.entries, final.ends,
    ?_, total, success, success.peak_eq, ?_, ?_, rfl, ?_⟩
  · omega
  · exact ⟨final.regs.count_eq, final.regs.one, final.regs.zero, final.regs.stackBase_eq,
      final.regs.tin_eq, final.regs.tout_eq, final.regs.offset_eq, final.regs.child_eq⟩
  · change (reg u registers.ptr).val = 0
    have done : (PaperB.ForestLayout.layout g root (2 * n)).stack = [] := by
      rw [rows]
      exact (PaperB.ForestLayout.layout_bucketChildren_exact tree).1
    rw [final.ptr, done]
    rfl
  · intro j hj
    exact (dfsFrame j hj).trans (seedFrame j hj)

end PaperB.RamForestProgram.Finish
