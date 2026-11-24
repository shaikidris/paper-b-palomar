module

public import PaperB.RamForestParentFinish

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.ArcParents

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.WordOps (ltb)
open PaperB.RamForestProgram.Finish
open PaperB.LabelledQuotient (ValidDepthTree)

variable {vertices arcs : Nat}
local notation "K" => (vertices + 1 + arcs)

/-- Include a dummy root, then one node per quotient head and one node
per input arc occurrence. Distinct parallel arcs remain distinct. -/
def root (vertices arcs : Nat) : Fin (vertices + 1 + arcs) :=
  ⟨0, Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self vertices) (Nat.le_add_right _ _))⟩

def headNode (arcs : Nat) (v : Fin vertices) : Fin (vertices + 1 + arcs) :=
  ⟨v.val + 1, by have := v.isLt; omega⟩

def arcNode (vertices : Nat) (e : Fin arcs) : Fin (vertices + 1 + arcs) :=
  ⟨vertices + 1 + e.val, by have := e.isLt; omega⟩

def parent (heads : Fin arcs → Fin vertices) (u : Fin K) : Fin K :=
  if inside : vertices + 1 ≤ u.val then
    headNode arcs (heads ⟨u.val - (vertices + 1), by have := u.isLt; omega⟩)
  else root vertices arcs

def depth (u : Fin K) : Nat :=
  if u.val = 0 then 0 else if u.val ≤ vertices then 1 else 2

@[simp] theorem parent_headNode (heads : Fin arcs → Fin vertices) (v : Fin vertices) :
    parent heads (headNode arcs v) = root vertices arcs := by
  unfold parent
  rw [dite_eq_right (fun h => by have := v.isLt; change vertices + 1 ≤ v.val + 1 at h; omega)]

@[simp] theorem parent_arcNode (heads : Fin arcs → Fin vertices) (e : Fin arcs) :
    parent heads (arcNode vertices e) = headNode arcs (heads e) := by
  unfold parent
  have wide : vertices + 1 ≤ (arcNode vertices e).val := by
    change vertices + 1 ≤ vertices + 1 + e.val
    omega
  rw [dite_eq_left wide]
  congr 2
  apply Fin.ext
  change vertices + 1 + e.val - (vertices + 1) = e.val
  omega

/-- The two-level auxiliary tree is independent of acyclicity of the
input quotient. Its ordinary rows are exactly incoming arc buckets. -/
theorem parent_tree (heads : Fin arcs → Fin vertices) :
    ValidDepthTree (root vertices arcs) (parent heads) (depth (vertices := vertices) (arcs := arcs)) := by
  refine ⟨?_, rfl, ?_⟩
  · unfold parent
    exact dite_eq_right (by change ¬ vertices + 1 ≤ 0; omega)
  · intro u notRoot
    have positive : u.val ≠ 0 := fun h => notRoot (Fin.ext h)
    by_cases small : u.val ≤ vertices
    · unfold parent
      rw [dite_eq_right (by omega)]
      have z : depth (root vertices arcs) = 0 := rfl
      rw [z]
      simp [depth, positive, small]
    · have large : vertices + 1 ≤ u.val := by omega
      unfold parent
      rw [dite_eq_left large]
      have dep (v : Fin vertices) : depth (headNode arcs v) = 1 := by
        have lt := v.isLt
        unfold depth
        change (if v.val + 1 = 0 then 0 else if v.val + 1 ≤ vertices then 1 else 2) = 1
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rw [dep]
      simp [depth, positive, small]

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- The input head column holds the original identifiers. The program
adds one only when forming the temporary head-node parent. -/
def HeadsAt (input : Input L) (base : Nat) (heads : Fin arcs → Fin vertices) : Prop :=
  ∀ e : Fin arcs, (input.words[base + e.val]?).map Fin.val = some (heads e).val

private def readHead : List (Instr bits 15) :=
  indexedInputRead registers.value registers.childBase registers.remain

private def writeParent : List (Instr bits 15) :=
  indexedDataWrite registers.tmp registers.stackBase registers.ptr registers.value

def code (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let branch : List (Instr bits 15) :=
    [.branchLt registers.ptr count 1 12, .branchLt registers.ptr clk 2 4,
      .add registers.value registers.zero registers.zero, .goto 8,
      .sub registers.remain registers.ptr clk]
  let tail : List (Instr bits 15) :=
    [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]
  let bump : Instr bits 15 := .add registers.value registers.value registers.one
  (branch ++ (readHead ++ [bump] ++ writeParent ++ tail)).toArray

private theorem readPlaced : Placed (code hi hw) 5 (readHead (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [readHead, indexedInputRead] at h

private theorem storePlaced : Placed (code hi hw) 8 (writeParent (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [writeParent, indexedDataWrite] at h

private structure AtLoop (a : Arena bits workCap K) (heads : Fin arcs → Fin vertices)
    (headAddr : Nat) (orig : Array (Word bits)) (i : Nat) (s : State L) : Prop where
  pc : s.pc = 0
  cursor : ParentCursor a (root vertices arcs) i s
  split : (reg s clk).val = vertices + 1
  headBase : (reg s registers.childBase).val = headAddr
  written : ∀ u : Fin K, u.val < i →
    (s.data[a.base + u.val]?).map Fin.val = some (parent heads u).val
  frame : ∀ j, (j < a.base ∨ a.base + K ≤ j) → s.data[j]? = orig[j]?

private theorem cursorKeep {a : Arena bits workCap K} {i : Nat} {s t : State L}
    (r : Fin 15) (temporary : r ∈ parentScratch)
    (h : ParentCursor a (root vertices arcs) i s)
    (preserve : ∀ q : Fin 15, q ≠ r → reg t q = reg s q) :
    ParentCursor a (root vertices arcs) i t :=
  h.unchanged (fun q hq => preserve q (fun e => hq (e ▸ temporary)))

private def cost (vertices i : Nat) : Nat := if i < vertices + 1 then 8 else 10

private theorem stage_value (input : Input L) {a : Arena bits workCap K}
    {heads : Fin arcs → Fin vertices} {headAddr : Nat}
    (room : headAddr + arcs ≤ inputCap) (inputHeads : HeadsAt input headAddr heads)
    (u : Fin K) (s : State L) (pc : s.pc = 1)
    (cur : ParentCursor a (root vertices arcs) u.val s)
    (split : (reg s clk).val = vertices + 1) (headBase : (reg s registers.childBase).val = headAddr) :
    ∃ t, Steps (code hi hw) input (if u.val < vertices + 1 then 3 else 5) s t ∧
      t.pc = 8 ∧ (reg t registers.value).val = (parent heads u).val ∧ t.data = s.data ∧
      (∀ q : Fin 15, q ≠ registers.remain → q ≠ registers.value → reg t q = reg s q) := by
  have tested : (code hi hw)[s.pc]? = some (.branchLt registers.ptr clk 2 4) := by rw [pc]; rfl
  have wide := a.wordFits
  by_cases old : u.val < vertices + 1
  · rw [ite_eq_left old]
    have yes : ltb (reg s registers.ptr) (reg s clk) = true :=
      (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [cur.ptrVal, split]; exact old)
    let v : State L := {s with pc := 2}
    have sv : step (code hi hw) input s = some (.next v) := by
      simpa only [v, yes, ite_true] using
        step_branchLt_at (input := input) tested (by rw [yes]; exact (show 2 < 13 by decide))
    have at2 : (code hi hw)[v.pc]? = some (.add registers.value registers.zero registers.zero) := rfl
    obtain ⟨w, vw, wpc, wval, wr, wm⟩ := step_add_at (input := input) at2 (show 3 < 13 by decide)
    have last : (code hi hw)[w.pc]? = some (.goto 8) := by rw [wpc]; rfl
    let t : State L := {w with pc := 8}
    have wt : step (code hi hw) input w = some (.next t) := step_goto_at last (show 8 < 13 by decide)
    have z : (reg v registers.zero).val = 0 := cur.ctrl.zero
    have fits : (reg v registers.zero).val + (reg v registers.zero).val < 2 ^ bits := by
      rw [z]; exact Nat.two_pow_pos bits
    refine ⟨t, .cons sv (.cons vw (.cons wt (.zero t))), rfl, ?_, wm, fun q _ hq => wr q hq⟩
    change (reg w registers.value).val = (parent heads u).val
    rw [wval, PaperB.WordOps.add_no_wrap _ _ fits, z]
    have p : parent heads u = root vertices arcs := dite_eq_right (by omega)
    rw [p]
    rfl
  · rw [ite_eq_right old]
    have cmp : ltb (reg s registers.ptr) (reg s clk) = false := by
      cases h : ltb (reg s registers.ptr) (reg s clk) with
      | false => rfl
      | true =>
        have lt := (PaperB.WordOps.ltb_eq_true _ _).mp h
        rw [cur.ptrVal, split] at lt
        exact (old lt).elim
    let v : State L := {s with pc := 4}
    have sv : step (code hi hw) input s = some (.next v) := by
      simpa only [v, cmp, Bool.false_eq_true, ite_false] using
        step_branchLt_at (input := input) tested (by rw [cmp]; exact (show 4 < 13 by decide))
    have at4 : (code hi hw)[v.pc]? = some (.sub registers.remain registers.ptr clk) := rfl
    obtain ⟨w, vw, wpc, wval, wr, wm⟩ := step_sub_at (input := input) at4 (show 5 < 13 by decide)
    have ul := u.isLt
    let e : Fin arcs := ⟨u.val - (vertices + 1), by omega⟩
    have address : (reg w registers.remain).val = e.val := by
      rw [wval, PaperB.WordOps.sub_val]
      change (2 ^ bits + (reg s registers.ptr).val - (reg s clk).val) % (2 ^ bits) = e.val
      rw [cur.ptrVal, split]
      change (2 ^ bits + u.val - (vertices + 1)) % (2 ^ bits) = u.val - (vertices + 1)
      rw [show 2 ^ bits + u.val - (vertices + 1) =
        2 ^ bits + (u.val - (vertices + 1)) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have wBase : (reg w registers.childBase).val = headAddr :=
      (congrArg Fin.val (wr _ (show registers.childBase ≠ registers.remain by decide))).trans headBase
    have eLt := e.isLt
    have readFits : (reg w registers.childBase).val + (reg w registers.remain).val < inputCap := by
      rw [wBase, address]; omega
    obtain ⟨x, wx, xpc, got, xr, xm⟩ := indexedInputRead_steps (input := input)
      readPlaced wpc (show 7 < 13 by decide) readFits
    have raw : (reg x registers.value).val = (heads e).val := by
      rw [wBase, address] at got
      have h := congrArg (Option.map Fin.val) got
      rw [inputHeads e] at h
      exact Option.some.inj h
    have unit : (reg x registers.one).val = 1 :=
      (congrArg Fin.val ((xr _ (show registers.one ≠ registers.value by decide)).trans
        (wr _ (show registers.one ≠ registers.remain by decide)))).trans cur.ctrl.one
    have headerFit : (reg x registers.value).val + (reg x registers.one).val < 2 ^ bits := by
      have := (heads e).isLt
      rw [raw, unit]; omega
    have at7 : (code hi hw)[x.pc]? = some (.add registers.value registers.value registers.one) := by
      rw [xpc]; rfl
    obtain ⟨t, xt, tpc, tVal, tr, tm⟩ := step_add_at (input := input) at7
      (by rw [xpc]; exact (show 8 < 13 by decide))
    refine ⟨t, (Steps.cons sv (.cons vw (.zero _))).append (wx.append (.cons xt (.zero _))),
      by rw [tpc, xpc], ?_, tm.trans (xm.trans wm),
      fun q h0 h1 => (tr q h1).trans ((xr q h1).trans (wr q h0))⟩
    rw [tVal, PaperB.WordOps.add_no_wrap _ _ headerFit, raw, unit]
    unfold parent
    rw [dite_eq_left (by omega)]
    rfl

private theorem iteration (input : Input L) {a : Arena bits workCap K}
    {heads : Fin arcs → Fin vertices} {headAddr : Nat} {orig : Array (Word bits)}
    (room : headAddr + arcs ≤ inputCap) (inputHeads : HeadsAt input headAddr heads)
    (i : Nat) (below : i < K) :
    BlockSpec (code hi hw) input (cost vertices i) (AtLoop a heads headAddr orig i)
      (AtLoop a heads headAddr orig (i + 1)) := by
  intro s h
  let u : Fin K := ⟨i, below⟩
  let x : State L := {s with pc := 1}
  have cmp : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr
      (by rw [h.cursor.ptrVal, h.cursor.ctrl.count_eq]; exact below)
  have guard : (code hi hw)[s.pc]? = some (.branchLt registers.ptr count 1 12) := by
    rw [h.pc]; rfl
  have sx : step (code hi hw) input s = some (.next x) := by
    simpa only [x, cmp, ite_true] using
      step_branchLt_at (input := input) guard (by rw [cmp]; exact (show 1 < 13 by decide))
  obtain ⟨y, xy, ypc, yWord, ym, yr⟩ :=
    stage_value input room inputHeads u x rfl (h.cursor.unchanged (fun _ _ => rfl)) h.split h.headBase
  have cy : ParentCursor a (root vertices arcs) i y :=
    h.cursor.unchanged (fun q keep => yr q
      (fun e => keep (e ▸ (show registers.remain ∈ parentScratch by decide)))
      (fun e => keep (e ▸ (show registers.value ∈ parentScratch by decide))))
  have storage := a.room
  have width := a.wordFits
  have storeFits : (reg y registers.stackBase).val + (reg y registers.ptr).val < workCap := by
    rw [cy.ctrl.stackBase_eq, cy.ptrVal]; omega
  obtain ⟨z, yz, zpc, zStore, _, zr⟩ := indexedDataWrite_steps (input := input)
    (s := y) storePlaced ypc (show 10 < 13 by decide)
    (show registers.value ≠ registers.tmp by decide) storeFits
  have cz := cursorKeep registers.tmp (by decide +revert) cy zr
  have incFetch : (code hi hw)[z.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [zpc]; rfl
  obtain ⟨v, zv, vpc, vPtr, vr, vm⟩ := step_add_at (input := input) incFetch
    (by rw [zpc]; exact (show 11 < 13 by decide))
  have last : (code hi hw)[v.pc]? = some (.goto 0) := by rw [vpc, zpc]; rfl
  let t : State L := {v with pc := 0}
  have vt : step (code hi hw) input v = some (.next t) := step_goto_at last (show 0 < 13 by decide)
  have nextFit : (reg z registers.ptr).val + (reg z registers.one).val < 2 ^ bits := by
    rw [cz.ptrVal, cz.ctrl.one]; omega
  have next : (reg t registers.ptr).val = i + 1 := by
    change (reg v registers.ptr).val = _
    rw [vPtr, PaperB.WordOps.add_no_wrap _ _ nextFit, cz.ptrVal, cz.ctrl.one]
  have rframe (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp)
      (hv : r ≠ registers.value) (hr : r ≠ registers.remain) : reg t r = reg s r :=
    (vr r hp).trans ((zr r ht).trans (yr r hr hv))
  have moved (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp)
      (hv : r ≠ registers.value) (hr : r ≠ registers.remain) : (reg t r).val = (reg s r).val :=
    congrArg Fin.val (rframe r hp ht hv hr)
  have ctrl : Control a t :=
    ⟨(moved count (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.count_eq,
      (moved registers.one (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.one,
      (moved registers.zero (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.zero,
      (moved registers.stackBase (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.stackBase_eq,
      (moved tinBase (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.tin_eq,
      (moved toutBase (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.tout_eq,
      (moved offsetBase (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.offset_eq,
      (moved childrenBase (by decide) (by decide) (by decide) (by decide)).trans h.cursor.ctrl.child_eq⟩
  have tc : ParentCursor a (root vertices arcs) (i + 1) t :=
    ⟨ctrl, (moved cmd (by decide) (by decide) (by decide) (by decide)).trans h.cursor.rootVal, next⟩
  have programRun := (Steps.cons sx xy).append (yz.append (.cons zv (.cons vt (.zero t))))
  have units : (if u.val < vertices + 1 then 3 else 5) + 1 + (2 + 2) = cost vertices i := by
    change (if i < vertices + 1 then 3 else 5) + 1 + (2 + 2) = _
    unfold cost
    split <;> rfl
  have memory : t.data = s.data.set (a.base + i) (reg y registers.value)
      (by rw [s.data_size]; change a.base + i < workCap; omega) := by
    change v.data = _
    rw [vm]
    simpa only [ym, cy.ctrl.stackBase_eq, cy.ptrVal] using zStore
  have keep (j : Nat) (ne : j ≠ a.base + i) : t.data[j]? = s.data[j]? := by
    rw [memory]
    exact Array.getElem?_set_ne _ ne.symm
  refine ⟨t, units ▸ programRun, ⟨rfl, tc,
    (moved clk (by decide) (by decide) (by decide) (by decide)).trans h.split,
    (moved registers.childBase (by decide) (by decide) (by decide) (by decide)).trans h.headBase,
    ?_, ?_⟩⟩
  · intro j hj
    by_cases e : j = u
    · subst j
      change (t.data[a.base + i]?).map Fin.val = _
      rw [memory, Array.getElem?_set_self, Option.map_some, yWord]
    · have ne : j.val ≠ i := fun eq => e (Fin.ext eq)
      rw [keep _ (by omega)]
      exact h.written _ (by omega)
  · intro j outside
    exact (keep j (by omega)).trans (h.frame j outside)

private theorem iteration_bound (vertices n : Nat) :
    iterationCost (cost vertices) n ≤ 10 * n := by
  induction n with
  | zero => simp [iterationCost]
  | succ n ih =>
    simp only [iterationCost, Nat.mul_succ]
    have once : cost vertices n ≤ 10 := by unfold cost; split <;> omega
    omega

/-- Pack the auxiliary parent column directly from the input head words.
In particular the root and the head-node parents are written by the
machine, so it assumes no initialized work cells. -/
theorem run_arc_parents (input : Input L) {a : Arena bits workCap K}
    (heads : Fin arcs → Fin vertices) (headAddr : Nat)
    (room : headAddr + arcs ≤ inputCap)
    (inputHeads : HeadsAt input headAddr heads) (s : State L)
    (pc : s.pc = 0) (cursor : ParentCursor a (root vertices arcs) 0 s)
    (split : (reg s clk).val = vertices + 1)
    (src : (reg s registers.childBase).val = headAddr) :
    ∃ t trace work, work ≤ 10 * K + 2 ∧
      run (code hi hw) input work s = some ⟨t, work⟩ ∧
      ParentCursor a (root vertices arcs) K t ∧ ParentAt a (parent heads) t.data ∧
      (∀ j, (j < a.base ∨ a.base + K ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (code hi hw) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : AtLoop a heads headAddr s.data 0 s :=
    ⟨pc, cursor, split, src, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  obtain ⟨v, steps, inv⟩ := loop_steps (code := code hi hw) (input := input)
    K (cost vertices) (AtLoop a heads headAddr s.data)
    (iteration input room inputHeads) s start
  have no : ltb (reg v registers.ptr) (reg v count) = false := by
    cases h : ltb (reg v registers.ptr) (reg v count) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp h
      rw [inv.cursor.ptrVal, inv.cursor.ctrl.count_eq] at lt
      omega
  let t : State L := {v with pc := 12}
  have fetch : (code hi hw)[v.pc]? = some (.branchLt registers.ptr count 1 12) := by
    rw [inv.pc]; rfl
  have vt : step (code hi hw) input v = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) fetch (by rw [no]; exact (show 12 < 13 by decide))
  have exec := (steps.append (.cons vt (.zero _))).halts (step_halt_at rfl)
  obtain ⟨states, runTrace⟩ := run_has_successfulTrace exec
  have b := iteration_bound vertices K
  exact ⟨t, states, _, by omega, exec, inv.cursor.unchanged (fun _ _ => rfl),
    fun u => inv.written u u.isLt, inv.frame, runTrace, runTrace.peak_eq⟩

end PaperB.RamForestProgram.ArcParents
