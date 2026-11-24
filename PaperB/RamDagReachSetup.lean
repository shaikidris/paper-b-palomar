module

public import PaperB.OraclePackedWidth
public import PaperB.DecreasingDAG
public import PaperB.Kahn
public import PaperB.RamForestPhaseLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamDagReach

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph

/-! ### Layout, raw DAG CSR input encoding, and disjoint work-memory banks -/

/-- Linear mutable work-memory capacity for all 4 phases of `RamDagReachKahn`:
- `[0 .. n)`: `inDeg`
- `[n .. 2n)`: `topoOrder`
- `[2n .. 3n)`: `marked`
- `[3n .. 4n)`: `origToDensePlusOne`
- `[4n .. 5n)`: `denseToOrig`
- `[5n .. 6n)`: `denseInDeg`
- `[6n .. 7n+1)`: `inStart`
- `[7n+1 .. 7n+1+m)`: `inSrc`
Plus 2 guard words so every computed address is strictly `< 2 ^ bits`. -/
def rawDagWorkCap (n m : Nat) : Nat := 7 * n + m + 3

theorem rawDagWorkCap_le (n m : Nat) : rawDagWorkCap n m ≤ 7 * (n + m + 1) := by
  unfold rawDagWorkCap
  omega

theorem dagWordBits_fit (slack n m : Nat) (hSlack : 3 ≤ slack) :
    let bits := OracleContract.wordBits slack n m
    rawDagInputCap n m ≤ 2 ^ bits ∧ rawDagWorkCap n m ≤ 2 ^ bits := by
  intro bits
  have hpow : 7 ≤ 2 ^ slack := by
    have : 2 ^ 3 ≤ 2 ^ slack := Nat.pow_le_pow_right (by decide) hSlack
    omega
  have hIn : rawDagInputCap n m < 2 ^ bits :=
    OracleContract.linear_payload_fits slack n m 4 (rawDagInputCap n m)
      (by omega) (rawDagInputCap_le n m)
  have hWork : rawDagWorkCap n m < 2 ^ bits :=
    OracleContract.linear_payload_fits slack n m 7 (rawDagWorkCap n m)
      hpow (rawDagWorkCap_le n m)
  exact ⟨Nat.le_of_lt hIn, Nat.le_of_lt hWork⟩

def inDegBase (n m : Nat) : Nat := 0 * n + 0 * m
def topoOrderBase (n m : Nat) : Nat := n + 0 * m
def markedBase (n m : Nat) : Nat := 2 * n + 0 * m
def origToDensePlusOneBase (n m : Nat) : Nat := 3 * n + 0 * m
def denseToOrigBase (n m : Nat) : Nat := 4 * n + 0 * m
def denseInDegBase (n m : Nat) : Nat := 5 * n + 0 * m
def inStartBase (n m : Nat) : Nat := 6 * n + 0 * m
def inSrcBase (n m : Nat) : Nat := 7 * n + 1 + 0 * m

@[simp] theorem inDegBase_eq (n m : Nat) : inDegBase n m = 0 := by
  simp [inDegBase]

@[simp] theorem topoOrderBase_eq (n m : Nat) : topoOrderBase n m = n := by
  simp [topoOrderBase]

@[simp] theorem markedBase_eq (n m : Nat) : markedBase n m = 2 * n := by
  simp [markedBase]

@[simp] theorem origToDensePlusOneBase_eq (n m : Nat) : origToDensePlusOneBase n m = 3 * n := by
  simp [origToDensePlusOneBase]

@[simp] theorem denseToOrigBase_eq (n m : Nat) : denseToOrigBase n m = 4 * n := by
  simp [denseToOrigBase]

@[simp] theorem denseInDegBase_eq (n m : Nat) : denseInDegBase n m = 5 * n := by
  simp [denseInDegBase]

@[simp] theorem inStartBase_eq (n m : Nat) : inStartBase n m = 6 * n := by
  simp [inStartBase]

@[simp] theorem inSrcBase_eq (n m : Nat) : inSrcBase n m = 7 * n + 1 := by
  simp [inSrcBase]

theorem outPrefix_succ_lt (g : Digraph) (u : Fin g.vertexCount) :
    outPrefix g (u.val + 1) = outPrefix g u.val + (g.outArcs u).length := by
  simp only [outPrefix, dite_eq_left u.isLt, Fin.eta]

theorem outPrefix_mono (g : Digraph) {i j : Nat} (h : i ≤ j) :
    outPrefix g i ≤ outPrefix g j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    rw [hi]
    exact Nat.le_refl 0
  | succ j ih =>
    by_cases hij : i = j + 1
    · rw [hij]
      exact Nat.le_refl _
    · have hprev := ih (by omega)
      simp only [outPrefix]
      omega

private theorem outPrefix_take_eq (g : Digraph) :
    ∀ u : Nat, u ≤ g.vertexCount →
      outPrefix g u = ((g.adj.toList.take u).map List.length).sum := by
  intro u
  induction u with
  | zero => intro _; simp [outPrefix]
  | succ u ih =>
    intro hu
    have huLt : u < g.vertexCount := by omega
    have hlen : u < g.adj.toList.length := by simpa [g.adj_size] using huLt
    have htake : g.adj.toList.take (u + 1) =
        g.adj.toList.take u ++ [g.adj.toList[u]'hlen] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlen]; rfl
    rw [htake, List.map_append, List.sum_append, ← ih (by omega)]
    simp only [outPrefix, dite_eq_left huLt, List.map_singleton, List.sum_singleton]
    congr 1

theorem outPrefix_vertexCount (g : Digraph) :
    outPrefix g g.vertexCount = g.arcCount := by
  rw [outPrefix_take_eq g g.vertexCount (Nat.le_refl _)]
  have hlen : g.adj.toList.length ≤ g.vertexCount := by simp [g.adj_size]
  rw [List.take_of_length_le hlen]
  unfold Digraph.arcCount
  exact (listLengthSum_eq_sum_lengths g.adj.toList).symm

private theorem flatten_take_length {α : Type} (xss : List (List α)) (u : Nat) :
    (xss.take u).flatten.length = ((xss.take u).map List.length).sum := by
  rw [List.length_flatten]

private theorem list_split_at {α : Type} (xs : List α) (u : Nat) (hu : u < xs.length) :
    xs = xs.take u ++ xs[u]'hu :: xs.drop (u + 1) := by
  induction u generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hu
    | cons x xs => rfl
  | succ u ih =>
    cases xs with
    | nil => simp at hu
    | cons x xs =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
        List.cons_append]
      exact congrArg (List.cons x) (ih xs (Nat.lt_of_succ_lt_succ hu))

private theorem flatten_getElem_of_take {α : Type} (xss : List (List α))
    (u : Nat) (hu : u < xss.length) (j : Nat) (hj : j < (xss[u]'hu).length) :
    (xss.flatten)[((xss.take u).map List.length).sum + j]? =
      some ((xss[u]'hu)[j]'hj) := by
  have hsplit : xss = xss.take u ++ xss[u]'hu :: xss.drop (u + 1) :=
    list_split_at xss u hu
  have hflat : xss.flatten =
      (xss.take u).flatten ++ (xss[u]'hu ++ (xss.drop (u + 1)).flatten) := by
    conv => lhs; rw [hsplit]
    rw [List.flatten_append, List.flatten_cons]
  have hpref : (xss.take u).flatten.length = ((xss.take u).map List.length).sum :=
    flatten_take_length xss u
  rw [hflat, List.getElem?_append_right (by rw [hpref]; omega), hpref,
    Nat.add_sub_cancel_left, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

private theorem toArray_getElem? {α : Type} (xs : List α) (i : Nat) :
    xs.toArray[i]? = xs[i]? := by
  by_cases h : i < xs.length <;> simp [h]

/-- Raw outgoing-CSR DAG input contract in immutable RAM `input.words`. -/
structure RawDagInput {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    (g : Digraph) (r : Fin g.vertexCount) : Prop where
  cap_ge : rawDagInputCap g.vertexCount g.arcCount ≤ inputCap
  hdr_n : (input.words[0]?).map Fin.val = some g.vertexCount
  hdr_m : (input.words[1]?).map Fin.val = some g.arcCount
  hdr_r : (input.words[2]?).map Fin.val = some r.val
  out_off : ∀ u : Nat, u ≤ g.vertexCount →
    (input.words[3 + u]?).map Fin.val = some (outPrefix g u)
  out_targets : ∀ (u : Fin g.vertexCount) (j : Nat) (hj : j < (g.outArcs u).length),
    (input.words[4 + g.vertexCount + outPrefix g u.val + j]?).map Fin.val =
      some ((g.outArcs u)[j]'hj).val

private def wordOfNat (bits x : Nat) (hx : x < 2 ^ bits) : Word bits :=
  ⟨x, hx⟩

private theorem finOfNat_val {bits x : Nat} (hx : x < 2 ^ bits) :
    (Fin.ofNat (2 ^ bits) x).val = x := by
  change x % 2 ^ bits = x
  exact Nat.mod_eq_of_lt hx

theorem rawInputOfDigraph_valid {bits workCap : Nat} (g : Digraph) (r : Fin g.vertexCount)
    (hi : rawDagInputCap g.vertexCount g.arcCount ≤ 2 ^ bits)
    (hw : workCap ≤ 2 ^ bits) :
    RawDagInput (rawInputOfDigraph g r hi hw) g r := by
  let n := g.vertexCount
  let m := g.arcCount
  have hnLt : n < 2 ^ bits := by unfold rawDagInputCap at hi; omega
  have hmLt : m < 2 ^ bits := by unfold rawDagInputCap at hi; omega
  have hrLt : r.val < 2 ^ bits := Nat.lt_trans r.isLt hnLt
  refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · change ((rawInputWords bits g r)[0]?).map Fin.val = some n
    rw [rawInputWords, Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_left (by simp)]
    simp; exact Nat.mod_eq_of_lt hnLt
  · change ((rawInputWords bits g r)[1]?).map Fin.val = some m
    rw [rawInputWords, Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_left (by simp)]
    simp; exact Nat.mod_eq_of_lt hmLt
  · change ((rawInputWords bits g r)[2]?).map Fin.val = some r.val
    rw [rawInputWords, Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_left (by simp)]
    simp; exact Nat.mod_eq_of_lt hrLt
  · intro u hu
    have hOffLt : outPrefix g u < 2 ^ bits := by
      have h1 := outPrefix_mono g hu
      rw [outPrefix_vertexCount] at h1
      omega
    change ((rawInputWords bits g r)[3 + u]?).map Fin.val = some (outPrefix g u)
    unfold rawInputWords
    rw [Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_right (by simp),
      show (3 : Nat) + u - #[Fin.ofNat (2 ^ bits) n, Fin.ofNat (2 ^ bits) m,
        Fin.ofNat (2 ^ bits) r.val].size = u by simp]
    simp [Nat.lt_succ_of_le hu]; exact Nat.mod_eq_of_lt hOffLt
  · intro u j hj
    have hTargetLt : ((g.outArcs u)[j]'hj).val < 2 ^ bits :=
      Nat.lt_trans ((g.outArcs u)[j]'hj).isLt hnLt
    change ((rawInputWords bits g r)[4 + n + outPrefix g u.val + j]?).map Fin.val =
      some ((g.outArcs u)[j]'hj).val
    unfold rawInputWords
    have hsz1 : (#[Fin.ofNat (2 ^ bits) n, Fin.ofNat (2 ^ bits) m,
        Fin.ofNat (2 ^ bits) r.val] ++
        Array.ofFn (fun k : Fin (n + 1) => Fin.ofNat (2 ^ bits) (outPrefix g k.val))).size =
        4 + n := by
      simp [Array.size_append]; omega
    rw [Array.getElem?_append_right (by rw [hsz1]; omega), hsz1,
      show 4 + n + outPrefix g u.val + j - (4 + n) = outPrefix g u.val + j by omega,
      Array.getElem?_map, toArray_getElem?]
    have huAdj : u.val < g.adj.toList.length := by simp [g.adj_size]
    have hflat := flatten_getElem_of_take g.adj.toList u.val huAdj j
      (by simpa [Digraph.outArcs] using hj)
    rw [← outPrefix_take_eq g u.val (Nat.le_of_lt u.isLt)] at hflat
    change ((outTargetsList g)[outPrefix g u.val + j]?) = some ((g.outArcs u)[j]'hj) at hflat
    rw [hflat, Option.map_some, Option.map_some]
    exact congrArg some (finOfNat_val hTargetLt)

theorem rawDagInput_out_targets_flat {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) :
    ∀ (e : Nat) (he : e < g.arcCount),
      (input.words[4 + g.vertexCount + e]?).map Fin.val =
        some ((outTargetsList g)[e]'(by rw [outTargetsList_length]; exact he)).val := by
  have find_slot : ∀ k : Nat, k ≤ g.vertexCount → ∀ e : Nat, e < outPrefix g k →
      ∃ (u : Fin g.vertexCount) (j : Nat) (hj : j < (g.outArcs u).length),
        u.val < k ∧ e = outPrefix g u.val + j := by
    intro k
    induction k with
    | zero => intro _ e he; simp [outPrefix] at he
    | succ k ih =>
      intro hk e he
      have hkLt : k < g.vertexCount := by omega
      simp only [outPrefix, dite_eq_left hkLt] at he
      by_cases hPrev : e < outPrefix g k
      · obtain ⟨u, j, hj, huk, heq⟩ := ih (by omega) e hPrev
        exact ⟨u, j, hj, by omega, heq⟩
      · refine ⟨⟨k, hkLt⟩, e - outPrefix g k, by omega, Nat.lt_succ_self k, ?_⟩
        change e = outPrefix g k + (e - outPrefix g k)
        omega
  intro e he
  have he' : e < outPrefix g g.vertexCount := by rwa [outPrefix_vertexCount]
  obtain ⟨u, j, hj, _, heq⟩ := find_slot g.vertexCount (Nat.le_refl _) e he'
  have huAdj : u.val < g.adj.toList.length := by simp [g.adj_size]
  have hflat := flatten_getElem_of_take g.adj.toList u.val huAdj j
    (by simpa [Digraph.outArcs] using hj)
  rw [← outPrefix_take_eq g u.val (Nat.le_of_lt u.isLt)] at hflat
  have hPos : (outTargetsList g)[outPrefix g u.val + j]? =
      some ((outTargetsList g)[e]'(by rw [outTargetsList_length]; exact he)) := by
    rw [← heq]
    exact List.getElem?_eq_getElem (by rw [outTargetsList_length]; exact he)
  have hEqVal : ((outTargetsList g)[e]'(by rw [outTargetsList_length]; exact he)) =
      (g.outArcs u)[j]'hj := by
    apply Option.some.inj
    exact hPos.symm.trans hflat
  rw [hEqVal, heq, ← Nat.add_assoc]
  exact raw.out_targets u j hj

/-! ### 16-register RAM helpers and generic bounded-while combinator -/

abbrev rZero : Fin 16 := 0
abbrev rOne  : Fin 16 := 1
abbrev rN    : Fin 16 := 2
abbrev rM    : Fin 16 := 3
abbrev rRoot : Fin 16 := 4
abbrev r5    : Fin 16 := 5
abbrev r6    : Fin 16 := 6
abbrev r7    : Fin 16 := 7
abbrev r8    : Fin 16 := 8
abbrev r9    : Fin 16 := 9
abbrev r10   : Fin 16 := 10
abbrev r11   : Fin 16 := 11
abbrev r12   : Fin 16 := 12
abbrev r13   : Fin 16 := 13
abbrev r14   : Fin 16 := 14
abbrev r15   : Fin 16 := 15

structure ConstRegs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (n m root : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  zero : (reg s rZero).val = 0
  one  : (reg s rOne).val = 1
  nVal : (reg s rN).val = n
  mVal : (reg s rM).val = m
  rootVal : (reg s rRoot).val = root

section RamHelpers

variable {bits : Nat} {L : Layout bits}

def putReg (s : State L) (d : Fin L.registerCount) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

theorem reg_putReg (s : State L) (d r : Fin L.registerCount) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r; simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp only [he, ite_false]
    exact Array.getElem_set_ne hd hr hv.symm

theorem step_imm_at {code : Program L} {input : Input L} {s : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d w)) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d w, hs, rfl, ?_, ?_, rfl⟩
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {d src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d (reg s src))) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d (reg s src))) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d (reg s src), hs, rfl, ?_, ?_, rfl⟩
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_loadInput_at {code : Program L} {input : Input L} {s : State L}
    {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw : input.words[(reg s a).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d w)) := by
    unfold step
    rw [hf]
    change (input.words[(reg s a).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d w, hs, rfl, ?_, ?_, rfl⟩
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_storeData_at {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.storeData addr src)) (hn : s.pc + 1 < code.size)
    (hbound : (reg s addr).val < s.data.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧ t.data = s.data.set (reg s addr).val (reg s src) hbound := by
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
          pc := s.pc + 1 }) else none)
    else none) = _
  rw [dite_eq_left_of_eq_true (eq_true hbound), ite_eq_left hn]

theorem sub_exact (x y : Word bits) (hle : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hx := x.isLt
  have hlt : x.val - y.val < 2 ^ bits := by omega
  rw [sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

theorem branchLt_true {x y : Word bits} (h : x.val < y.val) : ltb x y = true :=
  (ltb_eq_true x y).mpr h

theorem branchLt_false {x y : Word bits} (h : y.val ≤ x.val) : ltb x y = false := by
  cases hc : ltb x y with
  | false => rfl
  | true =>
    have hlt := (ltb_eq_true x y).mp hc
    omega

theorem reg_eq_of_regs_eq {s t : State L} (h : t.regs = s.regs) (r : Fin L.registerCount) :
    reg t r = reg s r := by
  change t.regs[r.val]'(by rw [t.regs_size]; exact r.isLt) =
    s.regs[r.val]'(by rw [s.regs_size]; exact r.isLt)
  simp only [h]

/-- Generic bounded-measure `while` loop combinator with per-state linear step budget. -/
theorem while_steps_budget {code : Program L} {input : Input L} {α : Type}
    (inv : α → State L → Prop) (meas : α → Nat) (budget : α → Nat) (post : α → State L → Prop)
    (stepCase : ∀ a s, inv a s →
      (∃ t, post a t ∧ ∃ k, k ≤ budget a ∧ run code input k s = some ⟨t, k⟩) ∨
      (∃ a' s' k, meas a' < meas a ∧ k + budget a' ≤ budget a ∧
        Steps code input k s s' ∧ inv a' s')) :
    ∀ bound a s, meas a ≤ bound → inv a s →
      ∃ aEnd t k, k ≤ budget a ∧ run code input k s = some ⟨t, k⟩ ∧ post aEnd t := by
  intro bound
  induction bound with
  | zero =>
    intro a s hm ha
    rcases stepCase a s ha with ⟨t, hpost, k, hk, hrun⟩ | ⟨a', _, _, hlt, _⟩
    · exact ⟨a, t, k, hk, hrun, hpost⟩
    · omega
  | succ b ih =>
    intro a s hm ha
    rcases stepCase a s ha with ⟨t, hpost, k, hk, hrun⟩ | ⟨a', s', k, hlt, hbud, hst, ha'⟩
    · exact ⟨a, t, k, hk, hrun, hpost⟩
    · obtain ⟨aEnd, t, k', hk', hrun', hpost'⟩ := ih a' s' (by omega) ha'
      obtain ⟨m, last, route, halt, cost⟩ := run_has_steps_then_halt hrun'
      obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
      have terminal : step code input last = some (.halted t) := by
        change t = last at sameHalt
        rw [sameHalt]
        exact step_halt_at atHalt
      have exec := (hst.append route).halts terminal
      change k' = m + 1 at cost
      rw [Nat.add_assoc, ← cost] at exec
      exact ⟨aEnd, t, k + k', by omega, exec, hpost'⟩

/-- Pipeline list of `Phase`s to one `Phase`. -/
def pipelinePhase : List (Phase L) → Phase L
  | [] => Phase.ofLast #[.halt] 0 rfl rfl rfl
  | p :: ps => Phase.link p (pipelinePhase ps)

theorem pipelinePhase_code (phases : List (Phase L)) :
    (pipelinePhase phases).code = pipeline phases := by
  induction phases with
  | nil => rfl
  | cons p ps ih =>
    change join p.code (pipelinePhase ps).code p.haltPC p.haltFits =
      join p.code (pipeline ps) p.haltPC p.haltFits
    rw [ih]

end RamHelpers

section Ram16Helpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

theorem step_imm16 {code : Program L16} {input : Input L16} {s : State L16}
    {d : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_imm_at hf hn

theorem step_mov16 {code : Program L16} {input : Input L16} {s : State L16}
    {d src : Fin 16}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_mov_at hf hn

theorem step_add16 {code : Program L16} {input : Input L16} {s : State L16}
    {dst lhs rhs : Fin 16}
    (hf : code[s.pc]? = some (.add dst lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = add (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  step_add_at hf hn

theorem step_sub16 {code : Program L16} {input : Input L16} {s : State L16}
    {dst lhs rhs : Fin 16}
    (hf : code[s.pc]? = some (.sub dst lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = sub (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  step_sub_at hf hn

theorem step_loadInput16 {code : Program L16} {input : Input L16} {s : State L16}
    {d a : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw' : input.words[(reg s a).val]? = some w) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadInput_at hf hn hw'

theorem step_loadData16 {code : Program L16} {input : Input L16} {s : State L16}
    {d a : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData d a))
    (hw' : s.data[(reg s a).val]? = some w) (hn : s.pc + 1 < code.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadData_at hf hw' hn

theorem step_storeData16 {code : Program L16} {input : Input L16} {s : State L16}
    {addr src : Fin 16}
    (hf : code[s.pc]? = some (.storeData addr src)) (hn : s.pc + 1 < code.size)
    (hbound : (reg s addr).val < s.data.size) :
    ∃ t : State L16, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧ t.data = s.data.set (reg s addr).val (reg s src) hbound :=
  step_storeData_at hf hn hbound

end Ram16Helpers

/-! ### Phase 0: Load constants (`0, 1, n, m, r`) and zero `inDeg[0..n-1]` -/

section Phase0Init

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def initCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.imm rZero ⟨0, by omega⟩,
    .imm rOne ⟨1, by omega⟩,
    .loadInput rN rZero,
    .loadInput rM rOne,
    .imm r5 ⟨2, by omega⟩,
    .loadInput rRoot r5,
    .imm r5 ⟨0, by omega⟩,
    .branchLt r5 rN 8 11,
    .storeData r5 rZero,
    .add r5 r5 rOne,
    .goto 7,
    .halt]

def initPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (initCode h5) 11 rfl rfl rfl

private theorem initPhase_size (h5 : 5 ≤ 2 ^ bits) : (initPhase (hi := hi) (hw := hw) h5).code.size = 12 := rfl

private structure InitLoop (n m root : Nat) (origData : Array (Word bits))
    (i : Nat) (s : State L16) : Prop where
  pc : s.pc = 7
  consts : ConstRegs n m root s
  idx : (reg s r5).val = i
  zeroes : ∀ j < i, (s.data[j]?).map Fin.val = some 0
  frame : ∀ j, (i ≤ j) → s.data[j]? = origData[j]?

theorem run_initPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ t, run (initPhase h5).code input (4 * n + 9) (Phase.initial s₀) = some ⟨t, 4 * n + 9⟩ ∧
      ConstRegs n m r.val t ∧
      (∀ j < n, (t.data[inDegBase n m + j]?).map Fin.val = some 0) ∧
      (∀ j, n ≤ j → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (initPhase h5).code
  have hCap := raw.cap_ge
  unfold rawDagInputCap at hCap
  have h5Lt : 5 ≤ 2 ^ bits := h5
  have h1 : 1 ≤ inputCap := by have := Fin.pos r; omega
  have h2 : 2 ≤ inputCap := by have := Fin.pos r; omega
  have h3 : 3 ≤ inputCap := by have := Fin.pos r; omega
  have hSz : code.size = 12 := initPhase_size h5
  have hw_lt0 : input.words[0]? = some ⟨n, by change g.vertexCount < 2 ^ bits; omega⟩ := by
    cases hw0 : input.words[0]? with
    | none => have hrn := raw.hdr_n; simp [hw0] at hrn
    | some w =>
      have := raw.hdr_n; rw [hw0, Option.map_some] at this
      exact congrArg some (Fin.ext (Option.some.inj this))
  have hw_lt1 : input.words[1]? = some ⟨m, by change g.arcCount < 2 ^ bits; omega⟩ := by
    cases hw1 : input.words[1]? with
    | none => have hrm := raw.hdr_m; simp [hw1] at hrm
    | some w =>
      have := raw.hdr_m; rw [hw1, Option.map_some] at this
      exact congrArg some (Fin.ext (Option.some.inj this))
  have hw_lt2 : input.words[2]? = some ⟨r.val, by have := r.isLt; omega⟩ := by
    cases hw2 : input.words[2]? with
    | none => have hrr := raw.hdr_r; simp [hw2] at hrr
    | some w =>
      have := raw.hdr_r; rw [hw2, Option.map_some] at this
      exact congrArg some (Fin.ext (Option.some.inj this))
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  obtain ⟨t1, h1s, h1pc, h1v, h1o, h1d⟩ := step_imm16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨t2, h2s, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_zero : (reg t2 rZero).val = 0 := by
    rw [h2o _ (by decide), h1v]
  have h2_one : (reg t2 rOne).val = 1 := by rw [h2v]
  obtain ⟨t3, h3s, h3pc, h3v, h3o, h3d⟩ := step_loadInput16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl)
    (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
    (by rw [h2_zero]; exact hw_lt0)
  have h3_one : (reg t3 rOne).val = 1 := by rw [h3o _ (by decide), h2_one]
  obtain ⟨t4, h4s, h4pc, h4v, h4o, h4d⟩ := step_loadInput16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
    (by rw [h3_one]; exact hw_lt1)
  obtain ⟨t5, h5s, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have h5_r5 : (reg t5 r5).val = 2 := by rw [h5v]
  obtain ⟨t6, h6s, h6pc, h6v, h6o, h6d⟩ := step_loadInput16 (input := input)
    (s := t5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
    (by rw [h5_r5]; exact hw_lt2)
  obtain ⟨t7, h7s, h7pc, h7v, h7o, h7d⟩ := step_imm16 (input := input)
    (s := t6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetupSteps : Steps code input 7 s_start t7 :=
    Steps.cons h1s (Steps.cons h2s (Steps.cons h3s (Steps.cons h4s
      (Steps.cons h5s (Steps.cons h6s (Steps.cons h7s (Steps.zero t7)))))))
  have hConsts7 : ConstRegs n m r.val t7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
        h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1v]
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
        h4o _ (by decide), h3o _ (by decide), h2v]
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
        h4o _ (by decide), h3v]
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4v]
    · rw [h7o _ (by decide), h6v]
  have hData7 : t7.data = s₀.data :=
    h7d.trans (h6d.trans (h5d.trans (h4d.trans (h3d.trans (h2d.trans h1d)))))
  have hInitLoop0 : InitLoop n m r.val s₀.data 0 t7 :=
    ⟨by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts7, by rw [h7v],
      fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun _ _ => by rw [hData7]⟩
  have hBody : ∀ i, i < n →
      BlockSpec code input 4 (InitLoop n m r.val s₀.data i)
        (InitLoop n m r.val s₀.data (i + 1)) := by
    intro i hiLt u hu
    have hCmp : ltb (reg u r5) (reg u rN) = true :=
      branchLt_true (by rw [hu.idx, hu.consts.nVal]; exact hiLt)
    have hf7 : code[u.pc]? = some (.branchLt r5 rN 8 11) := by rw [hu.pc]; rfl
    let u1 : State L16 := { u with pc := 8 }
    have hu1Pc : u1.pc = 8 := rfl
    have hs7 : step code input u = some (.next u1) := by
      simpa only [u1, hCmp, ite_true] using
        step_branchLt_at (input := input) hf7 (by rw [hSz, hCmp]; decide)
    have hBound : (reg u1 r5).val < u1.data.size := by
      change (reg u r5).val < u.data.size
      rw [u.data_size, hu.idx]
      change i < workCap
      unfold rawDagWorkCap at workRoom
      omega
    obtain ⟨u2, hs8, h2pc, h2regs, h2data⟩ := step_storeData16 (input := input)
      (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide) hBound
    have h2_r5 : (reg u2 r5).val = i := by
      rw [reg_eq_of_regs_eq h2regs r5]; exact hu.idx
    have h2_one : (reg u2 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq h2regs rOne]; exact hu.consts.one
    obtain ⟨u3, hs9, h3pc, h3val, h3o, h3data⟩ := step_add16 (input := input)
      (s := u2) (code := code) (by rw [h2pc]; rfl) (by rw [hSz, h2pc, hu1Pc]; decide)
    have hf10 : code[u3.pc]? = some (.goto 7) := by rw [h3pc, h2pc]; rfl
    let u4 : State L16 := { u3 with pc := 7 }
    have hs10 : step code input u3 = some (.next u4) :=
      step_goto_at hf10 (by rw [hSz]; decide)
    have hSumFit : (reg u2 r5).val + (reg u2 rOne).val < 2 ^ bits := by
      rw [h2_r5, h2_one]; unfold rawDagWorkCap at workRoom; omega
    have hConsts4 : ConstRegs n m r.val u4 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (congrArg Fin.val (h3o _ (by decide))).trans
          ((congrArg Fin.val (reg_eq_of_regs_eq h2regs rZero)).trans hu.consts.zero)
      · exact (congrArg Fin.val (h3o _ (by decide))).trans h2_one
      · exact (congrArg Fin.val (h3o _ (by decide))).trans
          ((congrArg Fin.val (reg_eq_of_regs_eq h2regs rN)).trans hu.consts.nVal)
      · exact (congrArg Fin.val (h3o _ (by decide))).trans
          ((congrArg Fin.val (reg_eq_of_regs_eq h2regs rM)).trans hu.consts.mVal)
      · exact (congrArg Fin.val (h3o _ (by decide))).trans
          ((congrArg Fin.val (reg_eq_of_regs_eq h2regs rRoot)).trans hu.consts.rootVal)
    have hIdx4 : (reg u4 r5).val = i + 1 := by
      change (reg u3 r5).val = i + 1
      rw [h3val, add_no_wrap _ _ hSumFit, h2_r5, h2_one]
    have hDataEq : u4.data = u.data.set i (reg u rZero)
        (by rw [u.data_size]; change i < workCap; unfold rawDagWorkCap at workRoom; omega) := by
      change u3.data = _
      rw [h3data]
      have hIdx1 : (reg u1 r5).val = i := hu.idx
      have hU1Data : u1.data = u.data := rfl
      have hU1Reg : reg u1 rZero = reg u rZero := rfl
      simpa only [hIdx1, hU1Data, hU1Reg] using h2data
    refine ⟨u4, Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.zero u4)))),
      rfl, hConsts4, hIdx4, ?_, ?_⟩
    · intro j hj
      rw [hDataEq]
      by_cases hji : j = i
      · subst j; rw [Array.getElem?_set_self, Option.map_some, hu.consts.zero]
      · rw [Array.getElem?_set_ne _ (Ne.symm hji)]; exact hu.zeroes j (by omega)
    · intro j hj
      rw [hDataEq, Array.getElem?_set_ne _ (by omega)]
      exact hu.frame j (by omega)
  have hIter := loop_steps n (fun _ => 4) (InitLoop n m r.val s₀.data) hBody t7 hInitLoop0
  have hCost : iterationCost (fun _ => 4) n = 4 * n := by
    clear hIter hInitLoop0
    induction n with
    | zero => rfl
    | succ k ih => simp [iterationCost, ih, Nat.mul_succ]
  rw [hCost] at hIter
  obtain ⟨uEnd, hStepsLoop, huEnd⟩ := hIter
  have hCmpEnd : ltb (reg uEnd r5) (reg uEnd rN) = false :=
    branchLt_false (by rw [huEnd.idx, huEnd.consts.nVal]; exact Nat.le_refl _)
  let t : State L16 := { uEnd with pc := 11 }
  have hfEnd : code[uEnd.pc]? = some (.branchLt r5 rN 8 11) := by rw [huEnd.pc]; rfl
  have hsEnd : step code input uEnd = some (.next t) := by
    simpa only [t, hCmpEnd, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hfEnd (by rw [hSz, hCmpEnd]; decide)
  have hHalt : step code input t = some (.halted t) := step_halt_at rfl
  have hExec := ((hSetupSteps.append hStepsLoop).append (Steps.cons hsEnd (Steps.zero t))).halts hHalt
  rw [show 7 + 4 * n + 1 + 1 = 4 * n + 9 by omega] at hExec
  refine ⟨t, hExec,
    ⟨huEnd.consts.zero, huEnd.consts.one, huEnd.consts.nVal, huEnd.consts.mVal,
      huEnd.consts.rootVal⟩, ?_, huEnd.frame⟩
  intro j hj
  simp only [inDegBase_eq, Nat.zero_add]
  exact huEnd.zeroes j hj

end Phase0Init

/-! ### Phase 1A: Count indegrees on `0..n-1` from `outTargets[0..m-1]` -/

section Phase1CountInDeg

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def countInDegCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.imm r5 ⟨4, by omega⟩,
    .add r5 r5 rN,
    .imm r6 ⟨0, by omega⟩,
    .branchLt r6 rM 4 11,
    .add r7 r5 r6,
    .loadInput r8 r7,
    .loadData r9 r8,
    .add r9 r9 rOne,
    .storeData r8 r9,
    .add r6 r6 rOne,
    .goto 3,
    .halt]

def countInDegPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (countInDegCode h5) 11 rfl rfl rfl

private theorem countInDegPhase_size (h5 : 5 ≤ 2 ^ bits) :
    (countInDegPhase (hi := hi) (hw := hw) h5).code.size = 12 := rfl

private structure InDegLoop (g : Digraph) (root : Nat) (origData : Array (Word bits))
    (e : Nat) (s : State L16) : Prop where
  pc : s.pc = 3
  consts : ConstRegs g.vertexCount g.arcCount root s
  base : (reg s r5).val = 4 + g.vertexCount
  edge : (reg s r6).val = e
  counts : ∀ v : Fin g.vertexCount,
    (s.data[v.val]?).map Fin.val = some (countOccurrence v ((outTargetsList g).take e))
  frame : ∀ j, g.vertexCount ≤ j → s.data[j]? = origData[j]?

private theorem countOccurrence_take_succ {n : Nat} (xs : List (Fin n)) (e : Nat)
    (he : e < xs.length) (v : Fin n) :
    countOccurrence v (xs.take (e + 1)) =
      countOccurrence v (xs.take e) + (if xs[e]'he = v then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some]
  induction xs.take e with
  | nil => simp [countOccurrence]
  | cons x ts ih =>
    simp only [List.cons_append, countOccurrence, ih]
    omega

private theorem countOccurrence_flatten {n : Nat} (xss : List (List (Fin n))) (v : Fin n) :
    countOccurrence v xss.flatten = (xss.map (countOccurrence v)).sum := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    simp only [List.flatten_cons, List.map_cons, List.sum_cons, ← ih]
    clear ih
    induction xs with
    | nil => simp [countOccurrence]
    | cons x xs ihxs => simp [countOccurrence, ihxs, Nat.add_assoc]

theorem countOccurrence_outTargetsList_eq_initialIndegree (g : Digraph) (v : Fin g.vertexCount) :
    countOccurrence v (outTargetsList g) = Kahn.initialIndegree g v := by
  unfold outTargetsList Kahn.initialIndegree
  rw [countOccurrence_flatten]
  have hEq : g.adj.toList = List.ofFn g.outArcs := by
    apply List.ext_getElem
    · simp [g.adj_size]
    · intro i hi hj
      simp [List.getElem_ofFn, Digraph.outArcs]
  rw [hEq, ← Digraph.indegrees_getElem]
  rfl

theorem run_countInDegPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (hZeroes : ∀ j < g.vertexCount, (s₀.data[inDegBase g.vertexCount g.arcCount + j]?).map Fin.val = some 0) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ t, run (countInDegPhase h5).code input (8 * m + 5) (Phase.initial s₀) =
        some ⟨t, 8 * m + 5⟩ ∧
      ConstRegs n m r.val t ∧
      (∀ v : Fin n, (t.data[inDegBase n m + v.val]?).map Fin.val =
        some (Kahn.initialIndegree g v)) ∧
      (∀ j, n ≤ j → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (countInDegPhase h5).code
  have hSz : code.size = 12 := countInDegPhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_imm16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_imm16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  have hBaseFit : 4 + n < 2 ^ bits := by
    change 4 + g.vertexCount < 2 ^ bits
    have := Fin.pos r
    have hwR := workRoom
    unfold rawDagWorkCap at hwR
    omega
  have h1_r5 : (reg t1 r5).val = 4 := by rw [h1v]
  have h1_rN : (reg t1 rN).val = n := by rw [h1o _ (by decide)]; exact hConsts.nVal
  have h2_r5 : (reg t2 r5).val = 4 + n := by
    rw [h2v, add_no_wrap _ _ (by rw [h1_r5, h1_rN]; exact hBaseFit), h1_r5, h1_rN]
  have hConsts3 : ConstRegs n m r.val t3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]; exact hConsts.zero
    · rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]; exact hConsts.one
    · rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]; exact hConsts.nVal
    · rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]; exact hConsts.mVal
    · rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]; exact hConsts.rootVal
  have hLoop0 : InDegLoop g r.val s₀.data 0 t3 := by
    refine ⟨by rw [h3pc, h2pc, h1pc, hStartPc], hConsts3, ?_, ?_, ?_, ?_⟩
    · rw [h3o _ (by decide), h2_r5]
    · rw [h3v]
    · intro v
      rw [h3d, h2d, h1d, List.take_zero]
      have hInitData : s_start.data = s₀.data := rfl
      rw [hInitData]
      simpa only [inDegBase_eq, Nat.zero_add, countOccurrence] using hZeroes v.val v.isLt
    · intro j _; rw [h3d, h2d, h1d]; rfl
  have hBody : ∀ e, e < m →
      BlockSpec code input 8 (InDegLoop g r.val s₀.data e) (InDegLoop g r.val s₀.data (e + 1)) := by
    intro e he u hu
    have hCmp : ltb (reg u r6) (reg u rM) = true :=
      branchLt_true (by rw [hu.edge, hu.consts.mVal]; exact he)
    have hf3 : code[u.pc]? = some (.branchLt r6 rM 4 11) := by rw [hu.pc]; rfl
    let u1 : State L16 := { u with pc := 4 }
    have hu1Pc : u1.pc = 4 := rfl
    have hs3 : step code input u = some (.next u1) := by
      simpa only [u1, hCmp, ite_true] using
        step_branchLt_at (input := input) hf3 (by rw [hSz, hCmp]; decide)
    obtain ⟨u2, hs4, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
      (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
    have hAddrFit : 4 + n + e < 2 ^ bits := by
      have := raw.cap_ge; unfold rawDagInputCap at this; omega
    have hAddrEq : (reg u2 r7).val = 4 + n + e := by
      rw [h2v, add_no_wrap _ _ (by change (reg u r5).val + (reg u r6).val < 2 ^ bits; rw [hu.base, hu.edge]; exact hAddrFit)]
      change (reg u r5).val + (reg u r6).val = _
      rw [hu.base, hu.edge]
    have heLen : e < (outTargetsList g).length := by rw [outTargetsList_length]; exact he
    let v : Fin g.vertexCount := (outTargetsList g)[e]'heLen
    have hwFlat := rawDagInput_out_targets_flat raw e he
    have hvInput : input.words[(reg u2 r7).val]? = some ⟨v.val, by
        have := raw.cap_ge; unfold rawDagInputCap at this; exact Nat.lt_trans v.isLt (by omega)⟩ := by
      rw [hAddrEq]
      dsimp only [n] at hwFlat ⊢
      cases hcell : input.words[4 + g.vertexCount + e]? with
      | none => simp [hcell] at hwFlat
      | some w =>
        rw [hcell, Option.map_some] at hwFlat
        exact congrArg some (Fin.ext (Option.some.inj hwFlat))
    obtain ⟨u3, hs5, h3pc, h3v, h3o, h3d⟩ := step_loadInput16 (input := input)
      (s := u2) (code := code) (by rw [h2pc]; rfl) (by rw [hSz, h2pc, hu1Pc]; decide) hvInput
    have h3_r8 : (reg u3 r8).val = v.val := by rw [h3v]
    have hDataBound : (reg u3 r8).val < u3.data.size := by
      rw [u3.data_size, h3_r8]
      change v.val < workCap
      unfold rawDagWorkCap at workRoom
      exact Nat.lt_of_lt_of_le v.isLt (by omega)
    let curDeg := countOccurrence v ((outTargetsList g).take e)
    have hCurLe : curDeg ≤ e := by
      clear hs3 hs4 hs5
      have hc : ∀ (xs : List (Fin g.vertexCount)), countOccurrence v xs ≤ xs.length := by
        intro xs; induction xs with | nil => simp [countOccurrence] | cons x xs ih => simp [countOccurrence]; split <;> omega
      exact Nat.le_trans (hc _) (by simp [List.length_take]; omega)
    have hCurLt : curDeg < 2 ^ bits := by
      have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
    have hDegMem : u3.data[(reg u3 r8).val]? = some ⟨curDeg, hCurLt⟩ := by
      rw [h3d, h2d, h3_r8]
      have hOld := hu.counts v
      cases hcell : u.data[v.val]? with
      | none => simp [hcell] at hOld
      | some w =>
        rw [hcell, Option.map_some] at hOld
        exact congrArg some (Fin.ext (Option.some.inj hOld))
    obtain ⟨u4, hs6, h4pc, h4v, h4o, h4d⟩ := step_loadData16 (input := input)
      (s := u3) (code := code) (by rw [h3pc, h2pc]; rfl) hDegMem
      (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
    have h4_r9 : (reg u4 r9).val = curDeg := by rw [h4v]
    have h4_one : (reg u4 rOne).val = 1 := by
      rw [h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
      exact hu.consts.one
    obtain ⟨u5, hs7, h5pc, h5v, h5o, h5d⟩ := step_add16 (input := input)
      (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc]; rfl)
      (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
    have hIncFit : curDeg + 1 < 2 ^ bits := by
      have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
    have h5_r9 : (reg u5 r9).val = curDeg + 1 := by
      rw [h5v, add_no_wrap _ _ (by rw [h4_r9, h4_one]; exact hIncFit), h4_r9, h4_one]
    have h5_r8 : (reg u5 r8).val = v.val := by
      rw [h5o _ (by decide), h4o _ (by decide), h3_r8]
    have h5Bound : (reg u5 r8).val < u5.data.size := by
      rw [u5.data_size, h5_r8]
      change v.val < workCap
      unfold rawDagWorkCap at workRoom
      exact Nat.lt_of_lt_of_le v.isLt (by omega)
    obtain ⟨u6, hs8, h6pc, h6regs, h6data⟩ := step_storeData16 (input := input)
      (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc]; rfl)
      (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) h5Bound
    have h6_r6 : (reg u6 r6).val = e := by
      rw [reg_eq_of_regs_eq h6regs r6, h5o _ (by decide), h4o _ (by decide),
        h3o _ (by decide), h2o _ (by decide)]; exact hu.edge
    have h6_one : (reg u6 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq h6regs rOne, h5o _ (by decide)]; exact h4_one
    obtain ⟨u7, hs9, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
      (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc]; rfl)
      (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
    let u8 : State L16 := { u7 with pc := 3 }
    have hs10 : step code input u7 = some (.next u8) :=
      step_goto_at (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc]; rfl) (by rw [hSz]; decide)
    have hEdgeFit : e + 1 < 2 ^ bits := by
      have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
    have hKeep (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7)
        (hn8 : regIdx ≠ r8) (hn9 : regIdx ≠ r9) : reg u8 regIdx = reg u regIdx := by
      change reg u7 regIdx = reg u regIdx
      rw [h7o _ hn6, reg_eq_of_regs_eq h6regs regIdx, h5o _ hn9, h4o _ hn9, h3o _ hn8, h2o _ hn7]
      rfl
    have hData8 : u8.data = u.data.set v.val (reg u5 r9)
        (by rw [u.data_size]; change v.val < workCap; unfold rawDagWorkCap at workRoom; exact Nat.lt_of_lt_of_le v.isLt (by omega)) := by
      change u7.data = _
      rw [h7d]
      simpa only [h5_r8, h5d, h4d, h3d, h2d] using h6data
    refine ⟨u8, Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.zero u8)))))))),
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨congrArg Fin.val (hKeep rZero (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.zero,
        congrArg Fin.val (hKeep rOne (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.one,
        congrArg Fin.val (hKeep rN (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.nVal,
        congrArg Fin.val (hKeep rM (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.mVal,
        congrArg Fin.val (hKeep rRoot (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.rootVal⟩
    · exact (congrArg Fin.val (hKeep r5 (by decide) (by decide) (by decide) (by decide))).trans hu.base
    · change (reg u7 r6).val = e + 1
      rw [h7v, add_no_wrap _ _ (by rw [h6_r6, h6_one]; exact hEdgeFit), h6_r6, h6_one]
    · intro w
      rw [hData8, countOccurrence_take_succ _ e heLen w]
      by_cases hwv : w = v
      · subst w
        rw [Array.getElem?_set_self, Option.map_some, h5_r9]
        dsimp only [curDeg]
        simp [v]
      · have hne : w.val ≠ v.val := fun h => hwv (Fin.ext h)
        rw [Array.getElem?_set_ne _ hne.symm, hu.counts w]
        simp [v, Ne.symm hwv]
    · intro j hj
      rw [hData8, Array.getElem?_set_ne _ (by have := v.isLt; omega)]
      exact hu.frame j hj
  have hIter := loop_steps m (fun _ => 8) (InDegLoop g r.val s₀.data) hBody t3 hLoop0
  have hCost : iterationCost (fun _ => 8) m = 8 * m := by
    clear hIter hLoop0
    induction m with
    | zero => rfl
    | succ k ih => simp [iterationCost, ih, Nat.mul_succ]
  rw [hCost] at hIter
  obtain ⟨uEnd, hStepsLoop, huEnd⟩ := hIter
  have hCmpEnd : ltb (reg uEnd r6) (reg uEnd rM) = false :=
    branchLt_false (by rw [huEnd.edge, huEnd.consts.mVal]; dsimp only [m]; exact Nat.le_refl _)
  let t : State L16 := { uEnd with pc := 11 }
  have hfEnd : code[uEnd.pc]? = some (.branchLt r6 rM 4 11) := by rw [huEnd.pc]; rfl
  have hsEnd : step code input uEnd = some (.next t) := by
    simpa only [t, hCmpEnd, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hfEnd (by rw [hSz, hCmpEnd]; decide)
  have hHalt : step code input t = some (.halted t) := step_halt_at rfl
  have hSetup : Steps code input 3 s_start t3 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.zero t3)))
  have hExec := ((hSetup.append hStepsLoop).append (Steps.cons hsEnd (Steps.zero t))).halts hHalt
  rw [show 3 + 8 * m + 1 + 1 = 8 * m + 5 by omega] at hExec
  refine ⟨t, hExec,
    ⟨huEnd.consts.zero, huEnd.consts.one, huEnd.consts.nVal, huEnd.consts.mVal,
      huEnd.consts.rootVal⟩, ?_, huEnd.frame⟩
  intro v
  have hfull : (outTargetsList g).take m = outTargetsList g := by
    rw [List.take_of_length_le (by rw [outTargetsList_length]; exact Nat.le_refl _)]
  have hv := huEnd.counts v
  rw [hfull, countOccurrence_outTargetsList_eq_initialIndegree] at hv
  simpa only [inDegBase_eq, Nat.zero_add] using hv

end Phase1CountInDeg

/-! ### Phase 1B: Seed zero-indegree Kahn queue into `topoOrder[0..n-1]` -/

section Phase1SeedQueue

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def seedQueueCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.imm r5 ⟨0, by omega⟩,
    .imm r6 ⟨0, by omega⟩,
    .branchLt r6 rN 3 10,
    .loadData r7 r6,
    .branchLt r7 rOne 5 8,
    .add r8 rN r5,
    .storeData r8 r6,
    .add r5 r5 rOne,
    .add r6 r6 rOne,
    .goto 2,
    .halt]

def seedQueuePhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (seedQueueCode h5) 10 rfl rfl rfl

private theorem seedQueuePhase_size (h5 : 5 ≤ 2 ^ bits) :
    (seedQueuePhase (hi := hi) (hw := hw) h5).code.size = 11 := rfl

def seedList (g : Digraph) : Nat → List (Fin g.vertexCount)
  | 0 => []
  | k + 1 =>
    if hk : k < g.vertexCount then
      let v : Fin g.vertexCount := ⟨k, hk⟩
      if Kahn.initialIndegree g v = 0 then seedList g k ++ [v] else seedList g k
    else seedList g k

private theorem seedList_lt (g : Digraph) (k : Nat) :
    ∀ v ∈ seedList g k, v.val < k := by
  induction k with
  | zero => intro v hv; simp [seedList] at hv
  | succ k ih =>
    intro v hv
    simp only [seedList] at hv
    split at hv
    · split at hv
      · rcases List.mem_append.mp hv with h1 | h2
        · exact Nat.lt_succ_of_lt (ih v h1)
        · have heq : v = ⟨k, by assumption⟩ := by simpa using h2
          subst v; exact Nat.lt_succ_self k
      · exact Nat.lt_succ_of_lt (ih v hv)
    · exact Nat.lt_succ_of_lt (ih v hv)

theorem seedList_nodup (g : Digraph) (k : Nat) : (seedList g k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    simp only [seedList]
    split
    · split
      · refine List.nodup_append.mpr ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb heq
        have hlt := seedList_lt g k a ha
        have hbEq : b = ⟨k, by assumption⟩ := by simpa using hb
        subst a; subst b
        exact Nat.ne_of_lt hlt rfl
      · exact ih
    · exact ih

theorem seedList_mem (g : Digraph) (k : Nat) (v : Fin g.vertexCount) :
    v ∈ seedList g k ↔ v.val < k ∧ Kahn.initialIndegree g v = 0 := by
  induction k with
  | zero => simp [seedList]
  | succ k ih =>
    simp only [seedList]
    by_cases hk : k < g.vertexCount
    · rw [dite_eq_left hk]
      by_cases hd : Kahn.initialIndegree g ⟨k, hk⟩ = 0
      · rw [ite_eq_left hd, List.mem_append, List.mem_singleton, ih]
        constructor
        · rintro (⟨hlt, hdv⟩ | rfl)
          · exact ⟨by omega, hdv⟩
          · exact ⟨Nat.lt_succ_self k, hd⟩
        · rintro ⟨hlt, hdv⟩
          by_cases he : v.val = k
          · right; exact Fin.ext he
          · left; exact ⟨by omega, hdv⟩
      · rw [ite_eq_right hd, ih]
        constructor
        · rintro ⟨hlt, hdv⟩; exact ⟨by omega, hdv⟩
        · rintro ⟨hlt, hdv⟩
          have hne : v.val ≠ k := by
            intro he
            have : v = ⟨k, hk⟩ := Fin.ext he
            subst v; exact hd hdv
          exact ⟨by omega, hdv⟩
    · rw [dite_eq_right hk, ih]
      have := v.isLt
      omega

theorem seedList_length_le (g : Digraph) (k : Nat) :
    (seedList g k).length ≤ k := by
  induction k with
  | zero => simp [seedList]
  | succ k ih =>
    simp only [seedList]
    split
    · split
      · simp; omega
      · exact Nat.le_succ_of_le ih
    · exact Nat.le_succ_of_le ih

private structure SeedLoop (g : Digraph) (root : Nat) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 2
  consts : ConstRegs g.vertexCount g.arcCount root s
  idx : (reg s r6).val = k
  qTail : (reg s r5).val = (seedList g k).length
  inDegs : ∀ v : Fin g.vertexCount,
    (s.data[v.val]?).map Fin.val = some (Kahn.initialIndegree g v)
  qMem : ∀ i : Nat, (hi : i < (seedList g k).length) →
    (s.data[g.vertexCount + i]?).map Fin.val = some ((seedList g k)[i]'hi).val
  frame : ∀ j, (j < g.vertexCount ∨ g.vertexCount + (seedList g k).length ≤ j) →
    s.data[j]? = origData[j]?

theorem run_seedQueuePhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (hInDeg : ∀ v : Fin g.vertexCount,
      (s₀.data[inDegBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (Kahn.initialIndegree g v)) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (steps : Nat) (q0 : List (Fin n)),
      steps ≤ 8 * n + 4 ∧
      run (seedQueuePhase h5).code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      q0.Nodup ∧
      q0.length ≤ n ∧
      (reg t r5).val = q0.length ∧
      (∀ v : Fin n, v ∈ q0 ↔ Kahn.initialIndegree g v = 0) ∧
      (∀ v : Fin n, (t.data[inDegBase n m + v.val]?).map Fin.val =
        some (Kahn.initialIndegree g v)) ∧
      (∀ i : Nat, (hi : i < q0.length) →
        (t.data[topoOrderBase n m + i]?).map Fin.val = some (q0[i]'hi).val) ∧
      (∀ j, (j < n ∨ n + q0.length ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (seedQueuePhase h5).code
  have hSz : code.size = 11 := seedQueuePhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_imm16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have hConsts2 : ConstRegs n m r.val t2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h2o _ (by decide), h1o _ (by decide)]; exact hConsts.zero
    · rw [h2o _ (by decide), h1o _ (by decide)]; exact hConsts.one
    · rw [h2o _ (by decide), h1o _ (by decide)]; exact hConsts.nVal
    · rw [h2o _ (by decide), h1o _ (by decide)]; exact hConsts.mVal
    · rw [h2o _ (by decide), h1o _ (by decide)]; exact hConsts.rootVal
  have hLoop0 : SeedLoop g r.val s₀.data 0 t2 := by
    refine ⟨by rw [h2pc, h1pc, hStartPc], hConsts2, by rw [h2v], by rw [h2o _ (by decide), h1v]; rfl,
      ?_, fun i hi => by simp [seedList] at hi, fun _ _ => by rw [h2d, h1d]; rfl⟩
    intro v
    have hInitData : s_start.data = s₀.data := rfl
    rw [h2d, h1d, hInitData]
    simpa only [inDegBase_eq, Nat.zero_add] using hInDeg v
  let SeedPost (k : Nat) (t : State L16) : Prop :=
    k = n ∧ ConstRegs n m r.val t ∧
    (reg t r5).val = (seedList g n).length ∧
    (∀ v : Fin n, (t.data[inDegBase n m + v.val]?).map Fin.val =
      some (Kahn.initialIndegree g v)) ∧
    (∀ i : Nat, (hi : i < (seedList g n).length) →
      (t.data[topoOrderBase n m + i]?).map Fin.val = some ((seedList g n)[i]'hi).val) ∧
    (∀ j, (j < n ∨ n + (seedList g n).length ≤ j) → t.data[j]? = s₀.data[j]?)
  have hStepCase : ∀ k u, (k ≤ n ∧ SeedLoop g r.val s₀.data k u) →
      (∃ t, SeedPost k t ∧ ∃ st, st ≤ 8 * (n - k) + 2 ∧ run code input st u = some ⟨t, st⟩) ∨
      (∃ k' u' st, (n - k') < (n - k) ∧ st + (8 * (n - k') + 2) ≤ 8 * (n - k) + 2 ∧
        Steps code input st u u' ∧ (k' ≤ n ∧ SeedLoop g r.val s₀.data k' u')) := by
    intro k u ⟨hkLe, hu⟩
    by_cases hk : k < n
    · right
      have hCmp : ltb (reg u r6) (reg u rN) = true :=
        branchLt_true (by rw [hu.idx, hu.consts.nVal]; exact hk)
      have hf2 : code[u.pc]? = some (.branchLt r6 rN 3 10) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 3 }
      have hu1Pc : u1.pc = 3 := rfl
      have hs2 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf2 (by rw [hSz, hCmp]; decide)
      let v : Fin g.vertexCount := ⟨k, hk⟩
      have hDegLe : Kahn.initialIndegree g v ≤ m := by
        rw [← countOccurrence_outTargetsList_eq_initialIndegree]
        have hc : ∀ (xs : List (Fin g.vertexCount)), countOccurrence v xs ≤ xs.length := by
          intro xs; induction xs with | nil => simp [countOccurrence] | cons x xs ih => simp [countOccurrence]; split <;> omega
        exact Nat.le_trans (hc _) (by rw [outTargetsList_length]; dsimp only [m]; exact Nat.le_refl _)
      have hDegFit : Kahn.initialIndegree g v < 2 ^ bits := by
        have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
      have hu1Deg : u1.data[(reg u1 r6).val]? = some ⟨Kahn.initialIndegree g v, hDegFit⟩ := by
        change u.data[(reg u r6).val]? = _
        rw [hu.idx]
        have hvOld := hu.inDegs v
        dsimp only [v] at hvOld
        cases hcell : u.data[k]? with
        | none => simp [hcell] at hvOld
        | some w =>
          rw [hcell, Option.map_some] at hvOld
          exact congrArg some (Fin.ext (Option.some.inj hvOld))
      obtain ⟨u2, hs3, h2pc, h2v, h2o, h2d⟩ := step_loadData16 (input := input)
        (s := u1) (code := code) rfl hu1Deg (by rw [hSz, hu1Pc]; decide)
      have h2_r7 : (reg u2 r7).val = Kahn.initialIndegree g v := by rw [h2v]
      have h2_one : (reg u2 rOne).val = 1 := by
        rw [h2o _ (by decide)]; exact hu.consts.one
      have h2_r5 : (reg u2 r5).val = (seedList g k).length := by
        rw [h2o _ (by decide)]; exact hu.qTail
      have h2_r6 : (reg u2 r6).val = k := by
        rw [h2o _ (by decide)]; exact hu.idx
      have h2_rN : (reg u2 rN).val = n := by
        rw [h2o _ (by decide)]; exact hu.consts.nVal
      have hSeedSucc : seedList g (k + 1) =
          if Kahn.initialIndegree g v = 0 then seedList g k ++ [v] else seedList g k := by
        rw [seedList, dite_eq_left hk]
      have hkFit : k + 1 < 2 ^ bits := by
        have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      by_cases hZero : Kahn.initialIndegree g v = 0
      · have hCmp4 : ltb (reg u2 r7) (reg u2 rOne) = true :=
          branchLt_true (by rw [h2_r7, h2_one, hZero]; decide)
        let u3 : State L16 := { u2 with pc := 5 }
        have hu3Pc : u3.pc = 5 := rfl
        have hf4 : code[u2.pc]? = some (.branchLt r7 rOne 5 8) := by rw [h2pc, hu1Pc]; rfl
        have hs4 : step code input u2 = some (.next u3) := by
          simpa only [u3, hCmp4, ite_true] using
            step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp4]; decide)
        have hqFit : n + (seedList g k).length < workCap := by
          have := seedList_length_le g k
          unfold rawDagWorkCap at workRoom
          dsimp only [n] at *
          omega
        have hqWordFit : (reg u3 rN).val + (reg u3 r5).val < 2 ^ bits := by
          change (reg u2 rN).val + (reg u2 r5).val < 2 ^ bits
          rw [h2_rN, h2_r5]; omega
        obtain ⟨u4, hs5, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
          (s := u3) (code := code) rfl (by rw [hSz, hu3Pc]; decide)
        have h4_r8 : (reg u4 r8).val = n + (seedList g k).length := by
          rw [h4v, add_no_wrap _ _ hqWordFit]
          change (reg u2 rN).val + (reg u2 r5).val = _
          rw [h2_rN, h2_r5]
        have h4Bound : (reg u4 r8).val < u4.data.size := by
          rw [u4.data_size, h4_r8]; change n + (seedList g k).length < workCap; exact hqFit
        obtain ⟨u5, hs6, h5pc, h5regs, h5data⟩ := step_storeData16 (input := input)
          (s := u4) (code := code) (by rw [h4pc, hu3Pc]; rfl) (by rw [hSz, h4pc, hu3Pc]; decide) h4Bound
        have h5_r5 : (reg u5 r5).val = (seedList g k).length := by
          rw [reg_eq_of_regs_eq h5regs r5, h4o _ (by decide)]; exact h2_r5
        have h5_one : (reg u5 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h5regs rOne, h4o _ (by decide)]; exact h2_one
        have h5_r6 : (reg u5 r6).val = k := by
          rw [reg_eq_of_regs_eq h5regs r6, h4o _ (by decide)]; exact h2_r6
        obtain ⟨u6, hs7, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
          (s := u5) (code := code) (by rw [h5pc, h4pc, hu3Pc]; rfl)
          (by rw [hSz, h5pc, h4pc, hu3Pc]; decide)
        have h6_r6 : (reg u6 r6).val = k := by
          rw [h6o _ (by decide)]; exact h5_r6
        have h6_one : (reg u6 rOne).val = 1 := by
          rw [h6o _ (by decide)]; exact h5_one
        obtain ⟨u7, hs8, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
          (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, hu3Pc]; rfl)
          (by rw [hSz, h6pc, h5pc, h4pc, hu3Pc]; decide)
        let u8 : State L16 := { u7 with pc := 2 }
        have hs9 : step code input u7 = some (.next u8) :=
          step_goto_at (by rw [h7pc, h6pc, h5pc, h4pc, hu3Pc]; rfl) (by rw [hSz]; decide)
        have hKeep (regIdx : Fin 16) (hn5 : regIdx ≠ r5) (hn6 : regIdx ≠ r6)
            (hn7 : regIdx ≠ r7) (hn8 : regIdx ≠ r8) : reg u8 regIdx = reg u regIdx := by
          change reg u7 regIdx = reg u regIdx
          rw [h7o _ hn6, h6o _ hn5, reg_eq_of_regs_eq h5regs regIdx, h4o _ hn8]
          change reg u2 regIdx = reg u regIdx
          rw [h2o _ hn7]
          rfl
        have hTailFit : (seedList g k).length + 1 < 2 ^ bits := by
          have := seedList_length_le g k
          have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
        have hData8 : u8.data = u.data.set (n + (seedList g k).length) (reg u4 r6)
            (by rw [u.data_size]; exact hqFit) := by
          change u7.data = _
          rw [h7d, h6d]
          have h3Data : u3.data = u2.data := rfl
          simpa only [h4_r8, h4d, h3Data, h2d] using h5data
        have h4_r6 : (reg u4 r6).val = k := by rw [h4o _ (by decide)]; exact h2_r6
        have hSeedLen : (seedList g (k + 1)).length = (seedList g k).length + 1 := by
          rw [hSeedSucc, ite_eq_left hZero, List.length_append, List.length_singleton]
        refine ⟨k + 1, u8, 8, by omega, by omega,
          Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
            (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.zero u8)))))))),
          ⟨by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · exact ⟨congrArg Fin.val (hKeep rZero (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.zero,
            congrArg Fin.val (hKeep rOne (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.one,
            congrArg Fin.val (hKeep rN (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.nVal,
            congrArg Fin.val (hKeep rM (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.mVal,
            congrArg Fin.val (hKeep rRoot (by decide) (by decide) (by decide) (by decide)) |>.trans hu.consts.rootVal⟩
        · change (reg u7 r6).val = k + 1
          rw [h7v, add_no_wrap _ _ (by rw [h6_r6, h6_one]; exact hkFit), h6_r6, h6_one]
        · change (reg u7 r5).val = (seedList g (k + 1)).length
          rw [h7o _ (by decide), h6v, add_no_wrap _ _ (by rw [h5_r5, h5_one]; exact hTailFit),
            h5_r5, h5_one, hSeedLen]
        · intro w
          rw [hData8, Array.getElem?_set_ne _ (by have := w.isLt; dsimp only [n]; omega)]
          exact hu.inDegs w
        · intro i hi
          rw [hData8]
          simp only [hSeedSucc, ite_eq_left hZero] at hi ⊢
          by_cases hiLast : i = (seedList g k).length
          · subst i
            dsimp only [n]
            rw [Array.getElem?_set_self, Option.map_some, h4_r6]
            simp [v]
          · have hiLt : i < (seedList g k).length := by
              rw [List.length_append, List.length_singleton] at hi
              omega
            rw [Array.getElem?_set_ne _ (by dsimp only [n]; omega), List.getElem_append_left hiLt]
            exact hu.qMem i hiLt
        · intro j hj
          rw [hSeedLen] at hj
          rw [hData8, Array.getElem?_set_ne _ (by dsimp only [n] at hj ⊢; omega)]
          exact hu.frame j (by omega)
      · have hPos : 1 ≤ Kahn.initialIndegree g v := Nat.pos_of_ne_zero hZero
        have hCmp4 : ltb (reg u2 r7) (reg u2 rOne) = false :=
          branchLt_false (by rw [h2_r7, h2_one]; exact hPos)
        let u3 : State L16 := { u2 with pc := 8 }
        have hu3Pc : u3.pc = 8 := rfl
        have hf4 : code[u2.pc]? = some (.branchLt r7 rOne 5 8) := by rw [h2pc, hu1Pc]; rfl
        have hs4 : step code input u2 = some (.next u3) := by
          simpa only [u3, hCmp4, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp4]; decide)
        have h3_r6 : (reg u3 r6).val = k := h2_r6
        have h3_one : (reg u3 rOne).val = 1 := h2_one
        obtain ⟨u4, hs5, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
          (s := u3) (code := code) rfl (by rw [hSz, hu3Pc]; decide)
        let u5 : State L16 := { u4 with pc := 2 }
        have hs6 : step code input u4 = some (.next u5) :=
          step_goto_at (by rw [h4pc, hu3Pc]; rfl) (by rw [hSz]; decide)
        have hKeep (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7) :
            reg u5 regIdx = reg u regIdx := by
          change reg u4 regIdx = reg u regIdx
          rw [h4o _ hn6]
          change reg u2 regIdx = reg u regIdx
          rw [h2o _ hn7]
          rfl
        have hData5 : u5.data = u.data := by change u4.data = u.data; rw [h4d]; exact h2d
        have hSeedSame : seedList g (k + 1) = seedList g k := by
          rw [hSeedSucc, ite_eq_right hZero]
        refine ⟨k + 1, u5, 5, by omega, by omega,
          Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.zero u5))))),
          ⟨by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · exact ⟨congrArg Fin.val (hKeep rZero (by decide) (by decide)) |>.trans hu.consts.zero,
            congrArg Fin.val (hKeep rOne (by decide) (by decide)) |>.trans hu.consts.one,
            congrArg Fin.val (hKeep rN (by decide) (by decide)) |>.trans hu.consts.nVal,
            congrArg Fin.val (hKeep rM (by decide) (by decide)) |>.trans hu.consts.mVal,
            congrArg Fin.val (hKeep rRoot (by decide) (by decide)) |>.trans hu.consts.rootVal⟩
        · change (reg u4 r6).val = k + 1
          rw [h4v, add_no_wrap _ _ (by rw [h3_r6, h3_one]; exact hkFit), h3_r6, h3_one]
        · rw [hSeedSame]
          exact (congrArg Fin.val (hKeep r5 (by decide) (by decide))).trans hu.qTail
        · intro w; rw [hData5]; exact hu.inDegs w
        · intro i hi
          rw [hData5]
          simpa only [hSeedSame] using hu.qMem i (by rw [← hSeedSame]; exact hi)
        · intro j hj; rw [hData5]; apply hu.frame j; rw [hSeedSame] at hj; exact hj
    · left
      have hEq : k = n := by omega
      have hCmp : ltb (reg u r6) (reg u rN) = false :=
        branchLt_false (by rw [hu.idx, hu.consts.nVal, hEq]; dsimp only [n]; exact Nat.le_refl _)
      let t : State L16 := { u with pc := 10 }
      have hf2 : code[u.pc]? = some (.branchLt r6 rN 3 10) := by rw [hu.pc]; rfl
      have hs2 : step code input u = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf2 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 u = some ⟨t, 2⟩ :=
        (Steps.cons hs2 (Steps.zero t)).halts hHalt
      refine ⟨t, ?_, 2, by omega, hRun2⟩
      refine ⟨hEq, ⟨hu.consts.zero, hu.consts.one, hu.consts.nVal, hu.consts.mVal,
          hu.consts.rootVal⟩, ?_, ?_, ?_, ?_⟩
      · exact (by change (reg u r5).val = (seedList g n).length; rw [← hEq]; exact hu.qTail)
      · intro v; simpa only [inDegBase_eq, Nat.zero_add] using hu.inDegs v
      · intro i hi; simpa only [hEq, topoOrderBase_eq] using hu.qMem i (hEq ▸ hi)
      · intro j hj; exact hu.frame j (hEq ▸ hj)
  obtain ⟨kEnd, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k u => k ≤ n ∧ SeedLoop g r.val s₀.data k u)
      (fun k => n - k) (fun k => 8 * (n - k) + 2) SeedPost hStepCase n 0 t2
      (Nat.le_refl _) ⟨Nat.zero_le _, hLoop0⟩
  have hSetup : Steps code input 2 s_start t2 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.zero t2))
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt
    rw [sameHalt]
    exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hkEq, hConstsEnd, hTailEnd, hInDegEnd, hQMemEnd, hFrameEnd⟩
  refine ⟨tEnd, 2 + loopSteps, seedList g n, by dsimp only [n] at hLoopLe ⊢; omega, hExec,
    hConstsEnd, seedList_nodup g n, seedList_length_le g n, hTailEnd, ?_, hInDegEnd, hQMemEnd, hFrameEnd⟩
  intro v
  rw [seedList_mem]
  exact ⟨fun ⟨_, hd⟩ => hd, fun hd => ⟨v.isLt, hd⟩⟩

end Phase1SeedQueue

/-! ### Phase 1C: Kahn BFS topological sort producing `topoOrder[0..n-1]` -/

section Phase1KahnBfs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def kahnBfsCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.imm r6 ⟨0, by omega⟩,
    .imm r7 ⟨3, by omega⟩,
    .imm r8 ⟨4, by omega⟩,
    .add r8 r8 rN,
    .branchLt r6 r5 5 25,
    .add r9 rN r6,
    .loadData r9 r9,
    .add r10 r7 r9,
    .loadInput r11 r10,
    .add r10 r10 rOne,
    .loadInput r12 r10,
    .branchLt r11 r12 12 23,
    .add r13 r8 r11,
    .loadInput r13 r13,
    .loadData r14 r13,
    .sub r14 r14 rOne,
    .storeData r13 r14,
    .branchLt r14 rOne 18 21,
    .add r15 rN r5,
    .storeData r15 r13,
    .add r5 r5 rOne,
    .add r11 r11 rOne,
    .goto 11,
    .add r6 r6 rOne,
    .goto 4,
    .halt]

def kahnBfsPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (kahnBfsCode h5) 25 rfl rfl rfl

private theorem kahnBfsPhase_size (h5 : 5 ≤ 2 ^ bits) :
    (kahnBfsPhase (hi := hi) (hw := hw) h5).code.size = 26 := rfl

/-- Remaining incoming arc count to `v` from vertices not yet in `done`. -/
def remIndeg (g : Digraph) (done : List (Fin g.vertexCount)) (v : Fin g.vertexCount) : Nat :=
  (List.ofFn (fun x : Fin g.vertexCount =>
    if x ∈ done then 0 else countOccurrence v (g.outArcs x))).sum

/-- Total outgoing arcs of vertices in `done`. -/
def processedArcsCount (g : Digraph) (done : List (Fin g.vertexCount)) : Nat :=
  (done.map (fun u => (g.outArcs u).length)).sum

theorem remIndeg_nil (g : Digraph) (v : Fin g.vertexCount) :
    remIndeg g [] v = Kahn.initialIndegree g v := by
  unfold remIndeg Kahn.initialIndegree
  have : (fun x : Fin g.vertexCount =>
      if x ∈ ([] : List (Fin g.vertexCount)) then 0 else countOccurrence v (g.outArcs x)) =
      fun x => countOccurrence v (g.outArcs x) := by
    funext x; simp
  rw [this]
  have hmap : List.ofFn (fun x : Fin g.vertexCount => countOccurrence v (g.outArcs x)) =
      (List.ofFn g.outArcs).map (countOccurrence v) := by
    apply List.ext_getElem <;> simp
  rw [hmap, ← Digraph.indegrees_getElem]
  rfl

private theorem sum_ofFn_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun x => f x + g x)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, ih]
    omega

private theorem ofFn_sum_succ {k : Nat} (f : Fin (k + 1) → Nat) :
    (List.ofFn f).sum =
      (List.ofFn (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).sum +
        f ⟨k, Nat.lt_succ_self k⟩ := by
  have hEq : List.ofFn f =
      List.ofFn (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ++
        [f ⟨k, Nat.lt_succ_self k⟩] := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      by_cases hik : i < k
      · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hik]), List.getElem_ofFn]
      · have hikEq : i = k := by simp at hi; omega
        subst i
        rw [List.getElem_ofFn, List.getElem_append_right (by simp)]
        simp
  rw [hEq, List.sum_append, List.sum_singleton]

private theorem nodup_filter_bool {α : Type} (p : α → Bool) {xs : List α} (hnd : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    have ihas := ih hcons.2
    by_cases hp : p a = true
    · rw [List.filter_cons, ite_eq_left hp]
      refine List.nodup_cons.mpr ⟨?_, ihas⟩
      intro hm
      exact hcons.1 (List.mem_filter.mp hm).1
    · have hp' : p a = false := by cases hpa : p a <;> simp_all
      rw [List.filter_cons, hp']
      exact ihas

private theorem nodup_filter_sum_le {α : Type} (xs : List α) (hnd : xs.Nodup)
    (p : α → Bool) (top : α) (f : α → Nat)
    (huniq : ∀ a ∈ xs, p a = false → a = top) :
    (xs.map f).sum ≤ ((xs.filter p).map f).sum + f top := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    by_cases hp : p a = true
    · have ihas := ih hcons.2 (fun b hb => huniq b (List.mem_cons_of_mem _ hb))
      simp only [List.filter_cons, hp, ↓reduceIte]
      simp only [List.map_cons, List.sum_cons] at ihas ⊢
      omega
    · have hp' : p a = false := by cases hpa : p a <;> simp_all
      have haTop : a = top := huniq a (List.mem_cons_self ..) hp'
      subst a
      have hEqF : (top :: as).filter p = as := by
        simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte]
        apply List.filter_eq_self.mpr
        intro b hb
        cases hpb : p b with
        | true => rfl
        | false =>
          have := huniq b (List.mem_cons_of_mem _ hb) hpb
          subst b
          exact False.elim (hcons.1 hb)
      rw [hEqF]
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem nodup_filter_length_eq {α : Type} (xs : List α) (hnd : xs.Nodup)
    (p : α → Bool) (top : α) (htop : top ∈ xs) (hpTop : p top = false)
    (huniq : ∀ a ∈ xs, p a = false → a = top) :
    xs.length = (xs.filter p).length + 1 := by
  induction xs with
  | nil => simp at htop
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp htop with rfl | hInAs
    · have hEqF : (top :: as).filter p = as := by
        simp only [List.filter_cons, hpTop, Bool.false_eq_true, ↓reduceIte]
        apply List.filter_eq_self.mpr
        intro b hb
        cases hpb : p b with
        | true => rfl
        | false =>
          have := huniq b (List.mem_cons_of_mem _ hb) hpb
          subst b
          exact False.elim (hcons.1 hb)
      rw [hEqF]; simp
    · have hne : a ≠ top := fun h => hcons.1 (h ▸ hInAs)
      have hpA : p a = true := by
        cases hpa : p a with
        | true => rfl
        | false => exact False.elim (hne (huniq a (List.mem_cons_self ..) hpa))
      have ihas := ih hcons.2 hInAs (fun b hb => huniq b (List.mem_cons_of_mem _ hb))
      simp only [List.filter_cons, hpA, ↓reduceIte]
      simp only [List.length_cons] at ihas ⊢
      omega

private theorem nodup_cover_length {n : Nat} (q : List (Fin n)) (hnd : q.Nodup)
    (hcov : ∀ v : Fin n, v ∈ q) : q.length = n := by
  have hGen : ∀ (k : Nat) (hk : k ≤ n) (ys : List (Fin n)),
      ys.Nodup → (∀ y ∈ ys, y.val < k) →
      (∀ i : Nat, (hi : i < k) → (⟨i, Nat.lt_of_lt_of_le hi hk⟩ : Fin n) ∈ ys) →
      ys.length = k := by
    intro k hk
    induction k with
    | zero =>
      intro ys _ hlt _
      cases ys with
      | nil => rfl
      | cons y _ => have := hlt y (by simp); omega
    | succ k ih =>
      intro ys hynd hlt hmem
      let top : Fin n := ⟨k, hk⟩
      let p : Fin n → Bool := fun y => decide (y.val ≠ k)
      have hy'nd : (ys.filter p).Nodup := nodup_filter_bool p hynd
      have hy'lt : ∀ y ∈ ys.filter p, y.val < k := by
        intro y hy
        have hflt := List.mem_filter.mp hy
        have hlt1 := hlt y hflt.1
        have hne : y.val ≠ k := by simpa [p] using hflt.2
        omega
      have hy'mem : ∀ i : Nat, (hi : i < k) → (⟨i, Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk)⟩ : Fin n) ∈ ys.filter p := by
        intro i hi
        exact List.mem_filter.mpr ⟨hmem i (by omega), by simp [p, Nat.ne_of_lt hi]⟩
      have hSub := ih (Nat.le_of_lt hk) (ys.filter p) hy'nd hy'lt hy'mem
      have hLenEq := nodup_filter_length_eq ys hynd p top (hmem k (Nat.lt_succ_self k))
        (by simp [p, top]) (fun a _ hfa => Fin.ext (by simpa [p] using hfa))
      omega
  exact hGen n (Nat.le_refl _) q hnd (fun y _ => y.isLt) (fun i hi => hcov ⟨i, hi⟩)

theorem remIndeg_append_singleton (g : Digraph) (done : List (Fin g.vertexCount))
    (u v : Fin g.vertexCount) (hu : u ∉ done) :
    remIndeg g done v = remIndeg g (done ++ [u]) v + countOccurrence v (g.outArcs u) := by
  unfold remIndeg
  let f1 : Fin g.vertexCount → Nat := fun x =>
    if x ∈ done ++ [u] then 0 else countOccurrence v (g.outArcs x)
  let f2 : Fin g.vertexCount → Nat := fun x =>
    if x = u then countOccurrence v (g.outArcs u) else 0
  have hPoint : (fun x => if x ∈ done then 0 else countOccurrence v (g.outArcs x)) =
      (fun x => f1 x + f2 x) := by
    funext x
    simp only [f1, f2, List.mem_append, List.mem_singleton]
    by_cases hxu : x = u
    · subst x; simp [hu]
    · simp [hxu]
  have hSingle : (List.ofFn f2).sum = countOccurrence v (g.outArcs u) := by
    clear f1 hPoint hu done
    have hsum : ∀ (k : Nat) (hk : k ≤ g.vertexCount),
        (List.ofFn (fun i : Fin k => if (⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ : Fin g.vertexCount) = u
          then countOccurrence v (g.outArcs u) else 0)).sum =
        if u.val < k then countOccurrence v (g.outArcs u) else 0 := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ofFn_sum_succ]
        have ih' := ih (Nat.le_of_lt hk)
        dsimp only at ih' ⊢
        rw [ih']
        by_cases huk : u.val = k
        · have heq : (⟨k, hk⟩ : Fin g.vertexCount) = u := Fin.ext huk.symm
          have hnot : ¬ u.val < k := by omega
          have hlt : u.val < k + 1 := by omega
          simp [heq, hnot, hlt]
        · have hne : (⟨k, hk⟩ : Fin g.vertexCount) ≠ u := fun h => huk (congrArg Fin.val h).symm
          have hiff : u.val < k + 1 ↔ u.val < k := by omega
          simp [hne, hiff]
    simpa only [Fin.eta, u.isLt, ite_true] using hsum g.vertexCount (Nat.le_refl _)
  rw [hPoint, sum_ofFn_add, hSingle]

theorem remIndeg_eq_zero_iff (g : Digraph) (done : List (Fin g.vertexCount))
    (v : Fin g.vertexCount) :
    remIndeg g done v = 0 ↔ ∀ x : Fin g.vertexCount, x ∉ done → ¬ g.HasArc x v := by
  unfold remIndeg
  have hSumZero : ∀ xs : List Nat, xs.sum = 0 ↔ ∀ a ∈ xs, a = 0 := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih => simp [Nat.add_eq_zero_iff, ih]
  rw [hSumZero]
  constructor
  · intro h x hx harc
    have hmem : (if x ∈ done then 0 else countOccurrence v (g.outArcs x)) ∈
        List.ofFn (fun y : Fin g.vertexCount =>
          if y ∈ done then 0 else countOccurrence v (g.outArcs y)) :=
      List.mem_ofFn.mpr ⟨x, rfl⟩
    have hz := h _ hmem
    rw [ite_eq_right hx] at hz
    have hpos := (Kahn.countOccurrence_pos_iff_row_mem v (g.outArcs x)).mpr harc
    omega
  · intro h a ha
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp ha
    by_cases hx : x ∈ done
    · simp [hx]
    · rw [ite_eq_right hx]
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact h x hx ((Kahn.countOccurrence_pos_iff_row_mem v (g.outArcs x)).mp hpos)

theorem processedArcsCount_append (g : Digraph) (done : List (Fin g.vertexCount))
    (u : Fin g.vertexCount) :
    processedArcsCount g (done ++ [u]) = processedArcsCount g done + (g.outArcs u).length := by
  simp [processedArcsCount]

theorem processedArcsCount_le (g : Digraph) (done : List (Fin g.vertexCount))
    (hnd : done.Nodup) :
    processedArcsCount g done ≤ g.arcCount := by
  have hAll : ∀ (k : Nat) (hk : k ≤ g.vertexCount) (xs : List (Fin g.vertexCount)),
      xs.Nodup → (∀ x ∈ xs, x.val < k) →
      (xs.map (fun u => (g.outArcs u).length)).sum ≤
        (List.ofFn (fun i : Fin k => (g.outArcs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).length)).sum := by
    intro k hk
    induction k with
    | zero =>
      intro xs _ hlt
      cases xs with
      | nil => simp
      | cons x _ => have := hlt x (by simp); omega
    | succ k ih =>
      intro xs hxnd hlt
      rw [ofFn_sum_succ]
      let top : Fin g.vertexCount := ⟨k, hk⟩
      let xs' := xs.filter (fun x => decide (x ≠ top))
      have hx'nd : xs'.Nodup := nodup_filter_bool _ hxnd
      have hx'lt : ∀ x ∈ xs', x.val < k := by
        intro x hx
        rcases List.mem_filter.mp hx with ⟨hxMem, hne⟩
        have hxlt := hlt x hxMem
        have hne' : x ≠ top := by simpa using hne
        have : x.val ≠ k := fun h => hne' (Fin.ext h)
        omega
      have hSub := ih (Nat.le_of_lt hk) xs' hx'nd hx'lt
      have hPart : (xs.map (fun u => (g.outArcs u).length)).sum ≤
          (xs'.map (fun u => (g.outArcs u).length)).sum + (g.outArcs top).length :=
        nodup_filter_sum_le xs hxnd (fun x => decide (x ≠ top)) top (fun u => (g.outArcs u).length)
          (fun a _ hfa => by simpa using hfa)
      exact Nat.le_trans hPart (Nat.add_le_add_right hSub _)
  have hFull := hAll g.vertexCount (Nat.le_refl _) done hnd (fun x _ => x.isLt)
  have hSumArc : (List.ofFn (fun i : Fin g.vertexCount =>
      (g.outArcs ⟨i.val, i.isLt⟩).length)).sum = g.arcCount := by
    have h1 : List.ofFn (fun i : Fin g.vertexCount =>
        (g.outArcs ⟨i.val, i.isLt⟩).length) = (List.ofFn g.outArcs).map List.length := by
      apply List.ext_getElem <;> simp
    have h2 : List.ofFn g.outArcs = g.adj.toList := by
      apply List.ext_getElem
      · simp [g.adj_size]
      · intro i hi hj; simp [Digraph.outArcs]
    rw [h1, h2, ← listLengthSum_eq_sum_lengths]
    rfl
  rw [hSumArc] at hFull
  exact hFull

private theorem nodup_length_le_fin {n : Nat} (xs : List (Fin n)) (hnd : xs.Nodup) :
    xs.length ≤ n := by
  have hAll : ∀ (k : Nat) (ys : List (Fin n)), ys.Nodup → (∀ y ∈ ys, y.val < k) → ys.length ≤ k := by
    intro k
    induction k with
    | zero =>
      intro ys _ hlt
      cases ys with
      | nil => simp
      | cons y _ => have := hlt y (by simp); omega
    | succ k ih =>
      intro ys hynd hlt
      let ys' := ys.filter (fun y => decide (y.val ≠ k))
      have hy'nd : ys'.Nodup := nodup_filter_bool _ hynd
      have hy'lt : ∀ y ∈ ys', y.val < k := by
        intro y hy
        rcases List.mem_filter.mp hy with ⟨hyMem, hne⟩
        have := hlt y hyMem
        have hne' : y.val ≠ k := by simpa using hne
        omega
      have hSub := ih ys' hy'nd hy'lt
      have hLen : ys.length ≤ ys'.length + 1 := by
        by_cases hk : k < n
        · have hSum := nodup_filter_sum_le ys hynd (fun y => decide (y.val ≠ k)) ⟨k, hk⟩ (fun _ => 1)
            (fun a _ hfa => Fin.ext (by simpa using hfa))
          have hMapOne : ∀ zs : List (Fin n), (zs.map (fun _ => 1)).sum = zs.length := by
            intro zs; induction zs with | nil => simp | cons _ _ ihz => simp [ihz]; omega
          simpa only [hMapOne] using hSum
        · have hEqF : ys' = ys := by
            apply List.filter_eq_self.mpr
            intro b _
            have := b.isLt
            simp; omega
          rw [hEqF]
          omega
      exact Nat.le_trans hLen (Nat.add_le_add_right hSub 1)
  exact hAll n xs hnd (fun y _ => y.isLt)

private theorem kahn_complete_of_acyclic (g : Digraph) (hacyc : g.IsAcyclic)
    (q : List (Fin g.vertexCount)) (hnd : q.Nodup)
    (hZero : ∀ v : Fin g.vertexCount, v ∈ q ↔ remIndeg g q v = 0)
    (hPair : q.Pairwise (fun a b => ¬ g.HasArc b a)) :
    g.IsTopologicalList q := by
  have hall : ∀ v : Fin g.vertexCount, v ∈ q := by
    obtain ⟨rank, hrank⟩ := hacyc
    intro v
    apply Classical.byContradiction
    intro hvNot
    let rem := (List.finRange g.vertexCount).filter (fun x => !decide (x ∈ q))
    have hremNe : rem ≠ [] := by
      intro he
      have hmem : v ∈ rem := List.mem_filter.mpr ⟨List.mem_finRange v, by simp [hvNot]⟩
      rw [he] at hmem
      cases hmem
    have hexMin : ∀ xs : List (Fin g.vertexCount), xs ≠ [] →
        ∃ u ∈ xs, ∀ w ∈ xs, rank u ≤ rank w := by
      intro xs
      induction xs with
      | nil => intro h; exact (h rfl).elim
      | cons a xs ih =>
        intro _
        cases xs with
        | nil => exact ⟨a, by simp, fun w hw => by simp at hw; subst w; exact Nat.le_refl _⟩
        | cons b bs =>
          obtain ⟨u, hu, hmin⟩ := ih (by simp)
          rcases Nat.le_total (rank a) (rank u) with hau | hua
          · refine ⟨a, by simp, fun w hw => ?_⟩
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact Nat.le_refl _
            · exact Nat.le_trans hau (hmin w hw')
          · refine ⟨u, List.mem_cons_of_mem _ hu, fun w hw => ?_⟩
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact hua
            · exact hmin w hw'
    obtain ⟨u, huRem, hMin⟩ := hexMin rem hremNe
    rcases List.mem_filter.mp huRem with ⟨_, huNotQ⟩
    have huNot : u ∉ q := by simpa using huNotQ
    have hZeroU : remIndeg g q u = 0 := by
      rw [remIndeg_eq_zero_iff]
      intro x hxNot harc
      have hxRem : x ∈ rem := List.mem_filter.mpr ⟨List.mem_finRange x, by simp [hxNot]⟩
      have hle := hMin x hxRem
      have hlt := hrank x u harc
      omega
    exact huNot ((hZero u).mpr hZeroU)
  refine ⟨hnd, hall, ?_⟩
  intro pre u post hsplit v huv
  have hv := hall v
  rw [hsplit] at hv
  rcases List.mem_append.mp hv with hvpre | hvrest
  · rw [hsplit, List.pairwise_append] at hPair
    exact False.elim (hPair.2.2 v hvpre u (by simp) huv)
  · rcases List.mem_cons.mp hvrest with rfl | hvpost
    · obtain ⟨rank, hrank⟩ := hacyc
      exact False.elim (Nat.lt_irrefl (rank v) (hrank v v huv))
    · exact hvpost

private structure KahnOuterInv (g : Digraph) (root : Nat) (origData : Array (Word bits))
    (k : Nat) (q : List (Fin g.vertexCount)) (s : State L16) : Prop where
  pc : s.pc = 4
  consts : ConstRegs g.vertexCount g.arcCount root s
  qNd : q.Nodup
  hkLe : k ≤ q.length
  qTail : (reg s r5).val = q.length
  qHead : (reg s r6).val = k
  offBase : (reg s r7).val = 3
  tgtBase : (reg s r8).val = 4 + g.vertexCount
  qMem : ∀ i : Nat, (hi : i < q.length) →
    (s.data[g.vertexCount + i]?).map Fin.val = some (q[i]'hi).val
  inDegs : ∀ v : Fin g.vertexCount,
    (s.data[v.val]?).map Fin.val = some (remIndeg g (q.take k) v)
  qZero : ∀ v : Fin g.vertexCount, v ∈ q ↔ remIndeg g (q.take k) v = 0
  topo : (q.take k).Pairwise (fun a b => ¬ g.HasArc b a)
  frame : ∀ j, 2 * g.vertexCount ≤ j → s.data[j]? = origData[j]?

private structure KahnInnerInv (g : Digraph) (root : Nat) (origData : Array (Word bits))
    (k : Nat) (u : Fin g.vertexCount) (j : Nat) (q : List (Fin g.vertexCount))
    (s : State L16) : Prop where
  pc : s.pc = 11
  consts : ConstRegs g.vertexCount g.arcCount root s
  qNd : q.Nodup
  hk1Le : k + 1 ≤ q.length
  huAt : q[k]'(by omega) = u
  hjLe : j ≤ (g.outArcs u).length
  qTail : (reg s r5).val = q.length
  qHead : (reg s r6).val = k
  offBase : (reg s r7).val = 3
  tgtBase : (reg s r8).val = 4 + g.vertexCount
  edgeIdx : (reg s r11).val = outPrefix g u.val + j
  edgeEnd : (reg s r12).val = outPrefix g u.val + (g.outArcs u).length
  qMem : ∀ i : Nat, (hi : i < q.length) →
    (s.data[g.vertexCount + i]?).map Fin.val = some (q[i]'hi).val
  inDegs : ∀ v : Fin g.vertexCount,
    (s.data[v.val]?).map Fin.val =
      some (remIndeg g (q.take (k + 1)) v + countOccurrence v ((g.outArcs u).drop j))
  qZero : ∀ v : Fin g.vertexCount,
    v ∈ q ↔ remIndeg g (q.take (k + 1)) v + countOccurrence v ((g.outArcs u).drop j) = 0
  topo : (q.take (k + 1)).Pairwise (fun a b => ¬ g.HasArc b a)
  frame : ∀ idx, 2 * g.vertexCount ≤ idx → s.data[idx]? = origData[idx]?

theorem run_kahnBfsPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (q0 : List (Fin g.vertexCount)) (hq0Nd : q0.Nodup)
    (hq0Tail : (reg s₀ r5).val = q0.length)
    (hq0Zero : ∀ v : Fin g.vertexCount, v ∈ q0 ↔ Kahn.initialIndegree g v = 0)
    (hInDeg : ∀ v : Fin g.vertexCount,
      (s₀.data[inDegBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (Kahn.initialIndegree g v))
    (hq0Mem : ∀ i : Nat, (hi : i < q0.length) →
      (s₀.data[topoOrderBase g.vertexCount g.arcCount + i]?).map Fin.val = some (q0[i]'hi).val) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (steps : Nat) (order : List (Fin n)) (hlen : order.length = n),
      steps ≤ 10 * n + 12 * m + 6 ∧
      run (kahnBfsPhase h5).code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      g.IsTopologicalList order ∧
      (∀ i : Nat, (hi : i < n) →
        (t.data[topoOrderBase n m + i]?).map Fin.val =
          some (order[i]'(by rw [hlen]; exact hi)).val) ∧
      (∀ j, 2 * n ≤ j → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (kahnBfsPhase h5).code
  have hSz : code.size = 26 := kahnBfsPhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_imm16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_imm16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 4 s_start t4 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.zero t4))))
  have hTgtFit : 4 + n < 2 ^ bits := by
    have := Fin.pos r
    have hwR := workRoom
    unfold rawDagWorkCap at hwR
    dsimp only [n] at *
    omega
  have hKeep4 (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7) (hn8 : regIdx ≠ r8) :
      reg t4 regIdx = reg s_start regIdx := by
    rw [h4o _ hn8, h3o _ hn8, h2o _ hn7, h1o _ hn6]
  have hConsts4 : ConstRegs n m r.val t4 :=
    ⟨(congrArg Fin.val (hKeep4 rZero (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep4 rOne (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep4 rN (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep4 rM (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep4 rRoot (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hData4 : t4.data = s₀.data := h4d.trans (h3d.trans (h2d.trans h1d))
  have h3_r8 : (reg t3 r8).val = 4 := by rw [h3v]
  have h3_rN : (reg t3 rN).val = n := by
    rw [h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    exact hConsts.nVal
  have hOuter0 : KahnOuterInv g r.val s₀.data 0 q0 t4 := by
    refine ⟨by rw [h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts4, hq0Nd, Nat.zero_le _, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact (congrArg Fin.val (hKeep4 r5 (by decide) (by decide) (by decide))).trans hq0Tail
    · rw [h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1v]
    · rw [h4o _ (by decide), h3o _ (by decide), h2v]
    · rw [h4v, add_no_wrap _ _ (by rw [h3_r8, h3_rN]; dsimp only [n]; exact hTgtFit),
        h3_r8, h3_rN]
    · intro i hi
      rw [hData4]
      simpa only [topoOrderBase_eq] using hq0Mem i hi
    · intro v
      rw [hData4, List.take_zero, remIndeg_nil]
      simpa only [inDegBase_eq, Nat.zero_add] using hInDeg v
    · intro v
      rw [List.take_zero, remIndeg_nil]
      exact hq0Zero v
    · simp
    · intro j _; rw [hData4]
  -- Inner loop stepping: from `KahnInnerInv g r.val s₀.data k u j q st` to completion at `pc = 23`
  let InnerState := Σ j : Nat, List (Fin g.vertexCount)
  let InnerPost (k : Nat) (_u : Fin g.vertexCount) (qOrig : List (Fin g.vertexCount))
      (p : InnerState) (st : State L16) : Prop :=
    st.pc = 23 ∧ ConstRegs n m r.val st ∧ p.2.Nodup ∧ k + 1 ≤ p.2.length ∧
    p.2.take (k + 1) = qOrig.take (k + 1) ∧
    (reg st r5).val = p.2.length ∧ (reg st r6).val = k ∧
    (reg st r7).val = 3 ∧ (reg st r8).val = 4 + n ∧
    (∀ i : Nat, (hi : i < p.2.length) →
      (st.data[n + i]?).map Fin.val = some (p.2[i]'hi).val) ∧
    (∀ v : Fin n, (st.data[v.val]?).map Fin.val = some (remIndeg g (p.2.take (k + 1)) v)) ∧
    (∀ v : Fin n, v ∈ p.2 ↔ remIndeg g (p.2.take (k + 1)) v = 0) ∧
    (p.2.take (k + 1)).Pairwise (fun a b => ¬ g.HasArc b a) ∧
    (∀ idx, 2 * n ≤ idx → st.data[idx]? = s₀.data[idx]?)
  have run_inner : ∀ (k : Nat) (u : Fin n) (st0 : State L16) (qStart : List (Fin n)),
      KahnInnerInv g r.val s₀.data k u 0 qStart st0 →
      ∃ (qEnd : List (Fin n)) (stEnd : State L16) (innerSteps : Nat),
        innerSteps ≤ 12 * (g.outArcs u).length + 1 ∧
        Steps code input innerSteps st0 stEnd ∧
        InnerPost k u qStart ⟨(g.outArcs u).length, qEnd⟩ stEnd := by
    intro k u st0 qStart hIn0
    have hInnerAux : ∀ (rem j : Nat) (q : List (Fin n)) (st : State L16),
        (g.outArcs u).length - j ≤ rem →
        KahnInnerInv g r.val s₀.data k u j q st →
        ∃ (qEnd : List (Fin n)) (stEnd : State L16) (steps : Nat),
          steps ≤ 12 * ((g.outArcs u).length - j) + 1 ∧
          Steps code input steps st stEnd ∧
          InnerPost k u q ⟨(g.outArcs u).length, qEnd⟩ stEnd := by
      intro rem
      induction rem with
      | zero =>
        intro j q st hRem hIn
        have hjEq : j = (g.outArcs u).length := by have := hIn.hjLe; omega
        have hCmp : ltb (reg st r11) (reg st r12) = false :=
          branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
        have hf11 : code[st.pc]? = some (.branchLt r11 r12 12 23) := by rw [hIn.pc]; rfl
        let stEnd : State L16 := { st with pc := 23 }
        have hs11 : step code input st = some (.next stEnd) := by
          simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf11 (by rw [hSz, hCmp]; decide)
        have hDrop : (g.outArcs u).drop j = [] := by
          rw [hjEq]; exact List.drop_length
        refine ⟨q, stEnd, 1, by omega, Steps.cons hs11 (Steps.zero stEnd),
          rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
          hIn.qNd, hIn.hk1Le, rfl, hIn.qTail, hIn.qHead, hIn.offBase, hIn.tgtBase,
          hIn.qMem, ?_, ?_, hIn.topo, hIn.frame⟩
        · intro v; simpa only [hDrop, countOccurrence, Nat.add_zero] using hIn.inDegs v
        · intro v; simpa only [hDrop, countOccurrence, Nat.add_zero] using hIn.qZero v
      | succ rem ih =>
        intro j q st hRem hIn
        by_cases hj : j < (g.outArcs u).length
        · have hCmp : ltb (reg st r11) (reg st r12) = true :=
            branchLt_true (by rw [hIn.edgeIdx, hIn.edgeEnd]; exact Nat.add_lt_add_left hj _)
          have hf11 : code[st.pc]? = some (.branchLt r11 r12 12 23) := by rw [hIn.pc]; rfl
          let u1 : State L16 := { st with pc := 12 }
          have hu1Pc : u1.pc = 12 := rfl
          have hs11 : step code input st = some (.next u1) := by
            simpa only [u1, hCmp, ite_true] using
              step_branchLt_at (input := input) hf11 (by rw [hSz, hCmp]; decide)
          have hEdgeBound : 4 + n + (outPrefix g u.val + j) < 2 ^ bits := by
            have h1 : outPrefix g u.val + j < outPrefix g (u.val + 1) := by
              rw [outPrefix_succ_lt g u]; omega
            have h2 : outPrefix g u.val + j < g.arcCount := by
              rw [← outPrefix_vertexCount g]
              exact Nat.lt_of_lt_of_le h1 (outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount))
            have := raw.cap_ge; unfold rawDagInputCap at this
            dsimp only [n] at *; omega
          have hAddrWordFit : (reg u1 r8).val + (reg u1 r11).val < 2 ^ bits := by
            change (reg st r8).val + (reg st r11).val < 2 ^ bits
            rw [hIn.tgtBase, hIn.edgeIdx]; exact hEdgeBound
          obtain ⟨u2, hs12, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
            (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
          have h2_r13 : (reg u2 r13).val = 4 + n + (outPrefix g u.val + j) := by
            rw [h2v, add_no_wrap _ _ hAddrWordFit]
            change (reg st r8).val + (reg st r11).val = _
            rw [hIn.tgtBase, hIn.edgeIdx]
          let v : Fin n := (g.outArcs u)[j]'hj
          have hvTarget := raw.out_targets u j hj
          have hvFit : v.val < 2 ^ bits := by
            have := raw.cap_ge; unfold rawDagInputCap at this; have := v.isLt; dsimp only [n] at *; omega
          have hvInput : input.words[(reg u2 r13).val]? = some ⟨v.val, hvFit⟩ := by
            rw [h2_r13, ← Nat.add_assoc]
            dsimp only [n]
            cases hcell : input.words[4 + g.vertexCount + outPrefix g u.val + j]? with
            | none => simp [hcell] at hvTarget
            | some w =>
              rw [hcell, Option.map_some] at hvTarget
              exact congrArg some (Fin.ext (Option.some.inj hvTarget))
          obtain ⟨u3, hs13, h3pc, h3v, h3o, h3d⟩ := step_loadInput16 (input := input)
            (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl)
            (by rw [hSz, h2pc, hu1Pc]; decide) hvInput
          have h3_r13 : (reg u3 r13).val = v.val := by rw [h3v]
          have hDropSplit : (g.outArcs u).drop j = v :: (g.outArcs u).drop (j + 1) := by
            have := list_split_at (g.outArcs u) j hj
            rw [List.drop_eq_getElem_cons hj]
          let curDeg := remIndeg g (q.take (k + 1)) v + countOccurrence v ((g.outArcs u).drop j)
          let nextDeg := remIndeg g (q.take (k + 1)) v + countOccurrence v ((g.outArcs u).drop (j + 1))
          have hCurEq : curDeg = nextDeg + 1 := by
            simp only [curDeg, nextDeg, hDropSplit, countOccurrence, ↓reduceIte]
            omega
          have hCurLt : curDeg < 2 ^ bits := by
            have hkLt : k < q.length := Nat.lt_of_succ_le hIn.hk1Le
            have htakeK1 : q.take (k + 1) = q.take k ++ [u] := by
              rw [List.take_add_one, List.getElem?_eq_getElem hkLt,
                hIn.huAt, Option.toList_some]
            have huNotPre : u ∉ q.take k := by
              intro hmem
              obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
              have hiLt : i < k := by simp only [List.length_take] at hi; omega
              have hqk : q[k]'hkLt = u := hIn.huAt
              have hqi : q[i]'(Nat.lt_trans hiLt hkLt) = u := by simpa only [List.getElem_take] using heq
              exact (Nat.ne_of_lt hiLt) (hIn.qNd.eq_of_getElem_eq (Nat.lt_trans hiLt hkLt) hkLt (hqi.trans hqk.symm))
            have hremEq := remIndeg_append_singleton g (q.take k) u v huNotPre
            rw [← htakeK1] at hremEq
            have hdropOcc : countOccurrence v ((g.outArcs u).drop j) ≤ countOccurrence v (g.outArcs u) := by
              have happ : countOccurrence v ((g.outArcs u).take j ++ (g.outArcs u).drop j) =
                  countOccurrence v ((g.outArcs u).take j) + countOccurrence v ((g.outArcs u).drop j) := by
                induction (g.outArcs u).take j with
                | nil => simp [countOccurrence]
                | cons y ys ihy => simp [countOccurrence, ihy, Nat.add_assoc]
              have hEqArc : countOccurrence v (g.outArcs u) =
                  countOccurrence v ((g.outArcs u).take j ++ (g.outArcs u).drop j) := by
                rw [List.take_append_drop]
              rw [hEqArc, happ]
              omega
            have hCurLeRem : curDeg ≤ remIndeg g (q.take k) v := by
              change remIndeg g (q.take (k + 1)) v + countOccurrence v ((g.outArcs u).drop j) ≤ _
              omega
            have hRemLeInit : remIndeg g (q.take k) v ≤ Kahn.initialIndegree g v := by
              rw [← remIndeg_nil g v]
              unfold remIndeg
              have h1 : (List.ofFn (fun x : Fin g.vertexCount =>
                  if x ∈ q.take k then 0 else countOccurrence v (g.outArcs x))) =
                  (List.finRange g.vertexCount).map (fun x =>
                    if x ∈ q.take k then 0 else countOccurrence v (g.outArcs x)) := by
                apply List.ext_getElem <;> simp
              have h2 : (List.ofFn (fun x : Fin g.vertexCount =>
                  if x ∈ ([] : List (Fin g.vertexCount)) then 0 else countOccurrence v (g.outArcs x))) =
                  (List.finRange g.vertexCount).map (fun x =>
                    if x ∈ ([] : List (Fin g.vertexCount)) then 0 else countOccurrence v (g.outArcs x)) := by
                apply List.ext_getElem <;> simp
              rw [h1, h2]
              have hsumLe : ∀ (α : Type) (xs : List α) (f1 f2 : α → Nat),
                  (∀ x ∈ xs, f1 x ≤ f2 x) → (xs.map f1).sum ≤ (xs.map f2).sum := by
                intro α xs f1 f2 hf
                induction xs with
                | nil => simp
                | cons y ys ihy =>
                  simp only [List.map_cons, List.sum_cons]
                  exact Nat.add_le_add (hf y (by simp)) (ihy (fun z hz => hf z (by simp [hz])))
              exact hsumLe _ _ _ _ (fun x _ => by split <;> simp)
            have hmLe : Kahn.initialIndegree g v ≤ m := by
              rw [← countOccurrence_outTargetsList_eq_initialIndegree]
              have hc : ∀ (xs : List (Fin g.vertexCount)), countOccurrence v xs ≤ xs.length := by
                intro xs; induction xs with | nil => simp [countOccurrence] | cons x xs ixs => simp [countOccurrence]; split <;> omega
              exact Nat.le_trans (hc _) (by rw [outTargetsList_length]; dsimp only [m]; exact Nat.le_refl _)
            have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
          have hDegMem : u3.data[(reg u3 r13).val]? = some ⟨curDeg, hCurLt⟩ := by
            rw [h3d, h2d, h3_r13]
            have hOld := hIn.inDegs v
            cases hcell : st.data[v.val]? with
            | none => simp [hcell] at hOld
            | some w =>
              rw [hcell, Option.map_some] at hOld
              exact congrArg some (Fin.ext (Option.some.inj hOld))
          obtain ⟨u4, hs14, h4pc, h4v, h4o, h4d⟩ := step_loadData16 (input := input)
            (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) hDegMem
            (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
          have h4_r14 : (reg u4 r14).val = curDeg := by rw [h4v]
          have h4_one : (reg u4 rOne).val = 1 := by
            rw [h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          obtain ⟨u5, hs15, h5pc, h5v, h5o, h5d⟩ := step_sub16 (input := input)
            (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h5_r14 : (reg u5 r14).val = nextDeg := by
            rw [h5v, sub_exact _ _ (by rw [h4_r14, h4_one]; omega), h4_r14, h4_one]; omega
          have h5_r13 : (reg u5 r13).val = v.val := by
            rw [h5o _ (by decide), h4o _ (by decide), h3_r13]
          have h5Bound : (reg u5 r13).val < u5.data.size := by
            rw [u5.data_size, h5_r13]; change v.val < workCap
            unfold rawDagWorkCap at workRoom; exact Nat.lt_of_lt_of_le v.isLt (by omega)
          obtain ⟨u6, hs16, h6pc, h6regs, h6data⟩ := step_storeData16 (input := input)
            (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) h5Bound
          have h6_r14 : (reg u6 r14).val = nextDeg := by
            rw [reg_eq_of_regs_eq h6regs r14]; exact h5_r14
          have h6_one : (reg u6 rOne).val = 1 := by
            rw [reg_eq_of_regs_eq h6regs rOne, h5o _ (by decide)]; exact h4_one
          have h6_rN : (reg u6 rN).val = n := by
            rw [reg_eq_of_regs_eq h6regs rN, h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.nVal
          have h6_r5 : (reg u6 r5).val = q.length := by
            rw [reg_eq_of_regs_eq h6regs r5, h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.qTail
          have h6_r11 : (reg u6 r11).val = outPrefix g u.val + j := by
            rw [reg_eq_of_regs_eq h6regs r11, h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.edgeIdx
          have h6_r13 : (reg u6 r13).val = v.val := by
            rw [reg_eq_of_regs_eq h6regs r13]; exact h5_r13
          have hEdgeNextFit : outPrefix g u.val + j + 1 < 2 ^ bits := by
            have := raw.cap_ge; unfold rawDagInputCap at this
            have hle := outPrefix_mono g (Nat.succ_le_of_lt u.isLt)
            simp only [outPrefix] at hle
            have hm := Nat.le_trans hle (outPrefix_mono g (Nat.le_refl _))
            rw [outPrefix_vertexCount] at hm
            omega
          by_cases hNextZero : nextDeg = 0
          · have hvNotQ : v ∉ q := by
              rw [hIn.qZero v]
              change curDeg ≠ 0
              omega
            have hCmp17 : ltb (reg u6 r14) (reg u6 rOne) = true :=
              branchLt_true (by rw [h6_r14, h6_one, hNextZero]; decide)
            let u7 : State L16 := { u6 with pc := 18 }
            have hu7Pc : u7.pc = 18 := rfl
            have hf17 : code[u6.pc]? = some (.branchLt r14 rOne 18 21) := by
              rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
            have hs17 : step code input u6 = some (.next u7) := by
              simpa only [u7, hCmp17, ite_true] using
                step_branchLt_at (input := input) hf17 (by rw [hSz, hCmp17]; decide)
            have hQFit : n + q.length < workCap := by
              have hqle := nodup_length_le_fin q hIn.qNd
              unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
            have hQWordFit : (reg u7 rN).val + (reg u7 r5).val < 2 ^ bits := by
              change (reg u6 rN).val + (reg u6 r5).val < 2 ^ bits
              rw [h6_rN, h6_r5]; unfold rawDagWorkCap at workRoom; omega
            obtain ⟨u8, hs18, h8pc, h8v, h8o, h8d⟩ := step_add16 (input := input)
              (s := u7) (code := code) rfl (by rw [hSz, hu7Pc]; decide)
            have h8_r15 : (reg u8 r15).val = n + q.length := by
              rw [h8v, add_no_wrap _ _ hQWordFit]
              change (reg u6 rN).val + (reg u6 r5).val = _
              rw [h6_rN, h6_r5]
            have h8Bound : (reg u8 r15).val < u8.data.size := by
              rw [u8.data_size, h8_r15]; change n + q.length < workCap; exact hQFit
            obtain ⟨u9, hs19, h9pc, h9regs, h9data⟩ := step_storeData16 (input := input)
              (s := u8) (code := code) (by rw [h8pc, hu7Pc]; rfl) (by rw [hSz, h8pc, hu7Pc]; decide) h8Bound
            have h9_r5 : (reg u9 r5).val = q.length := by
              rw [reg_eq_of_regs_eq h9regs r5, h8o _ (by decide)]; exact h6_r5
            have h9_one : (reg u9 rOne).val = 1 := by
              rw [reg_eq_of_regs_eq h9regs rOne, h8o _ (by decide)]; exact h6_one
            obtain ⟨u10, hs20, h10pc, h10v, h10o, h10d⟩ := step_add16 (input := input)
              (s := u9) (code := code) (by rw [h9pc, h8pc, hu7Pc]; rfl)
              (by rw [hSz, h9pc, h8pc, hu7Pc]; decide)
            have h10_r11 : (reg u10 r11).val = outPrefix g u.val + j := by
              rw [h10o _ (by decide), reg_eq_of_regs_eq h9regs r11, h8o _ (by decide)]; exact h6_r11
            have h10_one : (reg u10 rOne).val = 1 := by
              rw [h10o _ (by decide)]; exact h9_one
            obtain ⟨u11, hs21, h11pc, h11v, h11o, h11d⟩ := step_add16 (input := input)
              (s := u10) (code := code) (by rw [h10pc, h9pc, h8pc, hu7Pc]; rfl)
              (by rw [hSz, h10pc, h9pc, h8pc, hu7Pc]; decide)
            let u12 : State L16 := { u11 with pc := 11 }
            have hs22 : step code input u11 = some (.next u12) :=
              step_goto_at (by rw [h11pc, h10pc, h9pc, h8pc, hu7Pc]; rfl) (by rw [hSz]; decide)
            have hKeep12 (regIdx : Fin 16) (hn5 : regIdx ≠ r5) (hn11 : regIdx ≠ r11)
                (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) (hn15 : regIdx ≠ r15) :
                reg u12 regIdx = reg st regIdx := by
              change reg u11 regIdx = reg st regIdx
              rw [h11o _ hn11, h10o _ hn5, reg_eq_of_regs_eq h9regs regIdx, h8o _ hn15]
              change reg u6 regIdx = reg st regIdx
              rw [reg_eq_of_regs_eq h6regs regIdx, h5o _ hn14, h4o _ hn14, h3o _ hn13, h2o _ hn13]
              rfl
            have h8_r13 : (reg u8 r13).val = v.val := by
              rw [h8o _ (by decide)]; exact h6_r13
            have hDataMid : u6.data = st.data.set v.val (reg u5 r14)
                (by rw [st.data_size]; change v.val < workCap; unfold rawDagWorkCap at workRoom; exact Nat.lt_of_lt_of_le v.isLt (by omega)) := by
              have h5DataEq : u5.data = st.data := by rw [h5d, h4d, h3d, h2d]
              simpa only [h5_r13, h5DataEq] using h6data
            have hData12 : u12.data = u6.data.set (n + q.length) (reg u8 r13)
                (by rw [u6.data_size]; exact hQFit) := by
              change u11.data = _
              rw [h11d, h10d]
              have h7Data : u7.data = u6.data := rfl
              simpa only [h8_r15, h8d, h7Data] using h9data
            have hqNextNd : (q ++ [v]).Nodup :=
              List.nodup_append.mpr ⟨hIn.qNd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
                fun a ha b hb he => by simp at hb; subst b; subst a; exact hvNotQ ha⟩
            have hTakeNext : (q ++ [v]).take (k + 1) = q.take (k + 1) := by
              rw [List.take_append_of_le_length hIn.hk1Le]
            have hQTailFit : q.length + 1 < 2 ^ bits := by
              have hqle := nodup_length_le_fin q hIn.qNd
              unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
            have hInNext : KahnInnerInv g r.val s₀.data k u (j + 1) (q ++ [v]) u12 := by
              refine ⟨rfl, ?_, hqNextNd, by have := hIn.hk1Le; simp; omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨(congrArg Fin.val (hKeep12 rZero (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.zero,
                  (congrArg Fin.val (hKeep12 rOne (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.one,
                  (congrArg Fin.val (hKeep12 rN (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.nVal,
                  (congrArg Fin.val (hKeep12 rM (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.mVal,
                  (congrArg Fin.val (hKeep12 rRoot (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.rootVal⟩
              · rw [List.getElem_append_left (by have := hIn.hk1Le; omega : k < q.length)]; exact hIn.huAt
              · change (reg u11 r5).val = (q ++ [v]).length
                rw [h11o _ (by decide), h10v, add_no_wrap _ _ (by rw [h9_r5, h9_one]; exact hQTailFit),
                  h9_r5, h9_one]
                simp
              · exact (congrArg Fin.val (hKeep12 r6 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.qHead
              · exact (congrArg Fin.val (hKeep12 r7 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.offBase
              · exact (congrArg Fin.val (hKeep12 r8 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.tgtBase
              · change (reg u11 r11).val = outPrefix g u.val + (j + 1)
                rw [h11v, add_no_wrap _ _ (by rw [h10_r11, h10_one]; exact hEdgeNextFit), h10_r11, h10_one]
                omega
              · exact (congrArg Fin.val (hKeep12 r12 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hIn.edgeEnd
              · intro i hi
                rw [hData12]
                by_cases hiLast : i = q.length
                · subst i
                  dsimp only [n]
                  rw [Array.getElem?_set_self, Option.map_some, h8_r13]
                  simp
                · have hiLt : i < q.length := by simp at hi; omega
                  rw [Array.getElem?_set_ne _ (by dsimp only [n]; omega), hDataMid,
                    Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n]; omega),
                    List.getElem_append_left hiLt]
                  exact hIn.qMem i hiLt
              · intro w
                rw [hData12, Array.getElem?_set_ne _ (by have := w.isLt; dsimp only [n]; omega),
                  hDataMid, hTakeNext]
                by_cases hwv : w = v
                · subst w
                  rw [Array.getElem?_set_self, Option.map_some, h5_r14]
                · have hne : w.val ≠ v.val := fun h => hwv (Fin.ext h)
                  rw [Array.getElem?_set_ne _ hne.symm]
                  have hOld := hIn.inDegs w
                  have hSameOcc : countOccurrence w ((g.outArcs u).drop j) =
                      countOccurrence w ((g.outArcs u).drop (j + 1)) := by
                    rw [hDropSplit]; simp [countOccurrence, Ne.symm hwv]
                  rw [← hSameOcc]; exact hOld
              · intro w
                rw [hTakeNext, List.mem_append, List.mem_singleton]
                by_cases hwv : w = v
                · subst w
                  dsimp only [nextDeg] at hNextZero
                  exact iff_of_true (Or.inr rfl) (by omega)
                · have hSameOcc : countOccurrence w ((g.outArcs u).drop j) =
                      countOccurrence w ((g.outArcs u).drop (j + 1)) := by
                    rw [hDropSplit]; simp [countOccurrence, Ne.symm hwv]
                  rw [← hSameOcc]
                  simpa [hwv] using hIn.qZero w
              · rw [hTakeNext]; exact hIn.topo
              · intro idx hidx
                have hqle := nodup_length_le_fin (q ++ [v]) hqNextNd
                simp only [List.length_append, List.length_singleton] at hqle
                rw [hData12, Array.getElem?_set_ne _ (by dsimp only [n] at hidx hqle ⊢; omega),
                  hDataMid, Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n] at hidx ⊢; omega)]
                exact hIn.frame idx hidx
            have hSteps12 : Steps code input 12 st u12 :=
              Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
                (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18
                  (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21 (Steps.cons hs22 (Steps.zero u12))))))))))))
            obtain ⟨qEnd, stEnd, tailSteps, hTailLe, hTailSteps, hPost⟩ :=
              ih (j + 1) (q ++ [v]) u12 (by omega) hInNext
            rcases hPost with ⟨hp1, hp2, hp3, hp4, hpTake, hpRest⟩
            exact ⟨qEnd, stEnd, 12 + tailSteps, by omega, hSteps12.append hTailSteps,
              hp1, hp2, hp3, hp4, hpTake.trans hTakeNext, hpRest⟩
          · have hPos : 1 ≤ nextDeg := Nat.pos_of_ne_zero hNextZero
            have hCmp17 : ltb (reg u6 r14) (reg u6 rOne) = false :=
              branchLt_false (by rw [h6_r14, h6_one]; exact hPos)
            let u7 : State L16 := { u6 with pc := 21 }
            have hu7Pc : u7.pc = 21 := rfl
            have hf17 : code[u6.pc]? = some (.branchLt r14 rOne 18 21) := by
              rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
            have hs17 : step code input u6 = some (.next u7) := by
              simpa only [u7, hCmp17, Bool.false_eq_true, ite_false] using
                step_branchLt_at (input := input) hf17 (by rw [hSz, hCmp17]; decide)
            have h7_r11 : (reg u7 r11).val = outPrefix g u.val + j := h6_r11
            have h7_one : (reg u7 rOne).val = 1 := h6_one
            obtain ⟨u8, hs21, h8pc, h8v, h8o, h8d⟩ := step_add16 (input := input)
              (s := u7) (code := code) rfl (by rw [hSz, hu7Pc]; decide)
            let u9 : State L16 := { u8 with pc := 11 }
            have hs22 : step code input u8 = some (.next u9) :=
              step_goto_at (by rw [h8pc, hu7Pc]; rfl) (by rw [hSz]; decide)
            have hKeep9 (regIdx : Fin 16) (hn11 : regIdx ≠ r11)
                (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) :
                reg u9 regIdx = reg st regIdx := by
              change reg u8 regIdx = reg st regIdx
              rw [h8o _ hn11]
              change reg u6 regIdx = reg st regIdx
              rw [reg_eq_of_regs_eq h6regs regIdx, h5o _ hn14, h4o _ hn14, h3o _ hn13, h2o _ hn13]
              rfl
            have hData9 : u9.data = st.data.set v.val (reg u5 r14)
                (by rw [st.data_size]; change v.val < workCap; unfold rawDagWorkCap at workRoom; exact Nat.lt_of_lt_of_le v.isLt (by omega)) := by
              change u8.data = _
              rw [h8d]
              have h5DataEq : u5.data = st.data := by rw [h5d, h4d, h3d, h2d]
              simpa only [h5_r13, h5DataEq] using h6data
            have hInNext : KahnInnerInv g r.val s₀.data k u (j + 1) q u9 := by
              refine ⟨rfl, ?_, hIn.qNd, hIn.hk1Le, hIn.huAt, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hIn.topo, ?_⟩
              · exact ⟨(congrArg Fin.val (hKeep9 rZero (by decide) (by decide) (by decide))).trans hIn.consts.zero,
                  (congrArg Fin.val (hKeep9 rOne (by decide) (by decide) (by decide))).trans hIn.consts.one,
                  (congrArg Fin.val (hKeep9 rN (by decide) (by decide) (by decide))).trans hIn.consts.nVal,
                  (congrArg Fin.val (hKeep9 rM (by decide) (by decide) (by decide))).trans hIn.consts.mVal,
                  (congrArg Fin.val (hKeep9 rRoot (by decide) (by decide) (by decide))).trans hIn.consts.rootVal⟩
              · exact (congrArg Fin.val (hKeep9 r5 (by decide) (by decide) (by decide))).trans hIn.qTail
              · exact (congrArg Fin.val (hKeep9 r6 (by decide) (by decide) (by decide))).trans hIn.qHead
              · exact (congrArg Fin.val (hKeep9 r7 (by decide) (by decide) (by decide))).trans hIn.offBase
              · exact (congrArg Fin.val (hKeep9 r8 (by decide) (by decide) (by decide))).trans hIn.tgtBase
              · change (reg u8 r11).val = outPrefix g u.val + (j + 1)
                rw [h8v, add_no_wrap _ _ (by rw [h7_r11, h7_one]; exact hEdgeNextFit), h7_r11, h7_one]
                omega
              · exact (congrArg Fin.val (hKeep9 r12 (by decide) (by decide) (by decide))).trans hIn.edgeEnd
              · intro i hi
                rw [hData9, Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n]; omega)]
                exact hIn.qMem i hi
              · intro w
                rw [hData9]
                by_cases hwv : w = v
                · subst w
                  rw [Array.getElem?_set_self, Option.map_some, h5_r14]
                · have hne : w.val ≠ v.val := fun h => hwv (Fin.ext h)
                  rw [Array.getElem?_set_ne _ hne.symm]
                  have hSameOcc : countOccurrence w ((g.outArcs u).drop j) =
                      countOccurrence w ((g.outArcs u).drop (j + 1)) := by
                    rw [hDropSplit]; simp [countOccurrence, Ne.symm hwv]
                  rw [← hSameOcc]; exact hIn.inDegs w
              · intro w
                by_cases hwv : w = v
                · subst w
                  have hMemW : v ∈ q ↔ curDeg = 0 := hIn.qZero v
                  have hFalse : ¬ v ∈ q := by rw [hMemW]; omega
                  have hFalse2 : ¬ nextDeg = 0 := hNextZero
                  exact iff_of_false hFalse hFalse2
                · have hSameOcc : countOccurrence w ((g.outArcs u).drop j) =
                      countOccurrence w ((g.outArcs u).drop (j + 1)) := by
                    rw [hDropSplit]; simp [countOccurrence, Ne.symm hwv]
                  rw [← hSameOcc]; exact hIn.qZero w
              · intro idx hidx
                rw [hData9, Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n] at hidx ⊢; omega)]
                exact hIn.frame idx hidx
            have hSteps9 : Steps code input 9 st u9 :=
              Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
                (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs21
                  (Steps.cons hs22 (Steps.zero u9)))))))))
            obtain ⟨qEnd, stEnd, tailSteps, hTailLe, hTailSteps, hPost⟩ :=
              ih (j + 1) q u9 (by omega) hInNext
            exact ⟨qEnd, stEnd, 9 + tailSteps, by omega, hSteps9.append hTailSteps, hPost⟩
        · have hjEq : j = (g.outArcs u).length := by have := hIn.hjLe; omega
          have hCmp : ltb (reg st r11) (reg st r12) = false :=
            branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
          have hf11 : code[st.pc]? = some (.branchLt r11 r12 12 23) := by rw [hIn.pc]; rfl
          let stEnd : State L16 := { st with pc := 23 }
          have hs11 : step code input st = some (.next stEnd) := by
            simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
              step_branchLt_at (input := input) hf11 (by rw [hSz, hCmp]; decide)
          have hDrop : (g.outArcs u).drop j = [] := by rw [hjEq]; exact List.drop_length
          refine ⟨q, stEnd, 1, by omega, Steps.cons hs11 (Steps.zero stEnd),
            rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
            hIn.qNd, hIn.hk1Le, rfl, hIn.qTail, hIn.qHead, hIn.offBase, hIn.tgtBase,
            hIn.qMem, ?_, ?_, hIn.topo, hIn.frame⟩
          · intro v; simpa only [hDrop, countOccurrence, Nat.add_zero] using hIn.inDegs v
          · intro v; simpa only [hDrop, countOccurrence, Nat.add_zero] using hIn.qZero v
    simpa only [Nat.sub_zero] using hInnerAux (g.outArcs u).length 0 qStart st0 (Nat.le_refl _) hIn0
  -- Outer loop using `while_steps_budget`
  let OuterState := Σ k : Nat, List (Fin n)
  let OuterInv (p : OuterState) (s : State L16) : Prop :=
    p.1 ≤ n ∧ KahnOuterInv g r.val s₀.data p.1 p.2 s
  let OuterMeas (p : OuterState) : Nat := n - p.1
  let OuterBudget (p : OuterState) : Nat :=
    10 * (n - p.1) + 12 * (m - processedArcsCount g (p.2.take p.1)) + 2
  let OuterPost (_ : OuterState) (t : State L16) : Prop :=
    ∃ (order : List (Fin n)) (hlen : order.length = n),
      ConstRegs n m r.val t ∧ g.IsTopologicalList order ∧
      (∀ i : Nat, (hi : i < n) →
        (t.data[topoOrderBase n m + i]?).map Fin.val = some (order[i]'(by rw [hlen]; exact hi)).val) ∧
      (∀ j, 2 * n ≤ j → t.data[j]? = s₀.data[j]?)
  have hOuterStep : ∀ p st, OuterInv p st →
      (∃ t, OuterPost p t ∧ ∃ kSteps, kSteps ≤ OuterBudget p ∧
        run code input kSteps st = some ⟨t, kSteps⟩) ∨
      (∃ p' st' kSteps, OuterMeas p' < OuterMeas p ∧
        kSteps + OuterBudget p' ≤ OuterBudget p ∧
        Steps code input kSteps st st' ∧ OuterInv p' st') := by
    rintro ⟨k, q⟩ st ⟨hkN, hOut⟩
    dsimp only [OuterInv] at hkN hOut
    by_cases hk : k < q.length
    · right
      have hCmp : ltb (reg st r6) (reg st r5) = true :=
        branchLt_true (by rw [hOut.qHead, hOut.qTail]; exact hk)
      have hf4 : code[st.pc]? = some (.branchLt r6 r5 5 25) := by rw [hOut.pc]; rfl
      let u1 : State L16 := { st with pc := 5 }
      have hu1Pc : u1.pc = 5 := rfl
      have hs4 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp]; decide)
      have hQAddrFit : (reg u1 rN).val + (reg u1 r6).val < 2 ^ bits := by
        change (reg st rN).val + (reg st r6).val < 2 ^ bits
        have hqle := nodup_length_le_fin q hOut.qNd
        rw [hOut.consts.nVal, hOut.qHead]; unfold rawDagWorkCap at workRoom; omega
      obtain ⟨u2, hs5, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r9 : (reg u2 r9).val = n + k := by
        rw [h2v, add_no_wrap _ _ hQAddrFit]
        change (reg st rN).val + (reg st r6).val = _
        rw [hOut.consts.nVal, hOut.qHead]
      let u : Fin n := q[k]'hk
      have huMem : u2.data[(reg u2 r9).val]? = some ⟨u.val, by
          have := raw.cap_ge; unfold rawDagInputCap at this; have := u.isLt; dsimp only [n] at *; omega⟩ := by
        rw [h2_r9, h2d]
        change st.data[n + k]? = _
        have hqm := hOut.qMem k hk
        dsimp only [n]
        cases hcell : st.data[g.vertexCount + k]? with
        | none => simp [hcell] at hqm
        | some w =>
          rw [hcell, Option.map_some] at hqm
          exact congrArg some (Fin.ext (Option.some.inj hqm))
      obtain ⟨u3, hs6, h3pc, h3v, h3o, h3d⟩ := step_loadData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) huMem
        (by rw [hSz, h2pc, hu1Pc]; decide)
      have h3_r9 : (reg u3 r9).val = u.val := by rw [h3v]
      have h3_r7 : (reg u3 r7).val = 3 := by
        rw [h3o _ (by decide), h2o _ (by decide)]; exact hOut.offBase
      have hOffAddrFit : (reg u3 r7).val + (reg u3 r9).val < 2 ^ bits := by
        rw [h3_r7, h3_r9]; have := u.isLt; have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      obtain ⟨u4, hs7, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
      have h4_r10 : (reg u4 r10).val = 3 + u.val := by
        rw [h4v, add_no_wrap _ _ hOffAddrFit, h3_r7, h3_r9]
      have hOffStartFit : outPrefix g u.val < 2 ^ bits := by
        have := outPrefix_mono g (Nat.le_of_lt u.isLt); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff0 : input.words[(reg u4 r10).val]? = some ⟨outPrefix g u.val, hOffStartFit⟩ := by
        rw [h4_r10]
        have ho := raw.out_off u.val (Nat.le_of_lt u.isLt)
        cases hcell : input.words[3 + u.val]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u5, hs8, h5pc, h5v, h5o, h5d⟩ := step_loadInput16 (input := input)
        (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff0
      have h5_r10 : (reg u5 r10).val = 3 + u.val := by
        rw [h5o _ (by decide)]; exact h4_r10
      have h5_one : (reg u5 rOne).val = 1 := by
        rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
        exact hOut.consts.one
      have hOffAddr2Fit : (reg u5 r10).val + (reg u5 rOne).val < 2 ^ bits := by
        rw [h5_r10, h5_one]; have := u.isLt; have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      obtain ⟨u6, hs9, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
        (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h6_r10 : (reg u6 r10).val = 3 + (u.val + 1) := by
        rw [h6v, add_no_wrap _ _ hOffAddr2Fit, h5_r10, h5_one]; omega
      have hOffEndFit : outPrefix g (u.val + 1) < 2 ^ bits := by
        have := outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff1 : input.words[(reg u6 r10).val]? = some ⟨outPrefix g (u.val + 1), hOffEndFit⟩ := by
        rw [h6_r10]
        have ho := raw.out_off (u.val + 1) (by omega)
        cases hcell : input.words[3 + (u.val + 1)]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u7, hs10, h7pc, h7v, h7o, h7d⟩ := step_loadInput16 (input := input)
        (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff1
      have hKeep7 (regIdx : Fin 16) (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10)
          (hn11 : regIdx ≠ r11) (hn12 : regIdx ≠ r12) : reg u7 regIdx = reg st regIdx := by
        rw [h7o _ hn12, h6o _ hn10, h5o _ hn11, h4o _ hn10, h3o _ hn9, h2o _ hn9]
        rfl
      have hData7 : u7.data = st.data := by
        rw [h7d, h6d, h5d, h4d, h3d, h2d]
      have htakeK1 : q.take (k + 1) = q.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
      have huNotPre : u ∉ q.take k := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
        have hiLt : i < k := by simp only [List.length_take] at hi; omega
        have hqi : q[i]'(by omega) = u := by simpa only [List.getElem_take] using heq
        exact (Nat.ne_of_lt hiLt) (hOut.qNd.eq_of_getElem_eq (by omega) hk hqi)
      have hTopo1 : (q.take (k + 1)).Pairwise (fun a b => ¬ g.HasArc b a) := by
        rw [htakeK1, List.pairwise_append]
        refine ⟨hOut.topo, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb harc
        simp at hb; subst b
        have haQ : a ∈ q := List.take_subset k q ha
        have hza : remIndeg g (q.take k) a = 0 := (hOut.qZero a).mp haQ
        exact (remIndeg_eq_zero_iff g (q.take k) a).mp hza u huNotPre harc
      have hIn0 : KahnInnerInv g r.val s₀.data k u 0 q u7 := by
        refine ⟨by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc], ?_, hOut.qNd, hk, rfl,
          Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTopo1, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeep7 rZero (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.zero,
            (congrArg Fin.val (hKeep7 rOne (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.one,
            (congrArg Fin.val (hKeep7 rN (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.nVal,
            (congrArg Fin.val (hKeep7 rM (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.mVal,
            (congrArg Fin.val (hKeep7 rRoot (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.rootVal⟩
        · exact (congrArg Fin.val (hKeep7 r5 (by decide) (by decide) (by decide) (by decide))).trans hOut.qTail
        · exact (congrArg Fin.val (hKeep7 r6 (by decide) (by decide) (by decide) (by decide))).trans hOut.qHead
        · exact (congrArg Fin.val (hKeep7 r7 (by decide) (by decide) (by decide) (by decide))).trans hOut.offBase
        · exact (congrArg Fin.val (hKeep7 r8 (by decide) (by decide) (by decide) (by decide))).trans hOut.tgtBase
        · rw [h7o _ (by decide), h6o _ (by decide), h5v, Nat.add_zero]
        · exact (congrArg Fin.val h7v).trans (outPrefix_succ_lt g u)
        · intro i hi; rw [hData7]; exact hOut.qMem i hi
        · intro v
          rw [hData7, List.drop_zero, htakeK1, ← remIndeg_append_singleton g (q.take k) u v huNotPre]
          exact hOut.inDegs v
        · intro v
          rw [List.drop_zero, htakeK1, ← remIndeg_append_singleton g (q.take k) u v huNotPre]
          exact hOut.qZero v
        · intro idx hidx; rw [hData7]; exact hOut.frame idx hidx
      obtain ⟨qEnd, st23, innerSteps, hInnerLe, hInnerSteps, hPost⟩ := run_inner k u u7 q hIn0
      rcases hPost with ⟨h23pc, h23consts, h23nd, h23hk1, h23take, h23tail, h23head, h23off, h23tgt,
        h23mem, h23indeg, h23zero, h23topo, h23frame⟩
      have h23_r6 : (reg st23 r6).val = k := h23head
      have h23_one : (reg st23 rOne).val = 1 := h23consts.one
      have hk1Fit : k + 1 < 2 ^ bits := by
        have hqle := nodup_length_le_fin qEnd h23nd
        have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      obtain ⟨st24, hs23, h24pc, h24v, h24o, h24d⟩ := step_add16 (input := input)
        (s := st23) (code := code) (by rw [h23pc]; rfl) (by rw [hSz, h23pc]; decide)
      let stNext : State L16 := { st24 with pc := 4 }
      have hs24 : step code input st24 = some (.next stNext) :=
        step_goto_at (code := code) (by rw [h24pc, h23pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn6 : regIdx ≠ r6) : reg stNext regIdx = reg st23 regIdx :=
        h24o regIdx hn6
      have hDataNext : stNext.data = st23.data := h24d
      have hOutNext : KahnOuterInv g r.val s₀.data (k + 1) qEnd stNext := by
        refine ⟨rfl, ?_, h23nd, h23hk1, ?_, ?_, ?_, ?_, ?_, ?_, h23zero, h23topo, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide))).trans h23consts.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide))).trans h23consts.one,
            (congrArg Fin.val (hKeepNext rN (by decide))).trans h23consts.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide))).trans h23consts.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide))).trans h23consts.rootVal⟩
        · exact (congrArg Fin.val (hKeepNext r5 (by decide))).trans h23tail
        · change (reg st24 r6).val = k + 1
          rw [h24v, add_no_wrap _ _ (by rw [h23_r6, h23_one]; exact hk1Fit), h23_r6, h23_one]
        · exact (congrArg Fin.val (hKeepNext r7 (by decide))).trans h23off
        · exact (congrArg Fin.val (hKeepNext r8 (by decide))).trans h23tgt
        · intro i hi; rw [hDataNext]; exact h23mem i hi
        · intro v; rw [hDataNext]; exact h23indeg v
        · intro idx hidx; rw [hDataNext]; exact h23frame idx hidx
      have hPref7 : Steps code input 7 st u7 :=
        Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7
          (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.zero u7)))))))
      have hTail2 : Steps code input 2 st23 stNext :=
        Steps.cons hs23 (Steps.cons hs24 (Steps.zero stNext))
      have hAllSteps : Steps code input (7 + innerSteps + 2) st stNext :=
        (hPref7.append hInnerSteps).append hTail2
      have hTakeQEnd : qEnd.take (k + 1) = q.take k ++ [u] :=
        h23take.trans htakeK1
      have hArcInc : processedArcsCount g (qEnd.take (k + 1)) =
          processedArcsCount g (q.take k) + (g.outArcs u).length := by
        dsimp only [n] at hTakeQEnd
        rw [hTakeQEnd, processedArcsCount_append]
      have hArcLe : processedArcsCount g (qEnd.take (k + 1)) ≤ m :=
        processedArcsCount_le g (qEnd.take (k + 1)) (h23nd.sublist (List.take_sublist _ _))
      have hk1LeN : k + 1 ≤ n := by
        have := nodup_length_le_fin qEnd h23nd
        dsimp only [n] at *; omega
      refine ⟨⟨k + 1, qEnd⟩, stNext, 7 + innerSteps + 2, by dsimp only [OuterMeas]; omega,
        by dsimp only [OuterBudget]; omega, hAllSteps, hk1LeN, hOutNext⟩
    · left
      have hkEq : k = q.length := by have := hOut.hkLe; omega
      have hCmp : ltb (reg st r6) (reg st r5) = false :=
        branchLt_false (by rw [hOut.qHead, hOut.qTail, hkEq]; exact Nat.le_refl _)
      have hf4 : code[st.pc]? = some (.branchLt r6 r5 5 25) := by rw [hOut.pc]; rfl
      let t : State L16 := { st with pc := 25 }
      have hs4 : step code input st = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 st = some ⟨t, 2⟩ :=
        (Steps.cons hs4 (Steps.zero t)).halts hHalt
      have hTakeAll : q.take k = q := by rw [hkEq, List.take_length]
      have hZeroQ : ∀ v : Fin n, v ∈ q ↔ remIndeg g q v = 0 := fun v => by
        have := hOut.qZero v; rw [hTakeAll] at this; exact this
      have hTopoQ : q.Pairwise (fun a b => ¬ g.HasArc b a) := by
        have := hOut.topo; rw [hTakeAll] at this; exact this
      have hTopo : g.IsTopologicalList q :=
        kahn_complete_of_acyclic g acyc q hOut.qNd hZeroQ hTopoQ
      have hLen : q.length = n := nodup_cover_length q hOut.qNd hTopo.2.1
      refine ⟨t, ⟨q, hLen, ⟨hOut.consts.zero, hOut.consts.one, hOut.consts.nVal, hOut.consts.mVal,
          hOut.consts.rootVal⟩, hTopo, ?_, hOut.frame⟩, 2, by dsimp only [OuterBudget]; omega, hRun2⟩
      intro i hi
      simpa only [topoOrderBase_eq] using hOut.qMem i (by omega)
  obtain ⟨pEnd, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget OuterInv OuterMeas OuterBudget OuterPost hOuterStep n ⟨0, q0⟩ t4
      (Nat.le_refl _) ⟨Nat.zero_le _, hOuter0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt
    rw [sameHalt]
    exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨order, hLenEnd, hConstsEnd, hTopoEnd, hMemEnd, hFrameEnd⟩
  refine ⟨tEnd, 4 + loopSteps, order, hLenEnd, ?_, hExec, hConstsEnd, hTopoEnd, hMemEnd, hFrameEnd⟩
  dsimp only [OuterBudget, OuterMeas] at hLoopLe
  omega

end Phase1KahnBfs

end PaperB.RamDagReach
