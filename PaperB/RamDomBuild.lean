module

public import PaperB.RamForestDepthSeek
public import PaperB.DomPredecessorFold
public import PaperB.FullDomScan
public import PaperB.ConcreteDomOps
public import PaperB.OracleContract

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 Phase B2 (Part 1): 15-register Word-RAM dynamic skew-binary dominator
builder (`domBuildPhase` / `domBuildProgram`).

Reads `DenseIncomingSpec` from read-only `input.words`:
- `word 0`: `Q = qCount` (`1 ≤ Q`, root = `0`)
- `word 1`: `mReach`
- `[2 .. 2 + Q + 1)`: monotone `inStart[0..Q]` (`inStart[0] = 0`, `inStart[Q] = mReach`,
  with `inStart[v] < inStart[v + 1]` for all `1 ≤ v < Q`)
- `[3 + Q .. 3 + Q + mReach)`: `inSrc[0..mReach - 1]` (with every `u ∈ [inStart[v], inStart[v+1])`
  satisfying `u < v`).

Writes to `data` (using `registerCount = 15` and only `[0 .. 5 * Q + 10)` work words):
- `[0 .. Q)`: `domParent` (`domParent[0] = 0`, exact immediate dominator matching `Digraph.IsImmediateDominator`)
- `[Q .. 2 * Q)`: `domDepth` (`ValidDepthTree 0 domParent domDepth`)
- `[2 * Q .. 5 * Q)`: stride-3 `JumpForest` records (`Records (2 * Q) F data`, `ValidJumpForest F`)

Complexity: `O((Q + mReach) * L^2)` instructions (`L = OracleContract.L Q`), peak words
`inputCap + workCap + 15`.
-/

namespace PaperB.RamDomBuild

open PaperB
open PaperB.Digraph
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.DepthSeek
open PaperB.Jumps
open PaperB.LabelledQuotient (ValidDepthTree)

section StepHelpers

variable {bits : Nat} {L : Layout bits}

theorem sub_exact_word (x y : Word bits) (hle : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hx := x.isLt
  have hlt : x.val - y.val < 2 ^ bits := by omega
  rw [sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

private def putReg {bits : Nat} {L : Layout bits}
    (s : State L) (d : Fin L.registerCount) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_putReg {bits : Nat} {L : Layout bits}
    (s : State L) (d r : Fin L.registerCount) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp
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
  · intro r hr
    simp [reg_putReg, hr]

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
  · intro r hr
    simp [reg_putReg, hr]

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
  · intro r hr
    simp [reg_putReg, hr]

theorem step_storeData_at {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.storeData addr src))
    (hfit : (reg s addr).val < s.data.size)
    (hn : s.pc + 1 < code.size) :
    let t : State L :=
      { s with
        data := s.data.set (reg s addr).val (reg s src) hfit
        pc := s.pc + 1
        data_size := by simp only [Array.size_set, s.data_size] }
    step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧
      t.data = s.data.set (reg s addr).val (reg s src) hfit := by
  intro t
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold step
  rw [hf]
  change (if h : (reg s addr).val < s.data.size then
    if s.pc + 1 < code.size then
      some (Transition.next
        { s with
          data := s.data.set (reg s addr).val (reg s src) h
          pc := s.pc + 1
          data_size := by simp only [Array.size_set, s.data_size] })
    else none
    else none) = _
  rw [dite_eq_left hfit]
  exact ite_eq_left hn

end StepHelpers

section DenseSpec

/-- Input specification for the `EX5.1 Phase B2` dense reachable DAG in `input.words`. -/
structure DenseIncomingSpec {bits : Nat} {L : Layout bits}
    (input : Input L) (Q mReach : Nat) (inStart inSrc : Nat → Nat) : Prop where
  qPos : 1 ≤ Q
  inBounds : 3 + Q + mReach ≤ L.inputCap
  workBounds : 5 * Q + 10 ≤ L.workCap
  word0 : input.words[0]?.map Fin.val = some Q
  word1 : input.words[1]?.map Fin.val = some mReach
  startZero : inStart 0 = 0
  startEnd : inStart Q = mReach
  startMono : ∀ v, v < Q → inStart v ≤ inStart (v + 1)
  nonemptyRow : ∀ v, 1 ≤ v → v < Q → inStart v < inStart (v + 1)
  srcPred : ∀ v k, 1 ≤ v → v < Q → inStart v ≤ k → k < inStart (v + 1) → inSrc k < v
  startCell : ∀ i, i ≤ Q → input.words[2 + i]?.map Fin.val = some (inStart i)
  srcCell : ∀ k, k < mReach → input.words[3 + Q + k]?.map Fin.val = some (inSrc k)

theorem denseIncoming_inStart_le {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) :
    ∀ i j, i ≤ j → j ≤ Q → inStart i ≤ inStart j := by
  intro i j hij hj
  have aux : ∀ d, i + d ≤ Q → inStart i ≤ inStart (i + d) := by
    intro d
    induction d with
    | zero => intro _; exact Nat.le_refl _
    | succ d ih =>
      intro hd
      exact Nat.le_trans (ih (by omega)) (sp.startMono (i + d) (by omega))
  have hEq : i + (j - i) = j := by omega
  simpa only [hEq] using aux (j - i) (by omega)

/-- Outgoing adjacency list of `u` into heads `> u` extracted from `(inStart, inSrc)`. -/
def denseOutAdj (Q : Nat) (inStart inSrc : Nat → Nat) (u : Nat) :
    List (Fin Q) :=
  (List.finRange Q).filter fun v =>
    decide (1 ≤ v.val) &&
      (List.range (inStart (v.val + 1) - inStart v.val)).any fun off =>
        decide (inSrc (inStart v.val + off) = u)

/-- Canonical `Digraph` on `0..Q-1` corresponding to `(inStart, inSrc)`. -/
def denseDigraph (Q : Nat) (inStart inSrc : Nat → Nat) : Digraph where
  vertexCount := Q
  adj := Array.ofFn (fun u : Fin Q => denseOutAdj Q inStart inSrc u.val)
  adj_size := by simp

theorem denseDigraph_hasArc_iff (Q : Nat) (inStart inSrc : Nat → Nat)
    (u v : Fin Q) :
    (denseDigraph Q inStart inSrc).HasArc u v ↔
      1 ≤ v.val ∧ ∃ k, inStart v.val ≤ k ∧ k < inStart (v.val + 1) ∧ inSrc k = u.val := by
  unfold Digraph.HasArc Digraph.outArcs denseDigraph
  simp [denseOutAdj]
  intro _
  constructor
  · rintro ⟨off, hoff, hEq⟩
    exact ⟨inStart v.val + off, Nat.le_add_right _ _, by omega, hEq⟩
  · rintro ⟨k, hkLo, hkHi, hEq⟩
    exact ⟨k - inStart v.val, by omega, by rwa [Nat.add_sub_cancel' hkLo]⟩

theorem denseDigraph_progress {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) :
    ∀ u v : Fin Q,
      (denseDigraph Q inStart inSrc).HasArc u v → u.val < v.val := by
  intro u v huv
  obtain ⟨hv1, k, hkLo, hkHi, hSrc⟩ := (denseDigraph_hasArc_iff Q inStart inSrc u v).mp huv
  rw [← hSrc]
  exact sp.srcPred v.val k hv1 v.isLt hkLo hkHi

theorem denseDigraph_initiallyReachable {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) :
    let g := denseDigraph Q inStart inSrc
    let r : Fin Q := ⟨0, sp.qPos⟩
    ∀ v : Fin Q, g.InitiallyReachable r v := by
  intro g r v
  have aux : ∀ n : Nat, ∀ v : Fin Q, v.val ≤ n →
      g.InitiallyReachable r v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hv0 : v = r := Fin.ext (by change v.val = 0; omega)
      subst v
      exact AvoidPath.refl r not_false
    | succ n ih =>
      intro v hv
      by_cases hv0 : v.val = 0
      · have he : v = r := Fin.ext hv0
        subst v
        exact AvoidPath.refl r not_false
      · have hv1 : 1 ≤ v.val := Nat.pos_of_ne_zero hv0
        have hlt : inStart v.val < inStart (v.val + 1) := sp.nonemptyRow v.val hv1 v.isLt
        let k := inStart v.val
        have huLt : inSrc k < v.val := sp.srcPred v.val k hv1 v.isLt (Nat.le_refl k) hlt
        let u : Fin Q := ⟨inSrc k, Nat.lt_trans huLt v.isLt⟩
        have hReachU : g.InitiallyReachable r u := ih u (by change inSrc k ≤ n; omega)
        have hArc : g.HasArc u v :=
          (denseDigraph_hasArc_iff Q inStart inSrc u v).mpr ⟨hv1, k, Nat.le_refl k, hlt, rfl⟩
        exact AvoidPath.trans hReachU
          (AvoidPath.step u v v not_false hArc (AvoidPath.refl v not_false))
  exact aux v.val v (Nat.le_refl _)

theorem denseDigraph_root_dom {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) :
    let g := denseDigraph Q inStart inSrc
    let r : Fin Q := ⟨0, sp.qPos⟩
    ∀ d : Fin Q, g.Dominates r d r ↔ d = r := by
  intro g r d
  constructor
  · intro hd
    by_cases hdr : r = d
    · exact hdr.symm
    · have hc := hd (AvoidPath.refl r hdr)
      exact hc.elim
  · intro hd
    subst d
    exact dominates_refl

/-- Semantic dominator invariant on prefix `0 .. bound - 1` (`1 ≤ bound ≤ Q`) with
jump forest `F` (`F.size = bound`). -/
structure DomPrefixInv {bits : Nat} {L : Layout bits}
    (input : Input L) (Q mReach : Nat) (inStart inSrc : Nat → Nat)
    (bound : Nat) (F : JumpForest) (data : Array (Word bits)) : Prop where
  boundPos : 1 ≤ bound
  valid : ValidJumpForest F
  size_eq : F.size = bound
  records : Records (2 * Q) F data
  domParent : ∀ u < bound, (data[u]?).map Fin.val = some (F.parentOf u)
  domDepth : ∀ u < bound, (data[Q + u]?).map Fin.val = some (F.depthOf u)
  domSem : ∀ (hQ : 0 < Q) (x a : Fin Q), x.val < bound → a.val < bound →
    ((denseDigraph Q inStart inSrc).Dominates ⟨0, hQ⟩ a x ↔
      IsAncestor F a.val x.val)

private theorem avoidPath_val_le {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {avoid : Fin Q → Prop} {a b : Fin Q}
    (hp : AvoidPath (denseDigraph Q inStart inSrc).HasArc avoid a b) :
    a.val ≤ b.val := by
  induction hp with
  | refl _ _ => exact Nat.le_refl _
  | @step x y _ _ hxy _ ih =>
    have hlt : x.val < y.val := denseDigraph_progress sp x y hxy
    exact Nat.le_trans (Nat.le_of_lt hlt) ih

private theorem denseDigraph_dom_le {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {a x : Fin Q}
    (hd : (denseDigraph Q inStart inSrc).Dominates ⟨0, sp.qPos⟩ a x) :
    a.val ≤ x.val := by
  have hxReach := denseDigraph_initiallyReachable sp x
  have hSuf := initiallyReachable_suffix_of_dominates hxReach hd
  exact avoidPath_val_le sp hSuf

private theorem domPrefixInv_init {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {data : Array (Word bits)} (hSize : data.size = L.workCap)
    (hP0 : (data[0]?).map Fin.val = some 0)
    (hD0 : (data[Q]?).map Fin.val = some 0)
    (hF0 : (data[2 * Q]?).map Fin.val = some 0)
    (hF1 : (data[2 * Q + 1]?).map Fin.val = some 0)
    (hF2 : (data[2 * Q + 2]?).map Fin.val = some 0) :
    DomPrefixInv input Q mReach inStart inSrc 1 JumpForest.init data := by
  have hWork := sp.workBounds
  have hQ : 1 ≤ Q := sp.qPos
  have hRec : Records (2 * Q) JumpForest.init data := by
    refine ⟨ValidJumpForest.init, ?_, ?_, ?_, ?_⟩
    · change 2 * Q + 3 * 1 ≤ data.size
      omega
    · intro u hu
      have hu0 : u = 0 := by change u < 1 at hu; omega
      subst u
      rw [Nat.mul_zero, Nat.add_zero]
      exact hF0
    · intro u hu
      have hu0 : u = 0 := by change u < 1 at hu; omega
      subst u
      rw [Nat.mul_zero, Nat.add_zero]
      exact hF1
    · intro u hu
      have hu0 : u = 0 := by change u < 1 at hu; omega
      subst u
      rw [Nat.mul_zero, Nat.add_zero]
      exact hF2
  refine ⟨Nat.le_refl 1, ValidJumpForest.init, rfl, hRec, ?_, ?_, ?_⟩
  · intro u hu
    have hu0 : u = 0 := by omega
    subst u
    exact hP0
  · intro u hu
    have hu0 : u = 0 := by omega
    subst u
    exact hD0
  · intro hQ x a hx ha
    have hx0 : x = ⟨0, hQ⟩ := Fin.ext (by change x.val = 0; omega)
    have ha0 : a = ⟨0, hQ⟩ := Fin.ext (by change a.val = 0; omega)
    subst x; subst a
    constructor
    · intro _
      exact ⟨0, rfl⟩
    · intro _
      exact dominates_refl

private theorem domSem_extend {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {v : Nat} (hv1 : 1 ≤ v) (hvLt : v < Q)
    {F : JumpForest} {data : Array (Word bits)}
    (inv : DomPrefixInv input Q mReach inStart inSrc v F data)
    {d : Nat} (hdLt : d < v)
    (hdExact : ∀ a, a < v →
      (IsAncestor F a d ↔ ∀ k, inStart v ≤ k → k < inStart (v + 1) → IsAncestor F a (inSrc k))) :
    let g := denseDigraph Q inStart inSrc
    let r : Fin Q := ⟨0, sp.qPos⟩
    let vFin : Fin Q := ⟨v, hvLt⟩
    let dFin : Fin Q := ⟨d, Nat.lt_trans hdLt hvLt⟩
    g.IsImmediateDominator r dFin vFin ∧
    (∀ (x a : Fin Q), x.val < v + 1 → a.val < v + 1 →
      (g.Dominates r a x ↔ IsAncestor (F.appendLeaf d) a.val x.val)) := by
  intro g r vFin dFin
  have hValid : ValidJumpForest F := inv.valid
  have hdF : d < F.size := by rw [inv.size_eq]; exact hdLt
  have hReach : ∀ u : Fin Q, g.InitiallyReachable r u := denseDigraph_initiallyReachable sp
  have hProg : ∀ x y : Fin Q, g.HasArc x y → x.val < y.val := denseDigraph_progress sp
  have hVneR : vFin ≠ r := by
    intro h
    have hv0 := congrArg Fin.val h
    change v = 0 at hv0
    omega
  let rel : Fin Q → Fin Q → Prop := fun a u => IsAncestor F a.val u.val
  have hPredSem : ∀ a u : Fin Q, g.HasArc u vFin → g.InitiallyReachable r u →
      (rel a u ↔ g.Dominates r a u) := by
    intro a u huv _
    have huLt : u.val < v := hProg u vFin huv
    have huF : u.val < F.size := by rw [inv.size_eq]; exact huLt
    constructor
    · intro hAnc
      obtain ⟨j, hj⟩ := hAnc
      have haF : a.val < F.size := by rw [← hj]; exact hValid.iterParent_lt_size huF j
      have haLt : a.val < v := by rw [← inv.size_eq]; exact haF
      exact (inv.domSem sp.qPos u a huLt haLt).mpr ⟨j, hj⟩
    · intro hDom
      have haLe : a.val ≤ u.val := denseDigraph_dom_le sp hDom
      have haLt : a.val < v := Nat.lt_of_le_of_lt haLe huLt
      exact (inv.domSem sp.qPos u a huLt haLt).mp hDom
  have hParentSem : ∀ a : Fin Q, rel a dFin ↔ g.Dominates r a dFin := by
    intro a
    constructor
    · intro hAnc
      obtain ⟨j, hj⟩ := hAnc
      have haF : a.val < F.size := by rw [← hj]; exact hValid.iterParent_lt_size hdF j
      have haLt : a.val < v := by rw [← inv.size_eq]; exact haF
      exact (inv.domSem sp.qPos dFin a hdLt haLt).mpr ⟨j, hj⟩
    · intro hDom
      have haLe : a.val ≤ dFin.val := denseDigraph_dom_le sp hDom
      have haLt : a.val < v := Nat.lt_of_le_of_lt haLe hdLt
      exact (inv.domSem sp.qPos dFin a hdLt haLt).mp hDom
  have hAllAnc : ∀ a : Fin Q,
      (∀ u : Fin Q, g.HasArc u vFin → g.InitiallyReachable r u → rel a u) ↔
      (∀ k, inStart v ≤ k → k < inStart (v + 1) → IsAncestor F a.val (inSrc k)) := by
    intro a
    constructor
    · intro h k hkLo hkHi
      have huLt : inSrc k < v := sp.srcPred v k hv1 hvLt hkLo hkHi
      let u : Fin Q := ⟨inSrc k, Nat.lt_trans huLt hvLt⟩
      have hArc : g.HasArc u vFin :=
        (denseDigraph_hasArc_iff Q inStart inSrc u vFin).mpr ⟨hv1, k, hkLo, hkHi, rfl⟩
      exact h u hArc (hReach u)
    · intro h u huv _
      obtain ⟨_, k, hkLo, hkHi, hkSrc⟩ :=
        (denseDigraph_hasArc_iff Q inStart inSrc u vFin).mp huv
      change IsAncestor F a.val u.val
      rw [← hkSrc]
      exact h k hkLo hkHi
  have hD_pred : ∀ u : Fin Q, g.HasArc u vFin → g.InitiallyReachable r u → rel dFin u :=
    (hAllAnc dFin).mpr ((hdExact d hdLt).mp ⟨0, rfl⟩)
  have hD_min : ∀ a : Fin Q,
      (∀ u : Fin Q, g.HasArc u vFin → g.InitiallyReachable r u → rel a u) → rel a dFin := by
    intro a ha
    have hK := (hAllAnc a).mp ha
    have hk0 : inStart v < inStart (v + 1) := sp.nonemptyRow v hv1 hvLt
    have hPred0 : IsAncestor F a.val (inSrc (inStart v)) := hK (inStart v) (Nat.le_refl _) hk0
    have hs0Lt : inSrc (inStart v) < v := sp.srcPred v (inStart v) hv1 hvLt (Nat.le_refl _) hk0
    have hs0F : inSrc (inStart v) < F.size := by rw [inv.size_eq]; exact hs0Lt
    obtain ⟨j, hj⟩ := hPred0
    have haF : a.val < F.size := by rw [← hj]; exact hValid.iterParent_lt_size hs0F j
    have haLt : a.val < v := by rw [← inv.size_eq]; exact haF
    exact (hdExact a.val haLt).mpr hK
  have hIdom : g.IsImmediateDominator r dFin vFin :=
    (EX15.immediateDominator_iff_predecessor_lca_partial
      hProg (hReach vFin) hVneR rel hPredSem hParentSem).mpr ⟨hD_pred, hD_min⟩
  refine ⟨hIdom, ?_⟩
  intro x a hx ha
  by_cases hxv : x.val < v
  · constructor
    · intro hDom
      have haLe : a.val ≤ x.val := denseDigraph_dom_le sp hDom
      have haLt : a.val < v := Nat.lt_of_le_of_lt haLe hxv
      have hOld : IsAncestor F a.val x.val := (inv.domSem sp.qPos x a hxv haLt).mp hDom
      exact (isAncestor_appendLeaf_old hValid hdF (by rw [inv.size_eq]; exact hxv)).mpr hOld
    · intro hAnc
      have hOld : IsAncestor F a.val x.val :=
        (isAncestor_appendLeaf_old hValid hdF (by rw [inv.size_eq]; exact hxv)).mp hAnc
      obtain ⟨j, hj⟩ := hOld
      have haF : a.val < F.size :=
        by rw [← hj]; exact hValid.iterParent_lt_size (by rw [inv.size_eq]; exact hxv) j
      have haLt : a.val < v := by rw [← inv.size_eq]; exact haF
      exact (inv.domSem sp.qPos x a hxv haLt).mpr ⟨j, hj⟩
  · have hxvVal : x.val = v := by omega
    have hxvEq : x = vFin := Fin.ext hxvVal
    subst x
    by_cases hav : a.val = v
    · have haEq : a = vFin := Fin.ext hav
      subst a
      constructor
      · intro _
        exact ⟨0, rfl⟩
      · intro _
        exact dominates_refl
    · have haLt : a.val < v := by omega
      have haNeV : a ≠ vFin := fun e => hav (congrArg Fin.val e)
      constructor
      · intro hDom
        have hDomD : g.Dominates r a dFin := hIdom.2.2 a haNeV hDom
        have hOld : IsAncestor F a.val d := (inv.domSem sp.qPos dFin a hdLt haLt).mp hDomD
        change IsAncestor (F.appendLeaf d) a.val v
        rw [← inv.size_eq]
        exact (EX15.isAncestor_appendLeaf_new_slot hValid hdF).mpr (Or.inr hOld)
      · intro hAnc
        have hAnc' : IsAncestor (F.appendLeaf d) a.val F.size := by
          change IsAncestor (F.appendLeaf d) a.val v at hAnc
          simpa only [inv.size_eq] using hAnc
        rcases (EX15.isAncestor_appendLeaf_new_slot hValid hdF).mp hAnc' with hEq | hOld
        · exact absurd (hEq.trans inv.size_eq) hav
        · have hDomD : g.Dominates r a dFin := (inv.domSem sp.qPos dFin a hdLt haLt).mpr hOld
          exact fun p => dominates_trans hDomD hIdom.2.1 p

private theorem domPrefixInv_step {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {v : Nat} (hv1 : 1 ≤ v) (hvLt : v < Q)
    {F : JumpForest} {data data' : Array (Word bits)}
    (inv : DomPrefixInv input Q mReach inStart inSrc v F data)
    (hSize : data'.size = L.workCap)
    {d : Nat} (hdLt : d < v)
    (hdExact : ∀ a, a < v →
      (IsAncestor F a d ↔ ∀ k, inStart v ≤ k → k < inStart (v + 1) → IsAncestor F a (inSrc k)))
    (hKeepP : ∀ u < v, data'[u]? = data[u]?)
    (hKeepD : ∀ u < v, data'[Q + u]? = data[Q + u]?)
    (hKeepF : ∀ u < v,
      data'[2 * Q + 3 * u]? = data[2 * Q + 3 * u]? ∧
      data'[2 * Q + 1 + 3 * u]? = data[2 * Q + 1 + 3 * u]? ∧
      data'[2 * Q + 2 + 3 * u]? = data[2 * Q + 2 + 3 * u]?)
    (hNewP : (data'[v]?).map Fin.val = some d)
    (hNewD : (data'[Q + v]?).map Fin.val = some (F.depthOf d + 1))
    (hNewF0 : (data'[2 * Q + 3 * v]?).map Fin.val = some d)
    (hNewF1 : (data'[2 * Q + 1 + 3 * v]?).map Fin.val = some (F.depthOf d + 1))
    (hNewF2 : (data'[2 * Q + 2 + 3 * v]?).map Fin.val = some (F.mkAppendedRecord d).jump) :
    DomPrefixInv input Q mReach inStart inSrc (v + 1) (F.appendLeaf d) data' ∧
    (let g := denseDigraph Q inStart inSrc
     let r : Fin Q := ⟨0, sp.qPos⟩
     g.IsImmediateDominator r ⟨d, Nat.lt_trans hdLt hvLt⟩ ⟨v, hvLt⟩) := by
  have hdF : d < F.size := by rw [inv.size_eq]; exact hdLt
  have hValid' : ValidJumpForest (F.appendLeaf d) := ValidJumpForest.appendLeaf inv.valid hdF
  have hSize' : (F.appendLeaf d).size = v + 1 := by
    rw [JumpForest.size_appendLeaf, inv.size_eq]
  have hWork := sp.workBounds
  have hFit' : 2 * Q + 3 * (F.appendLeaf d).size ≤ data'.size := by
    rw [hSize', hSize]; omega
  have hRec' : Records (2 * Q) (F.appendLeaf d) data' := by
    refine ⟨hValid', hFit', ?_, ?_, ?_⟩
    · intro u hu
      rw [hSize'] at hu
      by_cases huv : u < v
      · have huF : u < F.size := by rw [inv.size_eq]; exact huv
        rw [parentOf_appendLeaf_old F d huF, (hKeepF u huv).1]
        exact inv.records.parent u huF
      · have heq : u = v := by omega
        subst u
        have hNew : (F.appendLeaf d).parentOf v = d := by
          change ((F.appendLeaf d).recordAt v).parent = d
          rw [← inv.size_eq, recordAt_appendLeaf_new F d]
          rfl
        rw [hNew]
        exact hNewF0
    · intro u hu
      rw [hSize'] at hu
      by_cases huv : u < v
      · have huF : u < F.size := by rw [inv.size_eq]; exact huv
        rw [depthOf_appendLeaf_old F d huF, (hKeepF u huv).2.1]
        exact inv.records.depth u huF
      · have heq : u = v := by omega
        subst u
        have hNew : (F.appendLeaf d).depthOf v = F.depthOf d + 1 := by
          change ((F.appendLeaf d).recordAt v).depth = _
          rw [← inv.size_eq, recordAt_appendLeaf_new F d]
          rfl
        rw [hNew]
        exact hNewF1
    · intro u hu
      rw [hSize'] at hu
      by_cases huv : u < v
      · have huF : u < F.size := by rw [inv.size_eq]; exact huv
        rw [jumpOf_appendLeaf_old F d huF, (hKeepF u huv).2.2]
        exact inv.records.jump u huF
      · have heq : u = v := by omega
        subst u
        have hNew : (F.appendLeaf d).jumpOf v = (F.mkAppendedRecord d).jump := by
          change ((F.appendLeaf d).recordAt v).jump = _
          rw [← inv.size_eq, recordAt_appendLeaf_new F d]
        rw [hNew]
        exact hNewF2
  obtain ⟨hIdom, hSem⟩ := domSem_extend sp hv1 hvLt inv hdLt hdExact
  refine ⟨⟨by omega, hValid', hSize', hRec', ?_, ?_, ?_⟩, hIdom⟩
  · intro u hu
    by_cases huv : u < v
    · have huF : u < F.size := by rw [inv.size_eq]; exact huv
      rw [parentOf_appendLeaf_old F d huF, hKeepP u huv]
      exact inv.domParent u huv
    · have heq : u = v := by omega
      subst u
      have hNew : (F.appendLeaf d).parentOf v = d := by
        change ((F.appendLeaf d).recordAt v).parent = d
        rw [← inv.size_eq, recordAt_appendLeaf_new F d]
        rfl
      rw [hNew]
      exact hNewP
  · intro u hu
    by_cases huv : u < v
    · have huF : u < F.size := by rw [inv.size_eq]; exact huv
      rw [depthOf_appendLeaf_old F d huF, hKeepD u huv]
      exact inv.domDepth u huv
    · have heq : u = v := by omega
      subst u
      have hNew : (F.appendLeaf d).depthOf v = F.depthOf d + 1 := by
        change ((F.appendLeaf d).recordAt v).depth = _
        rw [← inv.size_eq, recordAt_appendLeaf_new F d]
        rfl
      rw [hNew]
      exact hNewD
  · intro _ x a hx ha
    exact hSem x a hx ha

/-- Extract `Digraph.ParentSpec` and `ValidDepthTree` on the dense DAG from a final
`DomPrefixInv` at `bound = Q`. -/
theorem domPrefixInv_parentSpec {bits : Nat} {L : Layout bits}
    {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    {F : JumpForest} {data : Array (Word bits)}
    (inv : DomPrefixInv input Q mReach inStart inSrc Q F data)
    (parent : Fin Q → Fin Q) (depth : Fin Q → Nat)
    (hPar : ∀ v : Fin Q, (parent v).val = F.parentOf v.val)
    (hDep : ∀ v : Fin Q, depth v = F.depthOf v.val)
    (hIdomAll : ∀ v : Fin Q, 1 ≤ v.val →
      (denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, sp.qPos⟩ (parent v) v) :
    ParentSpec (denseDigraph Q inStart inSrc) ⟨0, sp.qPos⟩ parent ∧
    ValidDepthTree ⟨0, sp.qPos⟩ parent depth ∧
    (∀ v : Fin Q, (data[v.val]?).map Fin.val = some (parent v).val) ∧
    (∀ v : Fin Q, (data[Q + v.val]?).map Fin.val = some (depth v)) := by
  have hReach := denseDigraph_initiallyReachable sp
  obtain ⟨_, hFinv⟩ := inv.valid.exists_forestInvariant
  have hRoot : parent ⟨0, sp.qPos⟩ = ⟨0, sp.qPos⟩ := by
    apply Fin.ext
    rw [hPar ⟨0, sp.qPos⟩]
    exact hFinv.root_parent
  have hSpec : ParentSpec (denseDigraph Q inStart inSrc) ⟨0, sp.qPos⟩ parent := by
    refine ⟨hRoot, ?_⟩
    intro v hvr
    have hv1 : 1 ≤ v.val := by
      have : v.val ≠ 0 := fun e => hvr (Fin.ext e)
      omega
    exact Or.inl ⟨hReach v, hIdomAll v hv1⟩
  have hTree : ValidDepthTree ⟨0, sp.qPos⟩ parent depth := by
    refine ⟨hRoot, ?_, ?_⟩
    · rw [hDep ⟨0, sp.qPos⟩]
      exact hFinv.root_depth
    · intro v hvr
      have hv0 : v.val ≠ 0 := fun e => hvr (Fin.ext e)
      have hvF : v.val < F.size := by rw [inv.size_eq]; exact v.isLt
      rw [hDep v, hDep (parent v), hPar v]
      exact (hFinv.nodes v.val hvF).pos_depth (Nat.pos_of_ne_zero hv0)
  have hPDat : ∀ v : Fin Q, (data[v.val]?).map Fin.val = some (parent v).val := by
    intro v
    rw [hPar v]
    exact inv.domParent v.val v.isLt
  have hDDat : ∀ v : Fin Q, (data[Q + v.val]?).map Fin.val = some (depth v) := by
    intro v
    rw [hDep v]
    exact inv.domDepth v.val v.isLt
  exact ⟨hSpec, hTree, hPDat, hDDat⟩

end DenseSpec

section DomProgram

private def writeScratchInstrs {bits : Nat} (off : Nat) (src : Fin 15) (hOff : off < 2 ^ bits) :
    List (Instr bits 15) :=
  [.imm registers.tmp ⟨off, hOff⟩,
   .add registers.tmp registers.stackBase registers.tmp,
   .storeData registers.tmp src]

private def readScratchInstrs {bits : Nat} (dst : Fin 15) (off : Nat) (hOff : off < 2 ^ bits) :
    List (Instr bits 15) :=
  [.imm registers.tmp ⟨off, hOff⟩,
   .add registers.tmp registers.stackBase registers.tmp,
   .loadData dst registers.tmp]

private def readRecord3Instrs {bits : Nat} (dst baseReg node : Fin 15) : List (Instr bits 15) :=
  [ .add registers.tmp node node,
    .add registers.tmp registers.tmp node,
    .add registers.tmp baseReg registers.tmp,
    .loadData dst registers.tmp ]

private def readDepthInstrs {bits : Nat} (dst node : Fin 15) : List (Instr bits 15) :=
  readRecord3Instrs dst toutBase node

private def readJumpInstrs {bits : Nat} (dst node : Fin 15) : List (Instr bits 15) :=
  readRecord3Instrs dst offsetBase node

/-- Straight-line Phase 1A initializer (`size = 18`, `haltPC = 17`):
loads `Q := input[0]`, sets base pointers (`tinBase = 2*Q`, `toutBase = 2*Q+1`,
`offsetBase = 2*Q+2`, `stackBase = 5*Q`, `childrenBase = 3+Q`), seeds `v = 0`
in `domParent`, `domDepth`, and `JumpForest.init`, and initializes `v := 1` at `5*Q`. -/
def domInitCode {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hFits : 2 < 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  #[
    .imm registers.zero ⟨0, Nat.two_pow_pos bits⟩,                -- 0: r0 := 0
    .imm registers.one ⟨1, by omega⟩,                              -- 1: r1 := 1
    .loadInput count registers.zero,                               -- 2: count := Q
    .imm tinBase ⟨2, hFits⟩,                                       -- 3: tinBase := 2
    .add childrenBase tinBase count,                               -- 4: r14 := 2 + Q
    .add childrenBase childrenBase registers.one,                  -- 5: r14 := 3 + Q (inSrc base)
    .add tinBase count count,                                      -- 6: r11 := 2 * Q (F.parent col)
    .add toutBase tinBase registers.one,                           -- 7: r12 := 2 * Q + 1 (F.depth col)
    .add offsetBase toutBase registers.one,                        -- 8: r13 := 2 * Q + 2 (F.jump col)
    .add registers.stackBase tinBase tinBase,                      -- 9: r7 := 4 * Q
    .add registers.stackBase registers.stackBase count,            -- 10: r7 := 5 * Q (scratch base)
    .storeData registers.zero registers.zero,                      -- 11: data[0] := 0
    .storeData count registers.zero,                               -- 12: data[Q] := 0
    .storeData tinBase registers.zero,                             -- 13: data[2*Q] := 0
    .storeData toutBase registers.zero,                            -- 14: data[2*Q+1] := 0
    .storeData offsetBase registers.zero,                          -- 15: data[2*Q+2] := 0
    .storeData registers.stackBase registers.one,                  -- 16: data[5*Q] := 1 (v := 1)
    .halt                                                          -- 17
  ]

def domInitPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hFits : 2 < 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  Phase.ofLast (domInitCode hi hw hFits) 17 rfl rfl rfl

/-- Relocate jump targets inside a fragment of `seekProgram`. -/
private def shiftSeekInstr {bits : Nat} (base : Nat) : Instr bits 15 → Instr bits 15
  | .goto tgt => .goto (base + tgt)
  | .branchLt a b t f => .branchLt a b (base + t) (base + f)
  | op => op

/-- First 23 instructions of `RamForestDepthSeek.seekProgram` (omitting trailing `.halt`),
relocated by `+ 88` so `pc 0..22` live at `88..110` and exits jump to `111`. -/
private def seekPrefix (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  ((seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw).toList.take 23).map
    (shiftSeekInstr 88)

private theorem seekPrefix_length (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    (seekPrefix bits inputCap workCap hi hw).length = 23 := rfl

private theorem seekPrefix_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    (seekPrefix bits inputCap workCap hi hw).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def loopVBlock (bits : Nat) (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  readScratchInstrs registers.ptr 0 (by omega) ++
  [ .branchLt registers.ptr count 4 208,
    .imm registers.tmp ⟨2, by omega⟩,
    .add registers.tmp registers.tmp registers.ptr,
    .loadInput registers.remain registers.tmp,
    .add registers.tmp registers.tmp registers.one,
    .loadInput registers.value registers.tmp,
    .add registers.tmp childrenBase registers.remain,
    .loadInput registers.childBase registers.tmp,
    .add registers.remain registers.remain registers.one ] ++
  writeScratchInstrs 1 registers.remain (by omega) ++
  writeScratchInstrs 2 registers.value (by omega) ++
  writeScratchInstrs 3 registers.childBase (by omega)

private theorem loopVBlock_len (bits : Nat) (hTen : 10 ≤ 2 ^ bits) :
    (loopVBlock bits hTen).length = 21 := rfl

private theorem loopVBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (loopVBlock bits hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def loopArcBlock (bits : Nat) (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  readScratchInstrs registers.ptr 1 (by omega) ++
  readScratchInstrs registers.remain 2 (by omega) ++
  [ .branchLt registers.ptr registers.remain 28 157,
    .add registers.tmp childrenBase registers.ptr,
    .loadInput registers.value registers.tmp ] ++
  writeScratchInstrs 4 registers.value (by omega) ++
  readDepthInstrs clk registers.value ++
  readScratchInstrs registers.ptr 3 (by omega) ++
  readDepthInstrs registers.remain registers.ptr ++
  [ .branchLt clk registers.remain 45 46,
    .mov registers.remain clk,
    .add registers.remain registers.remain registers.one ] ++
  writeScratchInstrs 5 registers.zero (by omega) ++
  writeScratchInstrs 6 registers.remain (by omega)

private theorem loopArcBlock_len (bits : Nat) (hTen : 10 ≤ 2 ^ bits) :
    (loopArcBlock bits hTen).length = 32 := rfl

private theorem loopArcBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (loopArcBlock bits hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def bsearchBlock (bits : Nat) (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  readScratchInstrs registers.ptr 5 (by omega) ++
  readScratchInstrs registers.remain 6 (by omega) ++
  [ .add registers.value registers.ptr registers.one,
    .branchLt registers.value registers.remain 61 74,
    .sub registers.value registers.remain registers.ptr,
    .shr1 registers.value registers.value,
    .add cmd registers.ptr registers.value ] ++
  writeScratchInstrs 7 cmd (by omega) ++
  writeScratchInstrs 9 registers.zero (by omega) ++
  readScratchInstrs registers.ptr 3 (by omega) ++
  [ .goto 84,
    .imm registers.remain ⟨2, by omega⟩ ] ++
  writeScratchInstrs 9 registers.remain (by omega) ++
  readScratchInstrs cmd 5 (by omega) ++
  readScratchInstrs registers.ptr 3 (by omega)

private theorem bsearchBlock_len (bits : Nat) (hTen : 10 ≤ 2 ^ bits) :
    (bsearchBlock bits hTen).length = 31 := rfl

private theorem bsearchBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (bsearchBlock bits hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def seekPreloadBlock (bits : Nat) : List (Instr bits 15) :=
  readDepthInstrs clk registers.ptr

private theorem seekPreloadBlock_len (bits : Nat) :
    (seekPreloadBlock bits).length = 4 := rfl

private theorem seekPreloadBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    (seekPreloadBlock bits).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def dispatchBlock (bits : Nat) (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  readScratchInstrs registers.remain 9 (by omega) ++
  [ .branchLt registers.remain registers.one 115 128 ] ++
  writeScratchInstrs 8 registers.ptr (by omega) ++
  writeScratchInstrs 9 registers.one (by omega) ++
  readScratchInstrs cmd 7 (by omega) ++
  readScratchInstrs registers.ptr 4 (by omega) ++
  [ .goto 84,
    .imm registers.value ⟨2, by omega⟩,
    .branchLt registers.remain registers.value 130 146 ] ++
  readScratchInstrs registers.value 8 (by omega) ++
  readScratchInstrs cmd 7 (by omega) ++
  [ .branchLt registers.value registers.ptr 138 137,
    .branchLt registers.ptr registers.value 138 142 ] ++
  writeScratchInstrs 6 cmd (by omega) ++
  [ .goto 53 ] ++
  writeScratchInstrs 5 cmd (by omega) ++
  [ .goto 53 ] ++
  writeScratchInstrs 3 registers.ptr (by omega) ++
  readScratchInstrs registers.remain 1 (by omega) ++
  [ .add registers.remain registers.remain registers.one ] ++
  writeScratchInstrs 1 registers.remain (by omega) ++
  [ .goto 21 ]

private theorem dispatchBlock_len (bits : Nat) (hTen : 10 ≤ 2 ^ bits) :
    (dispatchBlock bits hTen).length = 46 := by
  simp only [dispatchBlock, readScratchInstrs, writeScratchInstrs,
    List.length_append, List.length_cons, List.length_nil]

private theorem dispatchBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (dispatchBlock bits hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [dispatchBlock, readScratchInstrs, writeScratchInstrs,
    List.all_append, List.all_cons, List.all_nil, nonHalt, Bool.and_true]

private def appendBodyBlock (bits : Nat) (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  readScratchInstrs registers.ptr 0 (by omega) ++
  readScratchInstrs registers.remain 3 (by omega) ++
  [ .storeData registers.ptr registers.remain,
    .add registers.value registers.ptr registers.ptr,
    .add registers.value registers.value registers.ptr,
    .add registers.tmp tinBase registers.value,
    .storeData registers.tmp registers.remain ] ++
  readDepthInstrs clk registers.remain ++
  [ .add registers.childBase clk registers.one,
    .add registers.tmp count registers.ptr,
    .storeData registers.tmp registers.childBase,
    .add registers.tmp toutBase registers.value,
    .storeData registers.tmp registers.childBase ] ++
  readJumpInstrs registers.childBase registers.remain ++
  readDepthInstrs cmd registers.childBase ++
  [ .sub clk clk cmd,
    .branchLt registers.zero clk 187 199 ] ++
  readJumpInstrs registers.childBase registers.childBase ++
  readDepthInstrs registers.value registers.childBase ++
  [ .sub cmd cmd registers.value,
    .branchLt clk cmd 199 197,
    .branchLt cmd clk 199 198,
    .mov registers.remain registers.childBase,
    .add registers.value registers.ptr registers.ptr,
    .add registers.value registers.value registers.ptr,
    .add registers.tmp offsetBase registers.value,
    .storeData registers.tmp registers.remain,
    .add registers.ptr registers.ptr registers.one ] ++
  writeScratchInstrs 0 registers.ptr (by omega) ++
  [ .goto 0 ]

private theorem appendBodyBlock_len (bits : Nat) (hTen : 10 ≤ 2 ^ bits) :
    (appendBodyBlock bits hTen).length = 51 := by
  simp only [appendBodyBlock, readScratchInstrs, writeScratchInstrs,
    readDepthInstrs, readJumpInstrs, readRecord3Instrs,
    List.length_append, List.length_cons, List.length_nil]

private theorem appendBodyBlock_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (appendBodyBlock bits hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [appendBodyBlock, readScratchInstrs, writeScratchInstrs,
    readDepthInstrs, readJumpInstrs, readRecord3Instrs,
    List.all_append, List.all_cons, List.all_nil, nonHalt, Bool.and_true]

private def domLoopBody (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loopVBlock bits hTen ++ loopArcBlock bits hTen ++ bsearchBlock bits hTen ++
    seekPreloadBlock bits ++ seekPrefix bits inputCap workCap hi hw ++
    dispatchBlock bits hTen ++ appendBodyBlock bits hTen

private theorem domLoopBody_len (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) :
    (domLoopBody bits inputCap workCap hi hw hTen).length = 208 := by
  simp only [domLoopBody, List.length_append,
    loopVBlock_len, loopArcBlock_len, bsearchBlock_len, seekPreloadBlock_len,
    seekPrefix_length, dispatchBlock_len, appendBodyBlock_len]

private theorem domLoopBody_nonHalt (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) :
    (domLoopBody bits inputCap workCap hi hw hTen).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [domLoopBody, List.all_append,
    loopVBlock_nonHalt bits inputCap workCap hi hw hTen,
    loopArcBlock_nonHalt bits inputCap workCap hi hw hTen,
    bsearchBlock_nonHalt bits inputCap workCap hi hw hTen,
    seekPreloadBlock_nonHalt bits inputCap workCap hi hw,
    seekPrefix_nonHalt bits inputCap workCap hi hw,
    dispatchBlock_nonHalt bits inputCap workCap hi hw hTen,
    appendBodyBlock_nonHalt bits inputCap workCap hi hw hTen, Bool.and_true]

/-- Main Phase 1B dynamic skew-binary dominator & LCA loop (`size = 209`, `haltPC = 208`).
Requires `10 ≤ 2 ^ bits` (satisfied automatically when `5 * Q + 10 ≤ workCap ≤ 2 ^ bits` with `Q ≥ 1`). -/
def domLoopCode {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  (domLoopBody bits inputCap workCap hi hw hTen ++ [Instr.halt]).toArray

private theorem domLoopCode_size {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) :
    (domLoopCode hi hw hTen).size = 209 := by
  simp [domLoopCode, domLoopBody_len]

private theorem domLoopCode_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) :
    (domLoopCode hi hw hTen)[208]? = some (Instr.halt : Instr bits 15) := by
  unfold domLoopCode
  rw [List.getElem?_toArray, List.getElem?_append_right (by rw [domLoopBody_len]; exact Nat.le_refl _),
    domLoopBody_len]
  rfl

def domLoopPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  Phase.ofLast (domLoopCode hi hw hTen) 208 (domLoopCode_size hi hw hTen)
    (domLoopCode_halt hi hw hTen) (by
      have hLen : (domLoopBody bits inputCap workCap hi hw hTen).length = 208 :=
        domLoopBody_len bits inputCap workCap hi hw hTen
      have hTake : (domLoopCode hi hw hTen).toList.take 208 =
          domLoopBody bits inputCap workCap hi hw hTen := by
        have hEq : (domLoopCode hi hw hTen).toList =
            domLoopBody bits inputCap workCap hi hw hTen ++ [Instr.halt] := rfl
        rw [hEq, ← hLen, List.take_left]
      rw [hTake]
      exact domLoopBody_nonHalt bits inputCap workCap hi hw hTen)

def domBuildPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  (domInitPhase hi hw (by omega)).link (domLoopPhase hi hw hTen)

def domBuildProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  (domBuildPhase hi hw hTen).code

end DomProgram

section DomProof

open PaperB.RamForestProgram.DepthSeek
open PaperB.JumpForestCommonAncestor

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private theorem placed_of_split {code : Program L} {pre mid post : List (Instr bits 15)}
    (hEq : code = (pre ++ mid ++ post).toArray) :
    Placed code pre.length mid := by
  rw [hEq, List.append_assoc]
  intro i op hOp
  have hLen : i < mid.length := by
    by_cases h : i < mid.length
    · exact h
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hOp; cases hOp
  rw [List.getElem?_toArray, List.getElem?_append_right (by omega),
    show pre.length + i - pre.length = i by omega,
    List.getElem?_append_left hLen]
  exact hOp

private theorem loopV_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 0 (loopVBlock bits hTen) :=
  placed_of_split (pre := []) (mid := loopVBlock bits hTen)
    (post := loopArcBlock bits hTen ++ bsearchBlock bits hTen ++ seekPreloadBlock bits ++
      seekPrefix bits inputCap workCap hi hw ++ dispatchBlock bits hTen ++
      appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.nil_append, List.append_assoc])

private theorem loopArc_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 21 (loopArcBlock bits hTen) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen) (mid := loopArcBlock bits hTen)
    (post := bsearchBlock bits hTen ++ seekPreloadBlock bits ++
      seekPrefix bits inputCap workCap hi hw ++ dispatchBlock bits hTen ++
      appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [loopVBlock_len] using h

private theorem bsearch_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 53 (bsearchBlock bits hTen) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen ++ loopArcBlock bits hTen) (mid := bsearchBlock bits hTen)
    (post := seekPreloadBlock bits ++ seekPrefix bits inputCap workCap hi hw ++
      dispatchBlock bits hTen ++ appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [List.length_append, loopVBlock_len, loopArcBlock_len] using h

private theorem seekPreload_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 84 (seekPreloadBlock bits) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen ++ loopArcBlock bits hTen ++ bsearchBlock bits hTen)
    (mid := seekPreloadBlock bits)
    (post := seekPrefix bits inputCap workCap hi hw ++ dispatchBlock bits hTen ++
      appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [List.length_append, loopVBlock_len, loopArcBlock_len, bsearchBlock_len] using h

private theorem seekPrefix_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 88 (seekPrefix bits inputCap workCap hi hw) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen ++ loopArcBlock bits hTen ++ bsearchBlock bits hTen ++
      seekPreloadBlock bits)
    (mid := seekPrefix bits inputCap workCap hi hw)
    (post := dispatchBlock bits hTen ++ appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [List.length_append, loopVBlock_len, loopArcBlock_len, bsearchBlock_len,
    seekPreloadBlock_len] using h

private theorem dispatch_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 111 (dispatchBlock bits hTen) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen ++ loopArcBlock bits hTen ++ bsearchBlock bits hTen ++
      seekPreloadBlock bits ++ seekPrefix bits inputCap workCap hi hw)
    (mid := dispatchBlock bits hTen)
    (post := appendBodyBlock bits hTen ++ [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [List.length_append, loopVBlock_len, loopArcBlock_len, bsearchBlock_len,
    seekPreloadBlock_len, seekPrefix_length] using h

private theorem appendBody_placed (hTen : 10 ≤ 2 ^ bits) :
    Placed (domLoopCode hi hw hTen) 157 (appendBodyBlock bits hTen) := by
  have h := placed_of_split (code := domLoopCode hi hw hTen)
    (pre := loopVBlock bits hTen ++ loopArcBlock bits hTen ++ bsearchBlock bits hTen ++
      seekPreloadBlock bits ++ seekPrefix bits inputCap workCap hi hw ++ dispatchBlock bits hTen)
    (mid := appendBodyBlock bits hTen)
    (post := [Instr.halt])
    (by simp only [domLoopCode, domLoopBody, List.append_assoc])
  simpa only [List.length_append, loopVBlock_len, loopArcBlock_len, bsearchBlock_len,
    seekPreloadBlock_len, seekPrefix_length, dispatchBlock_len] using h

private theorem step_concat {code : Program L} {input : Input L} {s t u : State L}
    {m n : Nat} (h1 : Steps code input m s t) (h2 : Steps code input n t u) :
    Steps code input (m + n) s u :=
  h1.append h2

private theorem readScratch_steps {code : Program L} {input : Input L} {s : State L}
    {base : Nat} {dst : Fin 15} {off : Nat} {hOff : off < 2 ^ bits} {w : Word bits}
    (hPlaced : Placed code base (readScratchInstrs dst off hOff))
    (hPC : s.pc = base)
    (hEnd : base + 3 < code.size)
    (hStack : (reg s registers.stackBase).val + off < s.data.size)
    (hVal : s.data[(reg s registers.stackBase).val + off]? = some w)
    (_hNe : dst ≠ registers.tmp) :
    ∃ t, Steps code input 3 s t ∧ t.pc = base + 3 ∧ t.data = s.data ∧
      reg t dst = w ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ registers.tmp → reg t r = reg s r) := by
  have hStackBaseNe : registers.stackBase ≠ registers.tmp := by decide
  have hf0 : code[s.pc]? = some (.imm registers.tmp ⟨off, hOff⟩) := by
    rw [hPC]; simpa only [Nat.add_zero] using hPlaced 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hr1t, hr1o, hd1⟩ := step_imm_at (input := input) hf0 (by omega)
  have hf1 : code[s1.pc]? = some (.add registers.tmp registers.stackBase registers.tmp) := by
    rw [hpc1, hPC]; exact hPlaced 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hr2t, hr2o, hd2⟩ := step_add_at (input := input) hf1 (by omega)
  have hAddr : (reg s2 registers.tmp).val = (reg s registers.stackBase).val + off := by
    rw [hr2t]
    have hsb1 : (reg s1 registers.stackBase).val = (reg s registers.stackBase).val :=
      congrArg Fin.val (hr1o registers.stackBase hStackBaseNe)
    have ht1 : (reg s1 registers.tmp).val = off := congrArg Fin.val hr1t
    have hFit : (reg s1 registers.stackBase).val + (reg s1 registers.tmp).val < 2 ^ bits := by
      rw [hsb1, ht1]; exact Nat.lt_of_lt_of_le hStack (by rw [s.data_size]; exact hw)
    rw [add_no_wrap _ _ hFit, hsb1, ht1]
  have hRead : s2.data[(reg s2 registers.tmp).val]? = some w := by
    rw [hd2, hd1, hAddr]; exact hVal
  have hf2 : code[s2.pc]? = some (.loadData dst registers.tmp) := by
    rw [hpc2, hpc1, hPC]; exact hPlaced 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hr3d, hr3o, hd3⟩ :=
    step_loadData_at (input := input) hf2 hRead (by omega)
  refine ⟨s3, .cons hs1 (.cons hs2 (.cons hs3 (.zero _))), by omega,
    hd3.trans (hd2.trans hd1), hr3d, ?_⟩
  intro r hrd hrt
  rw [hr3o r hrd, hr2o r hrt, hr1o r hrt]

private theorem reg_eq_of_regs_eq {s1 s2 : State L} (h : s1.regs = s2.regs) (r : Fin 15) :
    reg s1 r = reg s2 r := by
  cases s1; cases s2; cases h; rfl

private theorem regs_eq_of_forall {s1 s2 : State L}
    (h : ∀ r : Fin 15, reg s1 r = reg s2 r) : s1.regs = s2.regs := by
  refine Array.ext ?_ ?_
  · exact s1.regs_size.trans s2.regs_size.symm
  · intro i hi1 _
    have hi : i < 15 := by simpa only [s1.regs_size] using hi1
    exact h ⟨i, hi⟩

private theorem writeScratch_steps {code : Program L} {input : Input L} {s : State L}
    {base off : Nat} {src : Fin 15} {hOff : off < 2 ^ bits}
    (hPlaced : Placed code base (writeScratchInstrs off src hOff))
    (hPC : s.pc = base)
    (hEnd : base + 3 < code.size)
    (hStack : (reg s registers.stackBase).val + off < s.data.size)
    (hNe : src ≠ registers.tmp) :
    ∃ t, Steps code input 3 s t ∧ t.pc = base + 3 ∧ t.data.size = s.data.size ∧
      t.data[(reg s registers.stackBase).val + off]? = some (reg s src) ∧
      (∀ j, j ≠ (reg s registers.stackBase).val + off → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ registers.tmp → reg t r = reg s r) := by
  have hStackBaseNe : registers.stackBase ≠ registers.tmp := by decide
  have hf0 : code[s.pc]? = some (.imm registers.tmp ⟨off, hOff⟩) := by
    rw [hPC]; simpa only [Nat.add_zero] using hPlaced 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hr1t, hr1o, hd1⟩ := step_imm_at (input := input) hf0 (by omega)
  have hf1 : code[s1.pc]? = some (.add registers.tmp registers.stackBase registers.tmp) := by
    rw [hpc1, hPC]; exact hPlaced 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hr2t, hr2o, hd2⟩ := step_add_at (input := input) hf1 (by omega)
  have hAddr : (reg s2 registers.tmp).val = (reg s registers.stackBase).val + off := by
    rw [hr2t]
    have hsb1 : (reg s1 registers.stackBase).val = (reg s registers.stackBase).val :=
      congrArg Fin.val (hr1o registers.stackBase hStackBaseNe)
    have ht1 : (reg s1 registers.tmp).val = off := congrArg Fin.val hr1t
    have hFit : (reg s1 registers.stackBase).val + (reg s1 registers.tmp).val < 2 ^ bits := by
      rw [hsb1, ht1]; exact Nat.lt_of_lt_of_le hStack (by rw [s.data_size]; exact hw)
    rw [add_no_wrap _ _ hFit, hsb1, ht1]
  have hFit2 : (reg s2 registers.tmp).val < s2.data.size := by
    rw [hd2, hd1, hAddr]; exact hStack
  have hf2 : code[s2.pc]? = some (.storeData registers.tmp src) := by
    rw [hpc2, hpc1, hPC]; exact hPlaced 2 _ rfl
  obtain ⟨hs3, hpc3, hr3, hd3⟩ := step_storeData_at (input := input) hf2 hFit2 (by omega)
  refine ⟨_, .cons hs1 (.cons hs2 (.cons hs3 (.zero _))), by omega, ?_, ?_, ?_, ?_⟩
  · simp [hd2, hd1]
  · rw [hd3, Array.getElem?_set]
    split
    · have hSrc2 : reg s2 src = reg s src := (hr2o src hNe).trans (hr1o src hNe)
      rw [hSrc2]
    · rename_i hNeq
      exfalso; exact hNeq hAddr
  · intro j hj
    rw [hd3, Array.getElem?_set]
    split
    · rename_i hEq
      exfalso; exact hj (hEq.symm.trans hAddr)
    · rw [hd2, hd1]
  · intro r hr
    exact (reg_eq_of_regs_eq hr3 r).trans ((hr2o r hr).trans (hr1o r hr))

private theorem recordField_steps_at {code : Program L} {input : Input L} {s : State L}
    {base : Nat} {dst baseReg node : Fin 15} {w : Word bits}
    (hPlaced : Placed code base (readRecord3Instrs dst baseReg node))
    (hPC : s.pc = base)
    (hEnd : base + 4 < code.size)
    (hNodeNe : node ≠ registers.tmp) (hBaseNe : baseReg ≠ registers.tmp) (_hDstNe : dst ≠ registers.tmp)
    (hFit : (reg s baseReg).val + 3 * (reg s node).val < s.data.size)
    (hVal : s.data[(reg s baseReg).val + 3 * (reg s node).val]? = some w) :
    ∃ t, Steps code input 4 s t ∧ t.pc = base + 4 ∧ t.data = s.data ∧
      reg t dst = w ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ registers.tmp → reg t r = reg s r) := by
  have hf0 : code[s.pc]? = some (.add registers.tmp node node) := by
    rw [hPC]; simpa only [Nat.add_zero] using hPlaced 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hr1t, hr1o, hd1⟩ := step_add_at (input := input) hf0 (by omega)
  have h1Val : (reg s1 registers.tmp).val = 2 * (reg s node).val := by
    rw [hr1t]
    have hLt : (reg s node).val + (reg s node).val < 2 ^ bits :=
      Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_lt_of_le hFit (by rw [s.data_size]; exact hw))
    rw [add_no_wrap _ _ hLt]; omega
  have hf1 : code[s1.pc]? = some (.add registers.tmp registers.tmp node) := by
    rw [hpc1, hPC]; exact hPlaced 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hr2t, hr2o, hd2⟩ := step_add_at (input := input) hf1 (by omega)
  have h2Val : (reg s2 registers.tmp).val = 3 * (reg s node).val := by
    rw [hr2t]
    have hn1 : (reg s1 node).val = (reg s node).val := congrArg Fin.val (hr1o node hNodeNe)
    have hLt : (reg s1 registers.tmp).val + (reg s1 node).val < 2 ^ bits := by
      rw [h1Val, hn1]
      exact Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_lt_of_le hFit (by rw [s.data_size]; exact hw))
    rw [add_no_wrap _ _ hLt, h1Val, hn1]; omega
  have hf2 : code[s2.pc]? = some (.add registers.tmp baseReg registers.tmp) := by
    rw [hpc2, hpc1, hPC]; exact hPlaced 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hr3t, hr3o, hd3⟩ := step_add_at (input := input) hf2 (by omega)
  have h3Val : (reg s3 registers.tmp).val = (reg s baseReg).val + 3 * (reg s node).val := by
    rw [hr3t]
    have hb2 : (reg s2 baseReg).val = (reg s baseReg).val :=
      congrArg Fin.val ((hr2o baseReg hBaseNe).trans (hr1o baseReg hBaseNe))
    have hLt : (reg s2 baseReg).val + (reg s2 registers.tmp).val < 2 ^ bits := by
      rw [hb2, h2Val]
      exact Nat.lt_of_lt_of_le hFit (by rw [s.data_size]; exact hw)
    rw [add_no_wrap _ _ hLt, hb2, h2Val]
  have hRead : s3.data[(reg s3 registers.tmp).val]? = some w := by
    rw [hd3, hd2, hd1, h3Val]; exact hVal
  have hf3 : code[s3.pc]? = some (.loadData dst registers.tmp) := by
    rw [hpc3, hpc2, hpc1, hPC]; exact hPlaced 3 _ rfl
  obtain ⟨s4, hs4, hpc4, hr4d, hr4o, hd4⟩ :=
    step_loadData_at (input := input) hf3 hRead (by omega)
  refine ⟨s4, .cons hs1 (.cons hs2 (.cons hs3 (.cons hs4 (.zero _)))), by omega,
    hd4.trans (hd3.trans (hd2.trans hd1)), hr4d, ?_⟩
  intro r hrd hrt
  rw [hr4o r hrd, hr3o r hrt, hr2o r hrt, hr1o r hrt]

private def fixedReg (r : Fin 15) : Bool :=
  r == registers.zero || r == registers.one || r == registers.stackBase ||
  r == cmd || r == count || r == tinBase || r == toutBase ||
  r == offsetBase || r == childrenBase

private def seekInstrSafe {bits : Nat} (pc : Nat) : Instr bits 15 → Bool
  | .halt => decide (pc = 23)
  | .add dst _ _ => decide (pc < 23) && !fixedReg dst
  | .loadData dst _ => decide (pc < 23) && !fixedReg dst
  | .goto tgt => decide (pc < 23) && decide (tgt < 24)
  | .branchLt _ _ t f => decide (pc < 23) && decide (t < 24) && decide (f < 24)
  | _ => false

private theorem seekProgram_size :
    (seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw).size = 24 := rfl

private theorem seekProgram_instr_safe (i : Nat) (hiLt : i < 24) (op : Instr bits 15)
    (hOp : (seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw)[i]? = some op) :
    seekInstrSafe i op = true := by
  match i with
  | 0 => cases hOp; rfl
  | 1 => cases hOp; rfl
  | 2 => cases hOp; rfl
  | 3 => cases hOp; rfl
  | 4 => cases hOp; rfl
  | 5 => cases hOp; rfl
  | 6 => cases hOp; rfl
  | 7 => cases hOp; rfl
  | 8 => cases hOp; rfl
  | 9 => cases hOp; rfl
  | 10 => cases hOp; rfl
  | 11 => cases hOp; rfl
  | 12 => cases hOp; rfl
  | 13 => cases hOp; rfl
  | 14 => cases hOp; rfl
  | 15 => cases hOp; rfl
  | 16 => cases hOp; rfl
  | 17 => cases hOp; rfl
  | 18 => cases hOp; rfl
  | 19 => cases hOp; rfl
  | 20 => cases hOp; rfl
  | 21 => cases hOp; rfl
  | 22 => cases hOp; rfl
  | 23 => cases hOp; rfl
  | _ + 24 => omega

private theorem step_loadData_none {code : Program L} {input : Input L} {s : State L}
    {dst addr : Fin 15}
    (hInstr : code[s.pc]? = some (.loadData dst addr))
    (hNone : s.data[(reg s addr).val]? = none) :
    step code input s = none := by
  unfold step
  rw [hInstr]
  change (s.data[(reg s addr).val]? >>= fun v =>
    if s.pc + 1 < code.size then some (Transition.next (putReg s dst v)) else none) = none
  rw [hNone]
  rfl

private theorem seekProgram_step_cases {input : Input L} {s : State L} {tr : Transition L}
    (hStep : step (seekProgram hi hw) input s = some tr) :
    (s.pc = 23 ∧ tr = .halted s) ∨
    (∃ u op, (seekProgram hi hw)[s.pc]? = some op ∧ s.pc < 23 ∧ seekInstrSafe s.pc op = true ∧
      tr = .next u ∧ (∀ r : Fin 15, fixedReg r = true → reg u r = reg s r)) := by
  have hNoneOr : ∃ op, (seekProgram hi hw)[s.pc]? = some op := by
    cases h : (seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw)[s.pc]? with
    | none =>
      have hbad : step (seekProgram hi hw) input s = none := by simp [step, h]
      rw [hbad] at hStep; cases hStep
    | some op => exact ⟨op, rfl⟩
  obtain ⟨op, hInstr⟩ := hNoneOr
  have hPc : s.pc < 24 := by
    by_cases hc : s.pc < (seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw).size
    · rw [seekProgram_size] at hc; exact hc
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hInstr; cases hInstr
  have hSafe := seekProgram_instr_safe s.pc hPc op hInstr
  have hFixNe : ∀ dst : Fin 15, fixedReg dst = false → ∀ r : Fin 15, fixedReg r = true → r ≠ dst := by
    intro dst hd r hr hEq; subst hEq; rw [hr] at hd; cases hd
  cases op with
  | imm | mov | sub | band | shr1 | loadInput | storeData => cases hSafe
  | halt =>
    have h23 : s.pc = 23 := by simpa [seekInstrSafe] using hSafe
    have hHalt := step_halt_at (input := input) hInstr
    rw [hHalt] at hStep
    cases hStep
    exact Or.inl ⟨h23, rfl⟩
  | add dst a b =>
    simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hSafe
    obtain ⟨h23, hd⟩ := hSafe
    obtain ⟨u, hu, _, _, hro, _⟩ := step_add_at (input := input) hInstr (by rw [seekProgram_size]; omega)
    rw [hu] at hStep
    cases hStep
    exact Or.inr ⟨u, .add dst a b, hInstr, h23, by simp [seekInstrSafe, h23, hd], rfl,
      fun r hr => hro r (hFixNe dst hd r hr)⟩
  | loadData dst addr =>
    simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hSafe
    obtain ⟨h23, hd⟩ := hSafe
    cases hVal : s.data[(reg s addr).val]? with
    | none =>
      rw [step_loadData_none hInstr hVal] at hStep
      cases hStep
    | some w =>
      obtain ⟨u, hu, _, _, hro, _⟩ :=
        step_loadData_at (input := input) hInstr hVal (by rw [seekProgram_size]; omega)
      rw [hu] at hStep
      cases hStep
      exact Or.inr ⟨u, .loadData dst addr, hInstr, h23, by simp [seekInstrSafe, h23, hd], rfl,
        fun r hr => hro r (hFixNe dst hd r hr)⟩
  | goto tgt =>
    simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq] at hSafe
    obtain ⟨h23, ht⟩ := hSafe
    have hGo := step_goto_at (input := input) hInstr (by rw [seekProgram_size]; omega)
    rw [hGo] at hStep
    cases hStep
    exact Or.inr ⟨{ s with pc := tgt }, .goto tgt, hInstr, h23,
      by simp [seekInstrSafe, h23, ht], rfl, fun _ _ => rfl⟩
  | branchLt a b t f =>
    simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq] at hSafe
    obtain ⟨⟨h23, ht⟩, hf⟩ := hSafe
    have hBr := step_branchLt_at (input := input) hInstr
      (by split <;> rw [seekProgram_size] <;> omega)
    rw [hBr] at hStep
    cases hStep
    exact Or.inr ⟨{ s with pc := if ltb (reg s a) (reg s b) = true then t else f },
      .branchLt a b t f, hInstr, h23, by simp [seekInstrSafe, h23, ht, hf], rfl, fun _ _ => rfl⟩

private theorem seekProgram_run_to_domLoop (hTen : 10 ≤ 2 ^ bits) {input : Input L} :
    ∀ (k : Nat) (s0 t0 s : State L),
      run (seekProgram hi hw) input (k + 1) s0 = some ⟨t0, k + 1⟩ →
      s.pc = 88 + s0.pc →
      s.regs = s0.regs →
      s.data = s0.data →
      s0.pc < 24 →
      ∃ t, Steps (domLoopCode hi hw hTen) input k s t ∧
        t.pc = 111 ∧ t.regs = t0.regs ∧ t.data = t0.data ∧
        (∀ r : Fin 15, fixedReg r = true → reg t r = reg s0 r) := by
  intro k
  induction k with
  | zero =>
    intro s0 t0 s hRun hpc hregs hdata _
    cases hst : step (seekProgram hi hw) input s0 with
    | none => simp [run, hst] at hRun
    | some tr =>
      rcases seekProgram_step_cases hst with ⟨h23, rfl⟩ | ⟨u, _, _, _, _, rfl, _⟩
      · have hEq : t0 = s0 := by
          have := Option.some.inj (by simpa [run, hst] using hRun)
          cases this; rfl
        subst hEq
        exact ⟨s, .zero s, by omega, hregs, hdata, fun r _ => reg_eq_of_regs_eq hregs r⟩
      · simp [run, hst] at hRun
  | succ k ih =>
    intro s0 t0 s hRun hpc hregs hdata _
    cases hst : step (seekProgram hi hw) input s0 with
    | none => simp [run, hst] at hRun
    | some tr =>
      rcases seekProgram_step_cases hst with ⟨h23, rfl⟩ | ⟨u0, op, hInstr0, h23, hSafe, rfl, hFix0⟩
      · simp [run, hst] at hRun
      · rw [run, hst] at hRun
        dsimp only at hRun
        cases hru : run (seekProgram hi hw) input (k + 1) u0 with
        | none => rw [hru] at hRun; cases hRun
        | some q =>
          rw [hru] at hRun
          dsimp only at hRun
          have hq := Option.some.inj hRun
          have hq2 : run (seekProgram hi hw) input (k + 1) u0 = some ⟨t0, k + 1⟩ := by
            cases q; cases hq; exact hru
          have hDomSize : (domLoopCode hi hw hTen).size = 209 := domLoopCode_size hi hw hTen
          have hPlaced : (domLoopCode hi hw hTen)[s.pc]? = some (shiftSeekInstr 88 op) := by
            rw [hpc]
            have hGet0 : ((seekProgram (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw).toList.take 23)[s0.pc]? = some op := by
              rw [List.getElem?_take, ite_eq_left h23]; simpa using hInstr0
            have hPref : (seekPrefix bits inputCap workCap hi hw)[s0.pc]? = some (shiftSeekInstr 88 op) := by
              simp only [seekPrefix, List.getElem?_map, hGet0, Option.map_some]
            exact seekPrefix_placed hTen s0.pc (shiftSeekInstr 88 op) hPref
          have hRegEq : ∀ r : Fin 15, reg s r = reg s0 r := fun r => reg_eq_of_regs_eq hregs r
          have hStepDom : ∃ u, step (domLoopCode hi hw hTen) input s = some (.next u) ∧
              u.pc = 88 + u0.pc ∧ u.regs = u0.regs ∧ u.data = u0.data ∧ u0.pc < 24 := by
            cases op with
            | imm | mov | sub | band | shr1 | loadInput | storeData => cases hSafe
            | halt => simp [seekInstrSafe] at hSafe; omega
            | add dst a b =>
              obtain ⟨u0', h0, hu0pc, hu0d, hu0o, hu0data⟩ :=
                step_add_at (input := input) hInstr0 (by rw [seekProgram_size]; omega)
              rw [h0] at hst; cases hst
              obtain ⟨u, hu, hupc, hud, huo, hudata⟩ :=
                step_add_at (input := input) (by simpa [shiftSeekInstr] using hPlaced) (by omega)
              refine ⟨u, hu, by omega, regs_eq_of_forall ?_, by rw [hudata, hdata, hu0data], by omega⟩
              intro r
              by_cases hrd : r = dst
              · subst hrd; rw [hud, hu0d, hRegEq a, hRegEq b]
              · rw [huo r hrd, hu0o r hrd, hRegEq r]
            | loadData dst addr =>
              cases hVal : s0.data[(reg s0 addr).val]? with
              | none => rw [step_loadData_none hInstr0 hVal] at hst; cases hst
              | some w =>
                obtain ⟨u0', h0, hu0pc, hu0d, hu0o, hu0data⟩ :=
                  step_loadData_at (input := input) hInstr0 hVal (by rw [seekProgram_size]; omega)
                rw [h0] at hst; cases hst
                have hVals : s.data[(reg s addr).val]? = some w := by
                  rw [hdata, hRegEq addr]; exact hVal
                obtain ⟨u, hu, hupc, hud, huo, hudata⟩ :=
                  step_loadData_at (input := input) (by simpa [shiftSeekInstr] using hPlaced) hVals (by omega)
                refine ⟨u, hu, by omega, regs_eq_of_forall ?_, by rw [hudata, hdata, hu0data], by omega⟩
                intro r
                by_cases hrd : r = dst
                · subst hrd; exact hud.trans hu0d.symm
                · rw [huo r hrd, hu0o r hrd, hRegEq r]
            | goto tgt =>
              simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq] at hSafe
              have h0 := step_goto_at (input := input) hInstr0 (by rw [seekProgram_size]; omega)
              rw [h0] at hst; cases hst
              have hDom := step_goto_at (input := input) (by simpa [shiftSeekInstr] using hPlaced) (by omega)
              exact ⟨_, hDom, rfl, hregs, hdata, hSafe.2⟩
            | branchLt a b t f =>
              simp only [seekInstrSafe, Bool.and_eq_true, decide_eq_true_eq] at hSafe
              have h0 := step_branchLt_at (input := input) hInstr0
                (by split <;> rw [seekProgram_size] <;> omega)
              rw [h0] at hst; cases hst
              have hDom := step_branchLt_at (input := input) (by simpa [shiftSeekInstr] using hPlaced)
                (by split <;> omega)
              refine ⟨_, hDom, ?_, hregs, hdata, ?_⟩
              · simp only [hRegEq a, hRegEq b]
                split <;> rfl
              · dsimp only
                split <;> omega
          obtain ⟨u, hStepU, hupc, huregs, hudata, huLt⟩ := hStepDom
          obtain ⟨t, hTail, htpc, htregs, htdata, htfix⟩ := ih u0 t0 u hq2 hupc huregs hudata huLt
          exact ⟨t, .cons hStepU hTail, htpc, htregs, htdata,
            fun r hr => (htfix r hr).trans (hFix0 r hr)⟩

private theorem step_storeData_exists {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin 15}
    (hf : code[s.pc]? = some (.storeData addr src))
    (hfit : (reg s addr).val < s.data.size)
    (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧
      t.data = s.data.set (reg s addr).val (reg s src) hfit :=
  ⟨_, step_storeData_at hf hfit hn⟩

private def domFixedReg (r : Fin 15) : Bool :=
  r == registers.zero || r == registers.one || r == registers.stackBase ||
  r == count || r == tinBase || r == toutBase ||
  r == offsetBase || r == childrenBase

private theorem domFixed_implies_fixed (r : Fin 15) (hr : domFixedReg r = true) :
    fixedReg r = true := by
  revert r hr
  decide

private theorem workBounds_nat {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) : 5 * Q + 10 ≤ workCap :=
  sp.workBounds

private theorem inBounds_nat {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) : 3 + Q + mReach ≤ inputCap :=
  sp.inBounds

private structure DomRegsFixed (Q : Nat) (s : State L) : Prop where
  zeroVal : (reg s registers.zero).val = 0
  oneVal : (reg s registers.one).val = 1
  countVal : (reg s count).val = Q
  tinVal : (reg s tinBase).val = 2 * Q
  toutVal : (reg s toutBase).val = 2 * Q + 1
  offsetVal : (reg s offsetBase).val = 2 * Q + 2
  stackVal : (reg s registers.stackBase).val = 5 * Q
  childrenVal : (reg s childrenBase).val = 3 + Q

private theorem domRegsFixed_eq_of_eq {Q : Nat} {s t : State L}
    (hFix : DomRegsFixed Q s)
    (hEq : ∀ r : Fin 15, domFixedReg r = true → reg t r = reg s r) :
    DomRegsFixed Q t := by
  have hv : ∀ r : Fin 15, domFixedReg r = true → (reg t r).val = (reg s r).val :=
    fun r hr => congrArg Fin.val (hEq r hr)
  exact
    { zeroVal := (hv registers.zero rfl).trans hFix.zeroVal
      oneVal := (hv registers.one rfl).trans hFix.oneVal
      countVal := (hv count rfl).trans hFix.countVal
      tinVal := (hv tinBase rfl).trans hFix.tinVal
      toutVal := (hv toutBase rfl).trans hFix.toutVal
      offsetVal := (hv offsetBase rfl).trans hFix.offsetVal
      stackVal := (hv registers.stackBase rfl).trans hFix.stackVal
      childrenVal := (hv childrenBase rfl).trans hFix.childrenVal }

private theorem jumpForest_depthOf_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) : F.depthOf u < F.size := by
  obtain ⟨_, hInv⟩ := hF.exists_forestInvariant
  have hLe := hInv.depthOf_le_self hu
  omega

private theorem jumpForest_depth_eq_zero_iff {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) : F.depthOf u = 0 ↔ u = 0 := by
  obtain ⟨_, hInv⟩ := hF.exists_forestInvariant
  exact hInv.depth_eq_zero_iff hu

private theorem jumpForest_depth_jump_lt {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hPos : 0 < u) (hu : u < F.size) : F.depthOf (F.jumpOf u) < F.depthOf u := by
  obtain ⟨_, hInv⟩ := hF.exists_forestInvariant
  exact hInv.depth_jump_lt hPos hu

private theorem jumpForest_isAncestor_depth_le {F : JumpForest} (hF : ValidJumpForest F)
    {a u : Nat} (hu : u < F.size) (hAnc : IsAncestor F a u) :
    F.depthOf a ≤ F.depthOf u := by
  obtain ⟨k, hk⟩ := hAnc
  rw [← hk, hF.depth_iterParent hu k]
  omega

private theorem jumpForest_anc_mono_ne {F : JumpForest} (hF : ValidJumpForest F)
    {u w mid : Nat} (hu : u < F.size) (hw : w < F.size)
    (hMidU : mid ≤ F.depthOf u) (hMidW : mid ≤ F.depthOf w)
    (hNe : F.ancestorAtDepth u mid ≠ F.ancestorAtDepth w mid) :
    ∀ d, mid ≤ d → d ≤ F.depthOf u → d ≤ F.depthOf w →
      F.ancestorAtDepth u d ≠ F.ancestorAtDepth w d := by
  intro d hdLo hdU hdW hEq
  let z := F.ancestorAtDepth u d
  have hzSpecU := hF.ancestorAtDepth_spec hu hdU
  have hzSpecW := hF.ancestorAtDepth_spec hw hdW
  have hzAncU : IsAncestor F z u := hzSpecU.2.1
  have hzAncW : IsAncestor F z w := by change IsAncestor F (F.ancestorAtDepth u d) w; rw [hEq]; exact hzSpecW.2.1
  have hzDep : F.depthOf z = d := hzSpecU.2.2
  have hxSpec := hF.ancestorAtDepth_spec hzSpecU.1 (by rw [hzDep]; exact hdLo)
  have hxU : F.ancestorAtDepth u mid = F.ancestorAtDepth z mid :=
    ((hF.ancestorAtDepth_unique hu hMidU).mp ⟨IsAncestor.trans hxSpec.2.1 hzAncU, hxSpec.2.2⟩).symm
  have hxW : F.ancestorAtDepth w mid = F.ancestorAtDepth z mid :=
    ((hF.ancestorAtDepth_unique hw hMidW).mp ⟨IsAncestor.trans hxSpec.2.1 hzAncW, hxSpec.2.2⟩).symm
  exact hNe (hxU.trans hxW.symm)

private theorem jumpForest_lca_complete {F : JumpForest} (hF : ValidJumpForest F)
    {u w lo : Nat} (hu : u < F.size) (hw : w < F.size)
    (hLoU : lo ≤ F.depthOf u) (hLoW : lo ≤ F.depthOf w)
    (hEq : F.ancestorAtDepth u lo = F.ancestorAtDepth w lo)
    (hAbove : ∀ d, lo + 1 ≤ d → d ≤ F.depthOf u → d ≤ F.depthOf w →
      F.ancestorAtDepth u d ≠ F.ancestorAtDepth w d) :
    F.ancestorAtDepth u lo < F.size ∧
    (∀ a, a < F.size → (IsAncestor F a (F.ancestorAtDepth u lo) ↔ IsAncestor F a u ∧ IsAncestor F a w)) := by
  have hSpecU := hF.ancestorAtDepth_spec hu hLoU
  have hSpecW := hF.ancestorAtDepth_spec hw hLoW
  refine ⟨hSpecU.1, ?_⟩
  intro a _
  constructor
  · intro ha
    refine ⟨IsAncestor.trans ha hSpecU.2.1, IsAncestor.trans ha ?_⟩
    rw [hEq]
    exact hSpecW.2.1
  · rintro ⟨haU, haW⟩
    have haDU : F.depthOf a ≤ F.depthOf u := jumpForest_isAncestor_depth_le hF hu haU
    have haDW : F.depthOf a ≤ F.depthOf w := jumpForest_isAncestor_depth_le hF hw haW
    have haEqU : a = F.ancestorAtDepth u (F.depthOf a) :=
      (hF.ancestorAtDepth_unique hu haDU).mp ⟨haU, rfl⟩
    have haEqW : a = F.ancestorAtDepth w (F.depthOf a) :=
      (hF.ancestorAtDepth_unique hw haDW).mp ⟨haW, rfl⟩
    have hLeLo : F.depthOf a ≤ lo := by
      by_cases hGt : lo + 1 ≤ F.depthOf a
      · exfalso; exact hAbove (F.depthOf a) hGt haDU haDW (haEqU.symm.trans haEqW)
      · omega
    have h1 := hF.ancestor_eq_iterParent_of_depth hu haU haDU rfl
    have h2 := hF.ancestor_eq_iterParent_of_depth hu hSpecU.2.1 hLoU hSpecU.2.2
    have hSub : F.depthOf u - F.depthOf a = (F.depthOf u - lo) + (lo - F.depthOf a) := by omega
    refine ⟨lo - F.depthOf a, ?_⟩
    rw [h2, ← iterParent_add, ← hSub, ← h1]

private theorem jumpForest_mkAppendedRecord_jump_eq (F : JumpForest) (p : Nat) :
    let d := F.depthOf p
    let j1 := F.jumpOf p
    let d1 := F.depthOf j1
    let j2 := F.jumpOf j1
    let d2 := F.depthOf j2
    (F.mkAppendedRecord p).jump =
      if 0 < d - d1 ∧ d - d1 = d1 - d2 then j2 else p :=
  rfl

private theorem fin_ne_of_val {n : Nat} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab => h (congrArg Fin.val hab)

private theorem domInit_steps {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) (hTen : 10 ≤ 2 ^ bits)
    (s0 : State L) (hPC : s0.pc = 0) :
    ∃ t, Steps (domInitCode hi hw (by omega)) input 17 s0 t ∧ t.pc = 17 ∧
      DomRegsFixed Q t ∧
      DomPrefixInv input Q mReach inStart inSrc 1 JumpForest.init t.data ∧
      (t.data[5 * Q]?).map Fin.val = some 1 ∧
      (t.data.size = workCap) := by
  let code := domInitCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw (by omega)
  have hSize : code.size = 18 := rfl
  have hQFit : Q < 2 ^ bits := Nat.lt_of_lt_of_le (by have := sp.qPos; omega) (Nat.le_trans sp.workBounds hw)
  have hf0 : code[s0.pc]? = some (.imm registers.zero ⟨0, Nat.two_pow_pos bits⟩) := by rw [hPC]; rfl
  obtain ⟨s1, hs1, hpc1, hr1z, hr1o, _⟩ := step_imm_at (input := input) hf0 (by rw [hPC, hSize]; omega)
  have hf1 : code[s1.pc]? = some (.imm registers.one ⟨1, by omega⟩) := by rw [hpc1, hPC]; rfl
  obtain ⟨s2, hs2, hpc2, hr21, hr2o, _⟩ := step_imm_at (input := input) hf1 (by rw [hpc1, hPC, hSize]; omega)
  have h2Zero : (reg s2 registers.zero).val = 0 := by
    rw [hr2o registers.zero (fin_ne_of_val (by decide)), hr1z]
  have hQword : input.words[(reg s2 registers.zero).val]? = some ⟨Q, hQFit⟩ := by
    rw [h2Zero]
    have h0 := sp.word0
    cases hInp : input.words[0]? with
    | none => rw [hInp] at h0; cases h0
    | some w =>
      rw [hInp, Option.map_some] at h0
      have hwQ : w.val = Q := Option.some.inj h0
      congr 1; exact Fin.ext hwQ
  have hf2 : code[s2.pc]? = some (.loadInput count registers.zero) := by rw [hpc2, hpc1, hPC]; rfl
  obtain ⟨s3, hs3, hpc3, hr3c, hr3o, _⟩ :=
    step_loadInput_at (input := input) hf2 (by rw [hpc2, hpc1, hPC, hSize]; omega) hQword
  have hf3 : code[s3.pc]? = some (.imm tinBase ⟨2, by omega⟩) := by rw [hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s4, hs4, hpc4, hr4t, hr4o, _⟩ :=
    step_imm_at (input := input) hf3 (by rw [hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf4 : code[s4.pc]? = some (.add childrenBase tinBase count) := by
    rw [hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s5, hs5, hpc5, hr5ch, hr5o, _⟩ :=
    step_add_at (input := input) hf4 (by rw [hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf5 : code[s5.pc]? = some (.add childrenBase childrenBase registers.one) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s6, hs6, hpc6, hr6ch, hr6o, _⟩ :=
    step_add_at (input := input) hf5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf6 : code[s6.pc]? = some (.add tinBase count count) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s7, hs7, hpc7, hr7t, hr7o, _⟩ :=
    step_add_at (input := input) hf6 (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf7 : code[s7.pc]? = some (.add toutBase tinBase registers.one) := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s8, hs8, hpc8, hr8to, hr8o, _⟩ :=
    step_add_at (input := input) hf7 (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf8 : code[s8.pc]? = some (.add offsetBase toutBase registers.one) := by
    rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s9, hs9, hpc9, hr9off, hr9o, _⟩ :=
    step_add_at (input := input) hf8 (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf9 : code[s9.pc]? = some (.add registers.stackBase tinBase tinBase) := by
    rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s10, hs10, hpc10, hr10sb, hr10o, _⟩ :=
    step_add_at (input := input) hf9 (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have hf10 : code[s10.pc]? = some (.add registers.stackBase registers.stackBase count) := by
    rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC]; rfl
  obtain ⟨s11, hs11, hpc11, hr11sb, hr11o, _⟩ :=
    step_add_at (input := input) hf10 (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hPC, hSize]; omega)
  have h11z : (reg s11 registers.zero).val = 0 := by
    rw [hr11o registers.zero (fin_ne_of_val (by decide)), hr10o registers.zero (fin_ne_of_val (by decide)),
        hr9o registers.zero (fin_ne_of_val (by decide)), hr8o registers.zero (fin_ne_of_val (by decide)),
        hr7o registers.zero (fin_ne_of_val (by decide)), hr6o registers.zero (fin_ne_of_val (by decide)),
        hr5o registers.zero (fin_ne_of_val (by decide)), hr4o registers.zero (fin_ne_of_val (by decide)),
        hr3o registers.zero (fin_ne_of_val (by decide)), h2Zero]
  have h11one : (reg s11 registers.one).val = 1 := by
    rw [hr11o registers.one (fin_ne_of_val (by decide)), hr10o registers.one (fin_ne_of_val (by decide)),
        hr9o registers.one (fin_ne_of_val (by decide)), hr8o registers.one (fin_ne_of_val (by decide)),
        hr7o registers.one (fin_ne_of_val (by decide)), hr6o registers.one (fin_ne_of_val (by decide)),
        hr5o registers.one (fin_ne_of_val (by decide)), hr4o registers.one (fin_ne_of_val (by decide)),
        hr3o registers.one (fin_ne_of_val (by decide)), hr21]
  have h11c : (reg s11 count).val = Q := by
    rw [hr11o count (fin_ne_of_val (by decide)), hr10o count (fin_ne_of_val (by decide)),
        hr9o count (fin_ne_of_val (by decide)), hr8o count (fin_ne_of_val (by decide)),
        hr7o count (fin_ne_of_val (by decide)), hr6o count (fin_ne_of_val (by decide)),
        hr5o count (fin_ne_of_val (by decide)), hr4o count (fin_ne_of_val (by decide)), hr3c]
  have hc6 : (reg s6 count).val = Q := by
    rw [hr6o count (fin_ne_of_val (by decide)), hr5o count (fin_ne_of_val (by decide)),
        hr4o count (fin_ne_of_val (by decide)), hr3c]
  have h7t : (reg s7 tinBase).val = 2 * Q := by
    rw [hr7t, add_no_wrap _ _ (by rw [hc6]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), hc6]; omega
  have h11t : (reg s11 tinBase).val = 2 * Q := by
    rw [hr11o tinBase (fin_ne_of_val (by decide)), hr10o tinBase (fin_ne_of_val (by decide)),
        hr9o tinBase (fin_ne_of_val (by decide)), hr8o tinBase (fin_ne_of_val (by decide)), h7t]
  have h1_7 : (reg s7 registers.one).val = 1 := by
    rw [hr7o registers.one (fin_ne_of_val (by decide)), hr6o registers.one (fin_ne_of_val (by decide)),
        hr5o registers.one (fin_ne_of_val (by decide)), hr4o registers.one (fin_ne_of_val (by decide)),
        hr3o registers.one (fin_ne_of_val (by decide)), hr21]
  have h8to : (reg s8 toutBase).val = 2 * Q + 1 := by
    rw [hr8to, add_no_wrap _ _ (by rw [h7t, h1_7]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), h7t, h1_7]
  have h11to : (reg s11 toutBase).val = 2 * Q + 1 := by
    rw [hr11o toutBase (fin_ne_of_val (by decide)), hr10o toutBase (fin_ne_of_val (by decide)),
        hr9o toutBase (fin_ne_of_val (by decide)), h8to]
  have h1_8 : (reg s8 registers.one).val = 1 := by
    rw [hr8o registers.one (fin_ne_of_val (by decide)), h1_7]
  have h9off : (reg s9 offsetBase).val = 2 * Q + 2 := by
    rw [hr9off, add_no_wrap _ _ (by rw [h8to, h1_8]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), h8to, h1_8]
  have h11off : (reg s11 offsetBase).val = 2 * Q + 2 := by
    rw [hr11o offsetBase (fin_ne_of_val (by decide)), hr10o offsetBase (fin_ne_of_val (by decide)), h9off]
  have h11sb : (reg s11 registers.stackBase).val = 5 * Q := by
    have ht9 : (reg s9 tinBase).val = 2 * Q := by
      rw [hr9o tinBase (fin_ne_of_val (by decide)), hr8o tinBase (fin_ne_of_val (by decide)), h7t]
    have h10sb : (reg s10 registers.stackBase).val = 4 * Q := by
      rw [hr10sb, add_no_wrap _ _ (by rw [ht9]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), ht9]; omega
    have hc10 : (reg s10 count).val = Q := by
      rw [hr10o count (fin_ne_of_val (by decide)), hr9o count (fin_ne_of_val (by decide)),
          hr8o count (fin_ne_of_val (by decide)), hr7o count (fin_ne_of_val (by decide)),
          hr6o count (fin_ne_of_val (by decide)), hr5o count (fin_ne_of_val (by decide)),
          hr4o count (fin_ne_of_val (by decide)), hr3c]
    rw [hr11sb, add_no_wrap _ _ (by rw [h10sb, hc10]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), h10sb, hc10]; omega
  have h11ch : (reg s11 childrenBase).val = 3 + Q := by
    have hc4 : (reg s4 count).val = Q := by rw [hr4o count (fin_ne_of_val (by decide)), hr3c]
    have ht4 : (reg s4 tinBase).val = 2 := by rw [hr4t]
    have h5ch : (reg s5 childrenBase).val = 2 + Q := by
      rw [hr5ch, add_no_wrap _ _ (by rw [ht4, hc4]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), ht4, hc4]
    have h1_5 : (reg s5 registers.one).val = 1 := by
      rw [hr5o registers.one (fin_ne_of_val (by decide)), hr4o registers.one (fin_ne_of_val (by decide)),
          hr3o registers.one (fin_ne_of_val (by decide)), hr21]
    have h6ch : (reg s6 childrenBase).val = 3 + Q := by
      rw [hr6ch, add_no_wrap _ _ (by rw [h5ch, h1_5]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)), h5ch, h1_5]; omega
    rw [hr11o childrenBase (fin_ne_of_val (by decide)), hr10o childrenBase (fin_ne_of_val (by decide)),
        hr9o childrenBase (fin_ne_of_val (by decide)), hr8o childrenBase (fin_ne_of_val (by decide)),
        hr7o childrenBase (fin_ne_of_val (by decide)), h6ch]
  have hpc11_eq : s11.pc = 11 := by omega
  have hFit11 : (reg s11 registers.zero).val < s11.data.size := by
    rw [h11z, s11.data_size]; have := sp.workBounds; omega
  have hf11 : code[s11.pc]? = some (.storeData registers.zero registers.zero) := by rw [hpc11_eq]; rfl
  obtain ⟨s12, hs12, hpc12, hr12, hd12⟩ :=
    step_storeData_exists hf11 hFit11 (by rw [hpc11_eq, hSize]; omega)
  have h12r : ∀ r, reg s12 r = reg s11 r := fun r => reg_eq_of_regs_eq hr12 r
  have hFit12 : (reg s12 count).val < s12.data.size := by
    rw [h12r count, h11c, s12.data_size]; have := sp.workBounds; omega
  have hf12 : code[s12.pc]? = some (.storeData count registers.zero) := by rw [hpc12, hpc11_eq]; rfl
  obtain ⟨s13, hs13, hpc13, hr13, hd13⟩ :=
    step_storeData_exists hf12 hFit12 (by rw [hpc12, hpc11_eq, hSize]; omega)
  have h13r : ∀ r, reg s13 r = reg s12 r := fun r => reg_eq_of_regs_eq hr13 r
  have hFit13 : (reg s13 tinBase).val < s13.data.size := by
    rw [h13r tinBase, h12r tinBase, h11t, s13.data_size]; have := sp.workBounds; omega
  have hf13 : code[s13.pc]? = some (.storeData tinBase registers.zero) := by
    rw [hpc13, hpc12, hpc11_eq]; rfl
  obtain ⟨s14, hs14, hpc14, hr14, hd14⟩ :=
    step_storeData_exists hf13 hFit13 (by rw [hpc13, hpc12, hpc11_eq, hSize]; omega)
  have h14r : ∀ r, reg s14 r = reg s13 r := fun r => reg_eq_of_regs_eq hr14 r
  have hFit14 : (reg s14 toutBase).val < s14.data.size := by
    rw [h14r toutBase, h13r toutBase, h12r toutBase, h11to, s14.data_size]; have := sp.workBounds; omega
  have hf14 : code[s14.pc]? = some (.storeData toutBase registers.zero) := by
    rw [hpc14, hpc13, hpc12, hpc11_eq]; rfl
  obtain ⟨s15, hs15, hpc15, hr15, hd15⟩ :=
    step_storeData_exists hf14 hFit14 (by rw [hpc14, hpc13, hpc12, hpc11_eq, hSize]; omega)
  have h15r : ∀ r, reg s15 r = reg s14 r := fun r => reg_eq_of_regs_eq hr15 r
  have hFit15 : (reg s15 offsetBase).val < s15.data.size := by
    rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off, s15.data_size]
    have := sp.workBounds; omega
  have hf15 : code[s15.pc]? = some (.storeData offsetBase registers.zero) := by
    rw [hpc15, hpc14, hpc13, hpc12, hpc11_eq]; rfl
  obtain ⟨s16, hs16, hpc16, hr16, hd16⟩ :=
    step_storeData_exists hf15 hFit15 (by rw [hpc15, hpc14, hpc13, hpc12, hpc11_eq, hSize]; omega)
  have h16r : ∀ r, reg s16 r = reg s15 r := fun r => reg_eq_of_regs_eq hr16 r
  have hFit16 : (reg s16 registers.stackBase).val < s16.data.size := by
    rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
        h13r registers.stackBase, h12r registers.stackBase, h11sb, s16.data_size]
    have := sp.workBounds; omega
  have hf16 : code[s16.pc]? = some (.storeData registers.stackBase registers.one) := by
    rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11_eq]; rfl
  obtain ⟨s17, hs17, hpc17, hr17, hd17⟩ :=
    step_storeData_exists hf16 hFit16 (by rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11_eq, hSize]; omega)
  have h17r : ∀ r, reg s17 r = reg s11 r := fun r =>
    (reg_eq_of_regs_eq hr17 r).trans ((h16r r).trans ((h15r r).trans ((h14r r).trans ((h13r r).trans (h12r r)))))
  have hSteps : Steps code input 17 s0 s17 :=
    .cons hs1 (.cons hs2 (.cons hs3 (.cons hs4 (.cons hs5 (.cons hs6 (.cons hs7
    (.cons hs8 (.cons hs9 (.cons hs10 (.cons hs11 (.cons hs12 (.cons hs13 (.cons hs14
    (.cons hs15 (.cons hs16 (.cons hs17 (.zero _)))))))))))))))))
  have hQPos := sp.qPos
  have hCell5Q : (s17.data[5 * Q]?).map Fin.val = some 1 := by
    rw [hd17, Array.getElem?_set]; split
    · simp only [Option.map_some, h16r registers.one, h15r registers.one,
        h14r registers.one, h13r registers.one, h12r registers.one, h11one]
    · rename_i hNe; exfalso; apply hNe
      rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
          h13r registers.stackBase, h12r registers.stackBase, h11sb]
  have hCell0 : (s17.data[0]?).map Fin.val = some 0 := by
    rw [hd17, Array.getElem?_set]; split
    · rename_i hEq; have : (reg s16 registers.stackBase).val = 5 * Q := by
        rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
            h13r registers.stackBase, h12r registers.stackBase, h11sb]
      omega
    · rw [hd16, Array.getElem?_set]; split
      · rename_i hEq; have : (reg s15 offsetBase).val = 2 * Q + 2 := by
          rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off]
        omega
      · rw [hd15, Array.getElem?_set]; split
        · rename_i hEq; have : (reg s14 toutBase).val = 2 * Q + 1 := by
            rw [h14r toutBase, h13r toutBase, h12r toutBase, h11to]
          omega
        · rw [hd14, Array.getElem?_set]; split
          · rename_i hEq; have : (reg s13 tinBase).val = 2 * Q := by
              rw [h13r tinBase, h12r tinBase, h11t]
            omega
          · rw [hd13, Array.getElem?_set]; split
            · rename_i hEq; have : (reg s12 count).val = Q := by rw [h12r count, h11c]
              omega
            · rw [hd12, Array.getElem?_set]; split
              · simp only [Option.map_some, h11z]
              · rename_i hNe; exfalso; exact hNe h11z
  have hCellQ : (s17.data[Q]?).map Fin.val = some 0 := by
    rw [hd17, Array.getElem?_set]; split
    · rename_i hEq; have : (reg s16 registers.stackBase).val = 5 * Q := by
        rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
            h13r registers.stackBase, h12r registers.stackBase, h11sb]
      omega
    · rw [hd16, Array.getElem?_set]; split
      · rename_i hEq; have : (reg s15 offsetBase).val = 2 * Q + 2 := by
          rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off]
        omega
      · rw [hd15, Array.getElem?_set]; split
        · rename_i hEq; have : (reg s14 toutBase).val = 2 * Q + 1 := by
            rw [h14r toutBase, h13r toutBase, h12r toutBase, h11to]
          omega
        · rw [hd14, Array.getElem?_set]; split
          · rename_i hEq; have : (reg s13 tinBase).val = 2 * Q := by
              rw [h13r tinBase, h12r tinBase, h11t]
            omega
          · rw [hd13, Array.getElem?_set]; split
            · simp only [Option.map_some, h12r registers.zero, h11z]
            · rename_i hNe; exfalso; apply hNe; rw [h12r count, h11c]
  have hCell2Q : (s17.data[2 * Q]?).map Fin.val = some 0 := by
    rw [hd17, Array.getElem?_set]; split
    · rename_i hEq; have : (reg s16 registers.stackBase).val = 5 * Q := by
        rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
            h13r registers.stackBase, h12r registers.stackBase, h11sb]
      omega
    · rw [hd16, Array.getElem?_set]; split
      · rename_i hEq; have : (reg s15 offsetBase).val = 2 * Q + 2 := by
          rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off]
        omega
      · rw [hd15, Array.getElem?_set]; split
        · rename_i hEq; have : (reg s14 toutBase).val = 2 * Q + 1 := by
            rw [h14r toutBase, h13r toutBase, h12r toutBase, h11to]
          omega
        · rw [hd14, Array.getElem?_set]; split
          · simp only [Option.map_some, h13r registers.zero, h12r registers.zero, h11z]
          · rename_i hNe; exfalso; apply hNe; rw [h13r tinBase, h12r tinBase, h11t]
  have hCell2Q1 : (s17.data[2 * Q + 1]?).map Fin.val = some 0 := by
    rw [hd17, Array.getElem?_set]; split
    · rename_i hEq; have : (reg s16 registers.stackBase).val = 5 * Q := by
        rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
            h13r registers.stackBase, h12r registers.stackBase, h11sb]
      omega
    · rw [hd16, Array.getElem?_set]; split
      · rename_i hEq; have : (reg s15 offsetBase).val = 2 * Q + 2 := by
          rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off]
        omega
      · rw [hd15, Array.getElem?_set]; split
        · simp only [Option.map_some, h14r registers.zero, h13r registers.zero, h12r registers.zero, h11z]
        · rename_i hNe; exfalso; apply hNe; rw [h14r toutBase, h13r toutBase, h12r toutBase, h11to]
  have hCell2Q2 : (s17.data[2 * Q + 2]?).map Fin.val = some 0 := by
    rw [hd17, Array.getElem?_set]; split
    · rename_i hEq; have : (reg s16 registers.stackBase).val = 5 * Q := by
        rw [h16r registers.stackBase, h15r registers.stackBase, h14r registers.stackBase,
            h13r registers.stackBase, h12r registers.stackBase, h11sb]
      omega
    · rw [hd16, Array.getElem?_set]; split
      · simp only [Option.map_some, h15r registers.zero, h14r registers.zero,
            h13r registers.zero, h12r registers.zero, h11z]
      · rename_i hNe; exfalso; apply hNe; rw [h15r offsetBase, h14r offsetBase, h13r offsetBase, h12r offsetBase, h11off]
  refine ⟨s17, hSteps, by omega,
    { zeroVal := by rw [h17r registers.zero, h11z]
      oneVal := by rw [h17r registers.one, h11one]
      countVal := by rw [h17r count, h11c]
      tinVal := by rw [h17r tinBase, h11t]
      toutVal := by rw [h17r toutBase, h11to]
      offsetVal := by rw [h17r offsetBase, h11off]
      stackVal := by rw [h17r registers.stackBase, h11sb]
      childrenVal := by rw [h17r childrenBase, h11ch] },
    domPrefixInv_init sp s17.data_size hCell0 hCellQ hCell2Q hCell2Q1 hCell2Q2,
    hCell5Q, s17.data_size⟩

private theorem seekSubroutine_steps {input : Input L} {Q : Nat} (hTen : 10 ≤ 2 ^ bits)
    {F : JumpForest} {s : State L}
    (hPC : s.pc = 84)
    (hFix : DomRegsFixed Q s)
    (hRec : Records (2 * Q) F s.data)
    (hFLe : F.size ≤ Q)
    {u target : Nat} (hu : u < F.size) (_hTarget : target ≤ F.depthOf u)
    (hPtr : (reg s registers.ptr).val = u)
    (hCmd : (reg s cmd).val = target) :
    ∃ t k, k ≤ 60 * OracleContract.L Q + 5 ∧
      Steps (domLoopCode hi hw hTen) input k s t ∧
      t.pc = 111 ∧ t.data = s.data ∧
      DomRegsFixed Q t ∧
      (reg t registers.ptr).val = F.ancestorAtDepth u target ∧
      (reg t cmd).val = target := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hFitD : (reg s toutBase).val + 3 * (reg s registers.ptr).val < s.data.size := by
    rw [hFix.toutVal, hPtr]
    have := hRec.fit
    omega
  have hReadD : (s.data[(reg s toutBase).val + 3 * (reg s registers.ptr).val]?).map Fin.val =
      some (F.depthOf u) := by
    rw [hFix.toutVal, hPtr]; exact hRec.depth u hu
  cases hOptD : s.data[(reg s toutBase).val + 3 * (reg s registers.ptr).val]? with
  | none => rw [hOptD] at hReadD; cases hReadD
  | some wD =>
    rw [hOptD, Option.map_some] at hReadD
    have hwD : wD.val = F.depthOf u := Option.some.inj hReadD
    obtain ⟨s1, hs1, hpc1, hd1, hr1clk, hr1o⟩ :=
      recordField_steps_at (seekPreload_placed hTen) hPC (by rw [hCodeSize]; omega)
        (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)) hFitD hOptD
    have hClk1 : (reg s1 clk).val = F.depthOf u := by rw [hr1clk, hwD]
    have hPtr1 : (reg s1 registers.ptr).val = u := by
      rw [hr1o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hPtr]
    have hCmd1 : (reg s1 cmd).val = target := by
      rw [hr1o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hCmd]
    have hFix1 : DomRegsFixed Q s1 :=
      domRegsFixed_eq_of_eq hFix (fun r hr =>
        hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    let s0 : State L := { s1 with pc := 0 }
    have hFixed0 : Fixed (2 * Q) target s0 :=
      ⟨by change (reg s1 tinBase).val = 2 * Q; exact hFix1.tinVal,
       by change (reg s1 toutBase).val = 2 * Q + 1; exact hFix1.toutVal,
       by change (reg s1 offsetBase).val = 2 * Q + 2; exact hFix1.offsetVal,
       by change (reg s1 cmd).val = target; exact hCmd1,
       by change (reg s1 registers.zero).val = 0; exact hFix1.zeroVal⟩
    have hRec0 : Records (2 * Q) F s0.data := by rw [show s0.data = s.data from hd1]; exact hRec
    have hSeekAt : SeekAt (2 * Q) F target u s0 :=
      ⟨rfl, hFixed0, hRec0, hu, hPtr1, hClk1⟩
    have hIns : F.numInserted ≤ Q - 1 := by
      unfold JumpForest.numInserted
      change F.records.length - 1 ≤ Q - 1
      change F.records.length ≤ Q at hFLe
      omega
    have hExp : (Q - 1) + 2 ≤ 2 ^ OracleContract.L Q := by
      have hLt : Q + 1 < 2 ^ OracleContract.L Q :=
        (Nat.log2_lt (Nat.succ_ne_zero Q)).mp (Nat.lt_succ_self _)
      omega
    obtain ⟨t0, _, work, hWorkLe, hRun0, hAnc0, hData0, _, _⟩ :=
      run_depth_seek_logarithmic input s0 hSeekAt (Q - 1) (OracleContract.L Q) hIns hExp
    have hWorkPos : 1 ≤ work := by
      cases work with
      | zero => simp [run] at hRun0
      | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    obtain ⟨k0, rfl⟩ : ∃ k0, work = k0 + 1 := ⟨work - 1, by omega⟩
    obtain ⟨t, htSteps, htpc, htregs, htdata, htFix⟩ :=
      seekProgram_run_to_domLoop hTen k0 s0 t0 s1 hRun0 (by simp [s0, hpc1]) rfl rfl (by simp [s0])
    refine ⟨t, 4 + k0, by omega, hs1.append htSteps, htpc, by rw [htdata, hData0, hd1],
      domRegsFixed_eq_of_eq hFix1 (fun r hr => htFix r (domFixed_implies_fixed r hr)), ?_, ?_⟩
    · have := reg_eq_of_regs_eq htregs registers.ptr
      change (reg t registers.ptr).val = _
      rw [this, hAnc0]
    · have := htFix cmd rfl
      change (reg t cmd).val = _
      rw [this]; exact hCmd1

private theorem placed3_of_get {code : Program L} {base : Nat} {a b c : Instr bits 15}
    (h0 : code[base]? = some a)
    (h1 : code[base + 1]? = some b)
    (h2 : code[base + 2]? = some c) :
    Placed code base [a, b, c] := by
  intro i op hOp
  match i with
  | 0 => cases hOp; exact h0
  | 1 => cases hOp; exact h1
  | 2 => cases hOp; exact h2
  | _ + 3 => cases hOp

private theorem placed4_of_get {code : Program L} {base : Nat} {a b c d : Instr bits 15}
    (h0 : code[base]? = some a)
    (h1 : code[base + 1]? = some b)
    (h2 : code[base + 2]? = some c)
    (h3 : code[base + 3]? = some d) :
    Placed code base [a, b, c, d] := by
  intro i op hOp
  match i with
  | 0 => cases hOp; exact h0
  | 1 => cases hOp; exact h1
  | 2 => cases hOp; exact h2
  | 3 => cases hOp; exact h3
  | _ + 4 => cases hOp

private theorem loop_readScratch {input : Input L} {Q : Nat} (hTen : 10 ≤ 2 ^ bits)
    {s : State L} {base off v : Nat} {dst : Fin 15} {hOff : off < 2 ^ bits}
    (hPlaced : Placed (domLoopCode hi hw hTen) base (readScratchInstrs dst off hOff))
    (hPC : s.pc = base)
    (hEnd : base + 3 < 209)
    (hFix : DomRegsFixed Q s)
    (hWork : 5 * Q + 10 ≤ workCap)
    (hOff10 : off < 10)
    (hVal : (s.data[5 * Q + off]?).map Fin.val = some v)
    (hNe : dst ≠ registers.tmp) :
    ∃ t, Steps (domLoopCode hi hw hTen) input 3 s t ∧ t.pc = base + 3 ∧ t.data = s.data ∧
      (reg t dst).val = v ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ registers.tmp → reg t r = reg s r) := by
  have hStack : (reg s registers.stackBase).val + off < s.data.size := by
    rw [hFix.stackVal, s.data_size]
    change 5 * Q + off < workCap
    omega
  have hRead : (s.data[(reg s registers.stackBase).val + off]?).map Fin.val = some v := by
    rw [hFix.stackVal]; exact hVal
  cases hCell : s.data[(reg s registers.stackBase).val + off]? with
  | none => rw [hCell] at hRead; cases hRead
  | some w =>
    rw [hCell, Option.map_some] at hRead
    obtain ⟨t, htSteps, htpc, htdata, htdst, hto⟩ :=
      readScratch_steps hPlaced hPC (by rw [domLoopCode_size]; exact hEnd) hStack hCell hNe
    refine ⟨t, htSteps, htpc, htdata, ?_, hto⟩
    rw [htdst]; exact Option.some.inj hRead

private theorem loop_writeScratch {input : Input L} {Q : Nat} (hTen : 10 ≤ 2 ^ bits)
    {s : State L} {base off : Nat} {src : Fin 15} {hOff : off < 2 ^ bits}
    (hPlaced : Placed (domLoopCode hi hw hTen) base (writeScratchInstrs off src hOff))
    (hPC : s.pc = base)
    (hEnd : base + 3 < 209)
    (hFix : DomRegsFixed Q s)
    (hWork : 5 * Q + 10 ≤ workCap)
    (hOff10 : off < 10)
    (hNe : src ≠ registers.tmp) :
    ∃ t, Steps (domLoopCode hi hw hTen) input 3 s t ∧ t.pc = base + 3 ∧ t.data.size = s.data.size ∧
      (t.data[5 * Q + off]?).map Fin.val = some (reg s src).val ∧
      (∀ j, j ≠ 5 * Q + off → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ registers.tmp → reg t r = reg s r) := by
  have hStack : (reg s registers.stackBase).val + off < s.data.size := by
    rw [hFix.stackVal, s.data_size]
    change 5 * Q + off < workCap
    omega
  obtain ⟨t, htSteps, htpc, htsize, htcell, htkeep, hto⟩ :=
    writeScratch_steps hPlaced hPC (by rw [domLoopCode_size]; exact hEnd) hStack hNe
  rw [hFix.stackVal] at htcell htkeep
  refine ⟨t, htSteps, htpc, htsize, ?_, htkeep, hto⟩
  rw [htcell]; rfl

private structure BSearchState
    (Q v arcPtr arcEnd cur rhs loBound hiBound : Nat) (F : JumpForest) (s : State L) : Prop where
  fix : DomRegsFixed Q s
  dataSize : s.data.size = workCap
  workRoom : 5 * Q + 10 ≤ workCap
  fSizeLe : F.size ≤ Q
  fValid : ValidJumpForest F
  records : Records (2 * Q) F s.data
  curLt : cur < F.size
  rhsLt : rhs < F.size
  loLtHi : loBound < hiBound
  hiLe : hiBound ≤ min (F.depthOf cur) (F.depthOf rhs) + 1
  ancEq : F.ancestorAtDepth cur loBound = F.ancestorAtDepth rhs loBound
  ancNeAbove : ∀ d, hiBound ≤ d → d ≤ F.depthOf cur → d ≤ F.depthOf rhs →
    F.ancestorAtDepth cur d ≠ F.ancestorAtDepth rhs d
  slotV : (s.data[5 * Q + 0]?).map Fin.val = some v
  slotArcPtr : (s.data[5 * Q + 1]?).map Fin.val = some arcPtr
  slotArcEnd : (s.data[5 * Q + 2]?).map Fin.val = some arcEnd
  slotCur : (s.data[5 * Q + 3]?).map Fin.val = some cur
  slotRhs : (s.data[5 * Q + 4]?).map Fin.val = some rhs
  slotLo : (s.data[5 * Q + 5]?).map Fin.val = some loBound
  slotHi : (s.data[5 * Q + 6]?).map Fin.val = some hiBound

private theorem records_preserve {base : Nat} {F : JumpForest} {d1 d2 : Array (Word bits)}
    (hRec : Records base F d1) (hSize : d2.size = d1.size)
    (hKeep : ∀ j, j < base + 3 * F.size → d2[j]? = d1[j]?) :
    Records base F d2 := by
  refine ⟨hRec.valid, by rw [hSize]; exact hRec.fit, ?_, ?_, ?_⟩
  · intro u hu; rw [hKeep _ (by omega)]; exact hRec.parent u hu
  · intro u hu; rw [hKeep _ (by omega)]; exact hRec.depth u hu
  · intro u hu; rw [hKeep _ (by omega)]; exact hRec.jump u hu

private theorem records_preserve_ge {base : Nat} {F : JumpForest} {d1 d2 : Array (Word bits)}
    (hRec : Records base F d1) (hSize : d2.size = d1.size)
    (hKeep : ∀ j, base ≤ j → j < base + 3 * F.size → d2[j]? = d1[j]?) :
    Records base F d2 := by
  refine ⟨hRec.valid, by rw [hSize]; exact hRec.fit, ?_, ?_, ?_⟩
  · intro u hu; rw [hKeep _ (by omega) (by omega)]; exact hRec.parent u hu
  · intro u hu; rw [hKeep _ (by omega) (by omega)]; exact hRec.depth u hu
  · intro u hu; rw [hKeep _ (by omega) (by omega)]; exact hRec.jump u hu

private theorem bsearch_exit_steps {input : Input L} {Q v arcPtr arcEnd : Nat}
    (spWork : 5 * Q + 10 ≤ workCap) (hArcFit : arcPtr + 1 ≤ arcEnd) (hArcM : arcEnd < 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits)
    {cur rhs loBound hiBound : Nat} {F : JumpForest} {s : State L}
    (hPC : s.pc = 53)
    (bs : BSearchState Q v arcPtr arcEnd cur rhs loBound hiBound F s)
    (hEqHi : hiBound = loBound + 1) :
    ∃ t k, k ≤ 60 * OracleContract.L Q + 40 ∧
      Steps (domLoopCode hi hw hTen) input k s t ∧
      t.pc = 21 ∧ DomRegsFixed Q t ∧ t.data.size = workCap ∧
      (∀ j, j < 5 * Q → t.data[j]? = s.data[j]?) ∧
      (t.data[5 * Q + 0]?).map Fin.val = some v ∧
      (t.data[5 * Q + 1]?).map Fin.val = some (arcPtr + 1) ∧
      (t.data[5 * Q + 2]?).map Fin.val = some arcEnd ∧
      (∃ cur', cur' < F.size ∧ (t.data[5 * Q + 3]?).map Fin.val = some cur' ∧
        (∀ a, a < F.size → (IsAncestor F a cur' ↔ IsAncestor F a cur ∧ IsAncestor F a rhs))) := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hB := bsearch_placed (hi := hi) (hw := hw) hTen
  have hD := dispatch_placed (hi := hi) (hw := hw) hTen
  have hP53 : Placed code 53 (readScratchInstrs registers.ptr 5 (by omega)) :=
    placed3_of_get (hB 0 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 1 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 2 _ (by simp [bsearchBlock, readScratchInstrs]))
  have hP56 : Placed code 56 (readScratchInstrs registers.remain 6 (by omega)) :=
    placed3_of_get (hB 3 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 4 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 5 _ (by simp [bsearchBlock, readScratchInstrs]))
  obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
    loop_readScratch hTen hP53 hPC (by omega) bs.fix spWork (by omega) bs.slotLo (fin_ne_of_val (by decide))
  have hFix1 : DomRegsFixed Q s1 :=
    domRegsFixed_eq_of_eq bs.fix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  obtain ⟨s2, hs2, hpc2, hd2, hr2r, hr2o⟩ :=
    loop_readScratch hTen hP56 hpc1 (by omega) hFix1 spWork (by omega) (by rw [hd1]; exact bs.slotHi) (fin_ne_of_val (by decide))
  have hFix2 : DomRegsFixed Q s2 :=
    domRegsFixed_eq_of_eq hFix1 (fun r hr => hr2o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr2p : (reg s2 registers.ptr).val = loBound := by
    rw [hr2o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr1p]
  have h59 : code[s2.pc]? = some (.add registers.value registers.ptr registers.one) := by
    rw [hpc2]; exact hB 6 _ (by simp [bsearchBlock, readScratchInstrs])
  obtain ⟨s3, hs3, hpc3, hr3v, hr3o, hd3⟩ :=
    step_add_at (input := input) h59 (by rw [hCodeSize, hpc2]; omega)
  have hVal3 : (reg s3 registers.value).val = loBound + 1 := by
    have hFit : (reg s2 registers.ptr).val + (reg s2 registers.one).val < 2 ^ bits := by
      rw [hr2p, hFix2.oneVal]; have := bs.hiLe; have := jumpForest_depthOf_lt_size bs.fValid bs.curLt; have := bs.fSizeLe; omega
    rw [hr3v, add_no_wrap _ _ hFit, hr2p, hFix2.oneVal]
  have hRem3 : (reg s3 registers.remain).val = hiBound := by
    rw [hr3o registers.remain (fin_ne_of_val (by decide)), hr2r]
  have hFalse : ltb (reg s3 registers.value) (reg s3 registers.remain) = false := by
    cases hCmp : ltb (reg s3 registers.value) (reg s3 registers.remain) with
    | false => rfl
    | true => have hLt := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hVal3, hRem3] at hLt; omega
  have h60 : code[s3.pc]? = some (.branchLt registers.value registers.remain 61 74) := by
    rw [hpc3, hpc2]; exact hB 7 _ (by simp [bsearchBlock, readScratchInstrs])
  have hs34 := step_branchLt_at (input := input) h60 (by rw [hCodeSize]; split <;> omega)
  let s4 : State L := { s3 with pc := if ltb (reg s3 registers.value) (reg s3 registers.remain) = true then 61 else 74 }
  have hpc4 : s4.pc = 74 := by simp only [s4, hFalse, Bool.false_eq_true, ite_false]
  have hFix4 : DomRegsFixed Q s4 :=
    domRegsFixed_eq_of_eq hFix2 (fun r hr => hr3o r (fun e => by subst e; cases hr))
  have hd4 : s4.data = s.data := by change s3.data = s.data; rw [hd3, hd2, hd1]
  -- 74..83: imm remain 2, writeScratch 9 remain, readScratch cmd 5, readScratch ptr 3
  have h74 : code[s4.pc]? = some (.imm registers.remain ⟨2, by omega⟩) := by
    rw [hpc4]; exact hB 21 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs])
  obtain ⟨s5, hs5, hpc5, hr5r, hr5o, hd5⟩ :=
    step_imm_at (input := input) h74 (by rw [hCodeSize, hpc4]; omega)
  have hFix5 : DomRegsFixed Q s5 :=
    domRegsFixed_eq_of_eq hFix4 (fun r hr => hr5o r (fun e => by subst e; cases hr))
  have hP75 : Placed code 75 (writeScratchInstrs 9 registers.remain (by omega)) :=
    placed3_of_get (hB 22 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 23 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 24 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s6, hs6, hpc6, hd6size, h6slot9, h6keep, hr6o⟩ :=
    loop_writeScratch hTen hP75 (by omega) (by omega) hFix5 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix6 : DomRegsFixed Q s6 :=
    domRegsFixed_eq_of_eq hFix5 (fun r hr => hr6o r (fun e => by subst e; cases hr))
  have hP78 : Placed code 78 (readScratchInstrs cmd 5 (by omega)) :=
    placed3_of_get (hB 25 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 26 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 27 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s7, hs7, hpc7, hd7, hr7cmd, hr7o⟩ :=
    loop_readScratch hTen hP78 hpc6 (by omega) hFix6 spWork (by omega)
      (by rw [h6keep _ (by omega), hd5, hd4]; exact bs.slotLo) (fin_ne_of_val (by decide))
  have hFix7 : DomRegsFixed Q s7 :=
    domRegsFixed_eq_of_eq hFix6 (fun r hr => hr7o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hP81 : Placed code 81 (readScratchInstrs registers.ptr 3 (by omega)) :=
    placed3_of_get (hB 28 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 29 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 30 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s8, hs8, hpc8, hd8, hr8ptr, hr8o⟩ :=
    loop_readScratch hTen hP81 hpc7 (by omega) hFix7 spWork (by omega)
      (by rw [hd7, h6keep _ (by omega), hd5, hd4]; exact bs.slotCur) (fin_ne_of_val (by decide))
  have hFix8 : DomRegsFixed Q s8 :=
    domRegsFixed_eq_of_eq hFix7 (fun r hr => hr8o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr8cmd : (reg s8 cmd).val = loBound := by
    rw [hr8o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr7cmd]
  have hRec8 : Records (2 * Q) F s8.data := by
    have := bs.fSizeLe
    exact records_preserve bs.records (by rw [hd8, hd7, hd6size, hd5, hd4])
      (fun j hj => by rw [hd8, hd7, h6keep _ (by omega), hd5, hd4])
  have hLoLe : loBound ≤ F.depthOf cur := by have := bs.hiLe; have := bs.loLtHi; omega
  obtain ⟨s9, kSeek, hkSeek, hsSeek, hpc9, hd9, hFix9, hr9ptr, _⟩ :=
    seekSubroutine_steps hTen hpc8 hFix8 hRec8 bs.fSizeLe bs.curLt hLoLe hr8ptr hr8cmd
  -- Dispatch retMode = 2 at 111..114, 128..129, 146..156:
  have hP111 : Placed code 111 (readScratchInstrs registers.remain 9 (by omega)) :=
    placed3_of_get (hD 0 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 1 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 2 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h9slot9 : (s9.data[5 * Q + 9]?).map Fin.val = some 2 := by
    rw [hd9, hd8, hd7, h6slot9]; simp only [hr5r]
  obtain ⟨s10, hs10, hpc10, hd10, hr10rem, hr10o⟩ :=
    loop_readScratch hTen hP111 hpc9 (by omega) hFix9 spWork (by omega) h9slot9 (fin_ne_of_val (by decide))
  have hFix10 : DomRegsFixed Q s10 :=
    domRegsFixed_eq_of_eq hFix9 (fun r hr => hr10o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have h114 : code[s10.pc]? = some (.branchLt registers.remain registers.one 115 128) := by
    rw [hpc10]; exact hD 3 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs10_11 := step_branchLt_at (input := input) h114 (by rw [hCodeSize]; split <;> omega)
  have hCmp10 : ltb (reg s10 registers.remain) (reg s10 registers.one) = false := by
    cases hCmp : ltb (reg s10 registers.remain) (reg s10 registers.one) with
    | false => rfl
    | true => have hLt := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hr10rem, hFix10.oneVal] at hLt; omega
  let s11 : State L := { s10 with pc := if ltb (reg s10 registers.remain) (reg s10 registers.one) = true then 115 else 128 }
  have hpc11 : s11.pc = 128 := by simp only [s11, hCmp10, Bool.false_eq_true, ite_false]
  have hFix11 : DomRegsFixed Q s11 := domRegsFixed_eq_of_eq hFix10 (fun _ _ => rfl)
  have h128 : code[s11.pc]? = some (.imm registers.value ⟨2, by omega⟩) := by
    rw [hpc11]; exact hD 17 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  obtain ⟨s12, hs12, hpc12, hr12v, hr12o, hd12⟩ :=
    step_imm_at (input := input) h128 (by rw [hCodeSize, hpc11]; omega)
  have hFix12 : DomRegsFixed Q s12 :=
    domRegsFixed_eq_of_eq hFix11 (fun r hr => hr12o r (fun e => by subst e; cases hr))
  have hr12rem : (reg s12 registers.remain).val = 2 := by
    rw [hr12o registers.remain (fin_ne_of_val (by decide))]; exact hr10rem
  have hCmp12 : ltb (reg s12 registers.remain) (reg s12 registers.value) = false := by
    cases hCmp : ltb (reg s12 registers.remain) (reg s12 registers.value) with
    | false => rfl
    | true =>
      have hLt := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp
      simp only [hr12rem, hr12v] at hLt; omega
  have h129 : code[s12.pc]? = some (.branchLt registers.remain registers.value 130 146) := by
    rw [hpc12, hpc11]; exact hD 18 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs12_13 := step_branchLt_at (input := input) h129 (by rw [hCodeSize]; split <;> omega)
  let s13 : State L := { s12 with pc := if ltb (reg s12 registers.remain) (reg s12 registers.value) = true then 130 else 146 }
  have hpc13 : s13.pc = 146 := by simp only [s13, hCmp12, Bool.false_eq_true, ite_false]
  have hFix13 : DomRegsFixed Q s13 := domRegsFixed_eq_of_eq hFix12 (fun _ _ => rfl)
  have hr13ptr : (reg s13 registers.ptr).val = F.ancestorAtDepth cur loBound := by
    change (reg s12 registers.ptr).val = _
    rw [hr12o registers.ptr (fin_ne_of_val (by decide))]
    change (reg s10 registers.ptr).val = _
    rw [hr10o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr9ptr]
  have hd13eq : s13.data = s9.data := by
    change s12.data = s9.data; rw [hd12, show s11.data = s10.data from rfl, hd10]
  have hP146 : Placed code 146 (writeScratchInstrs 3 registers.ptr (by omega)) :=
    placed3_of_get (hD 35 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 36 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 37 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s14, hs14, hpc14, hd14size, h14slot3, h14keep, hr14o⟩ :=
    loop_writeScratch hTen hP146 hpc13 (by omega) hFix13 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix14 : DomRegsFixed Q s14 :=
    domRegsFixed_eq_of_eq hFix13 (fun r hr => hr14o r (fun e => by subst e; cases hr))
  have hP149 : Placed code 149 (readScratchInstrs registers.remain 1 (by omega)) :=
    placed3_of_get (hD 38 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 39 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 40 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s15, hs15, hpc15, hd15, hr15rem, hr15o⟩ :=
    loop_readScratch hTen hP149 hpc14 (by omega) hFix14 spWork (by omega)
      (by rw [h14keep _ (by omega), hd13eq, hd9, hd8, hd7, h6keep _ (by omega), hd5, hd4]; exact bs.slotArcPtr)
      (fin_ne_of_val (by decide))
  have hFix15 : DomRegsFixed Q s15 :=
    domRegsFixed_eq_of_eq hFix14 (fun r hr => hr15o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have h152 : code[s15.pc]? = some (.add registers.remain registers.remain registers.one) := by
    rw [hpc15]; exact hD 41 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  obtain ⟨s16, hs16, hpc16, hr16rem, hr16o, hd16⟩ :=
    step_add_at (input := input) h152 (by rw [hCodeSize, hpc15]; omega)
  have hFix16 : DomRegsFixed Q s16 :=
    domRegsFixed_eq_of_eq hFix15 (fun r hr => hr16o r (fun e => by subst e; cases hr))
  have hr16remVal : (reg s16 registers.remain).val = arcPtr + 1 := by
    have hFit : (reg s15 registers.remain).val + (reg s15 registers.one).val < 2 ^ bits := by
      rw [hr15rem, hFix15.oneVal]; omega
    rw [hr16rem, add_no_wrap _ _ hFit, hr15rem, hFix15.oneVal]
  have hP153 : Placed code 153 (writeScratchInstrs 1 registers.remain (by omega)) :=
    placed3_of_get (hD 42 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 43 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 44 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s17, hs17, hpc17, hd17size, h17slot1, h17keep, hr17o⟩ :=
    loop_writeScratch hTen hP153 (by omega) (by omega) hFix16 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix17 : DomRegsFixed Q s17 :=
    domRegsFixed_eq_of_eq hFix16 (fun r hr => hr17o r (fun e => by subst e; cases hr))
  have h156 : code[s17.pc]? = some (.goto 21) := by
    rw [hpc17]; exact hD 45 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs17_18 := step_goto_at (input := input) h156 (by rw [hCodeSize]; omega)
  let t : State L := { s17 with pc := 21 }
  have hStepsAll : Steps code input (18 + kSeek + 17) s t := by
    have p1 : Steps code input 18 s s8 := by
      have a : Steps code input 6 s s2 := hs1.append hs2
      have b : Steps code input 3 s2 s5 := Steps.cons hs3 (Steps.cons hs34 (Steps.cons hs5 (.zero _)))
      have c : Steps code input 9 s5 s8 := hs6.append (hs7.append hs8)
      simpa only [Nat.add_assoc] using (a.append b).append c
    have hsSeek' : Steps code input kSeek s8 s9 := hsSeek
    have p2 : Steps code input 17 s9 t := by
      have a : Steps code input 6 s9 s13 := hs10.append (Steps.cons hs10_11 (Steps.cons hs12 (Steps.cons hs12_13 (.zero _))))
      have b : Steps code input 11 s13 t := hs14.append (hs15.append (Steps.cons hs16 (hs17.append (Steps.cons hs17_18 (.zero _)))))
      simpa only [Nat.add_assoc] using a.append b
    simpa only [Nat.add_assoc] using (p1.append hsSeek').append p2
  have htDataSize : t.data.size = workCap := by
    change s17.data.size = workCap
    rw [hd17size, hd16, hd15, hd14size, hd13eq, hd9, hd8, hd7, hd6size, hd5, hd4]; exact bs.dataSize
  have hKeepPre : ∀ j, j < 5 * Q → t.data[j]? = s.data[j]? := by
    intro j hj
    change s17.data[j]? = s.data[j]?
    rw [h17keep _ (by omega), hd16, hd15, h14keep _ (by omega), hd13eq, hd9, hd8, hd7,
        h6keep _ (by omega), hd5, hd4]
  have hLCA := jumpForest_lca_complete bs.fValid bs.curLt bs.rhsLt hLoLe (by have := bs.hiLe; omega)
    bs.ancEq (fun d hd => bs.ancNeAbove d (by omega))
  refine ⟨t, 18 + kSeek + 17, by omega, hStepsAll, rfl,
    domRegsFixed_eq_of_eq hFix17 (fun _ _ => rfl), htDataSize, hKeepPre,
    ?_, ?_, ?_, F.ancestorAtDepth cur loBound, hLCA.1, ?_, hLCA.2⟩
  · change (s17.data[5 * Q + 0]?).map Fin.val = some v
    rw [h17keep _ (by omega), hd16, hd15, h14keep _ (by omega), hd13eq, hd9, hd8, hd7,
        h6keep _ (by omega), hd5, hd4]; exact bs.slotV
  · change (s17.data[5 * Q + 1]?).map Fin.val = some (arcPtr + 1)
    rw [h17slot1, hr16remVal]
  · change (s17.data[5 * Q + 2]?).map Fin.val = some arcEnd
    rw [h17keep _ (by omega), hd16, hd15, h14keep _ (by omega), hd13eq, hd9, hd8, hd7,
        h6keep _ (by omega), hd5, hd4]; exact bs.slotArcEnd
  · change (s17.data[5 * Q + 3]?).map Fin.val = some _
    rw [h17keep _ (by omega), hd16, hd15, h14slot3, hr13ptr]

private theorem bsearch_bisect_prefix {input : Input L} {Q v arcPtr arcEnd : Nat}
    (spWork : 5 * Q + 10 ≤ workCap) (hTen : 10 ≤ 2 ^ bits)
    {cur rhs loBound hiBound : Nat} {F : JumpForest} {s : State L}
    (hPC : s.pc = 53)
    (bs : BSearchState Q v arcPtr arcEnd cur rhs loBound hiBound F s)
    (hLt : loBound + 1 < hiBound) :
    let mid := loBound + (hiBound - loBound) / 2
    ∃ s26 : State L, ∃ k1 k2,
      k1 ≤ 60 * OracleContract.L Q + 5 ∧
      k2 ≤ 60 * OracleContract.L Q + 5 ∧
      Steps (domLoopCode hi hw hTen) input (21 + k1 + 17 + k2 + 12) s s26 ∧
      s26.pc = 136 ∧ DomRegsFixed Q s26 ∧
      (∀ j, j < 5 * Q + 7 → s26.data[j]? = s.data[j]?) ∧
      s26.data.size = workCap ∧
      loBound < mid ∧ mid < hiBound ∧
      mid ≤ F.depthOf cur ∧ mid ≤ F.depthOf rhs ∧
      (reg s26 cmd).val = mid ∧
      (reg s26 registers.value).val = F.ancestorAtDepth cur mid ∧
      (reg s26 registers.ptr).val = F.ancestorAtDepth rhs mid := by
  intro mid
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hB := bsearch_placed (hi := hi) (hw := hw) hTen
  have hD := dispatch_placed (hi := hi) (hw := hw) hTen
  have hDepthCur := jumpForest_depthOf_lt_size bs.fValid bs.curLt
  have hDepthRhs := jumpForest_depthOf_lt_size bs.fValid bs.rhsLt
  have hMinMax : hiBound < 2 ^ bits := by have := bs.hiLe; have := bs.fSizeLe; omega
  have hP53 : Placed code 53 (readScratchInstrs registers.ptr 5 (by omega)) :=
    placed3_of_get (hB 0 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 1 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 2 _ (by simp [bsearchBlock, readScratchInstrs]))
  have hP56 : Placed code 56 (readScratchInstrs registers.remain 6 (by omega)) :=
    placed3_of_get (hB 3 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 4 _ (by simp [bsearchBlock, readScratchInstrs]))
      (hB 5 _ (by simp [bsearchBlock, readScratchInstrs]))
  obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
    loop_readScratch (input := input) hTen hP53 hPC (by omega) bs.fix spWork (by omega) bs.slotLo (fin_ne_of_val (by decide))
  have hFix1 : DomRegsFixed Q s1 :=
    domRegsFixed_eq_of_eq bs.fix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  obtain ⟨s2, hs2, hpc2, hd2, hr2r, hr2o⟩ :=
    loop_readScratch (input := input) hTen hP56 hpc1 (by omega) hFix1 spWork (by omega) (by rw [hd1]; exact bs.slotHi) (fin_ne_of_val (by decide))
  have hFix2 : DomRegsFixed Q s2 :=
    domRegsFixed_eq_of_eq hFix1 (fun r hr => hr2o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr2p : (reg s2 registers.ptr).val = loBound := by
    rw [hr2o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr1p]
  have h59 : code[s2.pc]? = some (.add registers.value registers.ptr registers.one) := by
    rw [hpc2]; exact hB 6 _ (by simp [bsearchBlock, readScratchInstrs])
  obtain ⟨s3, hs3, hpc3, hr3v, hr3o, hd3⟩ :=
    step_add_at (input := input) h59 (by rw [hCodeSize, hpc2]; omega)
  have hVal3 : (reg s3 registers.value).val = loBound + 1 := by
    rw [hr3v, add_no_wrap _ _ (by rw [hr2p, hFix2.oneVal]; omega), hr2p, hFix2.oneVal]
  have hRem3 : (reg s3 registers.remain).val = hiBound := by
    rw [hr3o registers.remain (fin_ne_of_val (by decide)), hr2r]
  have hPtr3 : (reg s3 registers.ptr).val = loBound := by
    rw [hr3o registers.ptr (fin_ne_of_val (by decide)), hr2p]
  have hTrue : ltb (reg s3 registers.value) (reg s3 registers.remain) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hVal3, hRem3]; exact hLt)
  have h60 : code[s3.pc]? = some (.branchLt registers.value registers.remain 61 74) := by
    rw [hpc3, hpc2]; exact hB 7 _ (by simp [bsearchBlock, readScratchInstrs])
  have hs34 := step_branchLt_at (input := input) h60 (by rw [hCodeSize]; split <;> omega)
  let s4 : State L := { s3 with pc := if ltb (reg s3 registers.value) (reg s3 registers.remain) = true then 61 else 74 }
  have hpc4 : s4.pc = 61 := by simp only [s4, hTrue, ite_true]
  have hFix4 : DomRegsFixed Q s4 :=
    domRegsFixed_eq_of_eq hFix2 (fun r hr => hr3o r (fun e => by subst e; cases hr))
  have hd4 : s4.data = s.data := by change s3.data = s.data; rw [hd3, hd2, hd1]
  have hr4p : (reg s4 registers.ptr).val = loBound := hPtr3
  have hr4r : (reg s4 registers.remain).val = hiBound := hRem3
  have h61 : code[s4.pc]? = some (.sub registers.value registers.remain registers.ptr) := by
    rw [hpc4]; exact hB 8 _ (by simp [bsearchBlock, readScratchInstrs])
  obtain ⟨s5, hs5, hpc5, hr5v, hr5o, hd5⟩ :=
    step_sub_at (input := input) h61 (by rw [hCodeSize, hpc4]; omega)
  have hVal5 : (reg s5 registers.value).val = hiBound - loBound := by
    rw [hr5v, sub_exact_word _ _ (by rw [hr4r, hr4p]; omega), hr4r, hr4p]
  have h62 : code[s5.pc]? = some (.shr1 registers.value registers.value) := by
    rw [hpc5, hpc4]; exact hB 9 _ (by simp [bsearchBlock, readScratchInstrs])
  obtain ⟨s6, hs6, hpc6, hr6v, hr6o, hd6⟩ :=
    step_shr1_at (input := input) h62 (by rw [hCodeSize, hpc5, hpc4]; omega)
  have hVal6 : (reg s6 registers.value).val = (hiBound - loBound) / 2 := by
    rw [hr6v, hVal5]
  have hPtr6 : (reg s6 registers.ptr).val = loBound := by
    rw [hr6o registers.ptr (fin_ne_of_val (by decide)), hr5o registers.ptr (fin_ne_of_val (by decide)), hr4p]
  have h63 : code[s6.pc]? = some (.add cmd registers.ptr registers.value) := by
    rw [hpc6, hpc5, hpc4]; exact hB 10 _ (by simp [bsearchBlock, readScratchInstrs])
  obtain ⟨s7, hs7, hpc7, hr7cmd, hr7o, hd7⟩ :=
    step_add_at (input := input) h63 (by rw [hCodeSize, hpc6, hpc5, hpc4]; omega)
  let mid : Nat := loBound + (hiBound - loBound) / 2
  have hMidBounds : loBound < mid ∧ mid < hiBound := by dsimp [mid]; omega
  have hCmd7 : (reg s7 cmd).val = mid := by
    rw [hr7cmd, add_no_wrap _ _ (by rw [hPtr6, hVal6]; omega), hPtr6, hVal6]
  have hFix7 : DomRegsFixed Q s7 :=
    domRegsFixed_eq_of_eq hFix4 (fun r hr =>
      (hr7o r (fun e => by subst e; cases hr)).trans
        ((hr6o r (fun e => by subst e; cases hr)).trans (hr5o r (fun e => by subst e; cases hr))))
  have hP64 : Placed code 64 (writeScratchInstrs 7 cmd (by omega)) :=
    placed3_of_get (hB 11 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 12 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 13 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s8, hs8, hpc8, hd8size, h8slot7, h8keep, hr8o⟩ :=
    loop_writeScratch hTen hP64 (by omega) (by omega) hFix7 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix8 : DomRegsFixed Q s8 :=
    domRegsFixed_eq_of_eq hFix7 (fun r hr => hr8o r (fun e => by subst e; cases hr))
  have hP67 : Placed code 67 (writeScratchInstrs 9 registers.zero (by omega)) :=
    placed3_of_get (hB 14 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 15 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 16 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s9, hs9, hpc9, hd9size, h9slot9, h9keep, hr9o⟩ :=
    loop_writeScratch hTen hP67 hpc8 (by omega) hFix8 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix9 : DomRegsFixed Q s9 :=
    domRegsFixed_eq_of_eq hFix8 (fun r hr => hr9o r (fun e => by subst e; cases hr))
  have hP70 : Placed code 70 (readScratchInstrs registers.ptr 3 (by omega)) :=
    placed3_of_get (hB 17 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 18 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
      (hB 19 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s10, hs10, hpc10, hd10, hr10ptr, hr10o⟩ :=
    loop_readScratch hTen hP70 hpc9 (by omega) hFix9 spWork (by omega)
      (by rw [h9keep _ (by omega), h8keep _ (by omega), hd7, hd6, hd5, hd4]; exact bs.slotCur)
      (fin_ne_of_val (by decide))
  have hFix10 : DomRegsFixed Q s10 :=
    domRegsFixed_eq_of_eq hFix9 (fun r hr => hr10o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr10cmd : (reg s10 cmd).val = mid := by
    rw [hr10o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
        hr9o cmd (fin_ne_of_val (by decide)), hr8o cmd (fin_ne_of_val (by decide)), hCmd7]
  have h73 : code[s10.pc]? = some (.goto 84) := by
    rw [hpc10]; exact hB 20 _ (by simp [bsearchBlock, readScratchInstrs, writeScratchInstrs])
  have hs10_11 := step_goto_at (input := input) h73 (by rw [hCodeSize]; omega)
  let s11 : State L := { s10 with pc := 84 }
  have hMidCur : mid ≤ F.depthOf cur := by have := bs.hiLe; omega
  have hMidRhs : mid ≤ F.depthOf rhs := by have := bs.hiLe; omega
  have hRec11 : Records (2 * Q) F s11.data := by
    have := bs.fSizeLe
    exact records_preserve bs.records (by change s10.data.size = _; rw [hd10, hd9size, hd8size, hd7, hd6, hd5, hd4])
      (fun j hj => by change s10.data[j]? = _; rw [hd10, h9keep _ (by omega), h8keep _ (by omega), hd7, hd6, hd5, hd4])
  -- 1st seek: cur @ mid -> s12 at pc = 111:
  obtain ⟨s12, k1, hk1, hsSeek1, hpc12, hd12, hFix12, hr12ptr, _⟩ :=
    seekSubroutine_steps hTen (show s11.pc = 84 from rfl)
      (domRegsFixed_eq_of_eq hFix10 (fun _ _ => rfl)) hRec11 bs.fSizeLe bs.curLt hMidCur hr10ptr hr10cmd
  -- Dispatch retMode = 0 (111..127 -> 84):
  have hP111 : Placed code 111 (readScratchInstrs registers.remain 9 (by omega)) :=
    placed3_of_get (hD 0 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 1 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 2 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h12slot9 : (s12.data[5 * Q + 9]?).map Fin.val = some 0 := by
    rw [hd12]; change (s10.data[5 * Q + 9]?).map Fin.val = some 0
    rw [hd10, h9slot9, hFix8.zeroVal]
  obtain ⟨s13, hs13, hpc13, hd13, hr13rem, hr13o⟩ :=
    loop_readScratch hTen hP111 hpc12 (by omega) hFix12 spWork (by omega) h12slot9 (fin_ne_of_val (by decide))
  have hFix13 : DomRegsFixed Q s13 :=
    domRegsFixed_eq_of_eq hFix12 (fun r hr => hr13o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hCmp13 : ltb (reg s13 registers.remain) (reg s13 registers.one) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr13rem, hFix13.oneVal]; omega)
  have h114 : code[s13.pc]? = some (.branchLt registers.remain registers.one 115 128) := by
    rw [hpc13]; exact hD 3 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs13_14 := step_branchLt_at (input := input) h114 (by rw [hCodeSize]; split <;> omega)
  let s14 : State L := { s13 with pc := if ltb (reg s13 registers.remain) (reg s13 registers.one) = true then 115 else 128 }
  have hpc14 : s14.pc = 115 := by simp only [s14, hCmp13, ite_true]
  have hP115 : Placed code 115 (writeScratchInstrs 8 registers.ptr (by omega)) :=
    placed3_of_get (hD 4 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 5 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 6 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s15, hs15, hpc15, hd15size, h15slot8, h15keep, hr15o⟩ :=
    loop_writeScratch hTen hP115 hpc14 (by omega) (domRegsFixed_eq_of_eq hFix13 (fun _ _ => rfl))
      spWork (by omega) (fin_ne_of_val (by decide))
  have hFix15 : DomRegsFixed Q s15 :=
    domRegsFixed_eq_of_eq hFix13 (fun r hr => hr15o r (fun e => by subst e; cases hr))
  have hP118 : Placed code 118 (writeScratchInstrs 9 registers.one (by omega)) :=
    placed3_of_get (hD 7 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 8 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 9 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  obtain ⟨s16, hs16, hpc16, hd16size, h16slot9, h16keep, hr16o⟩ :=
    loop_writeScratch hTen hP118 hpc15 (by omega) hFix15 spWork (by omega) (fin_ne_of_val (by decide))
  have hFix16 : DomRegsFixed Q s16 :=
    domRegsFixed_eq_of_eq hFix15 (fun r hr => hr16o r (fun e => by subst e; cases hr))
  have hP121 : Placed code 121 (readScratchInstrs cmd 7 (by omega)) :=
    placed3_of_get (hD 10 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 11 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 12 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h16slot7 : (s16.data[5 * Q + 7]?).map Fin.val = some mid := by
    rw [h16keep _ (by omega), h15keep _ (by omega), hd13, hd12]
    change (s10.data[5 * Q + 7]?).map Fin.val = some mid
    rw [hd10, h9keep _ (by omega), h8slot7, hCmd7]
  obtain ⟨s17, hs17, hpc17, hd17, hr17cmd, hr17o⟩ :=
    loop_readScratch hTen hP121 hpc16 (by omega) hFix16 spWork (by omega) h16slot7 (fin_ne_of_val (by decide))
  have hFix17 : DomRegsFixed Q s17 :=
    domRegsFixed_eq_of_eq hFix16 (fun r hr => hr17o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hP124 : Placed code 124 (readScratchInstrs registers.ptr 4 (by omega)) :=
    placed3_of_get (hD 13 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 14 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 15 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h17slot4 : (s17.data[5 * Q + 4]?).map Fin.val = some rhs := by
    rw [hd17, h16keep _ (by omega), h15keep _ (by omega), hd13, hd12]
    change (s10.data[5 * Q + 4]?).map Fin.val = some rhs
    rw [hd10, h9keep _ (by omega), h8keep _ (by omega), hd7, hd6, hd5, hd4]; exact bs.slotRhs
  obtain ⟨s18, hs18, hpc18, hd18, hr18ptr, hr18o⟩ :=
    loop_readScratch hTen hP124 hpc17 (by omega) hFix17 spWork (by omega) h17slot4 (fin_ne_of_val (by decide))
  have hFix18 : DomRegsFixed Q s18 :=
    domRegsFixed_eq_of_eq hFix17 (fun r hr => hr18o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr18cmd : (reg s18 cmd).val = mid := by
    rw [hr18o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr17cmd]
  have h127 : code[s18.pc]? = some (.goto 84) := by
    rw [hpc18]; exact hD 16 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs18_19 := step_goto_at (input := input) h127 (by rw [hCodeSize]; omega)
  let s19 : State L := { s18 with pc := 84 }
  have hRec19 : Records (2 * Q) F s19.data := by
    have := bs.fSizeLe
    exact records_preserve hRec11 (by change s18.data.size = _; rw [hd18, hd17, hd16size, hd15size, hd13, hd12])
      (fun j hj => by change s18.data[j]? = s11.data[j]?; rw [hd18, hd17, h16keep _ (by omega), h15keep _ (by omega), hd13, hd12])
  -- 2nd seek: rhs @ mid -> s20 at pc = 111:
  obtain ⟨s20, k2, hk2, hsSeek2, hpc20, hd20, hFix20, hr20ptr, _⟩ :=
    seekSubroutine_steps hTen (show s19.pc = 84 from rfl)
      (domRegsFixed_eq_of_eq hFix18 (fun _ _ => rfl)) hRec19 bs.fSizeLe bs.rhsLt hMidRhs hr18ptr hr18cmd
  -- Dispatch retMode = 1 (111..114, 128..145 -> 53):
  have hP111' : Placed code 111 (readScratchInstrs registers.remain 9 (by omega)) := hP111
  have h20slot9 : (s20.data[5 * Q + 9]?).map Fin.val = some 1 := by
    rw [hd20]; change (s18.data[5 * Q + 9]?).map Fin.val = some 1
    rw [hd18, hd17, h16slot9, hFix15.oneVal]
  obtain ⟨s21, hs21, hpc21, hd21, hr21rem, hr21o⟩ :=
    loop_readScratch hTen hP111' hpc20 (by omega) hFix20 spWork (by omega) h20slot9 (fin_ne_of_val (by decide))
  have hFix21 : DomRegsFixed Q s21 :=
    domRegsFixed_eq_of_eq hFix20 (fun r hr => hr21o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hCmp21 : ltb (reg s21 registers.remain) (reg s21 registers.one) = false := by
    cases hCmp : ltb (reg s21 registers.remain) (reg s21 registers.one) with
    | false => rfl
    | true => have hLt := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hr21rem, hFix21.oneVal] at hLt; omega
  have h114' : code[s21.pc]? = some (.branchLt registers.remain registers.one 115 128) := by
    rw [hpc21]; exact hD 3 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs21_22 := step_branchLt_at (input := input) h114' (by rw [hCodeSize]; split <;> omega)
  let s22 : State L := { s21 with pc := if ltb (reg s21 registers.remain) (reg s21 registers.one) = true then 115 else 128 }
  have hpc22 : s22.pc = 128 := by simp only [s22, hCmp21, Bool.false_eq_true, ite_false]
  have h128 : code[s22.pc]? = some (.imm registers.value ⟨2, by omega⟩) := by
    rw [hpc22]; exact hD 17 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  obtain ⟨s23, hs23, hpc23, hr23v, hr23o, hd23⟩ :=
    step_imm_at (input := input) h128 (by rw [hCodeSize, hpc22]; omega)
  have hFix23 : DomRegsFixed Q s23 :=
    domRegsFixed_eq_of_eq hFix21 (fun r hr => hr23o r (fun e => by subst e; cases hr))
  have hr23rem : (reg s23 registers.remain).val = 1 := by
    rw [hr23o registers.remain (fin_ne_of_val (by decide))]; exact hr21rem
  have hCmp23 : ltb (reg s23 registers.remain) (reg s23 registers.value) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by simp only [hr23rem, hr23v]; omega)
  have h129 : code[s23.pc]? = some (.branchLt registers.remain registers.value 130 146) := by
    rw [hpc23, hpc22]; exact hD 18 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hs23_24 := step_branchLt_at (input := input) h129 (by rw [hCodeSize]; split <;> omega)
  let s24 : State L := { s23 with pc := if ltb (reg s23 registers.remain) (reg s23 registers.value) = true then 130 else 146 }
  have hpc24 : s24.pc = 130 := by simp only [s24, hCmp23, ite_true]
  have hP130 : Placed code 130 (readScratchInstrs registers.value 8 (by omega)) :=
    placed3_of_get (hD 19 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 20 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 21 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h24slot8 : (s24.data[5 * Q + 8]?).map Fin.val = some (F.ancestorAtDepth cur mid) := by
    change (s23.data[5 * Q + 8]?).map Fin.val = _
    rw [hd23, show s22.data = s21.data from rfl, hd21, hd20]
    change (s18.data[5 * Q + 8]?).map Fin.val = _
    rw [hd18, hd17, h16keep _ (by omega), h15slot8]
    change some (reg s13 registers.ptr).val = _
    rw [hr13o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr12ptr]
  obtain ⟨s25, hs25, hpc25, hd25, hr25val, hr25o⟩ :=
    loop_readScratch hTen hP130 hpc24 (by omega)
      (domRegsFixed_eq_of_eq hFix23 (fun _ _ => rfl)) spWork (by omega) h24slot8 (fin_ne_of_val (by decide))
  have hFix25 : DomRegsFixed Q s25 :=
    domRegsFixed_eq_of_eq hFix23 (fun r hr => hr25o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hP133 : Placed code 133 (readScratchInstrs cmd 7 (by omega)) :=
    placed3_of_get (hD 22 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 23 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 24 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h25slot7 : (s25.data[5 * Q + 7]?).map Fin.val = some mid := by
    rw [hd25]; change (s23.data[5 * Q + 7]?).map Fin.val = some mid
    rw [hd23, show s22.data = s21.data from rfl, hd21, hd20]
    change (s18.data[5 * Q + 7]?).map Fin.val = some mid
    rw [hd18, hd17, h16keep _ (by omega), h15keep _ (by omega), hd13, hd12]
    change (s10.data[5 * Q + 7]?).map Fin.val = some mid
    rw [hd10, h9keep _ (by omega), h8slot7, hCmd7]
  obtain ⟨s26, hs26, hpc26, hd26, hr26cmd, hr26o⟩ :=
    loop_readScratch hTen hP133 hpc25 (by omega) hFix25 spWork (by omega) h25slot7 (fin_ne_of_val (by decide))
  have hFix26 : DomRegsFixed Q s26 :=
    domRegsFixed_eq_of_eq hFix25 (fun r hr => hr26o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr26val : (reg s26 registers.value).val = F.ancestorAtDepth cur mid := by
    rw [hr26o registers.value (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr25val]
  have hr26ptr : (reg s26 registers.ptr).val = F.ancestorAtDepth rhs mid := by
    rw [hr26o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
        hr25o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
    change (reg s23 registers.ptr).val = _
    rw [hr23o registers.ptr (fin_ne_of_val (by decide))]
    change (reg s21 registers.ptr).val = _
    rw [hr21o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr20ptr]
  have h136 : code[s26.pc]? = some (.branchLt registers.value registers.ptr 138 137) := by
    rw [hpc26]; exact hD 25 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have h137 : code[137]? = some (.branchLt registers.ptr registers.value 138 142) :=
    hD 26 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hP138 : Placed code 138 (writeScratchInstrs 6 cmd (by omega)) :=
    placed3_of_get (hD 27 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 28 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 29 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have hP142 : Placed code 142 (writeScratchInstrs 5 cmd (by omega)) :=
    placed3_of_get (hD 31 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 32 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 33 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h141 : code[141]? = some (.goto 53) :=
    hD 30 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have h145 : code[145]? = some (.goto 53) :=
    hD 34 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  -- Common data properties of s26:
  have hs26keep : ∀ j, j < 5 * Q + 7 → s26.data[j]? = s.data[j]? := by
    intro j hj
    rw [hd26, hd25]; change s23.data[j]? = s.data[j]?
    rw [hd23, show s22.data = s21.data from rfl, hd21, hd20]
    change s18.data[j]? = s.data[j]?
    rw [hd18, hd17, h16keep _ (by omega), h15keep _ (by omega), hd13, hd12]
    change s10.data[j]? = s.data[j]?
    rw [hd10, h9keep _ (by omega), h8keep _ (by omega), hd7, hd6, hd5, hd4]
  have hs26size : s26.data.size = workCap := by
    rw [hd26, hd25]; change s23.data.size = workCap
    rw [hd23, show s22.data = s21.data from rfl, hd21, hd20]
    change s18.data.size = workCap
    rw [hd18, hd17, hd16size, hd15size, hd13, hd12]
    change s10.data.size = workCap
    rw [hd10, hd9size, hd8size, hd7, hd6, hd5, hd4]; exact bs.dataSize
  have hPrefix21 : Steps code input (21 + k1 + 17 + k2 + 12) s s26 := by
    have p1 : Steps code input 21 s s11 := by
      have a : Steps code input 6 s s2 := hs1.append hs2
      have b : Steps code input 5 s2 s7 := Steps.cons hs3 (Steps.cons hs34 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (.zero _)))))
      have c : Steps code input 10 s7 s11 := hs8.append (hs9.append (hs10.append (Steps.cons hs10_11 (.zero _))))
      simpa only [Nat.add_assoc] using (a.append b).append c
    have hsSeek1' : Steps code input k1 s11 s12 := hsSeek1
    have p2 : Steps code input 17 s12 s19 := by
      have a : Steps code input 4 s12 s14 := hs13.append (Steps.cons hs13_14 (.zero _))
      have b : Steps code input 13 s14 s19 := hs15.append (hs16.append (hs17.append (hs18.append (Steps.cons hs18_19 (.zero _)))))
      simpa only [Nat.add_assoc] using a.append b
    have hsSeek2' : Steps code input k2 s19 s20 := hsSeek2
    have p3 : Steps code input 12 s20 s26 := by
      have a : Steps code input 6 s20 s24 := hs21.append (Steps.cons hs21_22 (Steps.cons hs23 (Steps.cons hs23_24 (.zero _))))
      have b : Steps code input 6 s24 s26 := hs25.append hs26
      simpa only [Nat.add_assoc] using a.append b
    simpa only [Nat.add_assoc] using ((((p1.append hsSeek1').append p2).append hsSeek2').append p3)
  exact ⟨s26, k1, k2, hk1, hk2, hPrefix21, hpc26, hFix26, hs26keep, hs26size,
    hMidBounds.1, hMidBounds.2, hMidCur, hMidRhs, hr26cmd, hr26val, hr26ptr⟩

private theorem bsearch_bisect_steps {input : Input L} {Q v arcPtr arcEnd : Nat}
    (spWork : 5 * Q + 10 ≤ workCap) (hTen : 10 ≤ 2 ^ bits)
    {cur rhs loBound hiBound : Nat} {F : JumpForest} {s : State L}
    (hPC : s.pc = 53)
    (bs : BSearchState Q v arcPtr arcEnd cur rhs loBound hiBound F s)
    (hLt : loBound + 1 < hiBound) :
    ∃ t k lo' hi', k ≤ 120 * OracleContract.L Q + 66 ∧
      Steps (domLoopCode hi hw hTen) input k s t ∧
      t.pc = 53 ∧ (∀ j, j < 5 * Q → t.data[j]? = s.data[j]?) ∧
      BSearchState Q v arcPtr arcEnd cur rhs lo' hi' F t ∧
      hi' - lo' ≤ (hiBound - loBound + 1) / 2 := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hD := dispatch_placed (hi := hi) (hw := hw) hTen
  have h136 : code[136]? = some (.branchLt registers.value registers.ptr 138 137) :=
    hD 25 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have h137 : code[137]? = some (.branchLt registers.ptr registers.value 138 142) :=
    hD 26 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have hP138 : Placed code 138 (writeScratchInstrs 6 cmd (by omega)) :=
    placed3_of_get (hD 27 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 28 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 29 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have hP142 : Placed code 142 (writeScratchInstrs 5 cmd (by omega)) :=
    placed3_of_get (hD 31 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 32 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
      (hD 33 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs]))
  have h141 : code[141]? = some (.goto 53) :=
    hD 30 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  have h145 : code[145]? = some (.goto 53) :=
    hD 34 _ (by simp [dispatchBlock, readScratchInstrs, writeScratchInstrs])
  let mid := loBound + (hiBound - loBound) / 2
  obtain ⟨s26, k1, k2, hk1, hk2, hPrefix21, hpc26, hFix26, hs26keep, hs26size,
      hMidLo, hMidHi, hMidCur, hMidRhs, hr26cmd, hr26val, hr26ptr⟩ :=
    bsearch_bisect_prefix spWork hTen hPC bs hLt
  change loBound < mid at hMidLo
  change mid < hiBound at hMidHi
  change mid ≤ F.depthOf cur at hMidCur
  change mid ≤ F.depthOf rhs at hMidRhs
  change (reg s26 cmd).val = mid at hr26cmd
  change (reg s26 registers.value).val = F.ancestorAtDepth cur mid at hr26val
  change (reg s26 registers.ptr).val = F.ancestorAtDepth rhs mid at hr26ptr
  by_cases hAncEqMid : F.ancestorAtDepth cur mid = F.ancestorAtDepth rhs mid
  · have hc1 : ltb (reg s26 registers.value) (reg s26 registers.ptr) = false := by
      cases hCmp : ltb (reg s26 registers.value) (reg s26 registers.ptr) with
      | false => rfl
      | true =>
        have hLtC := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp
        rw [hr26val, hr26ptr, hAncEqMid] at hLtC; omega
    have hc2 : ltb (reg s26 registers.ptr) (reg s26 registers.value) = false := by
      cases hCmp : ltb (reg s26 registers.ptr) (reg s26 registers.value) with
      | false => rfl
      | true =>
        have hLtC := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp
        rw [hr26val, hr26ptr, hAncEqMid] at hLtC; omega
    have hs26_27 := step_branchLt_at (input := input) (by rw [hpc26]; exact h136) (by rw [hCodeSize]; split <;> omega)
    let s27 : State L := { s26 with pc := if ltb (reg s26 registers.value) (reg s26 registers.ptr) = true then 138 else 137 }
    have hpc27 : s27.pc = 137 := by simp only [s27, hc1, Bool.false_eq_true, ite_false]
    have hs27_28 := step_branchLt_at (input := input) (by rw [hpc27]; exact h137) (by rw [hCodeSize]; split <;> omega)
    let s28 : State L := { s27 with pc := if ltb (reg s27 registers.ptr) (reg s27 registers.value) = true then 138 else 142 }
    have hpc28 : s28.pc = 142 := by
      have hc2' : ltb (reg s27 registers.ptr) (reg s27 registers.value) = false := hc2
      simp only [s28, hc2', Bool.false_eq_true, ite_false]
    have hFix28 : DomRegsFixed Q s28 := domRegsFixed_eq_of_eq hFix26 (fun _ _ => rfl)
    obtain ⟨s29, hs29, hpc29, hd29size, h29slot5, h29keep, hr29o⟩ :=
      loop_writeScratch (input := input) hTen hP142 hpc28 (by omega) hFix28 spWork (by omega) (fin_ne_of_val (by decide))
    have hFix29 : DomRegsFixed Q s29 :=
      domRegsFixed_eq_of_eq hFix28 (fun r hr => hr29o r (fun e => by subst e; cases hr))
    have hs29_30 := step_goto_at (input := input) (by rw [hpc29]; exact h145) (by rw [hCodeSize]; omega)
    let t : State L := { s29 with pc := 53 }
    have htKeepPre : ∀ j, j < 5 * Q → t.data[j]? = s.data[j]? := fun j hj => by
      change s29.data[j]? = _; rw [h29keep _ (by omega)]; exact hs26keep _ (by omega)
    have htDataSize : t.data.size = workCap := by
      change s29.data.size = workCap; rw [hd29size]; exact hs26size
    have htRec : Records (2 * Q) F t.data :=
      records_preserve bs.records (by rw [htDataSize, bs.dataSize]) (fun j hj => htKeepPre j (by have := bs.fSizeLe; omega))
    refine ⟨t, (21 + k1 + 17 + k2 + 12) + 6, mid, hiBound, by omega,
      hPrefix21.append (Steps.cons hs26_27 (Steps.cons hs27_28 (hs29.append (Steps.cons hs29_30 (.zero _))))),
      rfl, htKeepPre,
      { fix := domRegsFixed_eq_of_eq hFix29 (fun _ _ => rfl), dataSize := htDataSize,
        workRoom := spWork, fSizeLe := bs.fSizeLe,
        fValid := bs.fValid, records := htRec, curLt := bs.curLt, rhsLt := bs.rhsLt,
        loLtHi := hMidHi, hiLe := bs.hiLe, ancEq := hAncEqMid, ancNeAbove := bs.ancNeAbove,
        slotV := by change (s29.data[5 * Q + 0]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotV,
        slotArcPtr := by change (s29.data[5 * Q + 1]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotArcPtr,
        slotArcEnd := by change (s29.data[5 * Q + 2]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotArcEnd,
        slotCur := by change (s29.data[5 * Q + 3]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotCur,
        slotRhs := by change (s29.data[5 * Q + 4]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotRhs,
        slotLo := by change (s29.data[5 * Q + 5]?).map Fin.val = _; rw [h29slot5]; change some (reg s26 cmd).val = _; rw [hr26cmd],
        slotHi := by change (s29.data[5 * Q + 6]?).map Fin.val = _; rw [h29keep _ (by omega), hs26keep _ (by omega)]; exact bs.slotHi },
      by dsimp [mid]; omega⟩
  · have hMidAbove : ∀ d, mid ≤ d → d ≤ F.depthOf cur → d ≤ F.depthOf rhs →
        F.ancestorAtDepth cur d ≠ F.ancestorAtDepth rhs d :=
      jumpForest_anc_mono_ne bs.fValid bs.curLt bs.rhsLt hMidCur hMidRhs hAncEqMid
    have hTo138 : ∃ s28 kB, kB ≤ 2 ∧ Steps code input kB s26 s28 ∧ s28.pc = 138 ∧
        s28.data = s26.data ∧ DomRegsFixed Q s28 ∧ (reg s28 cmd).val = mid := by
      by_cases hLtV : F.ancestorAtDepth cur mid < F.ancestorAtDepth rhs mid
      · have hc1 : ltb (reg s26 registers.value) (reg s26 registers.ptr) = true :=
          (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr26val, hr26ptr]; exact hLtV)
        have hs26_27 := step_branchLt_at (input := input) (by rw [hpc26]; exact h136) (by rw [hCodeSize]; split <;> omega)
        exact ⟨_, 1, by omega, Steps.cons hs26_27 (.zero _), by simp [hc1], rfl,
          domRegsFixed_eq_of_eq hFix26 (fun _ _ => rfl), hr26cmd⟩
      · have hLtP : F.ancestorAtDepth rhs mid < F.ancestorAtDepth cur mid := by omega
        have hc1 : ltb (reg s26 registers.value) (reg s26 registers.ptr) = false := by
          cases hCmp : ltb (reg s26 registers.value) (reg s26 registers.ptr) with
          | false => rfl
          | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hr26val, hr26ptr] at this; omega
        have hc2 : ltb (reg s26 registers.ptr) (reg s26 registers.value) = true :=
          (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr26val, hr26ptr]; exact hLtP)
        have hs26_27 := step_branchLt_at (input := input) (by rw [hpc26]; exact h136) (by rw [hCodeSize]; split <;> omega)
        let s27 : State L := { s26 with pc := if ltb (reg s26 registers.value) (reg s26 registers.ptr) = true then 138 else 137 }
        have hpc27 : s27.pc = 137 := by simp only [s27, hc1, Bool.false_eq_true, ite_false]
        have hs27_28 := step_branchLt_at (input := input) (by rw [hpc27]; exact h137) (by rw [hCodeSize]; split <;> omega)
        exact ⟨_, 2, by omega, Steps.cons hs26_27 (Steps.cons hs27_28 (.zero _)),
          by simp [show ltb (reg s27 registers.ptr) (reg s27 registers.value) = true from hc2],
          rfl, domRegsFixed_eq_of_eq hFix26 (fun _ _ => rfl), hr26cmd⟩
    obtain ⟨s28, kB, hkB, hsTo138, hpc28, hd28, hFix28, hr28cmd⟩ := hTo138
    obtain ⟨s29, hs29, hpc29, hd29size, h29slot6, h29keep, hr29o⟩ :=
      loop_writeScratch (input := input) hTen hP138 hpc28 (by omega) hFix28 spWork (by omega) (fin_ne_of_val (by decide))
    have hFix29 : DomRegsFixed Q s29 :=
      domRegsFixed_eq_of_eq hFix28 (fun r hr => hr29o r (fun e => by subst e; cases hr))
    have hs29_30 := step_goto_at (input := input) (by rw [hpc29]; exact h141) (by rw [hCodeSize]; omega)
    let t : State L := { s29 with pc := 53 }
    have htKeepPre : ∀ j, j < 5 * Q → t.data[j]? = s.data[j]? := fun j hj => by
      change s29.data[j]? = _; rw [h29keep _ (by omega), hd28]; exact hs26keep _ (by omega)
    have htDataSize : t.data.size = workCap := by
      change s29.data.size = workCap; rw [hd29size, hd28]; exact hs26size
    have htRec : Records (2 * Q) F t.data :=
      records_preserve bs.records (by rw [htDataSize, bs.dataSize]) (fun j hj => htKeepPre j (by have := bs.fSizeLe; omega))
    refine ⟨t, (21 + k1 + 17 + k2 + 12) + (kB + 4), loBound, mid, by omega,
      hPrefix21.append (hsTo138.append (hs29.append (Steps.cons hs29_30 (.zero _)))),
      rfl, htKeepPre,
      { fix := domRegsFixed_eq_of_eq hFix29 (fun _ _ => rfl), dataSize := htDataSize,
        workRoom := spWork, fSizeLe := bs.fSizeLe,
        fValid := bs.fValid, records := htRec, curLt := bs.curLt, rhsLt := bs.rhsLt,
        loLtHi := hMidLo, hiLe := by omega, ancEq := bs.ancEq, ancNeAbove := hMidAbove,
        slotV := by change (s29.data[5 * Q + 0]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotV,
        slotArcPtr := by change (s29.data[5 * Q + 1]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotArcPtr,
        slotArcEnd := by change (s29.data[5 * Q + 2]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotArcEnd,
        slotCur := by change (s29.data[5 * Q + 3]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotCur,
        slotRhs := by change (s29.data[5 * Q + 4]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotRhs,
        slotLo := by change (s29.data[5 * Q + 5]?).map Fin.val = _; rw [h29keep _ (by omega), hd28, hs26keep _ (by omega)]; exact bs.slotLo,
        slotHi := by change (s29.data[5 * Q + 6]?).map Fin.val = _; rw [h29slot6, hr28cmd] },
      by dsimp [mid]; omega⟩

private theorem bsearch_loop_steps {input : Input L} {Q v arcPtr arcEnd : Nat}
    (spWork : 5 * Q + 10 ≤ workCap) (hArcFit : arcPtr + 1 ≤ arcEnd) (hArcM : arcEnd < 2 ^ bits)
    (hTen : 10 ≤ 2 ^ bits) :
    ∀ (b : Nat) {cur rhs loBound hiBound : Nat} {F : JumpForest} {s : State L},
      s.pc = 53 →
      BSearchState Q v arcPtr arcEnd cur rhs loBound hiBound F s →
      hiBound - loBound ≤ 2 ^ b →
      ∃ t k, k ≤ (120 * OracleContract.L Q + 66) * b + (60 * OracleContract.L Q + 40) ∧
        Steps (domLoopCode hi hw hTen) input k s t ∧
        t.pc = 21 ∧ DomRegsFixed Q t ∧ t.data.size = workCap ∧
        (∀ j, j < 5 * Q → t.data[j]? = s.data[j]?) ∧
        (t.data[5 * Q + 0]?).map Fin.val = some v ∧
        (t.data[5 * Q + 1]?).map Fin.val = some (arcPtr + 1) ∧
        (t.data[5 * Q + 2]?).map Fin.val = some arcEnd ∧
        (∃ cur', cur' < F.size ∧ (t.data[5 * Q + 3]?).map Fin.val = some cur' ∧
          (∀ a, a < F.size → (IsAncestor F a cur' ↔ IsAncestor F a cur ∧ IsAncestor F a rhs))) := by
  intro b
  induction b with
  | zero =>
    intro cur rhs loBound hiBound F s hPC bs hSpan
    have hEqHi : hiBound = loBound + 1 := by have := bs.loLtHi; omega
    obtain ⟨t, k, hk, hSt, hpc, hFix, hd, hKeep, hv, hp, he, hCur⟩ :=
      bsearch_exit_steps spWork hArcFit hArcM hTen hPC bs hEqHi
    exact ⟨t, k, by simpa using hk, hSt, hpc, hFix, hd, hKeep, hv, hp, he, hCur⟩
  | succ b ih =>
    intro cur rhs loBound hiBound F s hPC bs hSpan
    by_cases hLt : loBound + 1 < hiBound
    · obtain ⟨s1, k1, lo', hi', hk1, hSt1, hpc1, hKeep1, bs1, hSpan1⟩ :=
        bsearch_bisect_steps spWork hTen hPC bs hLt
      have hPow : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
      have hSpan' : hi' - lo' ≤ 2 ^ b := by omega
      obtain ⟨t, k2, hk2, hSt2, hpc2, hFix2, hd2, hKeep2, hv2, hp2, he2, hCur2⟩ :=
        ih hpc1 bs1 hSpan'
      refine ⟨t, k1 + k2, ?_, hSt1.append hSt2, hpc2, hFix2, hd2,
        fun j hj => (hKeep2 j hj).trans (hKeep1 j hj), hv2, hp2, he2, hCur2⟩
      calc k1 + k2
          ≤ (120 * OracleContract.L Q + 66) +
              ((120 * OracleContract.L Q + 66) * b + (60 * OracleContract.L Q + 40)) := by omega
        _ = (120 * OracleContract.L Q + 66) * (b + 1) + (60 * OracleContract.L Q + 40) := by
              rw [Nat.mul_succ]; omega
    · have hEqHi : hiBound = loBound + 1 := by have := bs.loLtHi; omega
      obtain ⟨t, k, hk, hSt, hpc, hFix, hd, hKeep, hv, hp, he, hCur⟩ :=
        bsearch_exit_steps spWork hArcFit hArcM hTen hPC bs hEqHi
      exact ⟨t, k, Nat.le_trans hk (Nat.le_add_left _ _), hSt, hpc, hFix, hd, hKeep, hv, hp, he, hCur⟩

private theorem loop_readDepth {input : Input L} {Q : Nat} (hTen : 10 ≤ 2 ^ bits)
    {F : JumpForest} {s : State L} {base u : Nat} {dst node : Fin 15}
    (hPlaced : Placed (domLoopCode hi hw hTen) base (readDepthInstrs dst node))
    (hPC : s.pc = base)
    (hEnd : base + 4 < 209)
    (hFix : DomRegsFixed Q s)
    (hRec : Records (2 * Q) F s.data)
    (hu : u < F.size)
    (hNode : (reg s node).val = u)
    (hNodeNe : node ≠ registers.tmp) (hDstNe : dst ≠ registers.tmp) :
    ∃ t, Steps (domLoopCode hi hw hTen) input 4 s t ∧ t.pc = base + 4 ∧ t.data = s.data ∧
      (reg t dst).val = F.depthOf u ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ registers.tmp → reg t r = reg s r) := by
  have hFit : (reg s toutBase).val + 3 * (reg s node).val < s.data.size := by
    rw [hFix.toutVal, hNode]; have := hRec.fit; omega
  have hRead : (s.data[(reg s toutBase).val + 3 * (reg s node).val]?).map Fin.val =
      some (F.depthOf u) := by
    rw [hFix.toutVal, hNode]; exact hRec.depth u hu
  cases hCell : s.data[(reg s toutBase).val + 3 * (reg s node).val]? with
  | none => rw [hCell] at hRead; cases hRead
  | some w =>
    rw [hCell, Option.map_some] at hRead
    obtain ⟨t, htSt, htpc, htdata, htdst, hto⟩ :=
      recordField_steps_at hPlaced hPC (by rw [domLoopCode_size]; exact hEnd)
        hNodeNe (fin_ne_of_val (by decide)) hDstNe hFit hCell
    refine ⟨t, htSt, htpc, htdata, ?_, hto⟩
    rw [htdst]; exact Option.some.inj hRead

private theorem loop_readJump {input : Input L} {Q : Nat} (hTen : 10 ≤ 2 ^ bits)
    {F : JumpForest} {s : State L} {base u : Nat} {dst node : Fin 15}
    (hPlaced : Placed (domLoopCode hi hw hTen) base (readJumpInstrs dst node))
    (hPC : s.pc = base)
    (hEnd : base + 4 < 209)
    (hFix : DomRegsFixed Q s)
    (hRec : Records (2 * Q) F s.data)
    (hu : u < F.size)
    (hNode : (reg s node).val = u)
    (hNodeNe : node ≠ registers.tmp) (hDstNe : dst ≠ registers.tmp) :
    ∃ t, Steps (domLoopCode hi hw hTen) input 4 s t ∧ t.pc = base + 4 ∧ t.data = s.data ∧
      (reg t dst).val = F.jumpOf u ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ registers.tmp → reg t r = reg s r) := by
  have hFit : (reg s offsetBase).val + 3 * (reg s node).val < s.data.size := by
    rw [hFix.offsetVal, hNode]; have := hRec.fit; omega
  have hRead : (s.data[(reg s offsetBase).val + 3 * (reg s node).val]?).map Fin.val =
      some (F.jumpOf u) := by
    rw [hFix.offsetVal, hNode]; exact hRec.jump u hu
  cases hCell : s.data[(reg s offsetBase).val + 3 * (reg s node).val]? with
  | none => rw [hCell] at hRead; cases hRead
  | some w =>
    rw [hCell, Option.map_some] at hRead
    obtain ⟨t, htSt, htpc, htdata, htdst, hto⟩ :=
      recordField_steps_at hPlaced hPC (by rw [domLoopCode_size]; exact hEnd)
        hNodeNe (fin_ne_of_val (by decide)) hDstNe hFit hCell
    refine ⟨t, htSt, htpc, htdata, ?_, hto⟩
    rw [htdst]; exact Option.some.inj hRead

private theorem loopArc_all_steps {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) (hTen : 10 ≤ 2 ^ bits)
    {v arcEnd : Nat} (hv1 : 1 ≤ v) (hvLt : v < Q)
    (hArcEndEq : arcEnd = inStart (v + 1)) :
    ∀ (rem : Nat) {arcPtr cur : Nat} {F : JumpForest} {s : State L},
      s.pc = 21 →
      arcEnd = arcPtr + rem →
      inStart v + 1 ≤ arcPtr →
      arcPtr ≤ arcEnd →
      DomRegsFixed Q s →
      s.data.size = workCap →
      F.size = v →
      ValidJumpForest F →
      Records (2 * Q) F s.data →
      cur < F.size →
      (∀ a, a < v → (IsAncestor F a cur ↔
        ∀ k, inStart v ≤ k → k < arcPtr → IsAncestor F a (inSrc k))) →
      (s.data[5 * Q + 0]?).map Fin.val = some v →
      (s.data[5 * Q + 1]?).map Fin.val = some arcPtr →
      (s.data[5 * Q + 2]?).map Fin.val = some arcEnd →
      (s.data[5 * Q + 3]?).map Fin.val = some cur →
      ∃ t k cur', k ≤ 318 * rem * OracleContract.L Q ^ 2 + 7 ∧
        Steps (domLoopCode hi hw hTen) input k s t ∧
        t.pc = 157 ∧ DomRegsFixed Q t ∧ t.data.size = workCap ∧
        (∀ j, j < 5 * Q → t.data[j]? = s.data[j]?) ∧
        Records (2 * Q) F t.data ∧
        cur' < v ∧
        (∀ a, a < v → (IsAncestor F a cur' ↔
          ∀ k, inStart v ≤ k → k < arcEnd → IsAncestor F a (inSrc k))) ∧
        (t.data[5 * Q + 0]?).map Fin.val = some v ∧
        (t.data[5 * Q + 3]?).map Fin.val = some cur' := by
  intro rem
  induction rem with
  | zero =>
    intro arcPtr cur F s hPC hRem _ _ hFix hSize hFSz hValid hRec hCurLt hCurSem hSV hSP hSE hSC
    have hEqEnd : arcPtr = arcEnd := by omega
    let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
    have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
    have hA := loopArc_placed (hi := hi) (hw := hw) hTen
    have hP21 : Placed code 21 (readScratchInstrs registers.ptr 1 (by omega)) :=
      placed3_of_get (hA 0 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 1 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 2 _ (by simp [loopArcBlock, readScratchInstrs]))
    have hP24 : Placed code 24 (readScratchInstrs registers.remain 2 (by omega)) :=
      placed3_of_get (hA 3 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 4 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 5 _ (by simp [loopArcBlock, readScratchInstrs]))
    obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
      loop_readScratch hTen hP21 hPC (by omega) hFix sp.workBounds (by omega) hSP (fin_ne_of_val (by decide))
    have hFix1 : DomRegsFixed Q s1 :=
      domRegsFixed_eq_of_eq hFix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    obtain ⟨s2, hs2, hpc2, hd2, hr2r, hr2o⟩ :=
      loop_readScratch hTen hP24 hpc1 (by omega) hFix1 sp.workBounds (by omega) (by rw [hd1]; exact hSE) (fin_ne_of_val (by decide))
    have hFix2 : DomRegsFixed Q s2 :=
      domRegsFixed_eq_of_eq hFix1 (fun r hr => hr2o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hr2p : (reg s2 registers.ptr).val = arcPtr := by
      rw [hr2o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr1p]
    have hFalse : ltb (reg s2 registers.ptr) (reg s2 registers.remain) = false := by
      cases hCmp : ltb (reg s2 registers.ptr) (reg s2 registers.remain) with
      | false => rfl
      | true => have hLt := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hr2p, hr2r] at hLt; omega
    have h27 : code[s2.pc]? = some (.branchLt registers.ptr registers.remain 28 157) := by
      rw [hpc2]; exact hA 6 _ (by simp [loopArcBlock, readScratchInstrs])
    have hs23 := step_branchLt_at (input := input) h27 (by rw [hCodeSize]; split <;> omega)
    let t : State L := { s2 with pc := if ltb (reg s2 registers.ptr) (reg s2 registers.remain) = true then 28 else 157 }
    have htpc : t.pc = 157 := by simp only [t, hFalse, Bool.false_eq_true, ite_false]
    have htd : t.data = s.data := by change s2.data = s.data; rw [hd2, hd1]
    refine ⟨t, 7, cur, by omega, hs1.append (hs2.append (Steps.cons hs23 (.zero _))),
      htpc, domRegsFixed_eq_of_eq hFix2 (fun _ _ => rfl), by rw [htd]; exact hSize, fun _ _ => by rw [htd],
      by rw [htd]; exact hRec, by rw [← hFSz]; exact hCurLt,
      fun a ha => by rw [← hEqEnd]; exact hCurSem a ha,
      by rw [htd]; exact hSV, by rw [htd]; exact hSC⟩
  | succ rem ih =>
    intro arcPtr cur F s hPC hRem hArcLo hArcHi hFix hSize hFSz hValid hRec hCurLt hCurSem hSV hSP hSE hSC
    have hArcLt : arcPtr < arcEnd := by omega
    have hEndM : arcEnd ≤ mReach := by
      rw [hArcEndEq, ← sp.startEnd]; exact denseIncoming_inStart_le sp (v + 1) Q (by omega) (Nat.le_refl Q)
    have hInB := inBounds_nat sp
    have hWork := workBounds_nat sp
    have hSrcFit : arcEnd < 2 ^ bits := by omega
    let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
    have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
    have hA := loopArc_placed (hi := hi) (hw := hw) hTen
    have hP21 : Placed code 21 (readScratchInstrs registers.ptr 1 (by omega)) :=
      placed3_of_get (hA 0 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 1 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 2 _ (by simp [loopArcBlock, readScratchInstrs]))
    have hP24 : Placed code 24 (readScratchInstrs registers.remain 2 (by omega)) :=
      placed3_of_get (hA 3 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 4 _ (by simp [loopArcBlock, readScratchInstrs]))
        (hA 5 _ (by simp [loopArcBlock, readScratchInstrs]))
    obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
      loop_readScratch hTen hP21 hPC (by omega) hFix hWork (by omega) hSP (fin_ne_of_val (by decide))
    have hFix1 : DomRegsFixed Q s1 :=
      domRegsFixed_eq_of_eq hFix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    obtain ⟨s2, hs2, hpc2, hd2, hr2r, hr2o⟩ :=
      loop_readScratch hTen hP24 hpc1 (by omega) hFix1 hWork (by omega) (by rw [hd1]; exact hSE) (fin_ne_of_val (by decide))
    have hFix2 : DomRegsFixed Q s2 :=
      domRegsFixed_eq_of_eq hFix1 (fun r hr => hr2o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hr2p : (reg s2 registers.ptr).val = arcPtr := by
      rw [hr2o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr1p]
    have hTrue : ltb (reg s2 registers.ptr) (reg s2 registers.remain) = true :=
      (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr2p, hr2r]; exact hArcLt)
    have h27 : code[s2.pc]? = some (.branchLt registers.ptr registers.remain 28 157) := by
      rw [hpc2]; exact hA 6 _ (by simp [loopArcBlock, readScratchInstrs])
    have hs23 := step_branchLt_at (input := input) h27 (by rw [hCodeSize]; split <;> omega)
    let s3 : State L := { s2 with pc := if ltb (reg s2 registers.ptr) (reg s2 registers.remain) = true then 28 else 157 }
    have hpc3 : s3.pc = 28 := by simp only [s3, hTrue, ite_true]
    have hFix3 : DomRegsFixed Q s3 := domRegsFixed_eq_of_eq hFix2 (fun _ _ => rfl)
    have hr3p : (reg s3 registers.ptr).val = arcPtr := hr2p
    have h28 : code[s3.pc]? = some (.add registers.tmp childrenBase registers.ptr) := by
      rw [hpc3]; exact hA 7 _ (by simp [loopArcBlock, readScratchInstrs])
    obtain ⟨s4, hs4, hpc4, hr4t, hr4o, hd4⟩ :=
      step_add_at (input := input) h28 (by rw [hCodeSize, hpc3]; omega)
    have hFix4 : DomRegsFixed Q s4 :=
      domRegsFixed_eq_of_eq hFix3 (fun r hr => hr4o r (fun e => by subst e; cases hr))
    have hAddr4 : (reg s4 registers.tmp).val = 3 + Q + arcPtr := by
      have hFit : (reg s3 childrenBase).val + (reg s3 registers.ptr).val < 2 ^ bits := by
        rw [hFix3.childrenVal, hr3p]; omega
      rw [hr4t, add_no_wrap _ _ hFit, hFix3.childrenVal, hr3p]
    let rhs := inSrc arcPtr
    have hrhsLt : rhs < v := sp.srcPred v arcPtr hv1 hvLt (by omega) (by rw [← hArcEndEq]; exact hArcLt)
    have hrhsF : rhs < F.size := by rw [hFSz]; exact hrhsLt
    have hrhsFit : rhs < 2 ^ bits := Nat.lt_of_lt_of_le (by omega) (Nat.le_trans sp.workBounds hw)
    have hSrcWord : input.words[(reg s4 registers.tmp).val]? = some ⟨rhs, hrhsFit⟩ := by
      rw [hAddr4]
      have hC := sp.srcCell arcPtr (by omega)
      cases hInp : input.words[3 + Q + arcPtr]? with
      | none => rw [hInp] at hC; cases hC
      | some w =>
        rw [hInp, Option.map_some] at hC
        congr 1; exact Fin.ext (Option.some.inj hC)
    have h29 : code[s4.pc]? = some (.loadInput registers.value registers.tmp) := by
      rw [hpc4, hpc3]; exact hA 8 _ (by simp [loopArcBlock, readScratchInstrs])
    obtain ⟨s5, hs5, hpc5, hr5v, hr5o, hd5⟩ :=
      step_loadInput_at (input := input) h29 (by rw [hCodeSize, hpc4, hpc3]; omega) hSrcWord
    have hFix5 : DomRegsFixed Q s5 :=
      domRegsFixed_eq_of_eq hFix4 (fun r hr => hr5o r (fun e => by subst e; cases hr))
    have hP30 : Placed code 30 (writeScratchInstrs 4 registers.value (by omega)) :=
      placed3_of_get (hA 9 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs]))
        (hA 10 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs]))
        (hA 11 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs]))
    obtain ⟨s6, hs6, hpc6, hd6size, h6slot4, h6keep, hr6o⟩ :=
      loop_writeScratch hTen hP30 (by rw [hpc5, hpc4, hpc3]) (by omega) hFix5 sp.workBounds (by omega) (fin_ne_of_val (by decide))
    have hFix6 : DomRegsFixed Q s6 :=
      domRegsFixed_eq_of_eq hFix5 (fun r hr => hr6o r (fun e => by subst e; cases hr))
    have h6eq : ∀ j, j ≠ 5 * Q + 4 → s6.data[j]? = s.data[j]? := fun j hj => by
      rw [h6keep _ hj, hd5, hd4, show s3.data = s2.data from rfl, hd2, hd1]
    have hRec6 : Records (2 * Q) F s6.data :=
      records_preserve hRec (by rw [hd6size, hd5, hd4, show s3.data = s2.data from rfl, hd2, hd1])
        (fun j hj => h6eq j (by omega))
    have hr6v : (reg s6 registers.value).val = rhs := by
      rw [hr6o registers.value (fin_ne_of_val (by decide)), hr5v]
    have hP33 : Placed code 33 (readDepthInstrs clk registers.value) :=
      placed4_of_get (hA 12 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 13 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 14 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 15 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
    obtain ⟨s7, hs7, hpc7, hd7, hr7clk, hr7o⟩ :=
      loop_readDepth hTen hP33 hpc6 (by omega) hFix6 hRec6 hrhsF hr6v (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
    have hFix7 : DomRegsFixed Q s7 :=
      domRegsFixed_eq_of_eq hFix6 (fun r hr => hr7o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hP37 : Placed code 37 (readScratchInstrs registers.ptr 3 (by omega)) :=
      placed3_of_get (hA 16 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 17 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 18 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
    obtain ⟨s8, hs8, hpc8, hd8, hr8ptr, hr8o⟩ :=
      loop_readScratch hTen hP37 hpc7 (by omega) hFix7 sp.workBounds (by omega)
        (by rw [hd7, h6eq _ (by omega)]; exact hSC) (fin_ne_of_val (by decide))
    have hFix8 : DomRegsFixed Q s8 :=
      domRegsFixed_eq_of_eq hFix7 (fun r hr => hr8o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hRec8 : Records (2 * Q) F s8.data := by rw [hd8, hd7]; exact hRec6
    have hP40 : Placed code 40 (readDepthInstrs registers.remain registers.ptr) :=
      placed4_of_get (hA 19 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 20 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 21 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 22 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
    obtain ⟨s9, hs9, hpc9, hd9, hr9rem, hr9o⟩ :=
      loop_readDepth hTen hP40 hpc8 (by omega) hFix8 hRec8 hCurLt hr8ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
    have hFix9 : DomRegsFixed Q s9 :=
      domRegsFixed_eq_of_eq hFix8 (fun r hr => hr9o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hr9clk : (reg s9 clk).val = F.depthOf rhs := by
      rw [hr9o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
          hr8o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr7clk]
    have h44 : code[s9.pc]? = some (.branchLt clk registers.remain 45 46) := by
      rw [hpc9]; exact hA 23 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs])
    have h45 : code[45]? = some (.mov registers.remain clk) :=
      hA 24 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs])
    have h46 : code[46]? = some (.add registers.remain registers.remain registers.one) :=
      hA 25 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs])
    let minD := min (F.depthOf cur) (F.depthOf rhs)
    have hTo46 : ∃ s10 kMin, kMin ≤ 2 ∧ Steps code input kMin s9 s10 ∧ s10.pc = 46 ∧
        s10.data = s9.data ∧ DomRegsFixed Q s10 ∧ (reg s10 registers.remain).val = minD := by
      by_cases hCmpMin : F.depthOf rhs < F.depthOf cur
      · have hBr : ltb (reg s9 clk) (reg s9 registers.remain) = true :=
          (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr9clk, hr9rem]; exact hCmpMin)
        have hs9_10 := step_branchLt_at (input := input) h44 (by rw [hCodeSize]; split <;> omega)
        let s10a : State L := { s9 with pc := if ltb (reg s9 clk) (reg s9 registers.remain) = true then 45 else 46 }
        have hpc10a : s10a.pc = 45 := by simp only [s10a, hBr, ite_true]
        obtain ⟨s10b, hs10ab, hpc10b, hr10rem, hr10o, hd10b⟩ :=
          step_mov_at (input := input) (by rw [hpc10a]; exact h45) (by rw [hCodeSize, hpc10a]; omega)
        refine ⟨s10b, 2, by omega, Steps.cons hs9_10 (Steps.cons hs10ab (.zero _)), by omega, hd10b,
          domRegsFixed_eq_of_eq hFix9 (fun r hr => hr10o r (fun e => by subst e; cases hr)), ?_⟩
        rw [hr10rem]; change (reg s9 clk).val = _; rw [hr9clk]; dsimp [minD]; omega
      · have hBr : ltb (reg s9 clk) (reg s9 registers.remain) = false := by
          cases hC : ltb (reg s9 clk) (reg s9 registers.remain) with
          | false => rfl
          | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hC; rw [hr9clk, hr9rem] at this; omega
        have hs9_10 := step_branchLt_at (input := input) h44 (by rw [hCodeSize]; split <;> omega)
        refine ⟨_, 1, by omega, Steps.cons hs9_10 (.zero _), by simp [hBr], rfl,
          domRegsFixed_eq_of_eq hFix9 (fun _ _ => rfl), ?_⟩
        change (reg s9 registers.remain).val = _; rw [hr9rem]; dsimp [minD]; omega
    obtain ⟨s10, kMin, hkMin, hsTo46, hpc10, hd10, hFix10, hr10rem⟩ := hTo46
    have hMinLt : minD + 1 < 2 ^ bits := by
      have := jumpForest_depthOf_lt_size hValid hCurLt
      have := jumpForest_depthOf_lt_size hValid hrhsF
      dsimp [minD]; omega
    obtain ⟨s11, hs11, hpc11, hr11rem, hr11o, hd11⟩ :=
      step_add_at (input := input) (by rw [hpc10]; exact h46) (by rw [hCodeSize, hpc10]; omega)
    have hFix11 : DomRegsFixed Q s11 :=
      domRegsFixed_eq_of_eq hFix10 (fun r hr => hr11o r (fun e => by subst e; cases hr))
    have hr11remVal : (reg s11 registers.remain).val = minD + 1 := by
      rw [hr11rem, add_no_wrap _ _ (by rw [hr10rem, hFix10.oneVal]; exact hMinLt), hr10rem, hFix10.oneVal]
    have hP47 : Placed code 47 (writeScratchInstrs 5 registers.zero (by omega)) :=
      placed3_of_get (hA 26 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 27 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 28 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
    have hP50 : Placed code 50 (writeScratchInstrs 6 registers.remain (by omega)) :=
      placed3_of_get (hA 29 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 30 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
        (hA 31 _ (by simp [loopArcBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readRecord3Instrs]))
    obtain ⟨s12, hs12, hpc12, hd12size, h12slot5, h12keep, hr12o⟩ :=
      loop_writeScratch hTen hP47 (by omega) (by omega) hFix11 hWork (by omega) (fin_ne_of_val (by decide))
    have hFix12 : DomRegsFixed Q s12 :=
      domRegsFixed_eq_of_eq hFix11 (fun r hr => hr12o r (fun e => by subst e; cases hr))
    obtain ⟨s13, hs13, hpc13, hd13size, h13slot6, h13keep, hr13o⟩ :=
      loop_writeScratch hTen hP50 hpc12 (by omega) hFix12 hWork (by omega) (fin_ne_of_val (by decide))
    have hFix13 : DomRegsFixed Q s13 :=
      domRegsFixed_eq_of_eq hFix12 (fun r hr => hr13o r (fun e => by subst e; cases hr))
    have hs13keepPre : ∀ j, j < 5 * Q → s13.data[j]? = s.data[j]? := fun j hj => by
      rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7]; exact h6eq j (by omega)
    have hs13size : s13.data.size = workCap := by
      rw [hd13size, hd12size, hd11, hd10, hd9, hd8, hd7, hd6size, hd5, hd4,
          show s3.data = s2.data from rfl, hd2, hd1]; exact hSize
    have hRec13 : Records (2 * Q) F s13.data :=
      records_preserve hRec (by rw [hs13size, hSize]) (fun j hj => hs13keepPre j (by omega))
    have hs13bs : BSearchState Q v arcPtr arcEnd cur rhs 0 (minD + 1) F s13 :=
      { fix := hFix13, dataSize := hs13size, workRoom := hWork, fSizeLe := by omega,
        fValid := hValid, records := hRec13, curLt := hCurLt, rhsLt := hrhsF,
        loLtHi := Nat.zero_lt_succ minD, hiLe := Nat.le_refl _,
        ancEq := by rw [hValid.ancestorAtDepth_zero hCurLt, hValid.ancestorAtDepth_zero hrhsF],
        ancNeAbove := fun d hd1 hd2 hd3 => by dsimp [minD] at hd1; omega,
        slotV := by rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7, h6eq _ (by omega)]; exact hSV,
        slotArcPtr := by rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7, h6eq _ (by omega)]; exact hSP,
        slotArcEnd := by rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7, h6eq _ (by omega)]; exact hSE,
        slotCur := by rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7, h6eq _ (by omega)]; exact hSC,
        slotRhs := by rw [h13keep _ (by omega), h12keep _ (by omega), hd11, hd10, hd9, hd8, hd7, h6slot4, hr5v],
        slotLo := by rw [h13keep _ (by omega), h12slot5, hFix11.zeroVal],
        slotHi := by rw [h13slot6]; change some (reg s12 registers.remain).val = _; rw [hr12o registers.remain (fin_ne_of_val (by decide)), hr11remVal] }
    have hSpan : minD + 1 - 0 ≤ 2 ^ OracleContract.L Q := by
      have hLt : Q + 1 < 2 ^ OracleContract.L Q :=
        (Nat.log2_lt (Nat.succ_ne_zero Q)).mp (Nat.lt_succ_self _)
      have := jumpForest_depthOf_lt_size hValid hCurLt
      dsimp [minD]; omega
    obtain ⟨s14, kBS, hkBS, hsBS, hpc14, hFix14, hd14size, h14keep, h14v, h14p, h14e, curMid, hcurMidLt, h14cur, hcurMidSem⟩ :=
      bsearch_loop_steps hWork hArcLt hSrcFit hTen (OracleContract.L Q) hpc13 hs13bs hSpan
    have h14Rec : Records (2 * Q) F s14.data :=
      records_preserve hRec13 (by rw [hd14size, hs13size]) (fun j hj => h14keep j (by omega))
    have hCurMidSemFull : ∀ a, a < v → (IsAncestor F a curMid ↔
        ∀ k, inStart v ≤ k → k < arcPtr + 1 → IsAncestor F a (inSrc k)) := by
      intro a ha
      rw [hcurMidSem a (by rw [hFSz]; exact ha), hCurSem a ha]
      constructor
      · rintro ⟨hOld, hNew⟩ k hkLo hkHi
        by_cases hLt : k < arcPtr
        · exact hOld k hkLo hLt
        · have hkEq : k = arcPtr := by omega
          subst k; exact hNew
      · intro hAll
        exact ⟨fun k hk1 hk2 => hAll k hk1 (by omega), hAll arcPtr (by omega) (Nat.lt_succ_self _)⟩
    obtain ⟨t, kTail, cur', hkTail, hsTail, htpc, htFix, htdSize, htkeep, htRec, hcur'Lt, hcur'Sem, htv, htc⟩ :=
      ih hpc14 (by omega) (by omega) (by omega) hFix14 hd14size hFSz hValid h14Rec hcurMidLt hCurMidSemFull h14v h14p h14e h14cur
    have hOneLeL : 1 ≤ OracleContract.L Q := OracleContract.one_le_L Q
    have hkRound : 23 + kMin + 7 + kBS ≤ 318 * OracleContract.L Q ^ 2 := by
      have hL2 : OracleContract.L Q ≤ OracleContract.L Q ^ 2 := by
        calc OracleContract.L Q = OracleContract.L Q * 1 := (Nat.mul_one _).symm
          _ ≤ OracleContract.L Q * OracleContract.L Q := Nat.mul_le_mul_left _ hOneLeL
          _ = OracleContract.L Q ^ 2 := (Nat.pow_two _).symm
      have h1LeL2 : 1 ≤ OracleContract.L Q ^ 2 := Nat.le_trans hOneLeL hL2
      have hProd : (120 * OracleContract.L Q + 66) * OracleContract.L Q =
          120 * OracleContract.L Q ^ 2 + 66 * OracleContract.L Q := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.pow_two]
      calc 23 + kMin + 7 + kBS
          ≤ 32 + ((120 * OracleContract.L Q + 66) * OracleContract.L Q + (60 * OracleContract.L Q + 40)) := by omega
        _ = 120 * OracleContract.L Q ^ 2 + 126 * OracleContract.L Q + 72 := by
              rw [hProd]; omega
        _ ≤ 120 * OracleContract.L Q ^ 2 + 126 * OracleContract.L Q ^ 2 + 72 * OracleContract.L Q ^ 2 := by
              have h1 : 126 * OracleContract.L Q ≤ 126 * OracleContract.L Q ^ 2 := Nat.mul_le_mul_left 126 hL2
              have h2 : 72 ≤ 72 * OracleContract.L Q ^ 2 := by omega
              omega
        _ = 318 * OracleContract.L Q ^ 2 := by omega
    have hsArcPrefix : Steps code input (23 + kMin + 7) s s13 := by
      have p1 : Steps code input 23 s s9 := by
        have a : Steps code input 9 s s5 := hs1.append (hs2.append (Steps.cons hs23 (Steps.cons hs4 (Steps.cons hs5 (.zero _)))))
        have b : Steps code input 14 s5 s9 := hs6.append (hs7.append (hs8.append hs9))
        simpa only [Nat.add_assoc] using a.append b
      have p2 : Steps code input (kMin + 7) s9 s13 := by
        have b : Steps code input 7 s10 s13 := Steps.cons hs11 (hs12.append hs13)
        simpa only [Nat.add_assoc] using hsTo46.append b
      simpa only [Nat.add_assoc] using p1.append p2
    have hsAll : Steps code input ((23 + kMin + 7 + kBS) + kTail) s t :=
      (hsArcPrefix.append hsBS).append hsTail
    have hkAll : (23 + kMin + 7 + kBS) + kTail ≤ 318 * (rem + 1) * OracleContract.L Q ^ 2 + 7 := by
      have hMul : 318 * (rem + 1) * OracleContract.L Q ^ 2 =
          318 * rem * OracleContract.L Q ^ 2 + 318 * OracleContract.L Q ^ 2 := by
        rw [Nat.mul_add 318 rem 1, Nat.mul_one, Nat.add_mul]
      omega
    refine ⟨t, (23 + kMin + 7 + kBS) + kTail, cur', hkAll, hsAll, htpc, htFix, htdSize,
      fun j hj => (htkeep j hj).trans ((h14keep j hj).trans (hs13keepPre j hj)),
      htRec, hcur'Lt, hcur'Sem, htv, htc⟩

private theorem appendBody_skewJump {input : Input L} {Q v d : Nat}
    (hTen : 10 ≤ 2 ^ bits) (_hvLt : v < Q) (hdLt : d < v) (_hWork : 5 * Q + 10 ≤ workCap)
    {F : JumpForest} {s16 : State L} {baseData : Array (Word bits)}
    (hFSize : F.size = v) (hValid : ValidJumpForest F)
    (hRec : Records (2 * Q) F baseData) (hBaseData : s16.data = baseData)
    (hpc16 : s16.pc = 186) (hFix16 : DomRegsFixed Q s16)
    (hr16p : (reg s16 registers.ptr).val = v)
    (hr16r : (reg s16 registers.remain).val = d)
    (hr16cb : (reg s16 registers.childBase).val = F.jumpOf d)
    (hr16cmd : (reg s16 cmd).val = F.depthOf (F.jumpOf d))
    (hr16len1 : (reg s16 clk).val = F.depthOf d - F.depthOf (F.jumpOf d)) :
    ∃ s23 kJ, kJ ≤ 13 ∧
      Steps (domLoopCode hi hw hTen) input kJ s16 s23 ∧ s23.pc = 199 ∧
      s23.data = baseData ∧ DomRegsFixed Q s23 ∧ (reg s23 registers.ptr).val = v ∧
      (reg s23 registers.remain).val = (F.mkAppendedRecord d).jump := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hApp := appendBody_placed (hi := hi) (hw := hw) hTen
  have hdF : d < F.size := by rw [hFSize]; exact hdLt
  have hj1F : F.jumpOf d < F.size := hValid.jumpOf_lt_size hdF
  have h186 : code[s16.pc]? = some (.branchLt registers.zero clk 187 199) := by
    rw [hpc16]; exact hApp 29 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  have hP187 : Placed code 187 (readJumpInstrs registers.childBase registers.childBase) :=
    placed4_of_get (hApp 30 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 31 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 32 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 33 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
  have hP191 : Placed code 191 (readDepthInstrs registers.value registers.childBase) :=
    placed4_of_get (hApp 34 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 35 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 36 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 37 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
  have h195 : code[195]? = some (.sub cmd cmd registers.value) :=
    hApp 38 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  have h196 : code[196]? = some (.branchLt clk cmd 199 197) :=
    hApp 39 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  have h197 : code[197]? = some (.branchLt cmd clk 199 198) :=
    hApp 40 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  have h198 : code[198]? = some (.mov registers.remain registers.childBase) :=
    hApp 41 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  rw [jumpForest_mkAppendedRecord_jump_eq F d]
  by_cases hPos1 : 0 < F.depthOf d - F.depthOf (F.jumpOf d)
  · have hBr1 : ltb (reg s16 registers.zero) (reg s16 clk) = true :=
      (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hFix16.zeroVal, hr16len1]; exact hPos1)
    have hs16_17 := step_branchLt_at (input := input) h186 (by rw [hCodeSize]; split <;> omega)
    let s17 : State L := { s16 with pc := if ltb (reg s16 registers.zero) (reg s16 clk) = true then 187 else 199 }
    have hpc17 : s17.pc = 187 := by simp only [s17, hBr1, ite_true]
    have hFix17 : DomRegsFixed Q s17 := domRegsFixed_eq_of_eq hFix16 (fun _ _ => rfl)
    obtain ⟨s18, hs18, hpc18, hd18, hr18j2, hr18o⟩ :=
      loop_readJump hTen hP187 hpc17 (by omega) hFix17 (by rw [show s17.data = baseData from hBaseData]; exact hRec)
        hj1F hr16cb (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
    have hFix18 : DomRegsFixed Q s18 :=
      domRegsFixed_eq_of_eq hFix17 (fun r hr => hr18o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hj2F : F.jumpOf (F.jumpOf d) < F.size := hValid.jumpOf_lt_size hj1F
    obtain ⟨s19, hs19, hpc19, hd19, hr19d2, hr19o⟩ :=
      loop_readDepth hTen hP191 hpc18 (by omega) hFix18 (by rw [hd18, show s17.data = baseData from hBaseData]; exact hRec)
        hj2F hr18j2 (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
    have hFix19 : DomRegsFixed Q s19 :=
      domRegsFixed_eq_of_eq hFix18 (fun r hr => hr19o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hr19cmd : (reg s19 cmd).val = F.depthOf (F.jumpOf d) := by
      rw [hr19o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
          hr18o cmd (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
      exact hr16cmd
    obtain ⟨s20, hs20, hpc20, hr20len2, hr20o, hd20⟩ :=
      step_sub_at (input := input) (by rw [hpc19]; exact h195) (by rw [hCodeSize, hpc19]; omega)
    have hFix20 : DomRegsFixed Q s20 :=
      domRegsFixed_eq_of_eq hFix19 (fun r hr => hr20o r (fun e => by subst e; cases hr))
    have hLeD2 : F.depthOf (F.jumpOf (F.jumpOf d)) ≤ F.depthOf (F.jumpOf d) := by
      by_cases hjz : F.jumpOf d = 0
      · rw [hjz]; obtain ⟨_, hFi⟩ := hValid.exists_forestInvariant; rw [hFi.root_jump]; exact Nat.le_refl _
      · exact Nat.le_of_lt (jumpForest_depth_jump_lt hValid (Nat.pos_of_ne_zero hjz) hj1F)
    have hr20len2Val : (reg s20 cmd).val = F.depthOf (F.jumpOf d) - F.depthOf (F.jumpOf (F.jumpOf d)) := by
      rw [hr20len2, sub_exact_word _ _ (by rw [hr19cmd, hr19d2]; exact hLeD2), hr19cmd, hr19d2]
    have hr20len1 : (reg s20 clk).val = F.depthOf d - F.depthOf (F.jumpOf d) := by
      rw [hr20o clk (fin_ne_of_val (by decide)),
          hr19o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
          hr18o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
      exact hr16len1
    have hr20p : (reg s20 registers.ptr).val = v := by
      rw [hr20o registers.ptr (fin_ne_of_val (by decide)),
          hr19o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
          hr18o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
      exact hr16p
    have hr20r : (reg s20 registers.remain).val = d := by
      rw [hr20o registers.remain (fin_ne_of_val (by decide)),
          hr19o registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
          hr18o registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))]
      exact hr16r
    have hr20cb : (reg s20 registers.childBase).val = F.jumpOf (F.jumpOf d) := by
      rw [hr20o registers.childBase (fin_ne_of_val (by decide)),
          hr19o registers.childBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr18j2]
    have h20d : s20.data = baseData := by rw [hd20, hd19, hd18]; exact hBaseData
    by_cases hEqLen : F.depthOf d - F.depthOf (F.jumpOf d) =
        F.depthOf (F.jumpOf d) - F.depthOf (F.jumpOf (F.jumpOf d))
    · have hc1 : ltb (reg s20 clk) (reg s20 cmd) = false := by
        cases hC : ltb (reg s20 clk) (reg s20 cmd) with
        | false => rfl
        | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hC; rw [hr20len1, hr20len2Val, hEqLen] at this; omega
      have hc2 : ltb (reg s20 cmd) (reg s20 clk) = false := by
        cases hC : ltb (reg s20 cmd) (reg s20 clk) with
        | false => rfl
        | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hC; rw [hr20len1, hr20len2Val, hEqLen] at this; omega
      have hs20_21 := step_branchLt_at (input := input) (by rw [hpc20, hpc19]; exact h196) (by rw [hCodeSize]; split <;> omega)
      let s21 : State L := { s20 with pc := if ltb (reg s20 clk) (reg s20 cmd) = true then 199 else 197 }
      have hpc21 : s21.pc = 197 := by simp only [s21, hc1, Bool.false_eq_true, ite_false]
      have hs21_22 := step_branchLt_at (input := input) (by rw [hpc21]; exact h197) (by rw [hCodeSize]; split <;> omega)
      let s22 : State L := { s21 with pc := if ltb (reg s21 cmd) (reg s21 clk) = true then 199 else 198 }
      have hpc22 : s22.pc = 198 := by
        have hc2' : ltb (reg s21 cmd) (reg s21 clk) = false := hc2
        simp only [s22, hc2', Bool.false_eq_true, ite_false]
      obtain ⟨s23, hs23, hpc23, hr23r, hr23o, hd23⟩ :=
        step_mov_at (input := input) (by rw [hpc22]; exact h198) (by rw [hCodeSize, hpc22]; omega)
      refine ⟨s23, 13, by omega,
        Steps.cons hs16_17 (hs18.append (hs19.append (Steps.cons hs20 (Steps.cons hs20_21 (Steps.cons hs21_22 (Steps.cons hs23 (.zero _))))))),
        by omega, by rw [hd23]; exact h20d,
        domRegsFixed_eq_of_eq hFix20 (fun r hr => hr23o r (fun e => by subst e; cases hr)),
        by rw [hr23o registers.ptr (fin_ne_of_val (by decide))]; exact hr20p, ?_⟩
      rw [hr23r]; change (reg s20 registers.childBase).val = _; rw [hr20cb]
      have hPos2 : 0 < F.depthOf (F.jumpOf d) - F.depthOf (F.jumpOf (F.jumpOf d)) := hEqLen ▸ hPos1
      simp only [hPos2, hEqLen, and_self, ite_true]
    · by_cases hLt12 : F.depthOf d - F.depthOf (F.jumpOf d) <
          F.depthOf (F.jumpOf d) - F.depthOf (F.jumpOf (F.jumpOf d))
      · have hc1 : ltb (reg s20 clk) (reg s20 cmd) = true :=
          (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr20len1, hr20len2Val]; exact hLt12)
        have hs20_21 := step_branchLt_at (input := input) (by rw [hpc20, hpc19]; exact h196) (by rw [hCodeSize]; split <;> omega)
        refine ⟨_, 11, by omega,
          Steps.cons hs16_17 (hs18.append (hs19.append (Steps.cons hs20 (Steps.cons hs20_21 (.zero _))))),
          by simp [hc1], h20d, domRegsFixed_eq_of_eq hFix20 (fun _ _ => rfl), hr20p, ?_⟩
        change (reg s20 registers.remain).val = _; rw [hr20r]; simp [hPos1, hEqLen]
      · have hLt21 : F.depthOf (F.jumpOf d) - F.depthOf (F.jumpOf (F.jumpOf d)) <
            F.depthOf d - F.depthOf (F.jumpOf d) := by omega
        have hc1 : ltb (reg s20 clk) (reg s20 cmd) = false := by
          cases hC : ltb (reg s20 clk) (reg s20 cmd) with
          | false => rfl
          | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hC; rw [hr20len1, hr20len2Val] at this; omega
        have hc2 : ltb (reg s20 cmd) (reg s20 clk) = true :=
          (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr20len1, hr20len2Val]; exact hLt21)
        have hs20_21 := step_branchLt_at (input := input) (by rw [hpc20, hpc19]; exact h196) (by rw [hCodeSize]; split <;> omega)
        let s21 : State L := { s20 with pc := if ltb (reg s20 clk) (reg s20 cmd) = true then 199 else 197 }
        have hpc21 : s21.pc = 197 := by simp only [s21, hc1, Bool.false_eq_true, ite_false]
        have hs21_22 := step_branchLt_at (input := input) (by rw [hpc21]; exact h197) (by rw [hCodeSize]; split <;> omega)
        refine ⟨_, 12, by omega,
          Steps.cons hs16_17 (hs18.append (hs19.append (Steps.cons hs20 (Steps.cons hs20_21 (Steps.cons hs21_22 (.zero _)))))),
          by simp [show ltb (reg s21 cmd) (reg s21 clk) = true from hc2], h20d,
          domRegsFixed_eq_of_eq hFix20 (fun _ _ => rfl), hr20p, ?_⟩
        change (reg s20 registers.remain).val = _; exact Eq.trans hr20r (by simp [hPos1, hEqLen])
  · have hBr1 : ltb (reg s16 registers.zero) (reg s16 clk) = false := by
      cases hC : ltb (reg s16 registers.zero) (reg s16 clk) with
      | false => rfl
      | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hC; rw [hFix16.zeroVal, hr16len1] at this; omega
    have hs16_17 := step_branchLt_at (input := input) h186 (by rw [hCodeSize]; split <;> omega)
    refine ⟨_, 1, by omega, Steps.cons hs16_17 (.zero _), by simp [hBr1], hBaseData,
      domRegsFixed_eq_of_eq hFix16 (fun _ _ => rfl), hr16p, ?_⟩
    change (reg s16 registers.remain).val = _; exact Eq.trans hr16r (by simp [hPos1])

private theorem appendBody_phase1 {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) (hTen : 10 ≤ 2 ^ bits)
    {v d : Nat} (hv1 : 1 ≤ v) (hvLt : v < Q) (hdLt : d < v)
    {F : JumpForest} {s : State L}
    (hPC : s.pc = 157)
    (hFix : DomRegsFixed Q s)
    (hSize : s.data.size = workCap)
    (hInv : DomPrefixInv input Q mReach inStart inSrc v F s.data)
    (hSV : (s.data[5 * Q + 0]?).map Fin.val = some v)
    (hSC : (s.data[5 * Q + 3]?).map Fin.val = some d) :
    ∃ s16 : State L,
      Steps (domLoopCode hi hw hTen) input 29 s s16 ∧
      s16.pc = 186 ∧ DomRegsFixed Q s16 ∧ s16.data.size = workCap ∧
      Records (2 * Q) F s16.data ∧
      (reg s16 registers.ptr).val = v ∧
      (reg s16 registers.remain).val = d ∧
      (reg s16 registers.childBase).val = F.jumpOf d ∧
      (reg s16 cmd).val = F.depthOf (F.jumpOf d) ∧
      (reg s16 clk).val = F.depthOf d - F.depthOf (F.jumpOf d) ∧
      (∀ j, j < 5 * Q → j ≠ v → j ≠ Q + v →
        j ≠ 2 * Q + 3 * v → j ≠ 2 * Q + 1 + 3 * v → s16.data[j]? = s.data[j]?) ∧
      (s16.data[v]?).map Fin.val = some d ∧
      (s16.data[Q + v]?).map Fin.val = some (F.depthOf d + 1) ∧
      (s16.data[2 * Q + 3 * v]?).map Fin.val = some d ∧
      (s16.data[2 * Q + 1 + 3 * v]?).map Fin.val = some (F.depthOf d + 1) := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hApp := appendBody_placed (hi := hi) (hw := hw) hTen
  have hdF : d < F.size := by rw [hInv.size_eq]; exact hdLt
  have hWork := workBounds_nat sp
  have hDepthD := jumpForest_depthOf_lt_size hInv.valid hdF
  have hDLe : F.depthOf d < v := by rw [← hInv.size_eq]; exact hDepthD
  have hP157 : Placed code 157 (readScratchInstrs registers.ptr 0 (by omega)) :=
    placed3_of_get (hApp 0 _ (by simp [appendBodyBlock, readScratchInstrs]))
      (hApp 1 _ (by simp [appendBodyBlock, readScratchInstrs]))
      (hApp 2 _ (by simp [appendBodyBlock, readScratchInstrs]))
  have hP160 : Placed code 160 (readScratchInstrs registers.remain 3 (by omega)) :=
    placed3_of_get (hApp 3 _ (by simp [appendBodyBlock, readScratchInstrs]))
      (hApp 4 _ (by simp [appendBodyBlock, readScratchInstrs]))
      (hApp 5 _ (by simp [appendBodyBlock, readScratchInstrs]))
  obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
    loop_readScratch (input := input) hTen hP157 hPC (by omega) hFix hWork (by omega) hSV (fin_ne_of_val (by decide))
  have hFix1 : DomRegsFixed Q s1 :=
    domRegsFixed_eq_of_eq hFix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  obtain ⟨s2, hs2, hpc2, hd2, hr2r, hr2o⟩ :=
    loop_readScratch (input := input) hTen hP160 hpc1 (by omega) hFix1 hWork (by omega) (by rw [hd1]; exact hSC) (fin_ne_of_val (by decide))
  have hFix2 : DomRegsFixed Q s2 :=
    domRegsFixed_eq_of_eq hFix1 (fun r hr => hr2o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr2p : (reg s2 registers.ptr).val = v := by
    rw [hr2o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr1p]
  have h163 : code[s2.pc]? = some (.storeData registers.ptr registers.remain) := by
    rw [hpc2]; exact hApp 6 _ (by simp [appendBodyBlock, readScratchInstrs])
  have hFit2 : (reg s2 registers.ptr).val < s2.data.size := by
    rw [hr2p, hd2, hd1, hSize]; omega
  obtain ⟨s3, hs3, hpc3, hr3, hd3⟩ := step_storeData_exists (input := input) h163 hFit2 (by rw [hCodeSize, hpc2]; omega)
  have hFix3 : DomRegsFixed Q s3 :=
    domRegsFixed_eq_of_eq hFix2 (fun r _ => reg_eq_of_regs_eq hr3 r)
  have hr3p : (reg s3 registers.ptr).val = v := by rw [reg_eq_of_regs_eq hr3, hr2p]
  have hr3r : (reg s3 registers.remain).val = d := by rw [reg_eq_of_regs_eq hr3, hr2r]
  have h164 : code[s3.pc]? = some (.add registers.value registers.ptr registers.ptr) := by
    rw [hpc3, hpc2]; exact hApp 7 _ (by simp [appendBodyBlock, readScratchInstrs])
  obtain ⟨s4, hs4, hpc4, hr4v, hr4o, hd4⟩ := step_add_at (input := input) h164 (by rw [hCodeSize, hpc3, hpc2]; omega)
  have hFix4 : DomRegsFixed Q s4 :=
    domRegsFixed_eq_of_eq hFix3 (fun r hr => hr4o r (fun e => by subst e; cases hr))
  have hr4vVal : (reg s4 registers.value).val = 2 * v := by
    rw [hr4v, add_no_wrap _ _ (by rw [hr3p]; omega), hr3p]; omega
  have hr4p : (reg s4 registers.ptr).val = v := by rw [hr4o registers.ptr (fin_ne_of_val (by decide)), hr3p]
  have h165 : code[s4.pc]? = some (.add registers.value registers.value registers.ptr) := by
    rw [hpc4, hpc3, hpc2]; exact hApp 8 _ (by simp [appendBodyBlock, readScratchInstrs])
  obtain ⟨s5, hs5, hpc5, hr5v, hr5o, hd5⟩ := step_add_at (input := input) h165 (by rw [hCodeSize, hpc4, hpc3, hpc2]; omega)
  have hFix5 : DomRegsFixed Q s5 :=
    domRegsFixed_eq_of_eq hFix4 (fun r hr => hr5o r (fun e => by subst e; cases hr))
  have hr5vVal : (reg s5 registers.value).val = 3 * v := by
    rw [hr5v, add_no_wrap _ _ (by rw [hr4vVal, hr4p]; omega), hr4vVal, hr4p]; omega
  have h166 : code[s5.pc]? = some (.add registers.tmp tinBase registers.value) := by
    rw [hpc5, hpc4, hpc3, hpc2]; exact hApp 9 _ (by simp [appendBodyBlock, readScratchInstrs])
  obtain ⟨s6, hs6, hpc6, hr6t, hr6o, hd6⟩ := step_add_at (input := input) h166 (by rw [hCodeSize, hpc5, hpc4, hpc3, hpc2]; omega)
  have hFix6 : DomRegsFixed Q s6 :=
    domRegsFixed_eq_of_eq hFix5 (fun r hr => hr6o r (fun e => by subst e; cases hr))
  have hr6tVal : (reg s6 registers.tmp).val = 2 * Q + 3 * v := by
    rw [hr6t, add_no_wrap _ _ (by rw [hFix5.tinVal, hr5vVal]; omega), hFix5.tinVal, hr5vVal]
  have hFit6 : (reg s6 registers.tmp).val < s6.data.size := by
    rw [hr6tVal, show s6.data.size = workCap from s6.data_size]; omega
  have h167 : code[s6.pc]? = some (.storeData registers.tmp registers.remain) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2]; exact hApp 10 _ (by simp [appendBodyBlock, readScratchInstrs])
  obtain ⟨s7, hs7, hpc7, hr7, hd7⟩ :=
    step_storeData_exists (input := input) h167 hFit6 (by rw [hCodeSize, hpc6, hpc5, hpc4, hpc3, hpc2]; omega)
  have hFix7 : DomRegsFixed Q s7 := domRegsFixed_eq_of_eq hFix6 (fun r _ => reg_eq_of_regs_eq hr7 r)
  have hr7p : (reg s7 registers.ptr).val = v := by
    rw [reg_eq_of_regs_eq hr7, hr6o registers.ptr (fin_ne_of_val (by decide)),
        hr5o registers.ptr (fin_ne_of_val (by decide)), hr4p]
  have hr7v : (reg s7 registers.value).val = 3 * v := by
    rw [reg_eq_of_regs_eq hr7, hr6o registers.value (fin_ne_of_val (by decide)), hr5vVal]
  have hr7r : (reg s7 registers.remain).val = d := by
    rw [reg_eq_of_regs_eq hr7, hr6o registers.remain (fin_ne_of_val (by decide)),
        hr5o registers.remain (fin_ne_of_val (by decide)),
        hr4o registers.remain (fin_ne_of_val (by decide)), hr3r]
  have hEq7_2 : ∀ j, j ≠ v → j ≠ 2 * Q + 3 * v → s7.data[j]? = s.data[j]? := fun j h1 h2 => by
    rw [hd7, Array.getElem?_set]; split
    · rename_i hEq; exfalso; exact h2 (hEq.symm.trans hr6tVal)
    · rw [hd6, hd5, hd4, hd3, Array.getElem?_set]; split
      · rename_i hEq; exfalso; exact h1 (hEq.symm.trans hr2p)
      · rw [hd2, hd1]
  have hs7Rec : Records (2 * Q) F s7.data := by
    refine records_preserve_ge hInv.records (by rw [s7.data_size, hSize]) (fun j hjLo hjHi => ?_)
    rw [hInv.size_eq] at hjHi
    exact hEq7_2 j (by omega) (by omega)
  have hP168 : Placed code 168 (readDepthInstrs clk registers.remain) :=
    placed4_of_get (hApp 11 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs]))
      (hApp 12 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs]))
      (hApp 13 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs]))
      (hApp 14 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs]))
  obtain ⟨s8, hs8, hpc8, hd8, hr8clk, hr8o⟩ :=
    loop_readDepth (input := input) hTen hP168 (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]) (by omega)
      hFix7 hs7Rec hdF hr7r (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
  have hFix8 : DomRegsFixed Q s8 :=
    domRegsFixed_eq_of_eq hFix7 (fun r hr => hr8o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have h172 : code[s8.pc]? = some (.add registers.childBase clk registers.one) := by
    rw [hpc8]; exact hApp 15 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs])
  obtain ⟨s9, hs9, hpc9, hr9cb, hr9o, hd9⟩ := step_add_at (input := input) h172 (by rw [hCodeSize, hpc8]; omega)
  have hFix9 : DomRegsFixed Q s9 :=
    domRegsFixed_eq_of_eq hFix8 (fun r hr => hr9o r (fun e => by subst e; cases hr))
  have hr9cbVal : (reg s9 registers.childBase).val = F.depthOf d + 1 := by
    rw [hr9cb, add_no_wrap _ _ (by rw [hr8clk, hFix8.oneVal]; omega), hr8clk, hFix8.oneVal]
  have hr9p : (reg s9 registers.ptr).val = v := by
    rw [hr9o registers.ptr (fin_ne_of_val (by decide)), hr8o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr7p]
  have h173 : code[s9.pc]? = some (.add registers.tmp count registers.ptr) := by
    rw [hpc9, hpc8]; exact hApp 16 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs])
  obtain ⟨s10, hs10, hpc10, hr10t, hr10o, hd10⟩ := step_add_at (input := input) h173 (by rw [hCodeSize, hpc9, hpc8]; omega)
  have hFix10 : DomRegsFixed Q s10 :=
    domRegsFixed_eq_of_eq hFix9 (fun r hr => hr10o r (fun e => by subst e; cases hr))
  have hr10tVal : (reg s10 registers.tmp).val = Q + v := by
    rw [hr10t, add_no_wrap _ _ (by rw [hFix9.countVal, hr9p]; omega), hFix9.countVal, hr9p]
  have hFit10 : (reg s10 registers.tmp).val < s10.data.size := by
    rw [hr10tVal, show s10.data.size = workCap from s10.data_size]; omega
  have h174 : code[s10.pc]? = some (.storeData registers.tmp registers.childBase) := by
    rw [hpc10, hpc9, hpc8]; exact hApp 17 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs])
  obtain ⟨s11, hs11, hpc11, hr11, hd11⟩ := step_storeData_exists (input := input) h174 hFit10 (by rw [hCodeSize, hpc10, hpc9, hpc8]; omega)
  have hFix11 : DomRegsFixed Q s11 := domRegsFixed_eq_of_eq hFix10 (fun r _ => reg_eq_of_regs_eq hr11 r)
  have hr11v : (reg s11 registers.value).val = 3 * v := by
    rw [reg_eq_of_regs_eq hr11, hr10o registers.value (fin_ne_of_val (by decide)),
        hr9o registers.value (fin_ne_of_val (by decide)),
        hr8o registers.value (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr7v]
  have h175 : code[s11.pc]? = some (.add registers.tmp toutBase registers.value) := by
    rw [hpc11, hpc10, hpc9, hpc8]; exact hApp 18 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs])
  obtain ⟨s12, hs12, hpc12, hr12t, hr12o, hd12⟩ := step_add_at (input := input) h175 (by rw [hCodeSize, hpc11, hpc10, hpc9, hpc8]; omega)
  have hFix12 : DomRegsFixed Q s12 :=
    domRegsFixed_eq_of_eq hFix11 (fun r hr => hr12o r (fun e => by subst e; cases hr))
  have hr12tVal : (reg s12 registers.tmp).val = 2 * Q + 1 + 3 * v := by
    rw [hr12t, add_no_wrap _ _ (by rw [hFix11.toutVal, hr11v]; omega), hFix11.toutVal, hr11v]
  have hFit12 : (reg s12 registers.tmp).val < s12.data.size := by
    rw [hr12tVal, show s12.data.size = workCap from s12.data_size]; omega
  have h176 : code[s12.pc]? = some (.storeData registers.tmp registers.childBase) := by
    rw [hpc12, hpc11, hpc10, hpc9, hpc8]; exact hApp 19 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readRecord3Instrs])
  obtain ⟨s13, hs13, hpc13, hr13, hd13⟩ := step_storeData_exists (input := input) h176 hFit12 (by rw [hCodeSize, hpc12, hpc11, hpc10, hpc9, hpc8]; omega)
  have hFix13 : DomRegsFixed Q s13 := domRegsFixed_eq_of_eq hFix12 (fun r _ => reg_eq_of_regs_eq hr13 r)
  have hEq13_7 : ∀ j, j ≠ Q + v → j ≠ 2 * Q + 1 + 3 * v → s13.data[j]? = s7.data[j]? := fun j h1 h2 => by
    rw [hd13, Array.getElem?_set]; split
    · rename_i hEq; exfalso; exact h2 (hEq.symm.trans hr12tVal)
    · rw [hd12, hd11, Array.getElem?_set]; split
      · rename_i hEq; exfalso; exact h1 (hEq.symm.trans hr10tVal)
      · rw [hd10, hd9, hd8]
  have hs13Rec : Records (2 * Q) F s13.data := by
    refine records_preserve_ge hs7Rec (by rw [s13.data_size, s7.data_size]) (fun j hjLo hjHi => ?_)
    rw [hInv.size_eq] at hjHi
    exact hEq13_7 j (by omega) (by omega)
  have hr13r : (reg s13 registers.remain).val = d := by
    rw [reg_eq_of_regs_eq hr13, hr12o registers.remain (fin_ne_of_val (by decide)),
        reg_eq_of_regs_eq hr11, hr10o registers.remain (fin_ne_of_val (by decide)),
        hr9o registers.remain (fin_ne_of_val (by decide)),
        hr8o registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr7r]
  have hr13clk : (reg s13 clk).val = F.depthOf d := by
    rw [reg_eq_of_regs_eq hr13, hr12o clk (fin_ne_of_val (by decide)),
        reg_eq_of_regs_eq hr11, hr10o clk (fin_ne_of_val (by decide)),
        hr9o clk (fin_ne_of_val (by decide)), hr8clk]
  have hr13p : (reg s13 registers.ptr).val = v := by
    rw [reg_eq_of_regs_eq hr13, hr12o registers.ptr (fin_ne_of_val (by decide)),
        reg_eq_of_regs_eq hr11, hr10o registers.ptr (fin_ne_of_val (by decide)), hr9p]
  have hP177 : Placed code 177 (readJumpInstrs registers.childBase registers.remain) :=
    placed4_of_get (hApp 20 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 21 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 22 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 23 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
  obtain ⟨s14, hs14, hpc14, hd14, hr14j1, hr14o⟩ :=
    loop_readJump (input := input) hTen hP177 (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8]) (by omega)
      hFix13 hs13Rec hdF hr13r (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
  have hFix14 : DomRegsFixed Q s14 :=
    domRegsFixed_eq_of_eq hFix13 (fun r hr => hr14o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hj1F : F.jumpOf d < F.size := hInv.valid.jumpOf_lt_size hdF
  have hP181 : Placed code 181 (readDepthInstrs cmd registers.childBase) :=
    placed4_of_get (hApp 24 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 25 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 26 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 27 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
  obtain ⟨s15, hs15, hpc15, hd15, hr15d1, hr15o⟩ :=
    loop_readDepth (input := input) hTen hP181 hpc14 (by omega) hFix14 (by rw [hd14]; exact hs13Rec)
      hj1F hr14j1 (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide))
  have hFix15 : DomRegsFixed Q s15 :=
    domRegsFixed_eq_of_eq hFix14 (fun r hr => hr15o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
  have hr15clk : (reg s15 clk).val = F.depthOf d := by
    rw [hr15o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
        hr14o clk (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr13clk]
  have h185 : code[s15.pc]? = some (.sub clk clk cmd) := by
    rw [hpc15]; exact hApp 28 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s16, hs16, hpc16, hr16clk, hr16o, hd16⟩ := step_sub_at (input := input) h185 (by rw [hCodeSize, hpc15]; omega)
  have hFix16 : DomRegsFixed Q s16 :=
    domRegsFixed_eq_of_eq hFix15 (fun r hr => hr16o r (fun e => by subst e; cases hr))
  have hLeD1 : F.depthOf (F.jumpOf d) ≤ F.depthOf d := by
    by_cases hdz : d = 0
    · subst hdz; obtain ⟨_, hFi⟩ := hInv.valid.exists_forestInvariant; rw [hFi.root_jump]; exact Nat.le_refl _
    · exact Nat.le_of_lt (jumpForest_depth_jump_lt hInv.valid (Nat.pos_of_ne_zero hdz) hdF)
  have hs16_13 : s16.data = s13.data := by rw [hd16, hd15, hd14]
  have hsAll1 : Steps code input 29 s s16 := by
    have a : Steps code input 11 s s7 :=
      hs1.append (hs2.append (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (.zero _)))))))
    have b : Steps code input 9 s7 s13 :=
      hs8.append (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (.zero _))))))
    have c : Steps code input 9 s13 s16 := hs14.append (hs15.append (Steps.cons hs16 (.zero _)))
    simpa only [Nat.add_assoc] using (a.append b).append c
  refine ⟨s16, hsAll1, by rw [hpc16, hpc15], hFix16, s16.data_size,
    by rw [hs16_13]; exact hs13Rec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr16o registers.ptr (fin_ne_of_val (by decide)),
        hr15o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
        hr14o registers.ptr (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr13p]
  · rw [hr16o registers.remain (fin_ne_of_val (by decide)),
        hr15o registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)),
        hr14o registers.remain (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr13r]
  · rw [hr16o registers.childBase (fin_ne_of_val (by decide)),
        hr15o registers.childBase (fin_ne_of_val (by decide)) (fin_ne_of_val (by decide)), hr14j1]
  · rw [hr16o cmd (fin_ne_of_val (by decide)), hr15d1]
  · rw [hr16clk, sub_exact_word _ _ (by rw [hr15clk, hr15d1]; exact hLeD1), hr15clk, hr15d1]
  · exact fun j _ h1 h2 h3 h4 => by rw [hs16_13]; exact (hEq13_7 j h2 h4).trans (hEq7_2 j h1 h3)
  · rw [hs16_13, hEq13_7 v (by omega) (by omega), hd7, Array.getElem?_set]; split
    · rename_i hEq; exfalso; rw [hr6tVal] at hEq; omega
    · rw [hd6, hd5, hd4, hd3, Array.getElem?_set]; split
      · simp only [Option.map_some, hr2r]
      · rename_i hNe; exfalso; exact hNe hr2p
  · rw [hs16_13, hd13, Array.getElem?_set]; split
    · rename_i hEq; exfalso; rw [hr12tVal] at hEq; omega
    · rw [hd12, hd11, Array.getElem?_set]; split
      · simp only [Option.map_some]
        rw [hr10o registers.childBase (fin_ne_of_val (by decide)), hr9cbVal]
      · rename_i hNe; exfalso; exact hNe hr10tVal
  · rw [hs16_13, hEq13_7 (2 * Q + 3 * v) (by omega) (by omega), hd7, Array.getElem?_set]; split
    · simp only [Option.map_some]
      rw [hr6o registers.remain (fin_ne_of_val (by decide)),
          hr5o registers.remain (fin_ne_of_val (by decide)),
          hr4o registers.remain (fin_ne_of_val (by decide)), hr3r]
    · rename_i hNe; exfalso; exact hNe hr6tVal
  · rw [hs16_13, hd13, Array.getElem?_set]; split
    · simp only [Option.map_some]
      rw [hr12o registers.childBase (fin_ne_of_val (by decide)),
          reg_eq_of_regs_eq hr11, hr10o registers.childBase (fin_ne_of_val (by decide)), hr9cbVal]
    · rename_i hNe; exfalso; exact hNe hr12tVal

private theorem appendBody_steps {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) (hTen : 10 ≤ 2 ^ bits)
    {v d : Nat} (hv1 : 1 ≤ v) (hvLt : v < Q) (hdLt : d < v)
    {F : JumpForest} {s : State L}
    (hPC : s.pc = 157)
    (hFix : DomRegsFixed Q s)
    (hSize : s.data.size = workCap)
    (hInv : DomPrefixInv input Q mReach inStart inSrc v F s.data)
    (hdExact : ∀ a, a < v → (IsAncestor F a d ↔ ∀ k, inStart v ≤ k → k < inStart (v + 1) → IsAncestor F a (inSrc k)))
    (hSV : (s.data[5 * Q + 0]?).map Fin.val = some v)
    (hSC : (s.data[5 * Q + 3]?).map Fin.val = some d) :
    ∃ t k, k ≤ 51 ∧
      Steps (domLoopCode hi hw hTen) input k s t ∧
      t.pc = 0 ∧ DomRegsFixed Q t ∧ t.data.size = workCap ∧
      DomPrefixInv input Q mReach inStart inSrc (v + 1) (F.appendLeaf d) t.data ∧
      (denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, sp.qPos⟩
        ⟨d, Nat.lt_trans hdLt hvLt⟩ ⟨v, hvLt⟩ ∧
      (t.data[5 * Q + 0]?).map Fin.val = some (v + 1) := by
  let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
  have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
  have hApp := appendBody_placed (hi := hi) (hw := hw) hTen
  have hWork := workBounds_nat sp
  obtain ⟨s16, hsPhase1, hpc16, hFix16, h16size, h16Rec, hr16p, hr16r, hr16cb, hr16cmd, hr16len1,
      h16Keep, h16P, h16D, h16F0, h16F1⟩ :=
    appendBody_phase1 sp hTen hv1 hvLt hdLt hPC hFix hSize hInv hSV hSC
  obtain ⟨s23, kJ, hkJ, hsJump, hpc23, hd23, hFix23, hr23p, hr23rem⟩ :=
    appendBody_skewJump hTen hvLt hdLt hWork hInv.size_eq hInv.valid h16Rec rfl
      hpc16 hFix16 hr16p hr16r hr16cb hr16cmd hr16len1
  have h199 : code[s23.pc]? = some (.add registers.value registers.ptr registers.ptr) := by
    rw [hpc23]; exact hApp 42 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s24, hs24, hpc24, hr24v, hr24o, hd24⟩ := step_add_at (input := input) h199 (by rw [hCodeSize, hpc23]; omega)
  have hFix24 : DomRegsFixed Q s24 := domRegsFixed_eq_of_eq hFix23 (fun r hr => hr24o r (fun e => by subst e; cases hr))
  have hr24vVal : (reg s24 registers.value).val = 2 * v := by
    rw [hr24v, add_no_wrap _ _ (by rw [hr23p]; omega), hr23p]; omega
  have hr24p : (reg s24 registers.ptr).val = v := by rw [hr24o registers.ptr (fin_ne_of_val (by decide)), hr23p]
  have h200 : code[s24.pc]? = some (.add registers.value registers.value registers.ptr) := by
    rw [hpc24, hpc23]; exact hApp 43 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s25, hs25, hpc25, hr25v, hr25o, hd25⟩ := step_add_at (input := input) h200 (by rw [hCodeSize, hpc24, hpc23]; omega)
  have hFix25 : DomRegsFixed Q s25 := domRegsFixed_eq_of_eq hFix24 (fun r hr => hr25o r (fun e => by subst e; cases hr))
  have hr25vVal : (reg s25 registers.value).val = 3 * v := by
    rw [hr25v, add_no_wrap _ _ (by rw [hr24vVal, hr24p]; omega), hr24vVal, hr24p]; omega
  have h201 : code[s25.pc]? = some (.add registers.tmp offsetBase registers.value) := by
    rw [hpc25, hpc24, hpc23]; exact hApp 44 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s26, hs26, hpc26, hr26t, hr26o, hd26⟩ := step_add_at (input := input) h201 (by rw [hCodeSize, hpc25, hpc24, hpc23]; omega)
  have hFix26 : DomRegsFixed Q s26 := domRegsFixed_eq_of_eq hFix25 (fun r hr => hr26o r (fun e => by subst e; cases hr))
  have hr26tVal : (reg s26 registers.tmp).val = 2 * Q + 2 + 3 * v := by
    rw [hr26t, add_no_wrap _ _ (by rw [hFix25.offsetVal, hr25vVal]; omega), hFix25.offsetVal, hr25vVal]
  have hFit26 : (reg s26 registers.tmp).val < s26.data.size := by
    rw [hr26tVal, show s26.data.size = workCap from s26.data_size]; omega
  have h202 : code[s26.pc]? = some (.storeData registers.tmp registers.remain) := by
    rw [hpc26, hpc25, hpc24, hpc23]; exact hApp 45 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s27, hs27, hpc27, hr27, hd27⟩ := step_storeData_exists (input := input) h202 hFit26 (by rw [hCodeSize, hpc26, hpc25, hpc24, hpc23]; omega)
  have hFix27 : DomRegsFixed Q s27 := domRegsFixed_eq_of_eq hFix26 (fun r _ => reg_eq_of_regs_eq hr27 r)
  have hr27p : (reg s27 registers.ptr).val = v := by
    rw [reg_eq_of_regs_eq hr27, hr26o registers.ptr (fin_ne_of_val (by decide)),
        hr25o registers.ptr (fin_ne_of_val (by decide)), hr24p]
  have hr27r : (reg s27 registers.remain).val = (F.mkAppendedRecord d).jump := by
    rw [reg_eq_of_regs_eq hr27, hr26o registers.remain (fin_ne_of_val (by decide)),
        hr25o registers.remain (fin_ne_of_val (by decide)),
        hr24o registers.remain (fin_ne_of_val (by decide)), hr23rem]
  have h203 : code[s27.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [hpc27, hpc26, hpc25, hpc24, hpc23]; exact hApp 46 _ (by simp [appendBodyBlock, readScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  obtain ⟨s28, hs28, hpc28, hr28p, hr28o, hd28⟩ := step_add_at (input := input) h203 (by rw [hCodeSize, hpc27, hpc26, hpc25, hpc24, hpc23]; omega)
  have hFix28 : DomRegsFixed Q s28 := domRegsFixed_eq_of_eq hFix27 (fun r hr => hr28o r (fun e => by subst e; cases hr))
  have hr28pVal : (reg s28 registers.ptr).val = v + 1 := by
    rw [hr28p, add_no_wrap _ _ (by rw [hr27p, hFix27.oneVal]; omega), hr27p, hFix27.oneVal]
  have hP204 : Placed code 204 (writeScratchInstrs 0 registers.ptr (by omega)) :=
    placed3_of_get (hApp 47 _ (by simp [appendBodyBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 48 _ (by simp [appendBodyBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
      (hApp 49 _ (by simp [appendBodyBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs]))
  obtain ⟨s29, hs29, hpc29, hd29size, h29slot0, h29keep, hr29o⟩ :=
    loop_writeScratch (input := input) hTen hP204 (by omega) (by omega) hFix28 hWork (by omega) (fin_ne_of_val (by decide))
  have hFix29 : DomRegsFixed Q s29 :=
    domRegsFixed_eq_of_eq hFix28 (fun r hr => hr29o r (fun e => by subst e; cases hr))
  have h207 : code[s29.pc]? = some (.goto 0) := by
    rw [hpc29]; exact hApp 50 _ (by simp [appendBodyBlock, readScratchInstrs, writeScratchInstrs, readDepthInstrs, readJumpInstrs, readRecord3Instrs])
  have hs29_30 := step_goto_at (input := input) h207 (by rw [hCodeSize]; omega)
  have hEq29_16 : ∀ j, j < 5 * Q → j ≠ 2 * Q + 2 + 3 * v → s29.data[j]? = s16.data[j]? := fun j hj hne => by
    rw [h29keep _ (by omega), hd28, hd27, Array.getElem?_set]; split
    · rename_i hEq; exfalso; exact hne (hEq.symm.trans hr26tVal)
    · rw [hd26, hd25, hd24, hd23]
  have hKeepAll : ∀ j, j < 5 * Q → j ≠ v → j ≠ Q + v →
      j ≠ 2 * Q + 3 * v → j ≠ 2 * Q + 1 + 3 * v → j ≠ 2 * Q + 2 + 3 * v →
      s29.data[j]? = s.data[j]? := fun j hj h1 h2 h3 h4 h5 =>
    (hEq29_16 j hj h5).trans (h16Keep j hj h1 h2 h3 h4)
  have hKeepP : ∀ u < v, s29.data[u]? = s.data[u]? := fun u hu =>
    hKeepAll u (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hKeepD : ∀ u < v, s29.data[Q + u]? = s.data[Q + u]? := fun u hu =>
    hKeepAll (Q + u) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hKeepF : ∀ u < v, s29.data[2 * Q + 3 * u]? = s.data[2 * Q + 3 * u]? ∧
      s29.data[2 * Q + 1 + 3 * u]? = s.data[2 * Q + 1 + 3 * u]? ∧
      s29.data[2 * Q + 2 + 3 * u]? = s.data[2 * Q + 2 + 3 * u]? := fun u hu =>
    ⟨hKeepAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
     hKeepAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
     hKeepAll _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  have hNewP : (s29.data[v]?).map Fin.val = some d := by
    rw [hEq29_16 v (by omega) (by omega)]; exact h16P
  have hNewD : (s29.data[Q + v]?).map Fin.val = some (F.depthOf d + 1) := by
    rw [hEq29_16 (Q + v) (by omega) (by omega)]; exact h16D
  have hNewF0 : (s29.data[2 * Q + 3 * v]?).map Fin.val = some d := by
    rw [hEq29_16 (2 * Q + 3 * v) (by omega) (by omega)]; exact h16F0
  have hNewF1 : (s29.data[2 * Q + 1 + 3 * v]?).map Fin.val = some (F.depthOf d + 1) := by
    rw [hEq29_16 (2 * Q + 1 + 3 * v) (by omega) (by omega)]; exact h16F1
  have hNewF2 : (s29.data[2 * Q + 2 + 3 * v]?).map Fin.val = some (F.mkAppendedRecord d).jump := by
    rw [h29keep _ (by omega), hd28, hd27, Array.getElem?_set]; split
    · simp only [Option.map_some]
      rw [hr26o registers.remain (fin_ne_of_val (by decide)),
          hr25o registers.remain (fin_ne_of_val (by decide)),
          hr24o registers.remain (fin_ne_of_val (by decide)), hr23rem]
    · rename_i hNe; exfalso; exact hNe hr26tVal
  let t : State L := { s29 with pc := 0 }
  obtain ⟨hInv', hIdomV⟩ := domPrefixInv_step sp hv1 hvLt hInv (by rw [t.data_size]) hdLt hdExact
    hKeepP hKeepD hKeepF hNewP hNewD hNewF0 hNewF1 hNewF2
  have hsAll : Steps code input ((29 + kJ) + 9) s t := by
    have p2 : Steps code input 9 s23 t :=
      Steps.cons hs24 (Steps.cons hs25 (Steps.cons hs26 (Steps.cons hs27 (Steps.cons hs28 (hs29.append (Steps.cons hs29_30 (.zero _)))))))
    simpa only [Nat.add_assoc] using (hsPhase1.append hsJump).append p2
  exact ⟨t, (29 + kJ) + 9, by omega, hsAll, rfl,
    domRegsFixed_eq_of_eq hFix29 (fun _ _ => rfl), t.data_size, hInv', hIdomV,
    by change (s29.data[5 * Q + 0]?).map Fin.val = some (v + 1); rw [h29slot0, hr28pVal]⟩

private def IdomPrefix (Q bound : Nat) (hQ : 0 < Q) (inStart inSrc : Nat → Nat)
    (F : JumpForest) : Prop :=
  ∀ u : Fin Q, 1 ≤ u.val → u.val < bound →
    ∃ hp : F.parentOf u.val < Q,
      (denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, hQ⟩ ⟨F.parentOf u.val, hp⟩ u

private theorem loopV_steps {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc) (hTen : 10 ≤ 2 ^ bits) :
    ∀ (rem v : Nat) {F : JumpForest} {s : State L},
      s.pc = 0 →
      Q = v + rem →
      1 ≤ v →
      DomRegsFixed Q s →
      s.data.size = workCap →
      DomPrefixInv input Q mReach inStart inSrc v F s.data →
      IdomPrefix Q v sp.qPos inStart inSrc F →
      (s.data[5 * Q + 0]?).map Fin.val = some v →
      ∃ t k F', k ≤ 318 * (mReach - inStart v) * OracleContract.L Q ^ 2 + 79 * rem + 4 ∧
        Steps (domLoopCode hi hw hTen) input k s t ∧
        t.pc = 208 ∧
        DomRegsFixed Q t ∧
        t.data.size = workCap ∧
        DomPrefixInv input Q mReach inStart inSrc Q F' t.data ∧
        IdomPrefix Q Q sp.qPos inStart inSrc F' := by
  intro rem
  induction rem with
  | zero =>
    intro v F s hPC hQEq _ hFix hSize hInv hIdom hSV
    have hvQ : v = Q := by omega
    subst v
    let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
    have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
    have hV := loopV_placed (hi := hi) (hw := hw) hTen
    have hP0 : Placed code 0 (readScratchInstrs registers.ptr 0 (by omega)) :=
      placed3_of_get (hV 0 _ (by simp [loopVBlock, readScratchInstrs]))
        (hV 1 _ (by simp [loopVBlock, readScratchInstrs]))
        (hV 2 _ (by simp [loopVBlock, readScratchInstrs]))
    obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
      loop_readScratch hTen hP0 hPC (by omega) hFix sp.workBounds (by omega) hSV (fin_ne_of_val (by decide))
    have hFix1 : DomRegsFixed Q s1 :=
      domRegsFixed_eq_of_eq hFix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hFalse : ltb (reg s1 registers.ptr) (reg s1 count) = false := by
      cases hCmp : ltb (reg s1 registers.ptr) (reg s1 count) with
      | false => rfl
      | true => have := (PaperB.WordOps.ltb_eq_true _ _).mp hCmp; rw [hr1p, hFix1.countVal] at this; omega
    have h3 : code[s1.pc]? = some (.branchLt registers.ptr count 4 208) := by
      rw [hpc1]; exact hV 3 _ (by simp [loopVBlock, readScratchInstrs])
    have hs1_2 := step_branchLt_at (input := input) h3 (by rw [hCodeSize]; split <;> omega)
    let t : State L := { s1 with pc := if ltb (reg s1 registers.ptr) (reg s1 count) = true then 4 else 208 }
    have htpc : t.pc = 208 := by simp only [t, hFalse, Bool.false_eq_true, ite_false]
    have htd : t.data = s.data := hd1
    refine ⟨t, 4, F, by omega, hs1.append (Steps.cons hs1_2 (.zero _)), htpc,
      domRegsFixed_eq_of_eq hFix1 (fun _ _ => rfl),
      by rw [htd]; exact hSize, by rw [htd]; exact hInv, hIdom⟩
  | succ rem ih =>
    intro v F s hPC hQEq hv1 hFix hSize hInv hIdom hSV
    have hvLt : v < Q := by omega
    have hWork := workBounds_nat sp
    have hInB := inBounds_nat sp
    let code := domLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap) hi hw hTen
    have hCodeSize : code.size = 209 := domLoopCode_size hi hw hTen
    have hV := loopV_placed (hi := hi) (hw := hw) hTen
    have hP0 : Placed code 0 (readScratchInstrs registers.ptr 0 (by omega)) :=
      placed3_of_get (hV 0 _ (by simp [loopVBlock, readScratchInstrs]))
        (hV 1 _ (by simp [loopVBlock, readScratchInstrs]))
        (hV 2 _ (by simp [loopVBlock, readScratchInstrs]))
    obtain ⟨s1, hs1, hpc1, hd1, hr1p, hr1o⟩ :=
      loop_readScratch hTen hP0 hPC (by omega) hFix hWork (by omega) hSV (fin_ne_of_val (by decide))
    have hFix1 : DomRegsFixed Q s1 :=
      domRegsFixed_eq_of_eq hFix (fun r hr => hr1o r (fun e => by subst e; cases hr) (fun e => by subst e; cases hr))
    have hTrue : ltb (reg s1 registers.ptr) (reg s1 count) = true :=
      (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hr1p, hFix1.countVal]; exact hvLt)
    have h3 : code[s1.pc]? = some (.branchLt registers.ptr count 4 208) := by
      rw [hpc1]; exact hV 3 _ (by simp [loopVBlock, readScratchInstrs])
    have hs1_2 := step_branchLt_at (input := input) h3 (by rw [hCodeSize]; split <;> omega)
    let s2 : State L := { s1 with pc := if ltb (reg s1 registers.ptr) (reg s1 count) = true then 4 else 208 }
    have hpc2 : s2.pc = 4 := by simp only [s2, hTrue, ite_true]
    have hFix2 : DomRegsFixed Q s2 := domRegsFixed_eq_of_eq hFix1 (fun _ _ => rfl)
    have hr2p : (reg s2 registers.ptr).val = v := hr1p
    have h4 : code[s2.pc]? = some (.imm registers.tmp ⟨2, by omega⟩) := by
      rw [hpc2]; exact hV 4 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s3, hs3, hpc3, hr3t, hr3o, hd3⟩ :=
      step_imm_at (input := input) h4 (by rw [hCodeSize, hpc2]; omega)
    have hFix3 : DomRegsFixed Q s3 :=
      domRegsFixed_eq_of_eq hFix2 (fun r hr => hr3o r (fun e => by subst e; cases hr))
    have hr3p : (reg s3 registers.ptr).val = v := by
      rw [hr3o registers.ptr (fin_ne_of_val (by decide)), hr2p]
    have h5 : code[s3.pc]? = some (.add registers.tmp registers.tmp registers.ptr) := by
      rw [hpc3, hpc2]; exact hV 5 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s4, hs4, hpc4, hr4t, hr4o, hd4⟩ :=
      step_add_at (input := input) h5 (by rw [hCodeSize, hpc3, hpc2]; omega)
    have hFix4 : DomRegsFixed Q s4 :=
      domRegsFixed_eq_of_eq hFix3 (fun r hr => hr4o r (fun e => by subst e; cases hr))
    have hStartVLe : inStart v ≤ mReach := by
      rw [← sp.startEnd]; exact denseIncoming_inStart_le sp v Q (by omega) (Nat.le_refl Q)
    have hStartV1Le : inStart (v + 1) ≤ mReach := by
      rw [← sp.startEnd]; exact denseIncoming_inStart_le sp (v + 1) Q (by omega) (Nat.le_refl Q)
    have hInFit : mReach < 2 ^ bits := by omega
    have hr4tVal : (reg s4 registers.tmp).val = 2 + v := by
      have ht3 : (reg s3 registers.tmp).val = 2 := by rw [hr3t]
      rw [hr4t, add_no_wrap _ _ (by rw [ht3, hr3p]; omega), ht3, hr3p]
    have hStartVWord : input.words[(reg s4 registers.tmp).val]? = some ⟨inStart v, by omega⟩ := by
      rw [hr4tVal]
      have hC := sp.startCell v (by omega)
      cases hInp : input.words[2 + v]? with
      | none => rw [hInp] at hC; cases hC
      | some w => rw [hInp, Option.map_some] at hC; congr 1; exact Fin.ext (Option.some.inj hC)
    have h6 : code[s4.pc]? = some (.loadInput registers.remain registers.tmp) := by
      rw [hpc4, hpc3, hpc2]; exact hV 6 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s5, hs5, hpc5, hr5r, hr5o, hd5⟩ :=
      step_loadInput_at (input := input) h6 (by rw [hCodeSize, hpc4, hpc3, hpc2]; omega) hStartVWord
    have hFix5 : DomRegsFixed Q s5 :=
      domRegsFixed_eq_of_eq hFix4 (fun r hr => hr5o r (fun e => by subst e; cases hr))
    have hr5t : (reg s5 registers.tmp).val = 2 + v := by
      rw [hr5o registers.tmp (fin_ne_of_val (by decide)), hr4tVal]
    have h7 : code[s5.pc]? = some (.add registers.tmp registers.tmp registers.one) := by
      rw [hpc5, hpc4, hpc3, hpc2]; exact hV 7 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s6, hs6, hpc6, hr6t, hr6o, hd6⟩ :=
      step_add_at (input := input) h7 (by rw [hCodeSize, hpc5, hpc4, hpc3, hpc2]; omega)
    have hFix6 : DomRegsFixed Q s6 :=
      domRegsFixed_eq_of_eq hFix5 (fun r hr => hr6o r (fun e => by subst e; cases hr))
    have hr6tVal : (reg s6 registers.tmp).val = 2 + (v + 1) := by
      rw [hr6t, add_no_wrap _ _ (by rw [hr5t, hFix5.oneVal]; omega), hr5t, hFix5.oneVal]; omega
    have hStartV1Word : input.words[(reg s6 registers.tmp).val]? = some ⟨inStart (v + 1), by omega⟩ := by
      rw [hr6tVal]
      have hC := sp.startCell (v + 1) (by omega)
      cases hInp : input.words[2 + (v + 1)]? with
      | none => rw [hInp] at hC; cases hC
      | some w => rw [hInp, Option.map_some] at hC; congr 1; exact Fin.ext (Option.some.inj hC)
    have h8 : code[s6.pc]? = some (.loadInput registers.value registers.tmp) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2]; exact hV 8 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s7, hs7, hpc7, hr7v, hr7o, hd7⟩ :=
      step_loadInput_at (input := input) h8 (by rw [hCodeSize, hpc6, hpc5, hpc4, hpc3, hpc2]; omega) hStartV1Word
    have hFix7 : DomRegsFixed Q s7 :=
      domRegsFixed_eq_of_eq hFix6 (fun r hr => hr7o r (fun e => by subst e; cases hr))
    have hr7r : (reg s7 registers.remain).val = inStart v := by
      rw [hr7o registers.remain (fin_ne_of_val (by decide)),
          hr6o registers.remain (fin_ne_of_val (by decide)), hr5r]
    have h9 : code[s7.pc]? = some (.add registers.tmp childrenBase registers.remain) := by
      rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; exact hV 9 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s8, hs8, hpc8, hr8t, hr8o, hd8⟩ :=
      step_add_at (input := input) h9 (by rw [hCodeSize, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; omega)
    have hFix8 : DomRegsFixed Q s8 :=
      domRegsFixed_eq_of_eq hFix7 (fun r hr => hr8o r (fun e => by subst e; cases hr))
    have hRowNonempty : inStart v < inStart (v + 1) := sp.nonemptyRow v hv1 hvLt
    have hr8tVal : (reg s8 registers.tmp).val = 3 + Q + inStart v := by
      rw [hr8t, add_no_wrap _ _ (by rw [hFix7.childrenVal, hr7r]; omega),
          hFix7.childrenVal, hr7r]
    let cur0 := inSrc (inStart v)
    have hcur0Lt : cur0 < v := sp.srcPred v (inStart v) hv1 hvLt (Nat.le_refl _) hRowNonempty
    have hcur0Fit : cur0 < 2 ^ bits := by omega
    have hSrc0Word : input.words[(reg s8 registers.tmp).val]? = some ⟨cur0, hcur0Fit⟩ := by
      rw [hr8tVal]
      have hC := sp.srcCell (inStart v) (by omega)
      cases hInp : input.words[3 + Q + inStart v]? with
      | none => rw [hInp] at hC; cases hC
      | some w => rw [hInp, Option.map_some] at hC; congr 1; exact Fin.ext (Option.some.inj hC)
    have h10 : code[s8.pc]? = some (.loadInput registers.childBase registers.tmp) := by
      rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; exact hV 10 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s9, hs9, hpc9, hr9cb, hr9o, hd9⟩ :=
      step_loadInput_at (input := input) h10 (by rw [hCodeSize, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; omega) hSrc0Word
    have hFix9 : DomRegsFixed Q s9 :=
      domRegsFixed_eq_of_eq hFix8 (fun r hr => hr9o r (fun e => by subst e; cases hr))
    have hr9r : (reg s9 registers.remain).val = inStart v := by
      rw [hr9o registers.remain (fin_ne_of_val (by decide)),
          hr8o registers.remain (fin_ne_of_val (by decide)), hr7r]
    have h11 : code[s9.pc]? = some (.add registers.remain registers.remain registers.one) := by
      rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; exact hV 11 _ (by simp [loopVBlock, readScratchInstrs])
    obtain ⟨s10, hs10, hpc10, hr10r, hr10o, hd10⟩ :=
      step_add_at (input := input) h11 (by rw [hCodeSize, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2]; omega)
    have hFix10 : DomRegsFixed Q s10 :=
      domRegsFixed_eq_of_eq hFix9 (fun r hr => hr10o r (fun e => by subst e; cases hr))
    have hr10rVal : (reg s10 registers.remain).val = inStart v + 1 := by
      rw [hr10r, add_no_wrap _ _ (by rw [hr9r, hFix9.oneVal]; omega), hr9r, hFix9.oneVal]
    have hr10v : (reg s10 registers.value).val = inStart (v + 1) := by
      rw [hr10o registers.value (fin_ne_of_val (by decide)),
          hr9o registers.value (fin_ne_of_val (by decide)),
          hr8o registers.value (fin_ne_of_val (by decide)), hr7v]
    have hr10cb : (reg s10 registers.childBase).val = cur0 := by
      rw [hr10o registers.childBase (fin_ne_of_val (by decide)), hr9cb]
    have hP12 : Placed code 12 (writeScratchInstrs 1 registers.remain (by omega)) :=
      placed3_of_get (hV 12 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 13 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 14 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
    have hP15 : Placed code 15 (writeScratchInstrs 2 registers.value (by omega)) :=
      placed3_of_get (hV 15 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 16 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 17 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
    have hP18 : Placed code 18 (writeScratchInstrs 3 registers.childBase (by omega)) :=
      placed3_of_get (hV 18 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 19 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
        (hV 20 _ (by simp [loopVBlock, readScratchInstrs, writeScratchInstrs]))
    obtain ⟨s11, hs11, hpc11, hd11size, h11slot1, h11keep, hr11o⟩ :=
      loop_writeScratch hTen hP12 (by omega) (by omega) hFix10 hWork (by omega) (fin_ne_of_val (by decide))
    have hFix11 : DomRegsFixed Q s11 :=
      domRegsFixed_eq_of_eq hFix10 (fun r hr => hr11o r (fun e => by subst e; cases hr))
    obtain ⟨s12, hs12, hpc12, hd12size, h12slot2, h12keep, hr12o⟩ :=
      loop_writeScratch hTen hP15 hpc11 (by omega) hFix11 hWork (by omega) (fin_ne_of_val (by decide))
    have hFix12 : DomRegsFixed Q s12 :=
      domRegsFixed_eq_of_eq hFix11 (fun r hr => hr12o r (fun e => by subst e; cases hr))
    obtain ⟨s13, hs13, hpc13, hd13size, h13slot3, h13keep, hr13o⟩ :=
      loop_writeScratch hTen hP18 hpc12 (by omega) hFix12 hWork (by omega) (fin_ne_of_val (by decide))
    have hFix13 : DomRegsFixed Q s13 :=
      domRegsFixed_eq_of_eq hFix12 (fun r hr => hr13o r (fun e => by subst e; cases hr))
    have h13keepPre : ∀ j, j < 5 * Q → s13.data[j]? = s.data[j]? := fun j hj => by
      rw [h13keep _ (by omega), h12keep _ (by omega), h11keep _ (by omega),
          hd10, hd9, hd8, hd7, hd6, hd5, hd4, hd3, show s2.data = s1.data from rfl, hd1]
    have h13size : s13.data.size = workCap := by
      rw [hd13size, hd12size, hd11size, hd10, hd9, hd8, hd7, hd6, hd5, hd4, hd3,
          show s2.data = s1.data from rfl, hd1]; exact hSize
    have h13Rec : Records (2 * Q) F s13.data :=
      records_preserve hInv.records (by rw [h13size, hSize]) (fun j hj => h13keepPre j (by rw [hInv.size_eq] at hj; omega))
    have hcur0F : cur0 < F.size := by rw [hInv.size_eq]; exact hcur0Lt
    have hInitSem : ∀ a, a < v → (IsAncestor F a cur0 ↔ ∀ k, inStart v ≤ k → k < inStart v + 1 → IsAncestor F a (inSrc k)) := by
      intro a _
      constructor
      · intro ha k hk1 hk2; have : k = inStart v := by omega
        subst k; exact ha
      · intro hAll; exact hAll (inStart v) (Nat.le_refl _) (Nat.lt_succ_self _)
    let remArc := inStart (v + 1) - (inStart v + 1)
    obtain ⟨s14, kArc, d, hkArc, hsArc, hpc14, hFix14, hd14size, h14keepPre, _, hdLt, hdExact, h14sv, h14sc⟩ :=
      loopArc_all_steps sp hTen hv1 hvLt rfl remArc hpc13 (by dsimp [remArc]; omega)
        (Nat.le_refl _) hRowNonempty hFix13 h13size hInv.size_eq hInv.valid h13Rec hcur0F hInitSem
        (by rw [h13keep _ (by omega), h12keep _ (by omega), h11keep _ (by omega),
                hd10, hd9, hd8, hd7, hd6, hd5, hd4, hd3, show s2.data = s1.data from rfl, hd1]; exact hSV)
        (by rw [h13keep _ (by omega), h12keep _ (by omega), h11slot1, hr10rVal])
        (by rw [h13keep _ (by omega), h12slot2, hr11o registers.value (fin_ne_of_val (by decide)), hr10v])
        (by rw [h13slot3, hr12o registers.childBase (fin_ne_of_val (by decide)),
                hr11o registers.childBase (fin_ne_of_val (by decide)), hr10cb])
    have h14Inv : DomPrefixInv input Q mReach inStart inSrc v F s14.data :=
      { boundPos := hInv.boundPos
        valid := hInv.valid
        size_eq := hInv.size_eq
        records := records_preserve h13Rec (by rw [hd14size, h13size]) (fun j hj => h14keepPre j (by rw [hInv.size_eq] at hj; omega))
        domParent := fun u hu => by rw [h14keepPre u (by omega), h13keepPre u (by omega)]; exact hInv.domParent u hu
        domDepth := fun u hu => by rw [h14keepPre (Q + u) (by omega), h13keepPre (Q + u) (by omega)]; exact hInv.domDepth u hu
        domSem := hInv.domSem }
    obtain ⟨s15, kApp, hkApp, hsApp, hpc15, hFix15, hd15size, h15Inv, hIdomV, h15sv⟩ :=
      appendBody_steps sp hTen hv1 hvLt hdLt hpc14 hFix14 hd14size h14Inv hdExact h14sv h14sc
    have hDomEq : ∀ {a b x y : Fin Q}, a = b → x = y →
        ((denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, sp.qPos⟩ a x ↔
         (denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, sp.qPos⟩ b y) := by
      rintro a b x y rfl rfl; rfl
    have hIdom' : IdomPrefix Q (v + 1) sp.qPos inStart inSrc (F.appendLeaf d) := by
      intro u hu1 huLt
      by_cases huv : u.val < v
      · obtain ⟨hp, hId⟩ := hIdom u hu1 huv
        have huF : u.val < F.size := by rw [hInv.size_eq]; exact huv
        have hParEq : (F.appendLeaf d).parentOf u.val = F.parentOf u.val :=
          parentOf_appendLeaf_old F d huF
        refine ⟨by rw [hParEq]; exact hp, ?_⟩
        exact (hDomEq (Fin.ext hParEq) rfl).mpr hId
      · have huvEq : u.val = v := by omega
        have hParNew : (F.appendLeaf d).parentOf u.val = d := by
          rw [huvEq]
          change ((F.appendLeaf d).recordAt v).parent = d
          rw [← hInv.size_eq, recordAt_appendLeaf_new F d]; rfl
        have huFinEq : u = ⟨v, hvLt⟩ := Fin.ext huvEq
        refine ⟨by rw [hParNew]; exact Nat.lt_trans hdLt hvLt, ?_⟩
        exact (hDomEq (Fin.ext hParNew) huFinEq).mpr hIdomV
    obtain ⟨t, kTail, F', hkTail, hsTail, htpc, htFix, htdSize, htInv, htIdom⟩ :=
      ih (v + 1) hpc15 (by omega) (by omega) hFix15 hd15size h15Inv hIdom' h15sv
    have hsIter : Steps code input (21 + kArc + kApp) s s15 := by
      have p1 : Steps code input 21 s s13 := by
        have a : Steps code input 12 s s10 :=
          hs1.append (Steps.cons hs1_2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (.zero _))))))))))
        have b : Steps code input 9 s10 s13 := hs11.append (hs12.append hs13)
        simpa only [Nat.add_assoc] using a.append b
      simpa only [Nat.add_assoc] using (p1.append hsArc).append hsApp
    refine ⟨t, (21 + kArc + kApp) + kTail, F', ?_, hsIter.append hsTail, htpc, htFix, htdSize, htInv, htIdom⟩
    have hArcSplit : remArc + (mReach - inStart (v + 1)) ≤ mReach - inStart v := by
      dsimp [remArc]; omega
    calc (21 + kArc + kApp) + kTail
        ≤ 21 + (318 * remArc * OracleContract.L Q ^ 2 + 7) + 51 +
            (318 * (mReach - inStart (v + 1)) * OracleContract.L Q ^ 2 + 79 * rem + 4) := by omega
      _ = 318 * (remArc + (mReach - inStart (v + 1))) * OracleContract.L Q ^ 2 + 79 * (rem + 1) + 4 := by
            rw [Nat.mul_add 318 remArc, Nat.add_mul]; omega
      _ ≤ 318 * (mReach - inStart v) * OracleContract.L Q ^ 2 + 79 * (rem + 1) + 4 := by
            have := Nat.mul_le_mul_right (OracleContract.L Q ^ 2) (Nat.mul_le_mul_left 318 hArcSplit)
            omega

theorem run_domBuild {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    (s0 : State L) :
    let hTen : 10 ≤ 2 ^ bits := by have := workBounds_nat sp; have := sp.qPos; exact Nat.le_trans (by omega) hw
    ∃ t trace work F,
      work ≤ 318 * (Q + mReach) * OracleContract.L Q ^ 2 ∧
      run (domBuildProgram hi hw hTen) input work (Phase.initial s0) = some ⟨t, work⟩ ∧
      SuccessfulTrace (domBuildProgram hi hw hTen) input (Phase.initial s0) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      DomPrefixInv input Q mReach inStart inSrc Q F t.data ∧
      IdomPrefix Q Q sp.qPos inStart inSrc F ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q := by
  intro hTen
  obtain ⟨sMid, hsInit, hpcMid, hFixMid, hInvMid, h5QMid, hSizeMid⟩ :=
    domInit_steps sp hTen (Phase.initial s0) rfl
  have hHaltInit : step (domInitCode hi hw (by omega)) input sMid = some (.halted sMid) :=
    step_halt_at (by rw [hpcMid]; rfl)
  have hRunInit : run (domInitPhase hi hw (by omega)).code input 18 (Phase.initial s0) = some ⟨sMid, 18⟩ :=
    hsInit.halts hHaltInit
  have hIdom1 : IdomPrefix Q 1 sp.qPos inStart inSrc JumpForest.init :=
    fun u hu1 huLt => by omega
  obtain ⟨sEnd, kLoop, F, hkLoop, hsLoop, hpcEnd, hFixEnd, hSizeEnd, hInvEnd, hIdomEnd⟩ :=
    loopV_steps sp hTen (Q - 1) 1 (show (Phase.initial sMid).pc = 0 from rfl)
      (by have := sp.qPos; omega) (Nat.le_refl 1)
      (domRegsFixed_eq_of_eq hFixMid (fun _ _ => rfl)) hSizeMid hInvMid hIdom1 h5QMid
  have hHaltLoop : step (domLoopCode hi hw hTen) input sEnd = some (.halted sEnd) :=
    step_halt_at (by rw [hpcEnd]; exact domLoopCode_halt hi hw hTen)
  have hRunLoop : run (domLoopCode hi hw hTen) input (kLoop + 1) (Phase.initial sMid) =
      some ⟨sEnd, kLoop + 1⟩ :=
    hsLoop.halts hHaltLoop
  have hNonempty : 0 < (domLoopCode hi hw hTen).size := by
    rw [domLoopCode_size]; decide
  obtain ⟨t, trace, htRegs, htData, hRunAll, hTraceAll, hPeak⟩ :=
    PaperB.RamProgram.FixedROM.run_linked_pair (domInitPhase hi hw (by omega)) (domLoopCode hi hw hTen)
      hNonempty hRunInit hRunLoop
  have hFixT : DomRegsFixed Q t :=
    domRegsFixed_eq_of_eq hFixEnd (fun r _ => reg_eq_of_regs_eq htRegs r)
  have hOneLeL : 1 ≤ OracleContract.L Q := OracleContract.one_le_L Q
  have hL2 : 1 ≤ OracleContract.L Q ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ OracleContract.L Q * OracleContract.L Q := Nat.mul_le_mul hOneLeL hOneLeL
      _ = OracleContract.L Q ^ 2 := (Nat.pow_two _).symm
  have hWorkLe : 18 + (kLoop + 1) ≤ 318 * (Q + mReach) * OracleContract.L Q ^ 2 := by
    have hInLe : mReach - inStart 1 ≤ mReach := Nat.sub_le _ _
    have h1 : 318 * (mReach - inStart 1) * OracleContract.L Q ^ 2 ≤ 318 * mReach * OracleContract.L Q ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 318 hInLe)
    have hQPos := sp.qPos
    have h2 : 79 * (Q - 1) + 23 ≤ 318 * Q * OracleContract.L Q ^ 2 := by
      have : 79 * (Q - 1) + 23 ≤ 318 * Q := by omega
      calc 79 * (Q - 1) + 23 ≤ 318 * Q := this
        _ = 318 * Q * 1 := (Nat.mul_one _).symm
        _ ≤ 318 * Q * OracleContract.L Q ^ 2 := Nat.mul_le_mul_left _ hL2
    calc 18 + (kLoop + 1)
        ≤ 18 + (318 * (mReach - inStart 1) * OracleContract.L Q ^ 2 + 79 * (Q - 1) + 4) + 1 := by omega
      _ = 318 * (mReach - inStart 1) * OracleContract.L Q ^ 2 + (79 * (Q - 1) + 23) := by omega
      _ ≤ 318 * mReach * OracleContract.L Q ^ 2 + 318 * Q * OracleContract.L Q ^ 2 := Nat.add_le_add h1 h2
      _ = 318 * (Q + mReach) * OracleContract.L Q ^ 2 := by rw [Nat.mul_add, Nat.add_mul]; omega
  refine ⟨t, trace, 18 + (kLoop + 1), F, hWorkLe, hRunAll, hTraceAll, ?_, ?_, hIdomEnd,
    hFixT.zeroVal, hFixT.oneVal, hFixT.countVal⟩
  · simpa only [footprint] using hPeak
  · rw [htData]; exact hInvEnd

theorem run_domBuild_parentSpec {input : Input L} {Q mReach : Nat} {inStart inSrc : Nat → Nat}
    (sp : DenseIncomingSpec input Q mReach inStart inSrc)
    (s0 : State L) :
    let hTen : 10 ≤ 2 ^ bits := by have := workBounds_nat sp; have := sp.qPos; exact Nat.le_trans (by omega) hw
    ∃ t trace work, ∃ (parent : Fin Q → Fin Q) (depth : Fin Q → Nat),
      work ≤ 318 * (Q + mReach) * OracleContract.L Q ^ 2 ∧
      run (domBuildProgram hi hw hTen) input work (Phase.initial s0) = some ⟨t, work⟩ ∧
      SuccessfulTrace (domBuildProgram hi hw hTen) input (Phase.initial s0) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      ParentSpec (denseDigraph Q inStart inSrc) ⟨0, sp.qPos⟩ parent ∧
      ValidDepthTree ⟨0, sp.qPos⟩ parent depth ∧
      (∀ v : Fin Q, (t.data[v.val]?).map Fin.val = some (parent v).val) ∧
      (∀ v : Fin Q, (t.data[Q + v.val]?).map Fin.val = some (depth v)) ∧
      (∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val) ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t count).val = Q := by
  intro hTen
  obtain ⟨t, trace, work, F, hWork, hRun, hTrace, hPeak, hInv, hIdom, hz, hone, hcnt⟩ :=
    run_domBuild sp s0
  let parent : Fin Q → Fin Q := fun v =>
    if h0 : v.val = 0 then ⟨0, sp.qPos⟩
    else ⟨F.parentOf v.val, (hIdom v (Nat.pos_of_ne_zero h0) v.isLt).1⟩
  let depth : Fin Q → Nat := fun v => F.depthOf v.val
  have hPar : ∀ v : Fin Q, (parent v).val = F.parentOf v.val := by
    intro v
    by_cases h0 : v.val = 0
    · simp only [parent, dite_eq_left h0, h0]
      obtain ⟨_, hFi⟩ := hInv.valid.exists_forestInvariant
      exact hFi.root_parent.symm
    · simp only [parent, dite_eq_right h0]
  have hIdomAll : ∀ v : Fin Q, 1 ≤ v.val →
      (denseDigraph Q inStart inSrc).IsImmediateDominator ⟨0, sp.qPos⟩ (parent v) v := by
    intro v hv1
    have h0 : v.val ≠ 0 := by omega
    obtain ⟨hp, hId⟩ := hIdom v hv1 v.isLt
    have hEq : parent v = ⟨F.parentOf v.val, hp⟩ := Fin.ext (hPar v)
    rw [hEq]; exact hId
  obtain ⟨hSpec, hTree, hPDat, hDDat⟩ :=
    domPrefixInv_parentSpec sp hInv parent depth hPar (fun _ => rfl) hIdomAll
  have hParLt : ∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val := by
    intro v hv1
    rw [hPar v]
    obtain ⟨_, hFi⟩ := hInv.valid.exists_forestInvariant
    have hvF : v.val < F.size := by rw [hInv.size_eq]; exact v.isLt
    exact (hFi.nodes v.val hvF).pos_parent_lt hv1
  exact ⟨t, trace, work, parent, depth, hWork, hRun, hTrace, hPeak, hSpec, hTree,
    hPDat, hDDat, hParLt, hz, hone, hcnt⟩

end DomProof

end PaperB.RamDomBuild
