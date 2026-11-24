module

public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true

/-! Paper B's finite DAGs, bounded failures, and deterministic Word-RAM model.
The input is the outgoing adjacency lists in compressed sparse row form.
Construction keeps a flat index. Each later query can read that index and
its failure and target registers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

/-- Directed path over an explicit step relation `edge`, avoiding `failed` at every
    visited vertex including both endpoints (`refl` has length zero). -/
inductive AvoidPath {V : Type} (edge : V → V → Prop) (failed : V → Prop) :
    V → V → Prop where
  | refl (u : V) (alive : ¬ failed u) :
      AvoidPath edge failed u u
  | step (u w v : V)
      (alive : ¬ failed u)
      (arc : edge u w)
      (rest : AvoidPath edge failed w v) :
      AvoidPath edge failed u v

/-- Sum of list lengths, counting parallel arc occurrences with multiplicity. -/
def listLengthSum {α : Type} : List (List α) → Nat
  | [] => 0
  | xs :: xss => xs.length + listLengthSum xss

/-- Explicit query failure specification of at most two original vertex IDs.
    Two equal IDs `two a a` denote a singleton failure. -/
inductive FailureSet (n : Nat) : Type where
  | none : FailureSet n
  | one (a : Fin n) : FailureSet n
  | two (a b : Fin n) : FailureSet n
  deriving DecidableEq

namespace FailureSet

def Mem {n : Nat} (F : FailureSet n) (x : Fin n) : Prop :=
  match F with
  | .none => False
  | .one a => x = a
  | .two a b => x = a ∨ x = b

end FailureSet

/-- Explicit finite directed multigraph on original `Fin vertexCount` identifiers.
    Adjacency lists are concrete data (`Array` of `List`), with parallel arcs
    preserved as repeated list entries. -/
structure Digraph where
  vertexCount : Nat
  adj : Array (List (Fin vertexCount))
  adj_size : adj.size = vertexCount

namespace Digraph

/-- Outgoing adjacency list of `u`, preserving parallel arcs. -/
def outArcs (g : Digraph) (u : Fin g.vertexCount) : List (Fin g.vertexCount) :=
  g.adj[u.val]'(by rw [g.adj_size]; exact u.isLt)

/-- Existence of at least one arc `u → v` in `g`. -/
def HasArc (g : Digraph) (u v : Fin g.vertexCount) : Prop :=
  v ∈ g.outArcs u

/-- Total directed arc count `m = |E(G)|`, counting parallel arcs. -/
def arcCount (g : Digraph) : Nat :=
  listLengthSum g.adj.toList

/-- Separate acyclicity condition witnessed in `Prop` by a topological rank. -/
def IsAcyclic (g : Digraph) : Prop :=
  ∃ rank : Fin g.vertexCount → Nat,
    ∀ u v : Fin g.vertexCount, g.HasArc u v → rank u < rank v

/-- Surviving directed path in `g` avoiding `failed` (includes both endpoints and length zero). -/
abbrev SurvivingPath (g : Digraph) (failed : Fin g.vertexCount → Prop) :
    Fin g.vertexCount → Fin g.vertexCount → Prop :=
  AvoidPath g.HasArc failed

/-- Surviving `r`-to-`t` reachability in `g - F`. -/
def ReachableAvoiding (g : Digraph) (F : FailureSet g.vertexCount)
    (r t : Fin g.vertexCount) : Prop :=
  g.SurvivingPath F.Mem r t

end Digraph

/-- Concrete quotient arc carrying both its quotient head and the original physical
    tail `origTail` of the underlying DAG arc. -/
structure QuotientArc (origVertexCount vertexCount : Nat) where
  head : Fin vertexCount
  origTail : Fin origVertexCount
  deriving DecidableEq

/-- Explicit labelled sibling quotient `H_d` on `Fin vertexCount` with root `root`
    and an original physical tail in `Fin origVertexCount` on every quotient arc. -/
structure LabelledQuotient where
  origVertexCount : Nat
  vertexCount : Nat
  root : Fin vertexCount
  adj : Array (List (QuotientArc origVertexCount vertexCount))
  adj_size : adj.size = vertexCount

namespace LabelledQuotient

/-- Concrete list of labelled quotient arcs leaving `u`. -/
def outArcs (H : LabelledQuotient) (u : Fin H.vertexCount) :
    List (QuotientArc H.origVertexCount H.vertexCount) :=
  H.adj[u.val]'(by rw [H.adj_size]; exact u.isLt)

/-- Total number of labelled quotient arcs `m_H`, counting parallel exits. -/
def arcCount (H : LabelledQuotient) : Nat :=
  listLengthSum H.adj.toList

/-- Existence of a quotient arc `u → w` (for unlabelled suffix reachability). -/
def HasQuotientArc (H : LabelledQuotient) (u w : Fin H.vertexCount) : Prop :=
  ∃ e : QuotientArc H.origVertexCount H.vertexCount,
    e ∈ H.outArcs u ∧ e.head = w

/-- Acyclicity of the quotient witnessed in `Prop` by a topological rank. -/
def IsAcyclic (H : LabelledQuotient) : Prop :=
  ∃ rank : Fin H.vertexCount → Nat,
    ∀ u w : Fin H.vertexCount, H.HasQuotientArc u w → rank u < rank w

/-- Surviving path in `H` avoiding `failed` at all visited vertices (including endpoints). -/
abbrev SurvivingPath (H : LabelledQuotient) (failed : Fin H.vertexCount → Prop) :
    Fin H.vertexCount → Fin H.vertexCount → Prop :=
  AvoidPath H.HasQuotientArc failed

/-- Flat dominator structure of a sibling quotient (Lemma 2.1 / Section 3):
    every vertex is reachable from `H.root`, and deleting any single nonroot
    vertex `u` loses only `u`. -/
def IsFlat (H : LabelledQuotient) : Prop :=
  (∀ v : Fin H.vertexCount, H.SurvivingPath (fun _ => False) H.root v) ∧
  (∀ u v : Fin H.vertexCount, u ≠ H.root → v ≠ u →
    H.SurvivingPath (fun z => z = u) H.root v)

/-- Pair `B = {fst, snd}` of distinct nonroot vertices in `H`. -/
structure CutPair (H : LabelledQuotient) where
  fst : Fin H.vertexCount
  snd : Fin H.vertexCount
  fst_ne_root : fst ≠ H.root
  snd_ne_root : snd ≠ H.root
  ne : fst ≠ snd

namespace CutPair

def Mem {H : LabelledQuotient} (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  v = B.fst ∨ v = B.snd

instance instDecidableMem {H : LabelledQuotient} (B : CutPair H)
    (v : Fin H.vertexCount) : Decidable (B.Mem v) :=
  if h₁ : v = B.fst then
    isTrue (Or.inl h₁)
  else if h₂ : v = B.snd then
    isTrue (Or.inr h₂)
  else
    isFalse (fun h =>
      match h with
      | Or.inl h₁' => h₁ h₁'
      | Or.inr h₂' => h₂ h₂')

end CutPair

/-- `Z(B)`: vertices of `H` lost upon deleting `B` (including `B` itself). -/
def Lost (H : LabelledQuotient) (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  ¬ H.SurvivingPath B.Mem H.root v

/-- `J(B) = Z(B) \ B`: proper losses of `B` in `H`. -/
def ProperLoss (H : LabelledQuotient) (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  H.Lost B v ∧ ¬ B.Mem v

/-- Fresh endpoint membership `p ∈ P \ B`. -/
def IsFreshEndpoint {H : LabelledQuotient} (B P : CutPair H)
    (p : Fin H.vertexCount) : Prop :=
  P.Mem p ∧ ¬ B.Mem p

/-- Usable exit-tail membership `x ∈ X^B_s(y)` (Section 2):
    there exists a concrete labelled quotient arc `e` out of `s` with original
    physical tail `e.origTail = x` whose head `e.head` reaches `y` in `H - B`.
    Parallel quotient exits with distinct original tails remain distinct. -/
def ExitTailMem (H : LabelledQuotient) (B : CutPair H)
    (s y : Fin H.vertexCount) (x : Fin H.origVertexCount) : Prop :=
  ∃ e : QuotientArc H.origVertexCount H.vertexCount,
    e ∈ H.outArcs s ∧
    e.origTail = x ∧
    H.SurvivingPath B.Mem e.head y

end LabelledQuotient

end PaperB

/-! The instruction semantics, packed input ABI, and cost observations used
by the checked two-vertex-failure reachability oracle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Machine

abbrev Word (bits : Nat) := Fin (2 ^ bits)

end PaperB.Machine

namespace PaperB.WordOps

open PaperB.Machine

def zero (bits : Nat) : Word bits :=
  ⟨0, Nat.two_pow_pos bits⟩

/-- One word addition, modulo `2^bits`. -/
def add {bits : Nat} (x y : Word bits) : Word bits :=
  ⟨(x.val + y.val) % (2 ^ bits), Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- One word subtraction. Adding the modulus avoids truncated subtraction. -/
def sub {bits : Nat} (x y : Word bits) : Word bits :=
  ⟨(2 ^ bits + x.val - y.val) % (2 ^ bits),
    Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- One word bitwise AND. -/
def band {bits : Nat} (x y : Word bits) : Word bits :=
  ⟨x.val &&& y.val, by
    have hx : x.val < 2 ^ bits := x.isLt
    have hy : y.val < 2 ^ bits := y.isLt
    first
    | apply Nat.and_lt_two_pow <;> assumption
    | exact Nat.lt_of_le_of_lt (by apply Nat.and_le_left) hx
    | exact Nat.lt_of_le_of_lt (by apply Nat.and_le_right) hy⟩

/-- One unsigned word comparison. -/
def ltb {bits : Nat} (x y : Word bits) : Bool :=
  decide (x.val < y.val)

end PaperB.WordOps

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add sub band ltb)

structure Layout (bits : Nat) where
  registerCount : Nat
  inputCap : Nat
  workCap : Nat
  inputFits : inputCap ≤ 2 ^ bits
  workFits : workCap ≤ 2 ^ bits

-- The full preallocated input array is readable. It is not part of mutable state.
structure Input {bits : Nat} (L : Layout bits) where
  words : Array (Word bits)
  size_eq : words.size = L.inputCap

structure State {bits : Nat} (L : Layout bits) where
  regs : Array (Word bits)
  data : Array (Word bits)
  pc : Nat
  regs_size : regs.size = L.registerCount
  data_size : data.size = L.workCap

inductive Instr (bits registerCount : Nat) where
  | imm (dst : Fin registerCount) (value : Word bits)
  | mov (dst src : Fin registerCount)
  | add (dst lhs rhs : Fin registerCount)
  | sub (dst lhs rhs : Fin registerCount)
  | band (dst lhs rhs : Fin registerCount)
  | loadInput (dst addr : Fin registerCount)
  | loadData (dst addr : Fin registerCount)
  | storeData (addr src : Fin registerCount)
  | branchLt (lhs rhs : Fin registerCount) (ltPC gePC : Nat)
  | goto (target : Nat)
  | halt
  | shr1 (dst src : Fin registerCount)

abbrev Program {bits : Nat} (L : Layout bits) :=
  Array (Instr bits L.registerCount)

inductive Transition {bits : Nat} (L : Layout bits) where
  | next (state : State L)
  | halted (state : State L)

variable {bits : Nat} {L : Layout bits}

def readReg (s : State L) (r : Fin L.registerCount) : Word bits :=
  s.regs[r.val]'(by simpa only [s.regs_size] using r.isLt)

def writeReg (s : State L) (r : Fin L.registerCount) (w : Word bits) :
    State L :=
  let h : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  { s with
    regs := s.regs.set r.val w h
    regs_size := by simp only [Array.size_set, s.regs_size] }

def advance (code : Program L) (s : State L) (pc : Nat) :
    Option (Transition L) :=
  if pc < code.size then some (.next { s with pc := pc }) else none

/-- Unsigned right shift by one: exact natural division, without wraparound. -/
def shr1Word (w : Word bits) : Word bits :=
  ⟨w.val / 2, Nat.lt_of_le_of_lt (Nat.div_le_self w.val 2) w.isLt⟩

/-- Reject an invalid fetch, memory access, or chosen successor PC. -/
def step (code : Program L) (input : Input L) (s : State L) :
    Option (Transition L) := do
  let instr ← code[s.pc]?
  let put (dst : Fin L.registerCount) (w : Word bits) :=
    advance code (writeReg s dst w) (s.pc + 1)
  match instr with
  | .imm dst w => put dst w
  | .mov dst src => put dst (readReg s src)
  | .add dst x y => put dst (add (readReg s x) (readReg s y))
  | .sub dst x y => put dst (sub (readReg s x) (readReg s y))
  | .band dst x y => put dst (band (readReg s x) (readReg s y))
  | .loadInput dst addr => do
    let w ← input.words[(readReg s addr).val]?
    put dst w
  | .loadData dst addr => do
    let w ← s.data[(readReg s addr).val]?
    put dst w
  | .storeData addr src =>
    let i := (readReg s addr).val
    if h : i < s.data.size then
      advance code
        { s with
          data := s.data.set i (readReg s src) h
          data_size := by simp only [Array.size_set, s.data_size] }
        (s.pc + 1)
    else none
  | .branchLt x y ltPC gePC =>
    advance code s (if ltb (readReg s x) (readReg s y) then ltPC else gePC)
  | .goto target => advance code s target
  | .halt => some (.halted s)
  | .shr1 dst src => put dst (shr1Word (readReg s src))

structure Result {bits : Nat} (L : Layout bits) where
  finalState : State L
  executed : Nat

/-- Return a result only on halt. Halt counts as one executed instruction. -/
def run (code : Program L) (input : Input L) :
    Nat → State L → Option (Result L)
  | 0, _ => none
  | n + 1, s =>
    match step code input s with
    | none => none
    | some (.halted t) => some ⟨t, 1⟩
    | some (.next t) =>
      match run code input n t with
      | none => none
      | some r => some { r with executed := r.executed + 1 }

/-- Model word slots only: input, data, and registers; excludes code and PC. -/
def storageWords (input : Input L) (s : State L) : Nat :=
  input.words.size + s.data.size + s.regs.size

def footprint (L : Layout bits) : Nat :=
  L.inputCap + L.workCap + L.registerCount

end PaperB.RamProgram

namespace PaperB.OracleContract

def L (n : Nat) : Nat :=
  Nat.log2 (n + 1) + 1

theorem one_le_L (n : Nat) : 1 ≤ L n :=
  Nat.succ_le_succ (Nat.zero_le (Nat.log2 (n + 1)))

/-- The base width plus fixed, layout-dependent slack. Here `m`
counts arc occurrences, including parallel arcs. -/
def wordBits (wordSlack n m : Nat) : Nat :=
  L (n + m) + wordSlack

/-- `L s` is the ceiling of `log₂ (s + 2)`, so for fixed `wordSlack`
these bounds give Θ(log(n + m + 2)) bits uniformly in `n` and `m`,
including the single-vertex case. -/
theorem wordBits_bounds (wordSlack n m : Nat) :
    L (n + m) ≤ wordBits wordSlack n m ∧
    wordBits wordSlack n m ≤ (wordSlack + 1) * L (n + m) := by
  constructor
  · unfold wordBits
    exact Nat.le_add_right _ _
  · calc
      wordBits wordSlack n m = wordSlack + L (n + m) :=
        Nat.add_comm (L (n + m)) wordSlack
      _ = wordSlack * 1 + L (n + m) := by rw [Nat.mul_one]
      _ ≤ wordSlack * L (n + m) + L (n + m) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left wordSlack (one_le_L (n + m))) _
      _ = (wordSlack + 1) * L (n + m) := by rw [Nat.add_mul, Nat.one_mul]

/-- The single-vertex, zero-arc input uses two base bits. -/
theorem wordBits_single_vertex (wordSlack : Nat) :
    wordBits wordSlack 1 0 = 2 + wordSlack := by
  have h : L (1 + 0) = 2 := by decide
  rw [wordBits, h]

/-- The immutable index has only layout metadata and a flat word payload. -/
structure WordIndex where
  vertices : Nat
  bits : Nat
  words : Array (Fin (2 ^ bits))

structure BuildObservation (bits : Nat) where
  words : Array (Fin (2 ^ bits))
  operations : Nat
  peakLiveWords : Nat
  retainedWords : Nat

def BuildObservation.index {bits : Nat}
    (b : BuildObservation bits) (n : Nat) : WordIndex :=
  ⟨n, bits, b.words⟩

structure QueryObservation where
  answer : Bool
  operations : Nat

/--
Candidate interface, not an executable word-machine semantics. The fixed
`wordSlack` determines the build width and thus the index width seen by
the query program. The build observer takes the graph itself, which
stores its explicit adjacency lists.
EX0.3 must justify the layout and the interpretation of each observation as
a machine run. In particular, the build observation must charge for the
index header and the full retained footprint, not just the logical length
of the payload. `none` supplies no completed-run observation.
-/
structure CandidateInterface (wordSlack : Nat) where
  BuildProgram : Type
  QueryProgram : Type
  observeBuild : BuildProgram → (g : Digraph) → Fin g.vertexCount →
    Option (BuildObservation (wordBits wordSlack g.vertexCount g.arcCount))
  observeQuery : QueryProgram → (I : WordIndex) →
    FailureSet I.vertices → Fin I.vertices → Option QueryObservation

/--
EX0.2 candidate theorem type relative to `M`. The same deterministic build
and query programs and the same constant work for every acyclic graph and
root. The quantification over the two-slot failure sets and original targets
is after the single build observation.
-/
def Candidate {wordSlack : Nat} (M : CandidateInterface wordSlack)
    (buildExp queryExp : Nat) : Prop :=
  ∃ (build : M.BuildProgram) (query : M.QueryProgram) (C : Nat),
    0 < C ∧
    ∀ (g : Digraph) (r : Fin g.vertexCount),
      g.IsAcyclic →
      ∃ b : BuildObservation (wordBits wordSlack g.vertexCount g.arcCount),
        M.observeBuild build g r = some b ∧
        b.operations ≤ C * ((g.vertexCount + g.arcCount) * L g.vertexCount ^ buildExp) ∧
        b.peakLiveWords ≤ C * (g.vertexCount + g.arcCount) ∧
        b.words.size ≤ b.retainedWords ∧
        b.retainedWords ≤ C * g.vertexCount ∧
        ∀ (F : FailureSet g.vertexCount) (t : Fin g.vertexCount),
          ∃ q : QueryObservation,
            M.observeQuery query (b.index g.vertexCount) F t = some q ∧
            q.operations ≤ C * L g.vertexCount ^ queryExp ∧
            (q.answer = true ↔ g.ReachableAvoiding F r t)

def CandidateV13 {wordSlack : Nat} (M : CandidateInterface wordSlack) : Prop :=
  Candidate M 2 1

def CandidateV12 {wordSlack : Nat} (M : CandidateInterface wordSlack) : Prop :=
  Candidate M 3 3

end PaperB.OracleContract

namespace BinaryCapacity

def logWidth (n : Nat) : Nat := Nat.log2 (n + 1) + 1

theorem base_fits (n : Nat) : n + 1 < 2 ^ logWidth n := by
  unfold logWidth
  exact Nat.lt_log2_self

theorem cap_fits (n k slack : Nat) (hk : k ≤ 2 ^ slack) :
    k * (n + 1) < 2 ^ (logWidth n + slack) := by
  have hp : 0 < (2 : Nat) ^ slack := Nat.pow_pos (by decide)
  calc
    k * (n + 1) ≤ 2 ^ slack * (n + 1) := Nat.mul_le_mul_right _ hk
    _ < 2 ^ slack * 2 ^ logWidth n :=
      Nat.mul_lt_mul_of_pos_left (base_fits n) hp
    _ = 2 ^ (logWidth n + slack) := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ slack) (2 ^ logWidth n)]

end BinaryCapacity

namespace PaperB.OracleContract

/-- A physically measured linear payload fits the fixed-slack word width. -/
theorem linear_payload_fits (wordSlack n m factor cells : Nat)
    (hFactor : factor ≤ 2 ^ wordSlack) (hCells : cells ≤ factor * (n + m + 1)) :
    cells < 2 ^ wordBits wordSlack n m :=
  Nat.lt_of_le_of_lt hCells (BinaryCapacity.cap_fits (n + m) factor wordSlack hFactor)

end PaperB.OracleContract

namespace PaperB.OracleSealedIndexLayout

/-- Uniform fixed slack `wordSlack = 10` (`2^10 = 1024`) covering peak build
workspace, all retained words (`≤ 128 * n`), and all dense timestamps (`< 2 * n`). -/
def oracleWordSlack : Nat := 10

abbrev hdrTotalWords : Nat := 15

/-- Uniform fixed query scratch workspace (`workCap = 32`), zero-initialized
before each query without copying the sealed index. -/
abbrev queryWorkCap : Nat := 32

theorem oracle_slack_linear_fits (n m factor cells : Nat)
    (hFactor : factor ≤ 1024) (hCells : cells ≤ factor * (n + m + 1)) :
    cells < 2 ^ OracleContract.wordBits oracleWordSlack n m :=
  OracleContract.linear_payload_fits oracleWordSlack n m factor cells
    (Nat.le_trans hFactor (by decide : 1024 ≤ 2 ^ oracleWordSlack)) hCells

end PaperB.OracleSealedIndexLayout

namespace PaperB.RamDagReach

open PaperB
open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.Digraph

abbrev layout16 (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, inputCap, workCap, hi, hw⟩

/-- Exact immutable input length: `[n, m, r]`, `n + 1` CSR out-offsets, and `m` out-targets. -/
def rawDagInputCap (n m : Nat) : Nat := 4 + n + m

theorem rawDagInputCap_le (n m : Nat) : rawDagInputCap n m ≤ 4 * (n + m + 1) := by
  calc
    rawDagInputCap n m = 4 + (n + m) := Nat.add_assoc 4 n m
    _ ≤ 4 + 4 * (n + m) :=
      Nat.add_le_add_left (Nat.le_mul_of_pos_left (n + m) (by decide : 0 < 4)) 4
    _ = 4 * (n + m) + 4 * 1 := Nat.add_comm _ _
    _ = 4 * (n + m + 1) := (Nat.mul_add 4 (n + m) 1).symm

/-- Cumulative CSR outgoing-arc prefix offset `outPrefix g u`. -/
def outPrefix (g : Digraph) : Nat → Nat
  | 0 => 0
  | u + 1 => outPrefix g u + if h : u < g.vertexCount then (g.outArcs ⟨u, h⟩).length else 0

theorem listLengthSum_eq_sum_lengths {α : Type} (xss : List (List α)) :
    listLengthSum xss = (xss.map List.length).sum := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp only [listLengthSum, List.map_cons, List.sum_cons, ih]

/-- Flattened list of all outgoing target vertex IDs in CSR order. -/
def outTargetsList (g : Digraph) : List (Fin g.vertexCount) :=
  g.adj.toList.flatten

theorem outTargetsList_length (g : Digraph) :
    (outTargetsList g).length = g.arcCount := by
  unfold outTargetsList Digraph.arcCount
  rw [List.length_flatten, listLengthSum_eq_sum_lengths]

/-- Total construction of immutable raw DAG input words directly from `g.adj` and `r`. -/
def rawInputWords (bits : Nat) (g : Digraph) (r : Fin g.vertexCount) : Array (Word bits) :=
  let n := g.vertexCount
  let m := g.arcCount
  let header : Array (Word bits) :=
    #[Fin.ofNat (2 ^ bits) n, Fin.ofNat (2 ^ bits) m, Fin.ofNat (2 ^ bits) r.val]
  let offs : Array (Word bits) :=
    Array.ofFn fun u : Fin (n + 1) => Fin.ofNat (2 ^ bits) (outPrefix g u.val)
  let targets : Array (Word bits) :=
    (outTargetsList g).toArray.map (fun v => Fin.ofNat (2 ^ bits) v.val)
  header ++ offs ++ targets

theorem rawInputWords_size (bits : Nat) (g : Digraph) (r : Fin g.vertexCount) :
    (rawInputWords bits g r).size = rawDagInputCap g.vertexCount g.arcCount := by
  unfold rawInputWords rawDagInputCap
  simp [Array.size_append, outTargetsList_length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [← Nat.add_assoc]

/-- Construct an `Input` directly from `(g, r)` whenever `rawDagInputCap n m ≤ 2 ^ bits`. -/
def rawInputOfDigraph {bits workCap : Nat} (g : Digraph) (r : Fin g.vertexCount)
    (hi : rawDagInputCap g.vertexCount g.arcCount ≤ 2 ^ bits)
    (hw : workCap ≤ 2 ^ bits) :
    Input (layout16 bits (rawDagInputCap g.vertexCount g.arcCount) workCap hi hw) where
  words := rawInputWords bits g r
  size_eq := rawInputWords_size bits g r

end PaperB.RamDagReach

namespace PaperB.SealedBuild

open PaperB.Machine (Word)
open PaperB.RamProgram (Layout Input State Program Result run)

structure SealLayout {bits : Nat} (L : Layout bits) where
  registerFits : L.registerCount ≤ 2 ^ bits
  k : Nat
  k_le_workCap : k ≤ L.workCap

variable {bits : Nat} {L : Layout bits}

def initialState (L : Layout bits) : State L :=
  let zero : Word bits := ⟨0, Nat.pow_pos (by decide : 0 < (2 : Nat))⟩
  { regs := Array.replicate L.registerCount zero
    data := Array.replicate L.workCap zero
    pc := 0
    regs_size := by simp
    data_size := by simp }

/-- Copy exactly the chosen prefix. Its adequacy is a separate obligation. -/
def copyPrefix (cfg : SealLayout L) (s : State L) : Array (Word bits) :=
  Array.ofFn fun i : Fin cfg.k =>
    s.data[i.val]'(by
      rw [s.data_size]
      exact Nat.lt_of_lt_of_le i.isLt cfg.k_le_workCap)

end PaperB.SealedBuild

namespace PaperB.SealedQuery

open PaperB.Machine (Word)

structure Params (bits : Nat) where
  tag : Word bits
  failure0 : Word bits
  failure1 : Word bits
  target : Word bits

def zeroWord (bits : Nat) : Word bits :=
  ⟨0, Nat.pow_pos (by decide : 0 < (2 : Nat))⟩

/-- The register order is tag, first failure, second failure, target. -/
def Params.reg {bits : Nat} (q : Params bits) (i : Fin 4) : Word bits :=
  match i.val with
  | 0 => q.tag
  | 1 => q.failure0
  | 2 => q.failure1
  | _ => q.target

/-- Tags 0, 1, and 2 give the number of occupied failure slots.
Unused slots are zero; zero is also a valid ID in an occupied slot. -/
def Params.encode {bits n : Nat} (hn : n ≤ 2 ^ bits) (htag : 2 < 2 ^ bits)
    (failures : FailureSet n) (target : Fin n) : Params bits :=
  let vertexWord (v : Fin n) : Word bits :=
    ⟨v.val, Nat.lt_of_lt_of_le v.isLt hn⟩
  let z := zeroWord bits
  let t := vertexWord target
  match failures with
  | .none => ⟨z, z, z, t⟩
  | .one a => ⟨⟨1, Nat.lt_trans (by decide : 1 < 2) htag⟩, vertexWord a, z, t⟩
  | .two a b => ⟨⟨2, htag⟩, vertexWord a, vertexWord b, t⟩

structure Observation where
  answer : Bool
  executed : Nat
  initializedRegisters : Nat
  initializedWorkspace : Nat
  operations : Nat
  words : Nat

end PaperB.SealedQuery

namespace PaperB.SealedQueryR

open PaperB.Machine (Word)
open PaperB.SealedQuery (Params Observation)

def zeroWord (bits : Nat) : Word bits :=
  ⟨0, Nat.pow_pos (by decide : 0 < (2 : Nat))⟩

def layoutFor {bits : Nat} (R : Nat) (_hR : 4 ≤ R)
    (index : Array (Word bits)) (workCap : Nat)
    (hI : index.size ≤ 2 ^ bits) (hWork : workCap ≤ 2 ^ bits) :
    RamProgram.Layout bits where
  registerCount := R
  inputCap := index.size
  workCap := workCap
  inputFits := hI
  workFits := hWork

/-- The register count is fixed by the type. The workspace cap is chosen
with the bytecode; the only read-only RAM payload is `index`. -/
structure Phase (bits R : Nat) where
  hR : 4 ≤ R
  index : Array (Word bits)
  workCap : Nat
  hI : index.size ≤ 2 ^ bits
  hWork : workCap ≤ 2 ^ bits
  code : RamProgram.Program (layoutFor R hR index workCap hI hWork)

namespace Phase

variable {bits R : Nat}

def layout (p : Phase bits R) : RamProgram.Layout bits :=
  layoutFor R p.hR p.index p.workCap p.hI p.hWork

def input (p : Phase bits R) : RamProgram.Input p.layout :=
  ⟨p.index, rfl⟩

def initReg (q : Params bits) (i : Fin R) : Word bits :=
  if h : i.val < 4 then q.reg ⟨i.val, h⟩ else zeroWord bits

/-- Every run starts at PC zero with the ABI prefix, a zero register suffix,
and fresh zero workspace. The index is not copied into workspace. -/
def initialState (p : Phase bits R) (q : Params bits) :
    RamProgram.State p.layout where
  regs := Array.ofFn (initReg (R := R) q)
  data := Array.replicate p.workCap (zeroWord bits)
  pc := 0
  regs_size := by simp [layout, layoutFor]
  data_size := by simp [layout, layoutFor]

def report (p : Phase bits R) (s : RamProgram.State p.layout)
    (r : RamProgram.Result p.layout) : Observation :=
  let w := r.finalState.regs[0]'(by
    rw [r.finalState.regs_size]
    exact Nat.lt_of_lt_of_le (by decide : 0 < (4 : Nat)) p.hR)
  let nr := s.regs.size
  let nw := s.data.size
  { answer := decide (w.val ≠ 0)
    executed := r.executed
    initializedRegisters := nr
    initializedWorkspace := nw
    operations := r.executed + nr + nw
    words := RamProgram.storageWords p.input s }

/-- Report successful halts only. Charge the executed instructions (including
halt) and one operation per initialized word. Reading the answer is free. -/
def observe (p : Phase bits R) (q : Params bits) (fuel : Nat) :
    Option Observation :=
  let s := p.initialState q
  (RamProgram.run p.code p.input fuel s).map (p.report s)

end Phase

end PaperB.SealedQueryR

namespace PaperB.RamSealedOracleAssembly

open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamDagReach

/-- Uniform linear mutable workspace capacity `800 * (n + m + 1)`.
Exceeds all three stage thresholds (`512`, `640`, `800`) and fits strictly below
`2 ^ wordBits oracleWordSlack n m` (`1024 = 2 ^ 10`). -/
def masterWorkCap (n m : Nat) : Nat :=
  800 * (n + m + 1)

theorem masterWorkCap_ge_512 (n m : Nat) :
    512 * (n + m + 1) ≤ masterWorkCap n m := by
  unfold masterWorkCap; omega

theorem masterWorkCap_ge_640 (n m : Nat) :
    640 * (n + m + 1) ≤ masterWorkCap n m := by
  unfold masterWorkCap; omega

theorem masterWorkCap_ge_800 (n m : Nat) :
    800 * (n + m + 1) ≤ masterWorkCap n m := by
  unfold masterWorkCap; omega

theorem rawDagInputCap_fits (n m : Nat) :
    rawDagInputCap n m ≤ 2 ^ wordBits oracleWordSlack n m :=
  Nat.le_of_lt
    (oracle_slack_linear_fits n m 4 (rawDagInputCap n m) (by decide) (rawDagInputCap_le n m))

theorem masterWorkCap_lt (n m : Nat) :
    masterWorkCap n m < 2 ^ wordBits oracleWordSlack n m :=
  oracle_slack_linear_fits n m 800 (masterWorkCap n m) (by decide) (Nat.le_refl _)

theorem masterWorkCap_fits (n m : Nat) :
    masterWorkCap n m ≤ 2 ^ wordBits oracleWordSlack n m :=
  Nat.le_of_lt (masterWorkCap_lt n m)

theorem master_h32 (n m : Nat) :
    32 ≤ 2 ^ wordBits oracleWordSlack n m :=
  have workGe : 32 ≤ masterWorkCap n m :=
    Nat.le_trans (by decide : 32 ≤ 800) (Nat.le_mul_of_pos_right 800 (Nat.succ_pos _))
  Nat.le_of_lt (Nat.lt_of_le_of_lt workGe (masterWorkCap_lt n m))

theorem master_h100 (n m : Nat) :
    100 ≤ 2 ^ wordBits oracleWordSlack n m :=
  Nat.le_of_lt (Nat.lt_of_le_of_lt (by unfold masterWorkCap; omega) (masterWorkCap_lt n m))

def master_buildFuel (n m : Nat) : Nat :=
  140000 * ((n + m + 1) * L n ^ 2)

end PaperB.RamSealedOracleAssembly

namespace PaperB.RamSealedOracleObservation

open PaperB.Machine (Word)
open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamProgram

def observeSealedState {bits : Nat} {L : Layout bits} (code : Program L)
    (input : Input L) (fuel : Nat) (hRegs : L.registerCount ≤ 2 ^ bits) :
    Option (BuildObservation bits) :=
  match run code input fuel (SealedBuild.initialState L) with
  | none => none
  | some res =>
    let k := ((res.finalState.data[hdrTotalWords]?).map Fin.val).getD 0
    if hk : k ≤ L.workCap then
      let cfg : SealedBuild.SealLayout L := ⟨hRegs, k, hk⟩
      let retained := SealedBuild.copyPrefix cfg res.finalState
      some ⟨retained, res.executed + L.registerCount + L.workCap + retained.size,
        input.words.size + L.registerCount + L.workCap + retained.size, retained.size⟩
    else none

/-- Observe one successful execution and retain exactly the prefix named in
the halted state's header. -/
abbrev executeSealedState {bits : Nat} {L : Layout bits} (code : Program L)
    (input : Input L) (fuel : Nat) (hRegs : L.registerCount ≤ 2 ^ bits) :
    Option (BuildObservation bits) :=
  observeSealedState code input fuel hRegs

end PaperB.RamSealedOracleObservation

namespace PaperB.BytecodeContract

open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamProgram
open PaperB.RamDagReach
open PaperB.RamSealedOracleAssembly

def BuildCode : Type :=
  ∀ n m : Nat,
    Program (layout16 (wordBits oracleWordSlack n m) (rawDagInputCap n m)
      (masterWorkCap n m) (rawDagInputCap_fits n m) (masterWorkCap_fits n m))

def QueryCode : Type :=
  ∀ (bits cap : Nat), cap ≤ 2 ^ bits → queryWorkCap ≤ 2 ^ bits →
    2 < 2 ^ bits → Array (Instr bits 16)

def executeBuilder (build : BuildCode) (g : Digraph) (r : Fin g.vertexCount) :
    Option (BuildObservation (wordBits oracleWordSlack g.vertexCount g.arcCount)) :=
  let n := g.vertexCount
  let m := g.arcCount
  let bits := wordBits oracleWordSlack n m
  let L16 := layout16 bits (rawDagInputCap n m) (masterWorkCap n m)
    (rawDagInputCap_fits n m) (masterWorkCap_fits n m)
  let input := rawInputOfDigraph g r (rawDagInputCap_fits n m) (masterWorkCap_fits n m)
  RamSealedOracleObservation.executeSealedState (build n m) input (master_buildFuel n m)
    (show L16.registerCount ≤ 2 ^ bits from Nat.le_trans (by decide : 16 ≤ 32) (master_h32 n m))

def executeQuery (query : QueryCode) (I : WordIndex) (F : FailureSet I.vertices)
    (t : Fin I.vertices) : Option QueryObservation :=
  if h : I.words.size ≤ 2 ^ I.bits ∧ queryWorkCap ≤ 2 ^ I.bits ∧
      2 < 2 ^ I.bits ∧ I.vertices ≤ 2 ^ I.bits then
    let phase : SealedQueryR.Phase I.bits 16 :=
      { index := I.words, workCap := queryWorkCap, hR := by decide
        hI := h.1, hWork := h.2.1
        code := query I.bits I.words.size h.1 h.2.1 h.2.2.1 }
    (phase.observe (SealedQuery.Params.encode h.2.2.2 h.2.2.1 F t)
      (1200 * OracleContract.L I.vertices)).map fun o => ⟨o.answer, o.operations⟩
  else none

def fixedInterface (build : BuildCode) (query : QueryCode) : CandidateInterface oracleWordSlack where
  BuildProgram := Unit
  QueryProgram := Unit
  observeBuild := fun () g r => executeBuilder build g r
  observeQuery := fun () I F t => executeQuery query I F t

end PaperB.BytecodeContract

namespace PaperB.BytecodeContract

open PaperB.OracleContract

/-- Theorem 1.1. For a DAG with `n` vertices and `m` arc occurrences, fix
one builder code generator and one query code generator. Let `L` be
the ceiling of `log₂(n + 2)`. The builder takes `O((n + m)L²)` word operations,
uses `O(n + m)` peak words, and retains `O(n)` words. Using only this retained
index, a query takes `O(L)` operations and decides whether the original
target is reachable from the source after deleting the listed zero, one, or
two vertices. The builder runs before the failure set and target are named. -/
theorem twoFailureOracleBytecode :
    ∃ (build : BuildCode) (query : QueryCode), CandidateV13 (fixedInterface build query) := by
  sorry

end PaperB.BytecodeContract
