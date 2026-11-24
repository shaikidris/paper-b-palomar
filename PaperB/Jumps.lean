module

public import PaperB.ExitPaths

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Growing-tree skew-binary `parent` / `depth` / `jump` kernel (Paper B v1.3, Lemma 3.2, EX2.3):
    part 1 — store, persistence, skew-block forest invariant, depth-target traversal, and
    unique ancestor-at-depth correctness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

private def headNat : List Nat → Nat
  | [] => 0
  | x :: _ => x

private def tailNat : List Nat → List Nat
  | [] => []
  | _ :: xs => xs

private theorem list_length_snoc {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact congrArg (· + 1) ih

private theorem nat_strong_ind {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n := by
  have bounded : ∀ k m, m ≤ k → P m := by
    intro k
    induction k with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by omega
        rw [hm0]
        exact step 0 (fun _ hLt => by omega)
    | succ k ih =>
        intro m hm
        exact step m (fun j hj => ih j (by omega))
  exact bounded n n (Nat.le_refl n)

/-- Concrete per-node record in the growing skew-binary jump forest:
    one `parent`, one `depth`, and one `jump` index per node. -/
structure JumpRecord where
  parent : Nat
  depth : Nat
  jump : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Artificial root record at index `0` (`depth = 0`, `parent = 0`, `jump = 0`). -/
def rootRecord : JumpRecord :=
  { parent := 0, depth := 0, jump := 0 }

/-- Structural index lookup on a record list. -/
def listRecordAt? : List JumpRecord → Nat → Option JumpRecord
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, i + 1 => listRecordAt? rs i

theorem listRecordAt?_lt_none {rs : List JumpRecord} {i : Nat}
    (hge : rs.length ≤ i) : listRecordAt? rs i = none := by
  induction rs generalizing i with
  | nil => rfl
  | cons _ tl ih =>
      cases i with
      | zero =>
          simp only [List.length_cons] at hge
          omega
      | succ j =>
          simp only [List.length_cons] at hge
          exact ih (by omega)

theorem listRecordAt?_append_old (rs : List JumpRecord) (r : JumpRecord)
    {i : Nat} (hi : i < rs.length) :
    listRecordAt? (rs ++ [r]) i = listRecordAt? rs i := by
  induction rs generalizing i with
  | nil =>
      simp only [List.length_nil] at hi
      omega
  | cons _ tl ih =>
      cases i with
      | zero => rfl
      | succ j =>
          simp only [List.length_cons] at hi
          exact ih (by omega)

theorem listRecordAt?_append_new (rs : List JumpRecord) (r : JumpRecord) :
    listRecordAt? (rs ++ [r]) rs.length = some r := by
  induction rs with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Growing forest store indexed `0 .. size - 1` (`0` is the artificial root). -/
structure JumpForest where
  records : List JumpRecord
  deriving DecidableEq, Repr

namespace JumpForest

/-- Initial forest containing only the artificial root `0`. -/
def init : JumpForest :=
  { records := [rootRecord] }

/-- Total number of stored records (`1 + numInserted`). -/
def size (F : JumpForest) : Nat :=
  F.records.length

/-- Number of appended real nodes (`size - 1`). -/
def numInserted (F : JumpForest) : Nat :=
  F.records.length - 1

/-- Checked optional record lookup at index `u`. -/
def recordAt? (F : JumpForest) (u : Nat) : Option JumpRecord :=
  listRecordAt? F.records u

/-- Total record lookup at index `u` (defaults out-of-range indices to `rootRecord`). -/
def recordAt (F : JumpForest) (u : Nat) : JumpRecord :=
  match F.recordAt? u with
  | some r => r
  | none => rootRecord

def parentOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).parent

def depthOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).depth

def jumpOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).jump

/-- New leaf record formed under existing node `p` by Myers's skew-binary merge rule. -/
def mkAppendedRecord (F : JumpForest) (p : Nat) : JumpRecord :=
  let recP := F.recordAt p
  let a := recP.jump
  let recA := F.recordAt a
  let b := recA.jump
  let recB := F.recordAt b
  let len1 := recP.depth - recA.depth
  let len2 := recA.depth - recB.depth
  let j := if 0 < len1 ∧ len1 = len2 then b else p
  { parent := p, depth := recP.depth + 1, jump := j }

/-- Append a new leaf at index `F.size` under parent `p`. -/
def appendLeaf (F : JumpForest) (p : Nat) : JumpForest :=
  { records := F.records ++ [F.mkAppendedRecord p] }

theorem size_init : JumpForest.init.size = 1 := rfl

theorem numInserted_init : JumpForest.init.numInserted = 0 := rfl

theorem size_appendLeaf (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).size = F.size + 1 :=
  list_length_snoc F.records (F.mkAppendedRecord p)

end JumpForest

theorem recordAt?_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).recordAt? u = F.recordAt? u :=
  listRecordAt?_append_old F.records (F.mkAppendedRecord p) hu

theorem recordAt?_appendLeaf_new (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).recordAt? F.size = some (F.mkAppendedRecord p) :=
  listRecordAt?_append_new F.records (F.mkAppendedRecord p)

theorem recordAt_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).recordAt u = F.recordAt u := by
  unfold JumpForest.recordAt
  rw [recordAt?_appendLeaf_old F p hu]

theorem recordAt_appendLeaf_new (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).recordAt F.size = F.mkAppendedRecord p := by
  unfold JumpForest.recordAt
  rw [recordAt?_appendLeaf_new F p]

theorem parentOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).parentOf u = F.parentOf u := by
  unfold JumpForest.parentOf
  rw [recordAt_appendLeaf_old F p hu]

theorem depthOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).depthOf u = F.depthOf u := by
  unfold JumpForest.depthOf
  rw [recordAt_appendLeaf_old F p hu]

theorem jumpOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).jumpOf u = F.jumpOf u := by
  unfold JumpForest.jumpOf
  rw [recordAt_appendLeaf_old F p hu]

/-- Inductive validity of a growing `JumpForest` built from `init` by appending leaves
    under existing indices `p < F.size` across arbitrary branches. -/
inductive ValidJumpForest : JumpForest → Prop where
  | init : ValidJumpForest JumpForest.init
  | appendLeaf {F : JumpForest} {p : Nat}
      (hF : ValidJumpForest F) (hp : p < F.size) :
      ValidJumpForest (F.appendLeaf p)

namespace JumpForest

/-- Reflexive-transitive multi-step extension order by valid leaf insertions. -/
inductive Extends : JumpForest → JumpForest → Prop where
  | refl (F : JumpForest) : Extends F F
  | step {F₁ F₂ : JumpForest} {p : Nat}
      (hExt : Extends F₁ F₂) (hp : p < F₂.size) :
      Extends F₁ (F₂.appendLeaf p)

theorem Extends.size_le {F₁ F₂ : JumpForest} (h : F₁.Extends F₂) :
    F₁.size ≤ F₂.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step F₂ p _ _ ih =>
      have hSz := F₂.size_appendLeaf p
      omega

theorem Extends.recordAt?_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.recordAt? u = F₁.recordAt? u := by
  induction h with
  | refl => rfl
  | @step F₂ p hExt _ ih =>
      have hu₂ : u < F₂.size := Nat.lt_of_lt_of_le hu hExt.size_le
      rw [recordAt?_appendLeaf_old F₂ p hu₂]
      exact ih

theorem Extends.recordAt_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.recordAt u = F₁.recordAt u := by
  unfold JumpForest.recordAt
  rw [h.recordAt?_eq hu]

theorem Extends.parentOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.parentOf u = F₁.parentOf u := by
  unfold JumpForest.parentOf
  rw [h.recordAt_eq hu]

theorem Extends.depthOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.depthOf u = F₁.depthOf u := by
  unfold JumpForest.depthOf
  rw [h.recordAt_eq hu]

theorem Extends.jumpOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.jumpOf u = F₁.jumpOf u := by
  unfold JumpForest.jumpOf
  rw [h.recordAt_eq hu]

end JumpForest

/-! ### Concrete Witnesses: Root/Depth Zero, Merge Case (`2^2 - 1`), and Sibling Branching -/

theorem root_has_zero_fields :
    JumpForest.init.recordAt 0 = { parent := 0, depth := 0, jump := 0 } := rfl

/-- Five-node forest witnessing both a `2^2 - 1 = 3` skew merge at node `3` (`0 ← 1 ← 2 ← 3`)
    and nontrivial multi-branching via sibling `4` appended under internal node `1`. -/
def exampleBranchAndMerge : JumpForest :=
  (((JumpForest.init.appendLeaf 0).appendLeaf 1).appendLeaf 2).appendLeaf 1

theorem exampleBranchAndMerge_valid : ValidJumpForest exampleBranchAndMerge :=
  ValidJumpForest.appendLeaf
    (ValidJumpForest.appendLeaf
      (ValidJumpForest.appendLeaf
        (ValidJumpForest.appendLeaf ValidJumpForest.init (by decide))
        (by decide))
      (by decide))
    (by decide)

theorem merge_case_witness :
    exampleBranchAndMerge.recordAt 3 = { parent := 2, depth := 3, jump := 0 } := rfl

theorem branching_case_witness :
    exampleBranchAndMerge.recordAt 2 = { parent := 1, depth := 2, jump := 1 } ∧
      exampleBranchAndMerge.recordAt 4 = { parent := 1, depth := 2, jump := 1 } ∧
      exampleBranchAndMerge.recordAt 3 = { parent := 2, depth := 3, jump := 0 } :=
  ⟨rfl, rfl, rfl⟩

/-! ### Skew-Binary Block Sizes `2^k - 1` and Inductive `ForestInvariant` -/

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      change 0 < (2 ^ k) * 2
      omega

theorem pow2_succ (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  change (2 ^ k) * 2 = 2 ^ k + 2 ^ k
  omega

theorem pow2_strictMono {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  induction b with
  | zero => omega
  | succ b ih =>
      have hPos : 0 < 2 ^ b := pow2_pos b
      have hStep : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := pow2_succ b
      if hEq : a = b then
        rw [hEq, hStep]
        omega
      else
        have hLt : a < b := by omega
        have hIH : 2 ^ a < 2 ^ b := ih hLt
        rw [hStep]
        omega

theorem lt_of_pow2_lt {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  if hLt : a < b then
    exact hLt
  else if hEq : a = b then
    rw [hEq] at h
    omega
  else
    have hGt : b < a := by omega
    have hPowGt : 2 ^ b < 2 ^ a := pow2_strictMono hGt
    omega

/-- Skew-binary block size `2^k - 1` (`1 ≤ k`). -/
def blockSize (k : Nat) : Nat :=
  2 ^ k - 1

/-- Total depth represented by a list of block exponents. -/
def blockSum : List Nat → Nat
  | [] => 0
  | k :: rest => blockSize k + blockSum rest

def AllList (P : Nat → Prop) : List Nat → Prop
  | [] => True
  | x :: xs => P x ∧ AllList P xs

def StrictlyIncreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ StrictlyIncreasing (b :: rest)

/-- Strictly increasing exponents from the leaf upwards, except a possible leading tie. -/
def SkewIncreasing (ks : List Nat) : Prop :=
  StrictlyIncreasing ks ∨
    ∃ k rest, ks = k :: k :: rest ∧ StrictlyIncreasing (k :: rest)

/-- Exponent-list transition when appending one leaf below an ancestor chain with exponents `ks`. -/
def skewPush : List Nat → List Nat
  | k₁ :: k₂ :: rest =>
      if k₁ = k₂ then (k₁ + 1) :: rest else 1 :: k₁ :: k₂ :: rest
  | ks => 1 :: ks

theorem blockSize_pos {k : Nat} (hk : 1 ≤ k) : 0 < blockSize k := by
  cases k with
  | zero => omega
  | succ k' =>
      unfold blockSize
      have hPos := pow2_pos k'
      have hStep := pow2_succ k'
      omega

theorem blockSize_strictMono {a b : Nat} (hab : a < b) : blockSize a < blockSize b := by
  unfold blockSize
  have hPos := pow2_pos a
  have hLt := pow2_strictMono hab
  omega

theorem blockSize_merge (k : Nat) :
    blockSize k + blockSize k + 1 = blockSize (k + 1) := by
  unfold blockSize
  have hPos := pow2_pos k
  have hStep := pow2_succ k
  omega

theorem blockSum_skewPush (ks : List Nat) :
    blockSum (skewPush ks) = blockSum ks + 1 := by
  match ks with
  | [] => rfl
  | [k₁] =>
      simp only [skewPush, blockSum]
      have h1 : blockSize 1 = 1 := rfl
      omega
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq, ← hEq]
        simp only [blockSum]
        have hM := blockSize_merge k₁
        omega
      else
        rw [ite_eq_right hEq]
        simp only [blockSum]
        have h1 : blockSize 1 = 1 := rfl
        omega

theorem skewPush_ne_nil (ks : List Nat) :
    ∃ k rest, skewPush ks = k :: rest := by
  match ks with
  | [] => exact ⟨1, [], rfl⟩
  | [k₁] => exact ⟨1, [k₁], rfl⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        exact ⟨k₁ + 1, rest, rfl⟩
      else
        rw [ite_eq_right hEq]
        exact ⟨1, k₁ :: k₂ :: rest, rfl⟩

theorem allList_pos_skewPush {ks : List Nat}
    (hAll : AllList (fun k => 1 ≤ k) ks) :
    AllList (fun k => 1 ≤ k) (skewPush ks) := by
  match ks with
  | [] => exact ⟨by omega, trivial⟩
  | [k₁] => exact ⟨by omega, hAll⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        have hk₁ : 1 ≤ k₁ := hAll.1
        have hRest : AllList (fun k => 1 ≤ k) rest := hAll.2.2
        exact ⟨by omega, hRest⟩
      else
        rw [ite_eq_right hEq]
        exact ⟨by omega, hAll⟩

theorem skewIncreasing_skewPush {ks : List Nat}
    (hAll : AllList (fun k => 1 ≤ k) ks)
    (hSkew : SkewIncreasing ks) :
    SkewIncreasing (skewPush ks) := by
  match ks with
  | [] => exact Or.inl trivial
  | [k₁] =>
      have hk₁ : 1 ≤ k₁ := hAll.1
      if hEq1 : 1 = k₁ then
        rw [← hEq1]
        exact Or.inr ⟨1, [], rfl, trivial⟩
      else
        have hLt1 : 1 < k₁ := by omega
        exact Or.inl ⟨hLt1, trivial⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        have hStrictTail : StrictlyIncreasing (k₁ :: rest) := by
          cases hSkew with
          | inl hS =>
              have hLt : k₁ < k₂ := hS.1
              omega
          | inr hTie =>
              let ⟨k, rest', hListEq, hST⟩ := hTie
              have hkEq : k₁ = k := congrArg headNat hListEq
              have hTail1 : k₂ :: rest = k :: rest' := congrArg tailNat hListEq
              have hRestEq : rest = rest' := congrArg tailNat hTail1
              rw [hkEq, hRestEq]
              exact hST
        cases rest with
        | nil => exact Or.inl trivial
        | cons k₃ rest'' =>
            have hLt13 : k₁ < k₃ := hStrictTail.1
            have hStrict3 : StrictlyIncreasing (k₃ :: rest'') := hStrictTail.2
            if hEq3 : k₁ + 1 = k₃ then
              rw [hEq3]
              exact Or.inr ⟨k₃, rest'', rfl, hStrict3⟩
            else
              have hLt3 : k₁ + 1 < k₃ := by omega
              exact Or.inl ⟨hLt3, hStrict3⟩
      else
        rw [ite_eq_right hEq]
        have hStrictKs : StrictlyIncreasing (k₁ :: k₂ :: rest) := by
          cases hSkew with
          | inl hS => exact hS
          | inr hTie =>
              let ⟨k, rest', hListEq, _⟩ := hTie
              have hk₁ : k₁ = k := congrArg headNat hListEq
              have hTail1 : k₂ :: rest = k :: rest' := congrArg tailNat hListEq
              have hk₂ : k₂ = k := congrArg headNat hTail1
              omega
        have hk₁Pos : 1 ≤ k₁ := hAll.1
        if hEq1 : 1 = k₁ then
          rw [← hEq1] at hStrictKs ⊢
          exact Or.inr ⟨1, k₂ :: rest, rfl, hStrictKs⟩
        else
          have hLt1 : 1 < k₁ := by omega
          exact Or.inl ⟨hLt1, hStrictKs⟩

/-- Per-node structural and skew-binary invariant relative to ghost exponent map `exps`. -/
structure NodeSpec (F : JumpForest) (exps : Nat → List Nat) (u : Nat) : Prop where
  parent_lt_size : F.parentOf u < F.size
  jump_lt_size : F.jumpOf u < F.size
  root_spec : u = 0 → F.recordAt 0 = rootRecord ∧ exps 0 = []
  pos_parent_lt : 0 < u → F.parentOf u < u
  pos_jump_le_parent : 0 < u → F.jumpOf u ≤ F.parentOf u
  pos_jump_cases : 0 < u →
    F.jumpOf u = F.parentOf u ∨ F.jumpOf u = F.jumpOf (F.jumpOf (F.parentOf u))
  pos_depth : 0 < u → F.depthOf u = F.depthOf (F.parentOf u) + 1
  pos_exps_eq : 0 < u → exps u = skewPush (exps (F.parentOf u))
  depth_eq_blockSum : F.depthOf u = blockSum (exps u)
  exps_pos : AllList (fun k => 1 ≤ k) (exps u)
  exps_skew : SkewIncreasing (exps u)
  jump_exps : ∀ k rest, exps u = k :: rest → exps (F.jumpOf u) = rest
  jump_eq_parent_of_one : ∀ rest, exps u = 1 :: rest → F.jumpOf u = F.parentOf u

/-- Global skew-binary forest invariant across all `u < F.size`. -/
structure ForestInvariant (F : JumpForest) (exps : Nat → List Nat) : Prop where
  size_pos : 0 < F.size
  nodes : ∀ u : Nat, u < F.size → NodeSpec F exps u

namespace ForestInvariant

theorem root_record {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) :
    F.recordAt 0 = rootRecord :=
  ((inv.nodes 0 inv.size_pos).root_spec rfl).1

theorem root_parent {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.parentOf 0 = 0 := by
  unfold JumpForest.parentOf
  rw [inv.root_record]
  rfl

theorem root_depth {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.depthOf 0 = 0 := by
  unfold JumpForest.depthOf
  rw [inv.root_record]
  rfl

theorem root_jump {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.jumpOf 0 = 0 := by
  unfold JumpForest.jumpOf
  rw [inv.root_record]
  rfl

theorem jump_le_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.jumpOf u ≤ u := by
  if hPos : 0 < u then
    have spec := inv.nodes u hu
    have h1 := spec.pos_jump_le_parent hPos
    have h2 := spec.pos_parent_lt hPos
    omega
  else
    have hu0 : u = 0 := by omega
    rw [hu0, inv.root_jump]
    exact Nat.le_refl 0

theorem jump_lt_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hPos : 0 < u) (hu : u < F.size) :
    F.jumpOf u < u := by
  have spec := inv.nodes u hu
  have h1 := spec.pos_jump_le_parent hPos
  have h2 := spec.pos_parent_lt hPos
  omega

theorem depth_eq_zero_iff {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.depthOf u = 0 ↔ u = 0 := by
  constructor
  · intro hD
    if hPos : 0 < u then
      have hStep := (inv.nodes u hu).pos_depth hPos
      omega
    else
      omega
  · intro hEq
    rw [hEq]
    exact inv.root_depth

theorem depth_jump_lt {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hPos : 0 < u) (hu : u < F.size) :
    F.depthOf (F.jumpOf u) < F.depthOf u := by
  have specU := inv.nodes u hu
  let ⟨k, rest, hPush⟩ := skewPush_ne_nil (exps (F.parentOf u))
  have hExpsU : exps u = k :: rest := Eq.trans (specU.pos_exps_eq hPos) hPush
  have hkPos : 1 ≤ k := by
    have hAll := specU.exps_pos
    rw [hExpsU] at hAll
    exact hAll.1
  have hBPos : 0 < blockSize k := blockSize_pos hkPos
  have hExpsJ : exps (F.jumpOf u) = rest := specU.jump_exps k rest hExpsU
  have specJ := inv.nodes (F.jumpOf u) specU.jump_lt_size
  have hDU : F.depthOf u = blockSize k + blockSum rest := by
    rw [specU.depth_eq_blockSum, hExpsU]
    rfl
  have hDJ : F.depthOf (F.jumpOf u) = blockSum rest := by
    rw [specJ.depth_eq_blockSum, hExpsJ]
  omega

theorem depthOf_le_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.depthOf u ≤ u := by
  refine nat_strong_ind (P := fun w => w < F.size → F.depthOf w ≤ w) ?_ u hu
  intro w ih hw
  if hPos : 0 < w then
    have specW := inv.nodes w hw
    have hpLt : F.parentOf w < w := specW.pos_parent_lt hPos
    have hpSz : F.parentOf w < F.size := specW.parent_lt_size
    have hIH : F.depthOf (F.parentOf w) ≤ F.parentOf w := ih (F.parentOf w) hpLt hpSz
    have hStep := specW.pos_depth hPos
    omega
  else
    have hw0 : w = 0 := by omega
    rw [hw0, inv.root_depth]
    exact Nat.le_refl 0

end ForestInvariant

theorem ValidJumpForest.exists_forestInvariant {F : JumpForest}
    (hF : ValidJumpForest F) :
    ∃ exps : Nat → List Nat, ForestInvariant F exps := by
  induction hF with
  | init =>
      refine ⟨fun _ => [], ⟨by decide, ?_⟩⟩
      intro u hu
      have hSz : JumpForest.init.size = 1 := rfl
      have hu0 : u = 0 := by omega
      subst hu0
      refine
        { parent_lt_size := by decide
          jump_lt_size := by decide
          root_spec := fun _ => ⟨rfl, rfl⟩
          pos_parent_lt := fun hPos => by omega
          pos_jump_le_parent := fun hPos => by omega
          pos_jump_cases := fun hPos => by omega
          pos_depth := fun hPos => by omega
          pos_exps_eq := fun hPos => by omega
          depth_eq_blockSum := rfl
          exps_pos := trivial
          exps_skew := Or.inl trivial
          jump_exps := fun _ _ hEq => by cases hEq
          jump_eq_parent_of_one := fun _ hEq => by cases hEq }
  | @appendLeaf F p _ hp ih =>
      let ⟨exps, inv⟩ := ih
      let exps' : Nat → List Nat :=
        fun u => if u = F.size then skewPush (exps p) else exps u
      have hF'Size : (F.appendLeaf p).size = F.size + 1 := F.size_appendLeaf p
      have hExpsOld : ∀ w : Nat, w < F.size → exps' w = exps w := by
        intro w hw
        have hNe : w ≠ F.size := by omega
        exact ite_eq_right hNe
      have hExpsNew : exps' F.size = skewPush (exps p) :=
        ite_eq_left rfl
      refine ⟨exps', ⟨by omega, ?_⟩⟩
      intro u hu'
      if huOld : u < F.size then
        have specU := inv.nodes u huOld
        have hpOld : F.parentOf u < F.size := specU.parent_lt_size
        have hjOld : F.jumpOf u < F.size := specU.jump_lt_size
        have haOld : F.jumpOf (F.parentOf u) < F.size := (inv.nodes _ hpOld).jump_lt_size
        have hParEq : (F.appendLeaf p).parentOf u = F.parentOf u :=
          parentOf_appendLeaf_old F p huOld
        have hDepEq : (F.appendLeaf p).depthOf u = F.depthOf u :=
          depthOf_appendLeaf_old F p huOld
        have hJmpEq : (F.appendLeaf p).jumpOf u = F.jumpOf u :=
          jumpOf_appendLeaf_old F p huOld
        have hDepParEq :
            (F.appendLeaf p).depthOf ((F.appendLeaf p).parentOf u) =
              F.depthOf (F.parentOf u) := by
          rw [hParEq]
          exact depthOf_appendLeaf_old F p hpOld
        have hJmpParEq :
            (F.appendLeaf p).jumpOf ((F.appendLeaf p).parentOf u) =
              F.jumpOf (F.parentOf u) := by
          rw [hParEq]
          exact jumpOf_appendLeaf_old F p hpOld
        have hJmp2Eq :
            (F.appendLeaf p).jumpOf (F.jumpOf (F.parentOf u)) =
              F.jumpOf (F.jumpOf (F.parentOf u)) :=
          jumpOf_appendLeaf_old F p haOld
        refine
          { parent_lt_size := by rw [hParEq]; omega
            jump_lt_size := by rw [hJmpEq]; omega
            root_spec := fun hu0 => by
              subst hu0
              rw [recordAt_appendLeaf_old F p inv.size_pos, hExpsOld 0 inv.size_pos]
              exact specU.root_spec rfl
            pos_parent_lt := fun hPos => by rw [hParEq]; exact specU.pos_parent_lt hPos
            pos_jump_le_parent := fun hPos => by
              rw [hJmpEq, hParEq]
              exact specU.pos_jump_le_parent hPos
            pos_jump_cases := fun hPos => by
              rw [hJmpEq, hParEq, jumpOf_appendLeaf_old F p hpOld, hJmp2Eq]
              exact specU.pos_jump_cases hPos
            pos_depth := fun hPos => by
              rw [hDepEq, hDepParEq]
              exact specU.pos_depth hPos
            pos_exps_eq := fun hPos => by
              rw [hExpsOld u huOld, hParEq, hExpsOld (F.parentOf u) hpOld]
              exact specU.pos_exps_eq hPos
            depth_eq_blockSum := by
              rw [hDepEq, hExpsOld u huOld]
              exact specU.depth_eq_blockSum
            exps_pos := by rw [hExpsOld u huOld]; exact specU.exps_pos
            exps_skew := by rw [hExpsOld u huOld]; exact specU.exps_skew
            jump_exps := fun k rest hEq => by
              rw [hJmpEq, hExpsOld (F.jumpOf u) hjOld]
              rw [hExpsOld u huOld] at hEq
              exact specU.jump_exps k rest hEq
            jump_eq_parent_of_one := fun rest hEq => by
              rw [hJmpEq, hParEq]
              rw [hExpsOld u huOld] at hEq
              exact specU.jump_eq_parent_of_one rest hEq }
      else
        have huEq : u = F.size := by omega
        subst huEq
        have specP := inv.nodes p hp
        let a := F.jumpOf p
        have ha : a < F.size := specP.jump_lt_size
        have haLeP : a ≤ p := inv.jump_le_self hp
        have specA := inv.nodes a ha
        let b := F.jumpOf a
        have hb : b < F.size := specA.jump_lt_size
        have hbLeA : b ≤ a := inv.jump_le_self ha
        have specB := inv.nodes b hb
        have hRecNew : (F.appendLeaf p).recordAt F.size = F.mkAppendedRecord p :=
          recordAt_appendLeaf_new F p
        have hParNew : (F.appendLeaf p).parentOf F.size = p := by
          unfold JumpForest.parentOf
          rw [hRecNew]
          rfl
        have hDepNew : (F.appendLeaf p).depthOf F.size = F.depthOf p + 1 := by
          unfold JumpForest.depthOf
          rw [hRecNew]
          rfl
        let len1 := F.depthOf p - F.depthOf a
        let len2 := F.depthOf a - F.depthOf b
        have hJmpNew : (F.appendLeaf p).jumpOf F.size =
            if 0 < len1 ∧ len1 = len2 then b else p := by
          unfold JumpForest.jumpOf
          rw [hRecNew]
          rfl
        have hJmpA_F' : (F.appendLeaf p).jumpOf p = a := jumpOf_appendLeaf_old F p hp
        have hJmpB_F' : (F.appendLeaf p).jumpOf a = b := jumpOf_appendLeaf_old F p ha
        have hStepInvs :
            (∀ k rest, exps' F.size = k :: rest →
                exps' ((F.appendLeaf p).jumpOf F.size) = rest) ∧
              (∀ rest, exps' F.size = 1 :: rest →
                (F.appendLeaf p).jumpOf F.size = (F.appendLeaf p).parentOf F.size) := by
          rw [hExpsNew, hParNew]
          cases hExpsP : exps p with
          | nil =>
              have hDP0 : F.depthOf p = 0 := by
                rw [specP.depth_eq_blockSum, hExpsP]
                rfl
              have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                change ¬ (0 < F.depthOf p - F.depthOf a ∧ _)
                omega
              have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                rw [hJmpNew, ite_eq_right hNotCond]
              rw [hJ, hExpsOld p hp, hExpsP]
              dsimp only [skewPush]
              refine ⟨?_, fun _ _ => rfl⟩
              intro _ _ hEq
              exact (List.cons.inj hEq).2
          | cons k₁ tail1 =>
              cases tail1 with
              | nil =>
                  have hExpsA : exps a = [] := specP.jump_exps k₁ [] hExpsP
                  have hDA0 : F.depthOf a = 0 := by
                    rw [specA.depth_eq_blockSum, hExpsA]
                    rfl
                  have ha0 : a = 0 := (inv.depth_eq_zero_iff ha).mp hDA0
                  have hb0 : b = 0 := by
                    change F.jumpOf a = 0
                    rw [ha0]
                    exact inv.root_jump
                  have hDB0 : F.depthOf b = 0 := by
                    rw [hb0]
                    exact inv.root_depth
                  have hk₁Pos : 1 ≤ k₁ := by
                    have hAll := specP.exps_pos
                    rw [hExpsP] at hAll
                    exact hAll.1
                  have hDPPos : 0 < F.depthOf p := by
                    rw [specP.depth_eq_blockSum, hExpsP]
                    have hBP := blockSize_pos hk₁Pos
                    dsimp only [blockSum]
                    omega
                  have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                    change ¬ (0 < F.depthOf p - F.depthOf a ∧
                      F.depthOf p - F.depthOf a = F.depthOf a - F.depthOf b)
                    omega
                  have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                    rw [hJmpNew, ite_eq_right hNotCond]
                  rw [hJ, hExpsOld p hp, hExpsP]
                  dsimp only [skewPush]
                  refine ⟨?_, fun _ _ => rfl⟩
                  intro _ _ hEq
                  exact (List.cons.inj hEq).2
              | cons k₂ tl =>
                  have hAllP := specP.exps_pos
                  rw [hExpsP] at hAllP
                  have hk₁Pos : 1 ≤ k₁ := hAllP.1
                  have hk₂Pos : 1 ≤ k₂ := hAllP.2.1
                  have hExpsA : exps a = k₂ :: tl := specP.jump_exps k₁ (k₂ :: tl) hExpsP
                  have hExpsB : exps b = tl := specA.jump_exps k₂ tl hExpsA
                  have hDP : F.depthOf p = blockSize k₁ + (blockSize k₂ + blockSum tl) := by
                    rw [specP.depth_eq_blockSum, hExpsP]
                    rfl
                  have hDA : F.depthOf a = blockSize k₂ + blockSum tl := by
                    rw [specA.depth_eq_blockSum, hExpsA]
                    rfl
                  have hDB : F.depthOf b = blockSum tl := by
                    rw [specB.depth_eq_blockSum, hExpsB]
                  have hLen1 : len1 = blockSize k₁ := by
                    change F.depthOf p - F.depthOf a = blockSize k₁
                    omega
                  have hLen2 : len2 = blockSize k₂ := by
                    change F.depthOf a - F.depthOf b = blockSize k₂
                    omega
                  if hEqK : k₁ = k₂ then
                    have hCond : 0 < len1 ∧ len1 = len2 := by
                      rw [hLen1, hLen2, hEqK]
                      exact ⟨blockSize_pos hk₂Pos, rfl⟩
                    have hJ : (F.appendLeaf p).jumpOf F.size = b := by
                      rw [hJmpNew, ite_eq_left hCond]
                    have hPushEq : skewPush (k₁ :: k₂ :: tl) = (k₁ + 1) :: tl := by
                      dsimp only [skewPush]
                      exact ite_eq_left hEqK
                    rw [hJ, hExpsOld b hb, hExpsB, hPushEq]
                    refine ⟨?_, ?_⟩
                    · intro _ _ hEq
                      exact (List.cons.inj hEq).2
                    · intro _ hEq
                      have hk1Eq : k₁ + 1 = 1 := (List.cons.inj hEq).1
                      omega
                  else
                    have hSkewP := specP.exps_skew
                    rw [hExpsP] at hSkewP
                    have hLtK : k₁ < k₂ := by
                      cases hSkewP with
                      | inl hS => exact hS.1
                      | inr hTie =>
                          let ⟨k, _, hListEq, _⟩ := hTie
                          have hk₁Eq : k₁ = k := (List.cons.inj hListEq).1
                          have hTail1 := (List.cons.inj hListEq).2
                          have hk₂Eq : k₂ = k := (List.cons.inj hTail1).1
                          omega
                    have hBLt : blockSize k₁ < blockSize k₂ := blockSize_strictMono hLtK
                    have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                      rw [hLen1, hLen2]
                      omega
                    have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                      rw [hJmpNew, ite_eq_right hNotCond]
                    have hPushEq : skewPush (k₁ :: k₂ :: tl) = 1 :: k₁ :: k₂ :: tl := by
                      dsimp only [skewPush]
                      exact ite_eq_right hEqK
                    rw [hJ, hExpsOld p hp, hExpsP, hPushEq]
                    refine ⟨?_, fun _ _ => rfl⟩
                    intro _ _ hEq
                    exact (List.cons.inj hEq).2
        refine
          { parent_lt_size := by rw [hParNew]; omega
            jump_lt_size := by
              rw [hJmpNew]
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; omega
              else
                rw [ite_eq_right hC]; omega
            root_spec := fun _ => by
              have hPosSz := inv.size_pos
              omega
            pos_parent_lt := fun _ => by rw [hParNew]; exact hp
            pos_jump_le_parent := fun _ => by
              rw [hJmpNew, hParNew]
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; omega
              else
                rw [ite_eq_right hC]; omega
            pos_jump_cases := fun _ => by
              rw [hJmpNew, hParNew, hJmpA_F', hJmpB_F']
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; exact Or.inr rfl
              else
                rw [ite_eq_right hC]; exact Or.inl rfl
            pos_depth := fun _ => by
              rw [hDepNew, hParNew, depthOf_appendLeaf_old F p hp]
            pos_exps_eq := fun _ => by
              rw [hExpsNew, hParNew, hExpsOld p hp]
            depth_eq_blockSum := by
              rw [hDepNew, hExpsNew, blockSum_skewPush, specP.depth_eq_blockSum]
            exps_pos := by
              rw [hExpsNew]
              exact allList_pos_skewPush specP.exps_pos
            exps_skew := by
              rw [hExpsNew]
              exact skewIncreasing_skewPush specP.exps_pos specP.exps_skew
            jump_exps := hStepInvs.1
            jump_eq_parent_of_one := hStepInvs.2 }

/-! ### Depth-Target Traversal, Ancestry, Persistence, and Unique Ancestor-at-Depth -/

/-- Single move executed during depth-target traversal. -/
inductive JumpMove where
  | jump (src dst : Nat)
  | parent (src dst : Nat)
  deriving DecidableEq, Repr

namespace JumpForest

/-- One step from `u` toward `targetDepth`: jump if `targetDepth ≤ depthOf(jumpOf u)`, else parent. -/
def stepToDepth (F : JumpForest) (u targetDepth : Nat) : Nat :=
  let j := F.jumpOf u
  if targetDepth ≤ F.depthOf j then j else F.parentOf u

/-- Explicit move tag for one step from `u` toward `targetDepth`. -/
def stepMoveToDepth (F : JumpForest) (u targetDepth : Nat) : JumpMove :=
  let j := F.jumpOf u
  if targetDepth ≤ F.depthOf j then
    JumpMove.jump u j
  else
    JumpMove.parent u (F.parentOf u)

def traceMovesAux (F : JumpForest) : Nat → Nat → Nat → List JumpMove
  | 0, _, _ => []
  | fuel + 1, u, targetDepth =>
      if targetDepth < F.depthOf u then
        F.stepMoveToDepth u targetDepth ::
          F.traceMovesAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        []

theorem traceMovesAux_zero (F : JumpForest) (u targetDepth : Nat) :
    F.traceMovesAux 0 u targetDepth = [] := rfl

theorem traceMovesAux_succ (F : JumpForest) (fuel u targetDepth : Nat) :
    F.traceMovesAux (fuel + 1) u targetDepth =
      if targetDepth < F.depthOf u then
        F.stepMoveToDepth u targetDepth ::
          F.traceMovesAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        [] := rfl

/-- Exact sequence of `jump` / `parent` moves from `u` down to `targetDepth`. -/
def traceMoves (F : JumpForest) (u targetDepth : Nat) : List JumpMove :=
  F.traceMovesAux (F.depthOf u - targetDepth) u targetDepth

def traceVerticesAux (F : JumpForest) : Nat → Nat → Nat → List Nat
  | 0, u, _ => [u]
  | fuel + 1, u, targetDepth =>
      if targetDepth < F.depthOf u then
        u :: F.traceVerticesAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        [u]

theorem traceVerticesAux_zero (F : JumpForest) (u targetDepth : Nat) :
    F.traceVerticesAux 0 u targetDepth = [u] := rfl

theorem traceVerticesAux_succ (F : JumpForest) (fuel u targetDepth : Nat) :
    F.traceVerticesAux (fuel + 1) u targetDepth =
      if targetDepth < F.depthOf u then
        u :: F.traceVerticesAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        [u] := rfl

/-- Sequence of visited vertices along the depth-target traversal from `u`. -/
def traceVertices (F : JumpForest) (u targetDepth : Nat) : List Nat :=
  F.traceVerticesAux (F.depthOf u - targetDepth) u targetDepth

def ancestorAtDepthAux (F : JumpForest) : Nat → Nat → Nat → Nat
  | 0, u, _ => u
  | fuel + 1, u, targetDepth =>
      if targetDepth < F.depthOf u then
        F.ancestorAtDepthAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        u

theorem ancestorAtDepthAux_zero (F : JumpForest) (u targetDepth : Nat) :
    F.ancestorAtDepthAux 0 u targetDepth = u := rfl

theorem ancestorAtDepthAux_succ (F : JumpForest) (fuel u targetDepth : Nat) :
    F.ancestorAtDepthAux (fuel + 1) u targetDepth =
      if targetDepth < F.depthOf u then
        F.ancestorAtDepthAux fuel (F.stepToDepth u targetDepth) targetDepth
      else
        u := rfl

/-- Depth-target traversal returning the unique ancestor of `u` at `targetDepth`. -/
def ancestorAtDepth (F : JumpForest) (u targetDepth : Nat) : Nat :=
  F.ancestorAtDepthAux (F.depthOf u - targetDepth) u targetDepth

/-- `O(L)` ancestry test in the growing forest. -/
def decideAncestor (F : JumpForest) (a u : Nat) : Bool :=
  if F.depthOf a ≤ F.depthOf u ∧ F.ancestorAtDepth u (F.depthOf a) = a then
    true
  else
    false

/-- Iterated `parentOf` steps from `u`. -/
def iterParent (F : JumpForest) : Nat → Nat → Nat
  | 0, u => u
  | k + 1, u => F.iterParent k (F.parentOf u)

def realAncestorChainAux (F : JumpForest) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, u =>
      if u = 0 then [] else u :: F.realAncestorChainAux fuel (F.parentOf u)

theorem realAncestorChainAux_zero (F : JumpForest) (u : Nat) :
    F.realAncestorChainAux 0 u = [] := rfl

theorem realAncestorChainAux_succ (F : JumpForest) (fuel u : Nat) :
    F.realAncestorChainAux (fuel + 1) u =
      if u = 0 then [] else u :: F.realAncestorChainAux fuel (F.parentOf u) := rfl

/-- Real (positive) ancestors of `u` from `u` upwards, excluding artificial root `0`. -/
def realAncestorChain (F : JumpForest) (u : Nat) : List Nat :=
  F.realAncestorChainAux (F.depthOf u) u

end JumpForest

/-- Inclusive tree ancestry in `F`: reachable by zero or more `parentOf` steps. -/
def IsAncestor (F : JumpForest) (a u : Nat) : Prop :=
  ∃ k : Nat, F.iterParent k u = a

theorem IsAncestor.refl (F : JumpForest) (u : Nat) : IsAncestor F u u :=
  ⟨0, rfl⟩

theorem IsAncestor.parent (F : JumpForest) (u : Nat) : IsAncestor F (F.parentOf u) u :=
  ⟨1, rfl⟩

theorem iterParent_add (F : JumpForest) (k₁ k₂ u : Nat) :
    F.iterParent (k₁ + k₂) u = F.iterParent k₂ (F.iterParent k₁ u) := by
  induction k₁ generalizing u with
  | zero =>
      have h0 : 0 + k₂ = k₂ := by omega
      rw [h0]
      rfl
  | succ k₁ ih =>
      have hS : (k₁ + 1) + k₂ = (k₁ + k₂) + 1 := by omega
      rw [hS]
      exact ih (F.parentOf u)

theorem IsAncestor.trans {F : JumpForest} {a b c : Nat}
    (hab : IsAncestor F a b) (hbc : IsAncestor F b c) :
    IsAncestor F a c := by
  let ⟨k₂, hk₂⟩ := hab
  let ⟨k₁, hk₁⟩ := hbc
  refine ⟨k₁ + k₂, ?_⟩
  rw [iterParent_add, hk₁, hk₂]

theorem ValidJumpForest.parentOf_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) : F.parentOf u < F.size := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  exact (inv.nodes u hu).parent_lt_size

theorem ValidJumpForest.jumpOf_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) : F.jumpOf u < F.size := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  exact (inv.nodes u hu).jump_lt_size

theorem ValidJumpForest.stepToDepth_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (targetDepth : Nat) :
    F.stepToDepth u targetDepth < F.size := by
  unfold JumpForest.stepToDepth
  dsimp only
  if hJ : targetDepth ≤ F.depthOf (F.jumpOf u) then
    rw [ite_eq_left hJ]
    exact hF.jumpOf_lt_size hu
  else
    rw [ite_eq_right hJ]
    exact hF.parentOf_lt_size hu

theorem ValidJumpForest.iterParent_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (k : Nat) :
    F.iterParent k u < F.size := by
  induction k generalizing u with
  | zero => exact hu
  | succ _ ih => exact ih (hF.parentOf_lt_size hu)

theorem ValidJumpForest.depth_iterParent {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (k : Nat) :
    F.depthOf (F.iterParent k u) = F.depthOf u - k := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  induction k generalizing u with
  | zero =>
      dsimp only [JumpForest.iterParent]
      omega
  | succ k ih =>
      have hIH := ih (hF.parentOf_lt_size hu)
      change F.depthOf (F.iterParent k (F.parentOf u)) = F.depthOf u - (k + 1)
      rw [hIH]
      if hPos : 0 < u then
        have hStep := (inv.nodes u hu).pos_depth hPos
        omega
      else
        have hu0 : u = 0 := by omega
        rw [hu0, inv.root_parent, inv.root_depth]
        omega

theorem ValidJumpForest.iterParent_depthOf_eq_zero {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) :
    F.iterParent (F.depthOf u) u = 0 := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have hSz := hF.iterParent_lt_size hu (F.depthOf u)
  have hD := hF.depth_iterParent hu (F.depthOf u)
  exact (inv.depth_eq_zero_iff hSz).mp (by omega)

theorem ValidJumpForest.zero_isAncestor {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) :
    IsAncestor F 0 u :=
  ⟨F.depthOf u, hF.iterParent_depthOf_eq_zero hu⟩

theorem ValidJumpForest.jumpOf_isAncestor {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) :
    IsAncestor F (F.jumpOf u) u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  refine nat_strong_ind
    (P := fun w => w < F.size → IsAncestor F (F.jumpOf w) w) ?_ u hu
  intro w ih hw
  if hPos : 0 < w then
    have specW := inv.nodes w hw
    cases specW.pos_jump_cases hPos with
    | inl hPar =>
        rw [hPar]
        exact IsAncestor.parent F w
    | inr hTwo =>
        let p := F.parentOf w
        have hpLt : p < w := specW.pos_parent_lt hPos
        have hpSz : p < F.size := specW.parent_lt_size
        let a := F.jumpOf p
        have haLeP : a ≤ p := inv.jump_le_self hpSz
        have haLt : a < w := Nat.lt_of_le_of_lt haLeP hpLt
        have haSz : a < F.size := (inv.nodes p hpSz).jump_lt_size
        have hBA : IsAncestor F (F.jumpOf a) a := ih a haLt haSz
        have hAP : IsAncestor F a p := ih p hpLt hpSz
        have hPW : IsAncestor F p w := IsAncestor.parent F w
        rw [hTwo]
        exact IsAncestor.trans hBA (IsAncestor.trans hAP hPW)
  else
    have hw0 : w = 0 := by omega
    rw [hw0, inv.root_jump]
    exact IsAncestor.refl F 0

theorem ValidJumpForest.stepToDepth_isAncestor {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (targetDepth : Nat) :
    IsAncestor F (F.stepToDepth u targetDepth) u := by
  unfold JumpForest.stepToDepth
  dsimp only
  if hJ : targetDepth ≤ F.depthOf (F.jumpOf u) then
    rw [ite_eq_left hJ]
    exact hF.jumpOf_isAncestor hu
  else
    rw [ite_eq_right hJ]
    exact IsAncestor.parent F u

theorem ValidJumpForest.stepToDepth_lt_self {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hPos : 0 < u) (hu : u < F.size) (targetDepth : Nat) :
    F.stepToDepth u targetDepth < u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  unfold JumpForest.stepToDepth
  dsimp only
  if hJ : targetDepth ≤ F.depthOf (F.jumpOf u) then
    rw [ite_eq_left hJ]
    exact inv.jump_lt_self hPos hu
  else
    rw [ite_eq_right hJ]
    exact (inv.nodes u hu).pos_parent_lt hPos

theorem ValidJumpForest.depth_stepToDepth_ge {F : JumpForest} (hF : ValidJumpForest F)
    {u targetDepth : Nat} (hu : u < F.size) (hLt : targetDepth < F.depthOf u) :
    targetDepth ≤ F.depthOf (F.stepToDepth u targetDepth) := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have hPos : 0 < u := by
    if hP : 0 < u then exact hP
    else
      have hu0 : u = 0 := by omega
      rw [hu0, inv.root_depth] at hLt
      omega
  unfold JumpForest.stepToDepth
  dsimp only
  if hJ : targetDepth ≤ F.depthOf (F.jumpOf u) then
    rw [ite_eq_left hJ]
    exact hJ
  else
    rw [ite_eq_right hJ]
    have hStep := (inv.nodes u hu).pos_depth hPos
    omega

theorem ValidJumpForest.depth_stepToDepth_lt {F : JumpForest} (hF : ValidJumpForest F)
    {u targetDepth : Nat} (hu : u < F.size) (hLt : targetDepth < F.depthOf u) :
    F.depthOf (F.stepToDepth u targetDepth) < F.depthOf u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have hPos : 0 < u := by
    if hP : 0 < u then exact hP
    else
      have hu0 : u = 0 := by omega
      rw [hu0, inv.root_depth] at hLt
      omega
  unfold JumpForest.stepToDepth
  dsimp only
  if hJ : targetDepth ≤ F.depthOf (F.jumpOf u) then
    rw [ite_eq_left hJ]
    exact inv.depth_jump_lt hPos hu
  else
    rw [ite_eq_right hJ]
    have hStep := (inv.nodes u hu).pos_depth hPos
    omega

theorem ValidJumpForest.ancestorAtDepthAux_fuel_irrel {F : JumpForest} (hF : ValidJumpForest F) :
    ∀ (fuel₁ fuel₂ u d : Nat), u < F.size →
      F.depthOf u - d ≤ fuel₁ → F.depthOf u - d ≤ fuel₂ →
      F.ancestorAtDepthAux fuel₁ u d = F.ancestorAtDepthAux fuel₂ u d := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ u d _ h1 _
      have hNotLt : ¬ (d < F.depthOf u) := by omega
      rw [JumpForest.ancestorAtDepthAux_zero]
      cases fuel₂ with
      | zero => rw [JumpForest.ancestorAtDepthAux_zero]
      | succ f₂ => rw [JumpForest.ancestorAtDepthAux_succ, ite_eq_right hNotLt]
  | succ f₁ ih =>
      intro fuel₂ u d hu h1 h2
      rw [JumpForest.ancestorAtDepthAux_succ]
      if hLt : d < F.depthOf u then
        rw [ite_eq_left hLt]
        cases fuel₂ with
        | zero => omega
        | succ f₂ =>
            rw [JumpForest.ancestorAtDepthAux_succ, ite_eq_left hLt]
            have hNextSz := hF.stepToDepth_lt_size hu d
            have hNextLt := hF.depth_stepToDepth_lt hu hLt
            exact ih f₂ (F.stepToDepth u d) d hNextSz (by omega) (by omega)
      else
        rw [ite_eq_right hLt]
        cases fuel₂ with
        | zero => rw [JumpForest.ancestorAtDepthAux_zero]
        | succ f₂ => rw [JumpForest.ancestorAtDepthAux_succ, ite_eq_right hLt]

theorem ValidJumpForest.traceMovesAux_fuel_irrel {F : JumpForest} (hF : ValidJumpForest F) :
    ∀ (fuel₁ fuel₂ u d : Nat), u < F.size →
      F.depthOf u - d ≤ fuel₁ → F.depthOf u - d ≤ fuel₂ →
      F.traceMovesAux fuel₁ u d = F.traceMovesAux fuel₂ u d := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ u d _ h1 _
      have hNotLt : ¬ (d < F.depthOf u) := by omega
      rw [JumpForest.traceMovesAux_zero]
      cases fuel₂ with
      | zero => rw [JumpForest.traceMovesAux_zero]
      | succ f₂ => rw [JumpForest.traceMovesAux_succ, ite_eq_right hNotLt]
  | succ f₁ ih =>
      intro fuel₂ u d hu h1 h2
      rw [JumpForest.traceMovesAux_succ]
      if hLt : d < F.depthOf u then
        rw [ite_eq_left hLt]
        cases fuel₂ with
        | zero => omega
        | succ f₂ =>
            rw [JumpForest.traceMovesAux_succ, ite_eq_left hLt]
            have hNextSz := hF.stepToDepth_lt_size hu d
            have hNextLt := hF.depth_stepToDepth_lt hu hLt
            exact congrArg (List.cons (F.stepMoveToDepth u d))
              (ih f₂ (F.stepToDepth u d) d hNextSz (by omega) (by omega))
      else
        rw [ite_eq_right hLt]
        cases fuel₂ with
        | zero => rw [JumpForest.traceMovesAux_zero]
        | succ f₂ => rw [JumpForest.traceMovesAux_succ, ite_eq_right hLt]

theorem ancestorAtDepth_of_ge (F : JumpForest) {u d : Nat} (hGe : F.depthOf u ≤ d) :
    F.ancestorAtDepth u d = u := by
  unfold JumpForest.ancestorAtDepth
  have h0 : F.depthOf u - d = 0 := by omega
  rw [h0]
  rfl

theorem traceMoves_of_ge (F : JumpForest) {u d : Nat} (hGe : F.depthOf u ≤ d) :
    F.traceMoves u d = [] := by
  unfold JumpForest.traceMoves
  have h0 : F.depthOf u - d = 0 := by omega
  rw [h0]
  rfl

theorem ValidJumpForest.ancestorAtDepth_of_lt {F : JumpForest} (hF : ValidJumpForest F)
    {u d : Nat} (hu : u < F.size) (hLt : d < F.depthOf u) :
    F.ancestorAtDepth u d = F.ancestorAtDepth (F.stepToDepth u d) d := by
  have hFuel : F.depthOf u - d = (F.depthOf u - d - 1) + 1 := by omega
  have hLHS : F.ancestorAtDepth u d =
      F.ancestorAtDepthAux ((F.depthOf u - d - 1) + 1) u d :=
    congrArg (fun k => F.ancestorAtDepthAux k u d) hFuel
  rw [hLHS, JumpForest.ancestorAtDepthAux_succ, ite_eq_left hLt]
  have hNextSz := hF.stepToDepth_lt_size hu d
  have hNextLt := hF.depth_stepToDepth_lt hu hLt
  change F.ancestorAtDepthAux (F.depthOf u - d - 1) (F.stepToDepth u d) d =
    F.ancestorAtDepthAux (F.depthOf (F.stepToDepth u d) - d) (F.stepToDepth u d) d
  exact hF.ancestorAtDepthAux_fuel_irrel
    (F.depthOf u - d - 1) (F.depthOf (F.stepToDepth u d) - d)
    (F.stepToDepth u d) d hNextSz (by omega) (Nat.le_refl _)

theorem ValidJumpForest.traceMoves_of_lt {F : JumpForest} (hF : ValidJumpForest F)
    {u d : Nat} (hu : u < F.size) (hLt : d < F.depthOf u) :
    F.traceMoves u d =
      F.stepMoveToDepth u d :: F.traceMoves (F.stepToDepth u d) d := by
  have hFuel : F.depthOf u - d = (F.depthOf u - d - 1) + 1 := by omega
  have hLHS : F.traceMoves u d =
      F.traceMovesAux ((F.depthOf u - d - 1) + 1) u d :=
    congrArg (fun k => F.traceMovesAux k u d) hFuel
  rw [hLHS, JumpForest.traceMovesAux_succ, ite_eq_left hLt]
  have hNextSz := hF.stepToDepth_lt_size hu d
  have hNextLt := hF.depth_stepToDepth_lt hu hLt
  change F.stepMoveToDepth u d ::
      F.traceMovesAux (F.depthOf u - d - 1) (F.stepToDepth u d) d =
    F.stepMoveToDepth u d ::
      F.traceMovesAux (F.depthOf (F.stepToDepth u d) - d) (F.stepToDepth u d) d
  exact congrArg (List.cons (F.stepMoveToDepth u d))
    (hF.traceMovesAux_fuel_irrel
      (F.depthOf u - d - 1) (F.depthOf (F.stepToDepth u d) - d)
      (F.stepToDepth u d) d hNextSz (by omega) (Nat.le_refl _))

/-- Exactness of `ancestorAtDepth`: returns an inclusive tree ancestor of `u` in `< F.size`
    whose depth is `targetDepth` whenever `targetDepth ≤ F.depthOf u`. -/
theorem ValidJumpForest.ancestorAtDepth_spec {F : JumpForest} (hF : ValidJumpForest F)
    {u targetDepth : Nat} (hu : u < F.size) (hLe : targetDepth ≤ F.depthOf u) :
    F.ancestorAtDepth u targetDepth < F.size ∧
      IsAncestor F (F.ancestorAtDepth u targetDepth) u ∧
      F.depthOf (F.ancestorAtDepth u targetDepth) = targetDepth := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  refine nat_strong_ind
    (P := fun w => w < F.size → targetDepth ≤ F.depthOf w →
      F.ancestorAtDepth w targetDepth < F.size ∧
        IsAncestor F (F.ancestorAtDepth w targetDepth) w ∧
        F.depthOf (F.ancestorAtDepth w targetDepth) = targetDepth)
    ?_ u hu hLe
  intro w ih hw hLeW
  if hLt : targetDepth < F.depthOf w then
    have hPos : 0 < w := by
      if hP : 0 < w then exact hP
      else
        have hw0 : w = 0 := by omega
        rw [hw0, inv.root_depth] at hLt
        omega
    let next := F.stepToDepth w targetDepth
    have hNextLt : next < w := hF.stepToDepth_lt_self hPos hw targetDepth
    have hNextSz : next < F.size := hF.stepToDepth_lt_size hw targetDepth
    have hNextGe : targetDepth ≤ F.depthOf next := hF.depth_stepToDepth_ge hw hLt
    have hStepAnc : IsAncestor F next w := hF.stepToDepth_isAncestor hw targetDepth
    have hEq := hF.ancestorAtDepth_of_lt hw hLt
    let ⟨hAncSz, hAncNext, hAncDep⟩ := ih next hNextLt hNextSz hNextGe
    rw [hEq]
    exact ⟨hAncSz, IsAncestor.trans hAncNext hStepAnc, hAncDep⟩
  else
    have hEqD : F.depthOf w = targetDepth := by omega
    rw [ancestorAtDepth_of_ge F (by omega)]
    exact ⟨hw, IsAncestor.refl F w, hEqD⟩

/-- Uniqueness of tree ancestor at any `targetDepth ≤ F.depthOf u`. -/
theorem ValidJumpForest.ancestor_eq_iterParent_of_depth {F : JumpForest}
    (hF : ValidJumpForest F) {a u targetDepth : Nat}
    (hu : u < F.size) (hAnc : IsAncestor F a u)
    (hLe : targetDepth ≤ F.depthOf u) (hDepth : F.depthOf a = targetDepth) :
    a = F.iterParent (F.depthOf u - targetDepth) u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  let ⟨k, hk⟩ := hAnc
  have haSz : a < F.size := by
    rw [← hk]
    exact hF.iterParent_lt_size hu k
  have hDk : F.depthOf a = F.depthOf u - k := by
    rw [← hk]
    exact hF.depth_iterParent hu k
  if hPosD : 0 < targetDepth then
    have hkEq : k = F.depthOf u - targetDepth := by omega
    rw [← hkEq, hk]
  else
    have ha0 : a = 0 := (inv.depth_eq_zero_iff haSz).mp (by omega)
    have hSub : F.depthOf u - targetDepth = F.depthOf u := by omega
    rw [ha0, hSub, hF.iterParent_depthOf_eq_zero hu]

theorem ValidJumpForest.ancestorAtDepth_unique {F : JumpForest}
    (hF : ValidJumpForest F) {a u targetDepth : Nat}
    (hu : u < F.size) (hLe : targetDepth ≤ F.depthOf u) :
    (IsAncestor F a u ∧ F.depthOf a = targetDepth) ↔
      a = F.ancestorAtDepth u targetDepth := by
  let ⟨_, hAncRes, hDepRes⟩ := hF.ancestorAtDepth_spec hu hLe
  constructor
  · intro ⟨hAncA, hDepA⟩
    have h1 := hF.ancestor_eq_iterParent_of_depth hu hAncA hLe hDepA
    have h2 := hF.ancestor_eq_iterParent_of_depth hu hAncRes hLe hDepRes
    exact Eq.trans h1 h2.symm
  · intro hEq
    rw [hEq]
    exact ⟨hAncRes, hDepRes⟩

/-- Requesting `targetDepth = 0` from any valid node `u < F.size` returns the artificial root `0`. -/
theorem ValidJumpForest.ancestorAtDepth_zero {F : JumpForest}
    (hF : ValidJumpForest F) {u : Nat} (hu : u < F.size) :
    F.ancestorAtDepth u 0 = 0 := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  exact ((hF.ancestorAtDepth_unique hu (Nat.zero_le _)).mp
    ⟨hF.zero_isAncestor hu, inv.root_depth⟩).symm

/-- `decideAncestor a u` returns `true` iff `a` is an inclusive tree ancestor of `u`. -/
theorem ValidJumpForest.decideAncestor_eq_true_iff {F : JumpForest}
    (hF : ValidJumpForest F) {a u : Nat} (_ha : a < F.size) (hu : u < F.size) :
    F.decideAncestor a u = true ↔ IsAncestor F a u := by
  unfold JumpForest.decideAncestor
  constructor
  · intro hTrue
    if hCond : F.depthOf a ≤ F.depthOf u ∧ F.ancestorAtDepth u (F.depthOf a) = a then
      let ⟨hLe, hEq⟩ := hCond
      let ⟨_, hAnc, _⟩ := hF.ancestorAtDepth_spec hu hLe
      rw [hEq] at hAnc
      exact hAnc
    else
      rw [ite_eq_right hCond] at hTrue
      cases hTrue
  · intro hAnc
    let ⟨k, hk⟩ := hAnc
    have hDepA : F.depthOf a = F.depthOf u - k := by
      rw [← hk]
      exact hF.depth_iterParent hu k
    have hLe : F.depthOf a ≤ F.depthOf u := by omega
    have hEqA : a = F.ancestorAtDepth u (F.depthOf a) :=
      (hF.ancestorAtDepth_unique hu hLe).mp ⟨⟨k, hk⟩, rfl⟩
    rw [ite_eq_left ⟨hLe, hEqA.symm⟩]

/-! ### Persistence of Ancestry and Traversal Across `Extends` and `appendLeaf` -/

namespace JumpForest.Extends

theorem stepToDepth_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (targetDepth : Nat) :
    F₂.stepToDepth u targetDepth = F₁.stepToDepth u targetDepth := by
  have hjSz : F₁.jumpOf u < F₁.size := hValid₁.jumpOf_lt_size hu
  unfold JumpForest.stepToDepth
  dsimp only
  rw [hExt.jumpOf_eq hu, hExt.depthOf_eq hjSz, hExt.parentOf_eq hu]

theorem stepMoveToDepth_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (targetDepth : Nat) :
    F₂.stepMoveToDepth u targetDepth = F₁.stepMoveToDepth u targetDepth := by
  have hjSz : F₁.jumpOf u < F₁.size := hValid₁.jumpOf_lt_size hu
  unfold JumpForest.stepMoveToDepth
  dsimp only
  rw [hExt.jumpOf_eq hu, hExt.depthOf_eq hjSz, hExt.parentOf_eq hu]

theorem traceMoves_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (targetDepth : Nat) :
    F₂.traceMoves u targetDepth = F₁.traceMoves u targetDepth := by
  have aux : ∀ (fuel w : Nat), w < F₁.size →
      F₂.traceMovesAux fuel w targetDepth = F₁.traceMovesAux fuel w targetDepth := by
    intro fuel
    induction fuel with
    | zero => intro _ _; rfl
    | succ _ ih =>
        intro w hw
        rw [JumpForest.traceMovesAux_succ, JumpForest.traceMovesAux_succ,
          hExt.depthOf_eq hw, hExt.stepMoveToDepth_eq hValid₁ hw targetDepth,
          hExt.stepToDepth_eq hValid₁ hw targetDepth]
        if hLt : targetDepth < F₁.depthOf w then
          rw [ite_eq_left hLt, ite_eq_left hLt]
          exact congrArg (List.cons _) (ih _ (hValid₁.stepToDepth_lt_size hw targetDepth))
        else
          rw [ite_eq_right hLt, ite_eq_right hLt]
  unfold JumpForest.traceMoves
  rw [hExt.depthOf_eq hu]
  exact aux (F₁.depthOf u - targetDepth) u hu

theorem traceVertices_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (targetDepth : Nat) :
    F₂.traceVertices u targetDepth = F₁.traceVertices u targetDepth := by
  have aux : ∀ (fuel w : Nat), w < F₁.size →
      F₂.traceVerticesAux fuel w targetDepth = F₁.traceVerticesAux fuel w targetDepth := by
    intro fuel
    induction fuel with
    | zero => intro _ _; rfl
    | succ _ ih =>
        intro w hw
        rw [JumpForest.traceVerticesAux_succ, JumpForest.traceVerticesAux_succ,
          hExt.depthOf_eq hw, hExt.stepToDepth_eq hValid₁ hw targetDepth]
        if hLt : targetDepth < F₁.depthOf w then
          rw [ite_eq_left hLt, ite_eq_left hLt]
          exact congrArg (List.cons w) (ih _ (hValid₁.stepToDepth_lt_size hw targetDepth))
        else
          rw [ite_eq_right hLt, ite_eq_right hLt]
  unfold JumpForest.traceVertices
  rw [hExt.depthOf_eq hu]
  exact aux (F₁.depthOf u - targetDepth) u hu

theorem ancestorAtDepth_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (targetDepth : Nat) :
    F₂.ancestorAtDepth u targetDepth = F₁.ancestorAtDepth u targetDepth := by
  have aux : ∀ (fuel w : Nat), w < F₁.size →
      F₂.ancestorAtDepthAux fuel w targetDepth = F₁.ancestorAtDepthAux fuel w targetDepth := by
    intro fuel
    induction fuel with
    | zero => intro _ _; rfl
    | succ _ ih =>
        intro w hw
        rw [JumpForest.ancestorAtDepthAux_succ, JumpForest.ancestorAtDepthAux_succ,
          hExt.depthOf_eq hw, hExt.stepToDepth_eq hValid₁ hw targetDepth]
        if hLt : targetDepth < F₁.depthOf w then
          rw [ite_eq_left hLt, ite_eq_left hLt]
          exact ih _ (hValid₁.stepToDepth_lt_size hw targetDepth)
        else
          rw [ite_eq_right hLt, ite_eq_right hLt]
  unfold JumpForest.ancestorAtDepth
  rw [hExt.depthOf_eq hu]
  exact aux (F₁.depthOf u - targetDepth) u hu

theorem iterParent_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) (k : Nat) :
    F₂.iterParent k u = F₁.iterParent k u := by
  induction k generalizing u with
  | zero => rfl
  | succ _ ih =>
      unfold JumpForest.iterParent
      rw [hExt.parentOf_eq hu]
      exact ih (hValid₁.parentOf_lt_size hu)

theorem isAncestor_iff {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {a u : Nat} (hu : u < F₁.size) :
    IsAncestor F₂ a u ↔ IsAncestor F₁ a u := by
  constructor
  · intro ⟨k, hk⟩
    rw [hExt.iterParent_eq hValid₁ hu k] at hk
    exact ⟨k, hk⟩
  · intro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hExt.iterParent_eq hValid₁ hu k]
    exact hk

theorem decideAncestor_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {a u : Nat} (ha : a < F₁.size) (hu : u < F₁.size) :
    F₂.decideAncestor a u = F₁.decideAncestor a u := by
  unfold JumpForest.decideAncestor
  rw [hExt.depthOf_eq ha, hExt.depthOf_eq hu, hExt.ancestorAtDepth_eq hValid₁ hu]

theorem realAncestorChain_eq {F₁ F₂ : JumpForest}
    (hValid₁ : ValidJumpForest F₁) (hExt : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.realAncestorChain u = F₁.realAncestorChain u := by
  have aux : ∀ (fuel w : Nat), w < F₁.size →
      F₂.realAncestorChainAux fuel w = F₁.realAncestorChainAux fuel w := by
    intro fuel
    induction fuel with
    | zero => intro _ _; rfl
    | succ _ ih =>
        intro w hw
        rw [JumpForest.realAncestorChainAux_succ, JumpForest.realAncestorChainAux_succ]
        if hw0 : w = 0 then
          rw [ite_eq_left hw0, ite_eq_left hw0]
        else
          rw [ite_eq_right hw0, ite_eq_right hw0, hExt.parentOf_eq hw]
          exact congrArg (List.cons w) (ih _ (hValid₁.parentOf_lt_size hw))
  unfold JumpForest.realAncestorChain
  rw [hExt.depthOf_eq hu]
  exact aux (F₁.depthOf u) u hu

end JumpForest.Extends

theorem traceMoves_appendLeaf_old {F : JumpForest} (hF : ValidJumpForest F)
    {p u : Nat} (hp : p < F.size) (hu : u < F.size) (targetDepth : Nat) :
    (F.appendLeaf p).traceMoves u targetDepth = F.traceMoves u targetDepth :=
  (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).traceMoves_eq hF hu targetDepth

theorem ancestorAtDepth_appendLeaf_old {F : JumpForest} (hF : ValidJumpForest F)
    {p u : Nat} (hp : p < F.size) (hu : u < F.size) (targetDepth : Nat) :
    (F.appendLeaf p).ancestorAtDepth u targetDepth = F.ancestorAtDepth u targetDepth :=
  (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).ancestorAtDepth_eq hF hu targetDepth

theorem isAncestor_appendLeaf_old {F : JumpForest} (hF : ValidJumpForest F)
    {p a u : Nat} (hp : p < F.size) (hu : u < F.size) :
    IsAncestor (F.appendLeaf p) a u ↔ IsAncestor F a u :=
  (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).isAncestor_iff hF hu

theorem decideAncestor_appendLeaf_old {F : JumpForest} (hF : ValidJumpForest F)
    {p a u : Nat} (hp : p < F.size) (ha : a < F.size) (hu : u < F.size) :
    (F.appendLeaf p).decideAncestor a u = F.decideAncestor a u :=
  (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).decideAncestor_eq hF ha hu

/-! ### Checkpoint 2/2: Half-Block Descent, `ceilLog2`, Uniform `3 * L` Move Bound,
    `RecordOp` Cost Transcripts, and Explicit `EX0.3` Word-RAM Bridge -/

private theorem ite_true2 {α : Type} {P : Prop} [inst : Decidable P] (h : P) (a b : α) :
    (if P then a else b) = a := by
  cases inst with
  | isFalse hNot => exact False.elim (hNot h)
  | isTrue _ => rfl

private theorem ite_false2 {α : Type} {P : Prop} [inst : Decidable P] (h : ¬ P) (a b : α) :
    (if P then a else b) = b := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hYes => exact False.elim (h hYes)

private theorem nat_mul_le_mul_right2 (c : Nat) {a b : Nat} (h : a ≤ b) :
    a * c ≤ b * c := by
  induction c with
  | zero =>
      change 0 ≤ 0
      exact Nat.le_refl 0
  | succ k ih =>
      change a * k + a ≤ b * k + b
      omega

/-- Stepping to `parentOf u` from the head of a compound block `(k' + 1) :: rest` (`1 ≤ k'`)
    exposes two equal child blocks `k' :: k' :: rest` of size `2^k' - 1`. -/
theorem ForestInvariant.parent_exps_of_succ {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u k' : Nat} {rest : List Nat}
    (hu : u < F.size) (hk' : 1 ≤ k') (hExpsU : exps u = (k' + 1) :: rest) :
    exps (F.parentOf u) = k' :: k' :: rest := by
  have hPos : 0 < u := by
    if hP : 0 < u then exact hP
    else
      have hu0 : u = 0 := by omega
      have hRoot0 : exps 0 = [] := ((inv.nodes 0 inv.size_pos).root_spec rfl).2
      rw [hu0, hRoot0] at hExpsU
      cases hExpsU
  have hPush : skewPush (exps (F.parentOf u)) = (k' + 1) :: rest := by
    rw [← (inv.nodes u hu).pos_exps_eq hPos]
    exact hExpsU
  cases hExpsP : exps (F.parentOf u) with
  | nil =>
      rw [hExpsP] at hPush
      dsimp only [skewPush] at hPush
      have hHead : 1 = k' + 1 := (List.cons.inj hPush).1
      omega
  | cons x₁ tl1 =>
      cases tl1 with
      | nil =>
          rw [hExpsP] at hPush
          dsimp only [skewPush] at hPush
          have hHead : 1 = k' + 1 := (List.cons.inj hPush).1
          omega
      | cons x₂ tl2 =>
          rw [hExpsP] at hPush
          dsimp only [skewPush] at hPush
          if hEqX : x₁ = x₂ then
            rw [ite_true2 hEqX] at hPush
            have hHead : x₁ + 1 = k' + 1 := (List.cons.inj hPush).1
            have hTail : tl2 = rest := (List.cons.inj hPush).2
            have hx₁ : x₁ = k' := by omega
            have hx₂ : x₂ = k' := by omega
            rw [hx₁, hx₂, hTail]
          else
            rw [ite_false2 hEqX] at hPush
            have hHead : 1 = k' + 1 := (List.cons.inj hPush).1
            omega

/-- Within a single block of size `2^k - 1` (`blockSum rest < targetDepth`), one `parent`
    step plus at most one child-block `jump` halves the remaining block size, using at most
    `2 * (k - 1)` moves in total. -/
theorem ForestInvariant.within_block_moves_le {F : JumpForest} {exps : Nat → List Nat}
    (hF : ValidJumpForest F) (inv : ForestInvariant F exps) {targetDepth : Nat} :
    ∀ (k u : Nat) (rest : List Nat),
      1 ≤ k → u < F.size → exps u = k :: rest →
      blockSum rest < targetDepth →
      (F.traceMoves u targetDepth).length ≤ 2 * (k - 1) := by
  intro k
  induction k with
  | zero =>
      intro _ _ hk
      omega
  | succ k' ih =>
      intro u rest _ hu hExpsU hAbove
      if hGe : F.depthOf u ≤ targetDepth then
        rw [traceMoves_of_ge F hGe]
        simp only [List.length_nil]
        omega
      else
        have hLt : targetDepth < F.depthOf u := by omega
        if hk'Pos : 1 ≤ k' then
          have specU := inv.nodes u hu
          have hExpsJ : exps (F.jumpOf u) = rest :=
            specU.jump_exps (k' + 1) rest hExpsU
          have specJ := inv.nodes (F.jumpOf u) specU.jump_lt_size
          have hDJ : F.depthOf (F.jumpOf u) = blockSum rest := by
            rw [specJ.depth_eq_blockSum, hExpsJ]
          have hNotJump : ¬ (targetDepth ≤ F.depthOf (F.jumpOf u)) := by omega
          have hStepP : F.stepToDepth u targetDepth = F.parentOf u := by
            unfold JumpForest.stepToDepth
            dsimp only
            exact ite_false2 hNotJump _ _
          have hTraceU := hF.traceMoves_of_lt hu hLt
          rw [hStepP] at hTraceU
          have hp : F.parentOf u < F.size := specU.parent_lt_size
          have hExpsP : exps (F.parentOf u) = k' :: k' :: rest :=
            inv.parent_exps_of_succ hu hk'Pos hExpsU
          if hAboveLeft : blockSum (k' :: rest) < targetDepth then
            have hIH := ih (F.parentOf u) (k' :: rest) hk'Pos hp hExpsP hAboveLeft
            rw [hTraceU]
            simp only [List.length_cons]
            omega
          else
            have specP := inv.nodes (F.parentOf u) hp
            have ha : F.jumpOf (F.parentOf u) < F.size := specP.jump_lt_size
            have hExpsA : exps (F.jumpOf (F.parentOf u)) = k' :: rest :=
              specP.jump_exps k' (k' :: rest) hExpsP
            have specA := inv.nodes (F.jumpOf (F.parentOf u)) ha
            have hDA : F.depthOf (F.jumpOf (F.parentOf u)) = blockSum (k' :: rest) := by
              rw [specA.depth_eq_blockSum, hExpsA]
            have hDP : F.depthOf (F.parentOf u) =
                blockSize k' + blockSum (k' :: rest) := by
              rw [specP.depth_eq_blockSum, hExpsP]
              rfl
            have hBPos : 0 < blockSize k' := blockSize_pos hk'Pos
            have hJumpP : targetDepth ≤ F.depthOf (F.jumpOf (F.parentOf u)) := by omega
            have hLtP : targetDepth < F.depthOf (F.parentOf u) := by omega
            have hStepA : F.stepToDepth (F.parentOf u) targetDepth =
                F.jumpOf (F.parentOf u) := by
              unfold JumpForest.stepToDepth
              dsimp only
              exact ite_true2 hJumpP _ _
            have hTraceP := hF.traceMoves_of_lt hp hLtP
            rw [hStepA] at hTraceP
            have hIH := ih (F.jumpOf (F.parentOf u)) rest hk'Pos ha hExpsA hAbove
            rw [hTraceU, hTraceP]
            simp only [List.length_cons]
            omega
        else
          have hk'0 : k' = 0 := by omega
          subst hk'0
          have hDU : F.depthOf u = 1 + blockSum rest := by
            rw [(inv.nodes u hu).depth_eq_blockSum, hExpsU]
            rfl
          omega

/-- Combining whole-block jumps along `ks = exps u` with at most one within-block descent. -/
theorem ForestInvariant.traceMoves_le_length_plus {F : JumpForest} {exps : Nat → List Nat}
    (hF : ValidJumpForest F) (inv : ForestInvariant F exps) (M targetDepth : Nat) :
    ∀ (ks : List Nat) (u : Nat),
      u < F.size → exps u = ks →
      AllList (fun k => k ≤ M + 1) ks →
      (F.traceMoves u targetDepth).length ≤ ks.length + 2 * M := by
  intro ks
  induction ks with
  | nil =>
      intro u hu hExpsU _
      have hD0 : F.depthOf u = 0 := by
        rw [(inv.nodes u hu).depth_eq_blockSum, hExpsU]
        rfl
      rw [traceMoves_of_ge F (by omega)]
      simp only [List.length_nil]
      omega
  | cons k rest ih =>
      intro u hu hExpsU hBound
      if hGe : F.depthOf u ≤ targetDepth then
        rw [traceMoves_of_ge F hGe]
        simp only [List.length_nil]
        omega
      else
        have hLt : targetDepth < F.depthOf u := by omega
        have specU := inv.nodes u hu
        have hkPos : 1 ≤ k := by
          have hAllPos := specU.exps_pos
          rw [hExpsU] at hAllPos
          exact hAllPos.1
        have hkBound : k ≤ M + 1 := hBound.1
        have hRestBound : AllList (fun x => x ≤ M + 1) rest := hBound.2
        have hExpsJ : exps (F.jumpOf u) = rest := specU.jump_exps k rest hExpsU
        have hjSz : F.jumpOf u < F.size := specU.jump_lt_size
        if hJump : targetDepth ≤ F.depthOf (F.jumpOf u) then
          have hStepJ : F.stepToDepth u targetDepth = F.jumpOf u := by
            unfold JumpForest.stepToDepth
            dsimp only
            exact ite_true2 hJump _ _
          have hTraceU := hF.traceMoves_of_lt hu hLt
          rw [hStepJ] at hTraceU
          have hIH := ih (F.jumpOf u) hjSz hExpsJ hRestBound
          rw [hTraceU]
          simp only [List.length_cons]
          omega
        else
          have hDJ : F.depthOf (F.jumpOf u) = blockSum rest := by
            rw [(inv.nodes (F.jumpOf u) hjSz).depth_eq_blockSum, hExpsJ]
          have hAbove : blockSum rest < targetDepth := by omega
          have hWithin :=
            inv.within_block_moves_le hF k u rest hkPos hu hExpsU hAbove
          simp only [List.length_cons]
          omega

private theorem allList_ge_mono {a b : Nat} (hab : a ≤ b) :
    ∀ {ks : List Nat}, AllList (fun x => b ≤ x) ks → AllList (fun x => a ≤ x) ks
  | [], _ => trivial
  | _ :: _, h => ⟨Nat.le_trans hab h.1, allList_ge_mono hab h.2⟩

private theorem strictlyIncreasing_ge_head :
    ∀ (y : Nat) (rest : List Nat),
      StrictlyIncreasing (y :: rest) → AllList (fun z => y ≤ z) (y :: rest)
  | y, [], _ => ⟨Nat.le_refl y, trivial⟩
  | y, z :: tl, hS => by
      have hyz : y ≤ z := Nat.le_of_lt hS.1
      have hTail : AllList (fun w => z ≤ w) (z :: tl) :=
        strictlyIncreasing_ge_head z tl hS.2
      exact ⟨Nat.le_refl y, allList_ge_mono hyz hTail⟩

theorem strictlyIncreasing_length_le_sub {hi : Nat} :
    ∀ (ks : List Nat) (lo : Nat),
      StrictlyIncreasing ks →
      AllList (fun x => lo ≤ x) ks →
      AllList (fun x => x < hi) ks →
      ks.length ≤ hi - lo
  | [], _, _, _, _ => by
      simp only [List.length_nil]
      omega
  | [x], lo, _, hLo, hHi => by
      have h1 : lo ≤ x := hLo.1
      have h2 : x < hi := hHi.1
      simp only [List.length_cons, List.length_nil]
      omega
  | x :: y :: rest, lo, hS, hLo, hHi => by
      have hxLo : lo ≤ x := hLo.1
      have hxy : x < y := hS.1
      have hSuccLe : x + 1 ≤ y := by omega
      have hTailS : StrictlyIncreasing (y :: rest) := hS.2
      have hYHi : y < hi := hHi.2.1
      have hTailHi : AllList (fun z => z < hi) (y :: rest) := hHi.2
      have hGeY : AllList (fun z => y ≤ z) (y :: rest) :=
        strictlyIncreasing_ge_head y rest hTailS
      have hGeSuccX : AllList (fun z => x + 1 ≤ z) (y :: rest) :=
        allList_ge_mono hSuccLe hGeY
      have hIH : (y :: rest).length ≤ hi - (x + 1) :=
        strictlyIncreasing_length_le_sub (y :: rest) (x + 1) hTailS hGeSuccX hTailHi
      simp only [List.length_cons] at hIH ⊢
      omega

theorem skewIncreasing_length_le {ks : List Nat} {L : Nat}
    (hL : 1 ≤ L)
    (hSkew : SkewIncreasing ks)
    (hPos : AllList (fun x => 1 ≤ x) ks)
    (hLt : AllList (fun x => x < L) ks) :
    ks.length ≤ L := by
  cases hSkew with
  | inl hS =>
      have hSub := strictlyIncreasing_length_le_sub ks 1 hS hPos hLt
      omega
  | inr hTie =>
      let ⟨k, rest, hEq, hST⟩ := hTie
      rw [hEq] at hPos hLt ⊢
      have hTailPos : AllList (fun x => 1 ≤ x) (k :: rest) := hPos.2
      have hTailLt : AllList (fun x => x < L) (k :: rest) := hLt.2
      have hSub := strictlyIncreasing_length_le_sub (k :: rest) 1 hST hTailPos hTailLt
      simp only [List.length_cons] at hSub ⊢
      omega

theorem allList_lt_of_blockSum_le {n L : Nat} (hPow : n + 2 ≤ 2 ^ L) :
    ∀ (ks : List Nat), blockSum ks ≤ n → AllList (fun k => k < L) ks
  | [], _ => trivial
  | k :: rest, hSum => by
      dsimp only [blockSum] at hSum
      have hBk : blockSize k ≤ n := by omega
      have hRest : blockSum rest ≤ n := by omega
      have hPosPow : 0 < 2 ^ k := pow2_pos k
      have hPowK : 2 ^ k < 2 ^ L := by
        unfold blockSize at hBk
        omega
      exact ⟨lt_of_pow2_lt hPowK, allList_lt_of_blockSum_le hPow rest hRest⟩

private theorem allList_le_of_lt {L : Nat} (hL2 : 2 ≤ L) :
    ∀ {ks : List Nat},
      AllList (fun k => k < L) ks → AllList (fun k => k ≤ (L - 2) + 1) ks
  | [], _ => trivial
  | _ :: _, h => by
      have hk := h.1
      exact ⟨by omega, allList_le_of_lt hL2 h.2⟩

/-- Ceiling base-2 logarithm helper loop with structural fuel. -/
def ceilLog2Loop : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, m, acc =>
      if m ≤ 2 ^ acc then acc else ceilLog2Loop fuel m (acc + 1)

theorem ceilLog2Loop_zero (m acc : Nat) :
    ceilLog2Loop 0 m acc = acc := rfl

theorem ceilLog2Loop_succ (fuel m acc : Nat) :
    ceilLog2Loop (fuel + 1) m acc =
      if m ≤ 2 ^ acc then acc else ceilLog2Loop fuel m (acc + 1) := rfl

/-- Exact ceiling base-2 logarithm `⌈log₂ m⌉` (`0` for `m ≤ 1`, least `L` with `m ≤ 2 ^ L`). -/
def ceilLog2 (m : Nat) : Nat :=
  ceilLog2Loop m m 0

private theorem id_le_pow2 (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hPos := pow2_pos k
      have hStep := pow2_succ k
      omega

theorem pow2_ceilLog2_ge (m : Nat) : m ≤ 2 ^ ceilLog2 m := by
  have aux : ∀ (fuel acc : Nat), m ≤ acc + fuel →
      m ≤ 2 ^ ceilLog2Loop fuel m acc := by
    intro fuel
    induction fuel with
    | zero =>
        intro acc hB
        rw [ceilLog2Loop_zero]
        have hLe : m ≤ acc := by omega
        exact Nat.le_trans hLe (id_le_pow2 acc)
    | succ f ih =>
        intro acc hB
        rw [ceilLog2Loop_succ]
        if hLe : m ≤ 2 ^ acc then
          rw [ite_true2 hLe]
          exact hLe
        else
          rw [ite_false2 hLe]
          exact ih (acc + 1) (by omega)
  exact aux m 0 (by omega)

theorem ceilLog2_le_of_pow2_ge {m L : Nat} (hPow : m ≤ 2 ^ L) :
    ceilLog2 m ≤ L := by
  have aux : ∀ (fuel acc : Nat), acc ≤ L →
      ceilLog2Loop fuel m acc ≤ L := by
    intro fuel
    induction fuel with
    | zero =>
        intro acc hAcc
        rw [ceilLog2Loop_zero]
        exact hAcc
    | succ f ih =>
        intro acc hAcc
        rw [ceilLog2Loop_succ]
        if hLe : m ≤ 2 ^ acc then
          rw [ite_true2 hLe]
          exact hAcc
        else
          rw [ite_false2 hLe]
          have hAccLt : acc < L := by
            if hEq : acc = L then
              rw [hEq] at hLe
              exact False.elim (hLe hPow)
            else
              omega
          exact ih (acc + 1) (by omega)
  exact aux m 0 (Nat.zero_le L)

theorem ceilLog2_le_iff {m L : Nat} : ceilLog2 m ≤ L ↔ m ≤ 2 ^ L := by
  constructor
  · intro hLe
    have hBase := pow2_ceilLog2_ge m
    if hEq : ceilLog2 m = L then
      rw [← hEq]
      exact hBase
    else
      have hLt : ceilLog2 m < L := by omega
      exact Nat.le_trans hBase (Nat.le_of_lt (pow2_strictMono hLt))
  · exact ceilLog2_le_of_pow2_ge

/-- Uniform `O(L)` move bound (Paper B v1.3, Lemma 3.2): whenever `F.numInserted ≤ n` and
    `n + 2 ≤ 2 ^ L`, every depth-target traversal from `u < F.size` uses at most `3 * L` moves. -/
theorem traceMoves_length_le_of_bound {F : JumpForest} (hF : ValidJumpForest F)
    {u n L : Nat} (hu : u < F.size)
    (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L)
    (targetDepth : Nat) :
    (F.traceMoves u targetDepth).length ≤ 3 * L := by
  let ⟨exps, inv⟩ := hF.exists_forestInvariant
  if hL0 : L = 0 then
    rw [hL0] at hPow
    change n + 2 ≤ 1 at hPow
    omega
  else if hL1 : L = 1 then
    rw [hL1] at hPow ⊢
    change n + 2 ≤ 2 at hPow
    have hn0 : n = 0 := by omega
    have hSzPos : 0 < F.size := inv.size_pos
    have hNumEq : F.numInserted = F.size - 1 := rfl
    have hSz1 : F.size = 1 := by omega
    have hu0 : u = 0 := by omega
    rw [hu0]
    have hD0 : F.depthOf 0 = 0 := inv.root_depth
    rw [traceMoves_of_ge F (by omega)]
    simp only [List.length_nil]
    omega
  else
    have hL2 : 2 ≤ L := by omega
    have hDepLeSelf : F.depthOf u ≤ u := inv.depthOf_le_self hu
    have hNumEq : F.numInserted = F.size - 1 := rfl
    have hDepLeN : F.depthOf u ≤ n := by omega
    have specU := inv.nodes u hu
    have hSumLeN : blockSum (exps u) ≤ n := by
      rw [← specU.depth_eq_blockSum]
      exact hDepLeN
    have hLtL : AllList (fun k => k < L) (exps u) :=
      allList_lt_of_blockSum_le hPow (exps u) hSumLeN
    have hBoundM : AllList (fun k => k ≤ (L - 2) + 1) (exps u) :=
      allList_le_of_lt hL2 hLtL
    have hLenLe : (exps u).length ≤ L :=
      skewIncreasing_length_le (by omega) specU.exps_skew specU.exps_pos hLtL
    have hMoves :=
      inv.traceMoves_le_length_plus hF (L - 2) targetDepth (exps u) u hu rfl hBoundM
    omega

/-- Concrete `ceilLog2` specialization: `≤ 3 * ceilLog2 (n + 2)` moves for `F.numInserted ≤ n`. -/
theorem traceMoves_length_le_ceilLog2 {F : JumpForest} (hF : ValidJumpForest F)
    {u n : Nat} (hu : u < F.size) (hInserted : F.numInserted ≤ n)
    (targetDepth : Nat) :
    (F.traceMoves u targetDepth).length ≤ 3 * ceilLog2 (n + 2) :=
  traceMoves_length_le_of_bound hF hu hInserted (pow2_ceilLog2_ge (n + 2)) targetDepth

/-- Quotient specialization for `H : LabelledQuotient` (`F.numInserted ≤ H.vertexCount`). -/
theorem traceMoves_length_le_for_quotient (H : LabelledQuotient)
    {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (hNodes : F.numInserted ≤ H.vertexCount)
    (targetDepth : Nat) :
    (F.traceMoves u targetDepth).length ≤ 3 * ceilLog2 (H.vertexCount + 2) :=
  traceMoves_length_le_ceilLog2 hF hu hNodes targetDepth

theorem traceVertices_length (F : JumpForest) (u targetDepth : Nat) :
    (F.traceVertices u targetDepth).length =
      (F.traceMoves u targetDepth).length + 1 := by
  have aux : ∀ (fuel w : Nat),
      (F.traceVerticesAux fuel w targetDepth).length =
        (F.traceMovesAux fuel w targetDepth).length + 1 := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ _ ih =>
        intro w
        rw [JumpForest.traceVerticesAux_succ, JumpForest.traceMovesAux_succ]
        if hLt : targetDepth < F.depthOf w then
          rw [ite_true2 hLt, ite_true2 hLt]
          simp only [List.length_cons]
          exact congrArg (· + 1) (ih (F.stepToDepth w targetDepth))
        else
          rw [ite_false2 hLt, ite_false2 hLt]
          rfl
  exact aux (F.depthOf u - targetDepth) u

/-! ### Record-Operation Transcripts, Word-Range Bounds, and `EX0.3` Word-RAM Bridge -/

/-- Primitive indexed record-store operation (`O(1)` slot read or end-of-array append). -/
inductive RecordOp where
  | read (idx : Nat)
  | append (rec : JumpRecord)
  deriving DecidableEq, Repr

namespace JumpForest

/-- Exact `4`-operation `RecordOp` transcript of `F.appendLeaf p`:
    `3` record reads (`p`, `a = jump(p)`, `b = jump(a)`) and `1` record append. -/
def appendLeafOps (F : JumpForest) (p : Nat) : List RecordOp :=
  let recP := F.recordAt p
  let a := recP.jump
  let recA := F.recordAt a
  let b := recA.jump
  [RecordOp.read p, RecordOp.read a, RecordOp.read b,
   RecordOp.append (F.mkAppendedRecord p)]

/-- Record reads performed during a single `JumpMove`. -/
def stepReadOps (F : JumpForest) : JumpMove → List RecordOp
  | JumpMove.jump _ dst => [RecordOp.read dst]
  | JumpMove.parent src dst => [RecordOp.read (F.jumpOf src), RecordOp.read dst]

def movesReadOps (F : JumpForest) : List JumpMove → List RecordOp
  | [] => []
  | m :: ms => F.stepReadOps m ++ F.movesReadOps ms

theorem movesReadOps_nil (F : JumpForest) :
    F.movesReadOps [] = [] := rfl

theorem movesReadOps_cons (F : JumpForest) (m : JumpMove) (ms : List JumpMove) :
    F.movesReadOps (m :: ms) = F.stepReadOps m ++ F.movesReadOps ms := rfl

/-- Record-read transcript for `F.ancestorAtDepth u targetDepth`:
    initial read of `u` plus at most two reads per move along `traceMoves`. -/
def traceReadOps (F : JumpForest) (u targetDepth : Nat) : List RecordOp :=
  RecordOp.read u :: F.movesReadOps (F.traceMoves u targetDepth)

end JumpForest

/-- Every `appendLeaf` insertion performs exactly `4` primitive record operations. -/
theorem appendLeafOps_length (F : JumpForest) (p : Nat) :
    (F.appendLeafOps p).length = 4 := rfl

/-- Retained record count is linear: `n + 1` triples (`JumpRecord`s) after `n` insertions. -/
theorem retained_records_eq {F : JumpForest} (hF : ValidJumpForest F) :
    F.records.length = F.numInserted + 1 := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have hPos : 0 < F.records.length := inv.size_pos
  have hNum : F.numInserted = F.records.length - 1 := rfl
  omega

private theorem movesReadOps_length_le (F : JumpForest) :
    ∀ (ms : List JumpMove), (F.movesReadOps ms).length ≤ 2 * ms.length
  | [] => by
      rw [JumpForest.movesReadOps_nil]
      simp only [List.length_nil]
      omega
  | m :: ms => by
      rw [JumpForest.movesReadOps_cons]
      have hIH := movesReadOps_length_le F ms
      cases m with
      | jump _ dst =>
          change (RecordOp.read dst :: F.movesReadOps ms).length ≤ 2 * (ms.length + 1)
          simp only [List.length_cons]
          omega
      | parent src dst =>
          change (RecordOp.read (F.jumpOf src) :: RecordOp.read dst ::
            F.movesReadOps ms).length ≤ 2 * (ms.length + 1)
          simp only [List.length_cons]
          omega

/-- Every depth-target traversal reads at most `6 * L + 1` records when `n + 2 ≤ 2 ^ L`. -/
theorem traceReadOps_length_le {F : JumpForest} (hF : ValidJumpForest F)
    {u n L : Nat} (hu : u < F.size)
    (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L)
    (targetDepth : Nat) :
    (F.traceReadOps u targetDepth).length ≤ 6 * L + 1 := by
  unfold JumpForest.traceReadOps
  simp only [List.length_cons]
  have hM := movesReadOps_length_le F (F.traceMoves u targetDepth)
  have hT := traceMoves_length_le_of_bound hF hu hInserted hPow targetDepth
  omega

/-- All stored scalar fields (`parent`, `depth`, `jump`) are bounded by `F.numInserted`,
    and `depthOf (jumpOf u) ≤ depthOf u` ensures non-underflowing depth subtractions. -/
theorem record_fields_bounded {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) :
    (F.recordAt u).parent ≤ F.numInserted ∧
      (F.recordAt u).depth ≤ F.numInserted ∧
      (F.recordAt u).jump ≤ F.numInserted ∧
      F.depthOf (F.jumpOf u) ≤ F.depthOf u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have specU := inv.nodes u hu
  have hParSz : F.parentOf u < F.size := specU.parent_lt_size
  have hJmpSz : F.jumpOf u < F.size := specU.jump_lt_size
  have hDepLe : F.depthOf u ≤ u := inv.depthOf_le_self hu
  have hNumEq : F.numInserted = F.size - 1 := rfl
  have hDJLe : F.depthOf (F.jumpOf u) ≤ F.depthOf u := by
    if hPos : 0 < u then
      exact Nat.le_of_lt (inv.depth_jump_lt hPos hu)
    else
      have hu0 : u = 0 := by omega
      rw [hu0, inv.root_jump]
      exact Nat.le_refl _
  have hParEq : (F.recordAt u).parent = F.parentOf u := rfl
  have hDepEq : (F.recordAt u).depth = F.depthOf u := rfl
  have hJmpEq : (F.recordAt u).jump = F.jumpOf u := rfl
  rw [hParEq, hDepEq, hJmpEq]
  exact ⟨by omega, by omega, by omega, hDJLe⟩

theorem record_fields_lt_pow2 {F : JumpForest} (hF : ValidJumpForest F)
    {u n W : Nat} (hu : u < F.size)
    (hInserted : F.numInserted ≤ n) (hWord : n + 2 ≤ 2 ^ W) :
    F.size < 2 ^ W ∧
      (F.recordAt u).parent < 2 ^ W ∧
      (F.recordAt u).depth < 2 ^ W ∧
      (F.recordAt u).jump < 2 ^ W := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  have hPos : 0 < F.size := inv.size_pos
  have hNumEq : F.numInserted = F.size - 1 := rfl
  let ⟨hP, hD, hJ, _⟩ := record_fields_bounded hF hu
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Explicit `EX0.3` (`PaperB.Machine`) Word-RAM bridge contract required to translate
    abstract `RecordOp` counts and bounded `Nat` arithmetic (`< 2 ^ wordWidth`) on
    `JumpForest` into physical Word-RAM instruction and word counts:
    1. Flat preallocated/resizable array layout of `JumpRecord` triples (`wordsPerRecord`
       words per slot plus `headerWords` header words) up to `maxNodes + 1` records.
    2. `O(1)` (`costPerRead`) `wordWidth`-bit Word-RAM instructions per in-bounds record read.
    3. `O(1)` (`costPerAppend`) `wordWidth`-bit Word-RAM instructions per leaf-record
       computation (two non-underflowing subtractions, comparisons, increment) and slot write. -/
structure WordRamRecordBridge where
  wordWidth : Nat
  maxNodes : Nat
  wordCapacity : maxNodes + 2 ≤ 2 ^ wordWidth
  costPerRead : Nat
  costPerAppend : Nat
  wordsPerRecord : Nat
  headerWords : Nat

/-- Conditional Word-RAM cost theorem given an `EX0.3` `WordRamRecordBridge`:
    every stored field fits strictly in `wordWidth` bits (`< 2 ^ wordWidth`), each
    `appendLeaf` costs `3 * costPerRead + costPerAppend` (`O(1)`), retained storage is
    `headerWords + wordsPerRecord * (F.numInserted + 1)` words (`O(n)`), and every
    depth-target query costs at most `(6 * L + 1) * costPerRead` (`O(L)`). -/
theorem ram_cost_of_bridge (B : WordRamRecordBridge)
    {F : JumpForest} (hF : ValidJumpForest F)
    (hCap : F.numInserted ≤ B.maxNodes)
    {u : Nat} (hu : u < F.size) (p targetDepth : Nat) :
    let L := ceilLog2 (B.maxNodes + 2)
    (F.size < 2 ^ B.wordWidth ∧
      (F.recordAt u).parent < 2 ^ B.wordWidth ∧
      (F.recordAt u).depth < 2 ^ B.wordWidth ∧
      (F.recordAt u).jump < 2 ^ B.wordWidth) ∧
    (F.appendLeafOps p).length = 4 ∧
    F.records.length = F.numInserted + 1 ∧
    (F.traceReadOps u targetDepth).length * B.costPerRead ≤
      (6 * L + 1) * B.costPerRead := by
  intro L
  have hFields := record_fields_lt_pow2 hF hu hCap B.wordCapacity
  have hReadLen : (F.traceReadOps u targetDepth).length ≤ 6 * L + 1 :=
    traceReadOps_length_le hF hu hCap (pow2_ceilLog2_ge (B.maxNodes + 2)) targetDepth
  exact ⟨hFields, appendLeafOps_length F p, retained_records_eq hF,
    nat_mul_le_mul_right2 B.costPerRead hReadLen⟩

/-! ### `EX0.3` Concrete `Array Nat` Word-Address / Read / Write Realization (Part 1/2:
    Flat Region Layout, `initWords`, `readRecordWords`, `appendLeafWords`, and Frame) -/

private theorem dite_true {α : Type} {P : Prop} [inst : Decidable P]
    (h : P) (t : P → α) (e : ¬ P → α) :
    (if hp : P then t hp else e hp) = t h := by
  cases inst with
  | isFalse hNot => exact False.elim (hNot h)
  | isTrue _ => rfl

private theorem dite_false {α : Type} {P : Prop} [inst : Decidable P]
    (h : ¬ P) (t : P → α) (e : ¬ P → α) :
    (if hp : P then t hp else e hp) = e h := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hYes => exact False.elim (h hYes)

private theorem jumpRecord_ext {r₁ r₂ : JumpRecord}
    (hp : r₁.parent = r₂.parent) (hd : r₁.depth = r₂.depth) (hj : r₁.jump = r₂.jump) :
    r₁ = r₂ := by
  cases r₁ with
  | mk p₁ d₁ j₁ =>
      cases r₂ with
      | mk p₂ d₂ j₂ =>
          dsimp only at hp hd hj
          rw [hp, hd, hj]

private theorem array_size_set (mem : Array Nat) (addr val : Nat)
    (h : addr < mem.size) :
    (mem.set addr val h).size = mem.size := by
  simp

private theorem array_getElem_set_self (mem : Array Nat) (addr val : Nat)
    (h : addr < mem.size) (h' : addr < (mem.set addr val h).size) :
    (mem.set addr val h)[addr]'h' = val := by
  simp

private theorem array_getElem_set_ne (mem : Array Nat) (addr val j : Nat)
    (h : addr < mem.size) (hj : j < mem.size)
    (hj' : j < (mem.set addr val h).size) (hne : addr ≠ j) :
    (mem.set addr val h)[j]'hj' = mem[j]'hj := by
  simp [Array.getElem_set, hne]

/-- Concrete word-memory read on `Array Nat` (in-bounds `mem[addr]`, `0` out-of-bounds). -/
def readWord (mem : Array Nat) (addr : Nat) : Nat :=
  if h : addr < mem.size then mem[addr]'h else 0

/-- Concrete word-memory write on `Array Nat` (in-bounds `mem.set addr val h`). -/
def writeWord (mem : Array Nat) (addr val : Nat) : Array Nat :=
  if h : addr < mem.size then mem.set addr val h else mem

theorem readWord_of_lt {mem : Array Nat} {addr : Nat} (h : addr < mem.size) :
    readWord mem addr = mem[addr]'h :=
  dite_true h _ _

theorem readWord_of_ge {mem : Array Nat} {addr : Nat} (h : ¬ addr < mem.size) :
    readWord mem addr = 0 :=
  dite_false h _ _

theorem writeWord_of_lt {mem : Array Nat} {addr val : Nat} (h : addr < mem.size) :
    writeWord mem addr val = mem.set addr val h :=
  dite_true h _ _

theorem writeWord_of_ge {mem : Array Nat} {addr val : Nat} (h : ¬ addr < mem.size) :
    writeWord mem addr val = mem :=
  dite_false h _ _

theorem writeWord_size (mem : Array Nat) (addr val : Nat) :
    (writeWord mem addr val).size = mem.size := by
  if h : addr < mem.size then
    rw [writeWord_of_lt h]
    exact array_size_set mem addr val h
  else
    rw [writeWord_of_ge h]

theorem readWord_writeWord_self {mem : Array Nat} {addr val : Nat}
    (h : addr < mem.size) :
    readWord (writeWord mem addr val) addr = val := by
  rw [writeWord_of_lt h]
  have h' : addr < (mem.set addr val h).size := by
    have hSz := array_size_set mem addr val h
    omega
  rw [readWord_of_lt h']
  exact array_getElem_set_self mem addr val h h'

theorem readWord_writeWord_ne (mem : Array Nat) (addr val j : Nat) (hne : addr ≠ j) :
    readWord (writeWord mem addr val) j = readWord mem j := by
  if h : addr < mem.size then
    rw [writeWord_of_lt h]
    if hj : j < mem.size then
      have hj' : j < (mem.set addr val h).size := by
        have hSz := array_size_set mem addr val h
        omega
      rw [readWord_of_lt hj', readWord_of_lt hj]
      exact array_getElem_set_ne mem addr val j h hj hj' hne
    else
      have hj' : ¬ j < (mem.set addr val h).size := by
        have hSz := array_size_set mem addr val h
        omega
      rw [readWord_of_ge hj', readWord_of_ge hj]
  else
    rw [writeWord_of_ge h]

theorem getElem_writeWord_ne {mem : Array Nat} {addr val j : Nat}
    (hj : j < mem.size) (hj' : j < (writeWord mem addr val).size) (hne : addr ≠ j) :
    (writeWord mem addr val)[j]'hj' = mem[j]'hj := by
  rw [← readWord_of_lt hj', ← readWord_of_lt hj]
  exact readWord_writeWord_ne mem addr val j hne

/-- Single word-level access event in flat `Array Nat` memory. -/
inductive WordAccess where
  | read (addr : Nat)
  | write (addr val : Nat)
  deriving DecidableEq, Repr

def WordAccess.addr : WordAccess → Nat
  | WordAccess.read a => a
  | WordAccess.write a _ => a

def AllAccessesInRegion (lo hi : Nat) : List WordAccess → Prop
  | [] => True
  | op :: ops => (lo ≤ op.addr ∧ op.addr < hi) ∧ AllAccessesInRegion lo hi ops

theorem allAccessesInRegion_append {lo hi : Nat} {xs ys : List WordAccess}
    (hx : AllAccessesInRegion lo hi xs) (hy : AllAccessesInRegion lo hi ys) :
    AllAccessesInRegion lo hi (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons _ _ ih => exact ⟨hx.1, ih hx.2⟩

/-- `W`-bit Word-RAM fit predicate: `mem.size ≤ 2 ^ W` and every cell `< 2 ^ W`. -/
structure WordMemFit (W : Nat) (mem : Array Nat) : Prop where
  size_le : mem.size ≤ 2 ^ W
  word_lt : ∀ (i : Nat) (hi : i < mem.size), mem[i]'hi < 2 ^ W

theorem WordMemFit.writeWord {W : Nat} {mem : Array Nat}
    (fit : WordMemFit W mem) {addr val : Nat}
    (_hAddr : addr < mem.size) (hVal : val < 2 ^ W) :
    WordMemFit W (PaperB.writeWord mem addr val) := by
  refine ⟨?_, ?_⟩
  · rw [writeWord_size]
    exact fit.size_le
  · intro i hi'
    have hi : i < mem.size := by
      have hSz := writeWord_size mem addr val
      omega
    rw [← readWord_of_lt hi']
    if hEq : addr = i then
      subst hEq
      rw [readWord_writeWord_self hi]
      exact hVal
    else
      rw [readWord_writeWord_ne mem addr val i hEq, readWord_of_lt hi]
      exact fit.word_lt i hi

/-- Reserved flat word region `[baseAddr, baseAddr + 1 + 3 * (maxNodes + 1))` for a
    `JumpForest` of capacity `maxNodes` (`baseAddr` stores `size`; slot `u` occupies
    `baseAddr + 1 + 3 * u + {0, 1, 2}` for `parent`, `depth`, `jump`). -/
structure JumpWordRegion where
  W : Nat
  baseAddr : Nat
  maxNodes : Nat
  wordCapacity : maxNodes + 2 ≤ 2 ^ W

namespace JumpWordRegion

def endAddr (R : JumpWordRegion) : Nat :=
  R.baseAddr + 1 + 3 * (R.maxNodes + 1)

def slotAddr (R : JumpWordRegion) (u : Nat) : Nat :=
  R.baseAddr + 1 + 3 * u

def parentAddr (R : JumpWordRegion) (u : Nat) : Nat :=
  R.slotAddr u

def depthAddr (R : JumpWordRegion) (u : Nat) : Nat :=
  R.slotAddr u + 1

def jumpAddr (R : JumpWordRegion) (u : Nat) : Nat :=
  R.slotAddr u + 2

theorem slot_addrs_inRegion (R : JumpWordRegion) {u : Nat} (hu : u ≤ R.maxNodes) :
    R.baseAddr < R.parentAddr u ∧
      R.parentAddr u < R.depthAddr u ∧
      R.depthAddr u < R.jumpAddr u ∧
      R.jumpAddr u < R.endAddr := by
  unfold parentAddr depthAddr jumpAddr slotAddr endAddr
  omega

end JumpWordRegion

/-- Representation invariant linking an abstract `F : JumpForest` to flat word memory `mem`. -/
structure JumpWordLayout (R : JumpWordRegion) (F : JumpForest) (mem : Array Nat) : Prop where
  valid : ValidJumpForest F
  inserted_le : F.numInserted ≤ R.maxNodes
  region_inBounds : R.endAddr ≤ mem.size
  mem_fit : WordMemFit R.W mem
  size_word : readWord mem R.baseAddr = F.size
  slot_parent : ∀ u : Nat, u < F.size → readWord mem (R.parentAddr u) = F.parentOf u
  slot_depth : ∀ u : Nat, u < F.size → readWord mem (R.depthAddr u) = F.depthOf u
  slot_jump : ∀ u : Nat, u < F.size → readWord mem (R.jumpAddr u) = F.jumpOf u

/-- Write the three fields `(parent, depth, jump)` of `rec` at slot `u` (`3` word writes). -/
def writeRecordWords (R : JumpWordRegion) (mem : Array Nat)
    (u : Nat) (rec : JumpRecord) : Array Nat × List WordAccess :=
  let aP := R.parentAddr u
  let aD := R.depthAddr u
  let aJ := R.jumpAddr u
  let mem1 := writeWord mem aP rec.parent
  let mem2 := writeWord mem1 aD rec.depth
  let mem3 := writeWord mem2 aJ rec.jump
  (mem3, [WordAccess.write aP rec.parent, WordAccess.write aD rec.depth,
    WordAccess.write aJ rec.jump])

theorem writeRecordWords_size (R : JumpWordRegion) (mem : Array Nat)
    (u : Nat) (rec : JumpRecord) :
    (writeRecordWords R mem u rec).1.size = mem.size := by
  unfold writeRecordWords
  dsimp only
  rw [writeWord_size, writeWord_size, writeWord_size]

theorem writeRecordWords_fit {R : JumpWordRegion} {mem : Array Nat}
    (fit : WordMemFit R.W mem) (hReg : R.endAddr ≤ mem.size)
    {u : Nat} (hu : u ≤ R.maxNodes) {rec : JumpRecord}
    (hP : rec.parent < 2 ^ R.W) (hD : rec.depth < 2 ^ R.W) (hJ : rec.jump < 2 ^ R.W) :
    WordMemFit R.W (writeRecordWords R mem u rec).1 := by
  have hB := R.slot_addrs_inRegion hu
  unfold writeRecordWords
  dsimp only
  have fit1 : WordMemFit R.W (writeWord mem (R.parentAddr u) rec.parent) :=
    fit.writeWord (by omega) hP
  have hSz1 : (writeWord mem (R.parentAddr u) rec.parent).size = mem.size :=
    writeWord_size _ _ _
  have fit2 : WordMemFit R.W
      (writeWord (writeWord mem (R.parentAddr u) rec.parent) (R.depthAddr u) rec.depth) :=
    fit1.writeWord (by omega) hD
  have hSz2 :
      (writeWord (writeWord mem (R.parentAddr u) rec.parent) (R.depthAddr u) rec.depth).size =
        mem.size := by
    rw [writeWord_size, hSz1]
  exact fit2.writeWord (by omega) hJ

theorem writeRecordWords_read_self {R : JumpWordRegion} {mem : Array Nat}
    (hReg : R.endAddr ≤ mem.size) {u : Nat} (hu : u ≤ R.maxNodes) (rec : JumpRecord) :
    readWord (writeRecordWords R mem u rec).1 (R.parentAddr u) = rec.parent ∧
      readWord (writeRecordWords R mem u rec).1 (R.depthAddr u) = rec.depth ∧
      readWord (writeRecordWords R mem u rec).1 (R.jumpAddr u) = rec.jump := by
  have hB := R.slot_addrs_inRegion hu
  unfold writeRecordWords
  dsimp only
  have hSz1 : (writeWord mem (R.parentAddr u) rec.parent).size = mem.size :=
    writeWord_size _ _ _
  have hSz2 :
      (writeWord (writeWord mem (R.parentAddr u) rec.parent) (R.depthAddr u) rec.depth).size =
        mem.size := by
    rw [writeWord_size, hSz1]
  refine ⟨?_, ?_, ?_⟩
  · rw [readWord_writeWord_ne _ _ _ _ (by omega),
      readWord_writeWord_ne _ _ _ _ (by omega),
      readWord_writeWord_self (by omega)]
  · rw [readWord_writeWord_ne _ _ _ _ (by omega),
      readWord_writeWord_self (by omega)]
  · exact readWord_writeWord_self (by omega)

theorem writeRecordWords_read_other (R : JumpWordRegion) (mem : Array Nat)
    (u : Nat) (rec : JumpRecord) {addr : Nat}
    (h1 : R.parentAddr u ≠ addr) (h2 : R.depthAddr u ≠ addr) (h3 : R.jumpAddr u ≠ addr) :
    readWord (writeRecordWords R mem u rec).1 addr = readWord mem addr := by
  unfold writeRecordWords
  dsimp only
  rw [readWord_writeWord_ne _ _ _ _ h3,
    readWord_writeWord_ne _ _ _ _ h2,
    readWord_writeWord_ne _ _ _ _ h1]

theorem writeRecordWords_inRegion (R : JumpWordRegion) (mem : Array Nat)
    {u : Nat} (hu : u ≤ R.maxNodes) (rec : JumpRecord) :
    AllAccessesInRegion R.baseAddr R.endAddr (writeRecordWords R mem u rec).2 := by
  have hB := R.slot_addrs_inRegion hu
  unfold writeRecordWords AllAccessesInRegion WordAccess.addr
  dsimp only
  change (R.baseAddr ≤ R.parentAddr u ∧ R.parentAddr u < R.endAddr) ∧
    (R.baseAddr ≤ R.depthAddr u ∧ R.depthAddr u < R.endAddr) ∧
    (R.baseAddr ≤ R.jumpAddr u ∧ R.jumpAddr u < R.endAddr) ∧ True
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

/-- Read the three fields `(parent, depth, jump)` at slot `u` (`3` word reads). -/
def readRecordWords (R : JumpWordRegion) (mem : Array Nat)
    (u : Nat) : JumpRecord × List WordAccess :=
  let aP := R.parentAddr u
  let aD := R.depthAddr u
  let aJ := R.jumpAddr u
  let p := readWord mem aP
  let d := readWord mem aD
  let j := readWord mem aJ
  ({ parent := p, depth := d, jump := j },
   [WordAccess.read aP, WordAccess.read aD, WordAccess.read aJ])

theorem readRecordWords_spec {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u : Nat} (hu : u < F.size) :
    (readRecordWords R mem u).1 = F.recordAt u ∧
      (readRecordWords R mem u).2.length = 3 ∧
      AllAccessesInRegion R.baseAddr R.endAddr (readRecordWords R mem u).2 := by
  let ⟨_, inv⟩ := hLay.valid.exists_forestInvariant
  have hSzPos : 0 < F.size := inv.size_pos
  have hNumEq : F.numInserted = F.size - 1 := rfl
  have hInsLe := hLay.inserted_le
  have huMax : u ≤ R.maxNodes := by omega
  have hB := R.slot_addrs_inRegion huMax
  refine ⟨?_, rfl, ?_⟩
  · apply jumpRecord_ext
    · exact hLay.slot_parent u hu
    · exact hLay.slot_depth u hu
    · exact hLay.slot_jump u hu
  · unfold readRecordWords AllAccessesInRegion WordAccess.addr
    dsimp only
    change (R.baseAddr ≤ R.parentAddr u ∧ R.parentAddr u < R.endAddr) ∧
      (R.baseAddr ≤ R.depthAddr u ∧ R.depthAddr u < R.endAddr) ∧
      (R.baseAddr ≤ R.jumpAddr u ∧ R.jumpAddr u < R.endAddr) ∧ True
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

/-- Initialize `[R.baseAddr, R.endAddr)` to represent `JumpForest.init` (`4` word writes). -/
def initWords (R : JumpWordRegion) (mem : Array Nat) : Array Nat × List WordAccess :=
  let w0 := writeRecordWords R mem 0 rootRecord
  let mem2 := writeWord w0.1 R.baseAddr 1
  (mem2, w0.2 ++ [WordAccess.write R.baseAddr 1])

theorem initWords_spec (R : JumpWordRegion) (mem : Array Nat)
    (hReg : R.endAddr ≤ mem.size) (hFit : WordMemFit R.W mem) :
    JumpWordLayout R JumpForest.init (initWords R mem).1 ∧
      (initWords R mem).1.size = mem.size ∧
      (initWords R mem).2.length = 4 ∧
      AllAccessesInRegion R.baseAddr R.endAddr (initWords R mem).2 ∧
      ∀ (j : Nat) (hj : j < mem.size) (hj' : j < (initWords R mem).1.size),
        (j < R.baseAddr ∨ R.endAddr ≤ j) →
        ((initWords R mem).1)[j]'hj' = mem[j]'hj := by
  have hB0 := R.slot_addrs_inRegion (Nat.zero_le R.maxNodes)
  have hCap := R.wordCapacity
  have h0Lt : 0 < 2 ^ R.W := pow2_pos R.W
  have h1Lt : 1 < 2 ^ R.W := by omega
  have hSzW0 : (writeRecordWords R mem 0 rootRecord).1.size = mem.size :=
    writeRecordWords_size R mem 0 rootRecord
  have hSzInit : (initWords R mem).1.size = mem.size := by
    unfold initWords
    dsimp only
    rw [writeWord_size, hSzW0]
  have hFitW0 : WordMemFit R.W (writeRecordWords R mem 0 rootRecord).1 :=
    writeRecordWords_fit hFit hReg (Nat.zero_le _) h0Lt h0Lt h0Lt
  have hFitInit : WordMemFit R.W (initWords R mem).1 := by
    unfold initWords
    dsimp only
    exact hFitW0.writeWord (by omega) h1Lt
  let ⟨hReadP0, hReadD0, hReadJ0⟩ :=
    writeRecordWords_read_self hReg (Nat.zero_le R.maxNodes) rootRecord
  have hLay : JumpWordLayout R JumpForest.init (initWords R mem).1 :=
    { valid := ValidJumpForest.init
      inserted_le := Nat.zero_le R.maxNodes
      region_inBounds := by rw [hSzInit]; exact hReg
      mem_fit := hFitInit
      size_word := by
        unfold initWords
        dsimp only
        exact readWord_writeWord_self (by omega)
      slot_parent := fun u hu => by
        have hSzI : JumpForest.init.size = 1 := rfl
        have hu0 : u = 0 := by omega
        subst hu0
        unfold initWords
        dsimp only
        rw [readWord_writeWord_ne _ _ _ _ (by omega), hReadP0]
        rfl
      slot_depth := fun u hu => by
        have hSzI : JumpForest.init.size = 1 := rfl
        have hu0 : u = 0 := by omega
        subst hu0
        unfold initWords
        dsimp only
        rw [readWord_writeWord_ne _ _ _ _ (by omega), hReadD0]
        rfl
      slot_jump := fun u hu => by
        have hSzI : JumpForest.init.size = 1 := rfl
        have hu0 : u = 0 := by omega
        subst hu0
        unfold initWords
        dsimp only
        rw [readWord_writeWord_ne _ _ _ _ (by omega), hReadJ0]
        rfl }
  have hInReg : AllAccessesInRegion R.baseAddr R.endAddr (initWords R mem).2 := by
    unfold initWords
    dsimp only
    refine allAccessesInRegion_append
      (writeRecordWords_inRegion R mem (Nat.zero_le _) rootRecord) ?_
    unfold AllAccessesInRegion WordAccess.addr
    have hBase : R.baseAddr < R.endAddr := by unfold JumpWordRegion.endAddr; omega
    exact ⟨⟨Nat.le_refl _, hBase⟩, trivial⟩
  refine ⟨hLay, hSzInit, rfl, hInReg, ?_⟩
  intro j hj hj' hOut
  rw [← readWord_of_lt hj', ← readWord_of_lt hj]
  unfold initWords
  dsimp only
  rw [readWord_writeWord_ne _ _ _ _ (by omega)]
  exact writeRecordWords_read_other R mem 0 rootRecord (by omega) (by omega) (by omega)

/-- Concrete `Array Nat` implementation of `F.appendLeaf p` (`14` word accesses:
    `1` size read + `9` field reads + `3` field writes + `1` size write). -/
def appendLeafWords (R : JumpWordRegion) (mem : Array Nat)
    (p : Nat) : Array Nat × List WordAccess :=
  let sz := readWord mem R.baseAddr
  let rP := readRecordWords R mem p
  let recP := rP.1
  let rA := readRecordWords R mem recP.jump
  let recA := rA.1
  let rB := readRecordWords R mem recA.jump
  let recB := rB.1
  let len1 := recP.depth - recA.depth
  let len2 := recA.depth - recB.depth
  let j := if 0 < len1 ∧ len1 = len2 then recA.jump else p
  let newRec : JumpRecord := { parent := p, depth := recP.depth + 1, jump := j }
  let wRec := writeRecordWords R mem sz newRec
  let mem2 := writeWord wRec.1 R.baseAddr (sz + 1)
  (mem2,
   WordAccess.read R.baseAddr ::
     (rP.2 ++ rA.2 ++ rB.2 ++ wRec.2 ++ [WordAccess.write R.baseAddr (sz + 1)]))

/-- Full refinement, `< 2 ^ W` word-fit preservation, frame theorem, and `14`-access bound
    for `appendLeafWords`. -/
theorem appendLeafWords_spec {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem)
    (hRoom : F.numInserted < R.maxNodes) {p : Nat} (hp : p < F.size) :
    JumpWordLayout R (F.appendLeaf p) (appendLeafWords R mem p).1 ∧
      (appendLeafWords R mem p).1.size = mem.size ∧
      (appendLeafWords R mem p).2.length = 14 ∧
      AllAccessesInRegion R.baseAddr R.endAddr (appendLeafWords R mem p).2 ∧
      ∀ (j : Nat) (hj : j < mem.size) (hj' : j < (appendLeafWords R mem p).1.size),
        (j < R.baseAddr ∨ R.endAddr ≤ j) →
        ((appendLeafWords R mem p).1)[j]'hj' = mem[j]'hj := by
  let ⟨_, inv⟩ := hLay.valid.exists_forestInvariant
  have hSzPos : 0 < F.size := inv.size_pos
  have hNumEq : F.numInserted = F.size - 1 := rfl
  have hReg : R.endAddr ≤ mem.size := hLay.region_inBounds
  have hSzMax : F.size ≤ R.maxNodes := by omega
  have hBSz := R.slot_addrs_inRegion hSzMax
  have hValid' : ValidJumpForest (F.appendLeaf p) :=
    ValidJumpForest.appendLeaf hLay.valid hp
  have hSize' : (F.appendLeaf p).size = F.size + 1 := F.size_appendLeaf p
  have hIns' : (F.appendLeaf p).numInserted ≤ R.maxNodes := by
    have hNum' : (F.appendLeaf p).numInserted = (F.appendLeaf p).size - 1 := rfl
    omega
  have ha : (F.recordAt p).jump < F.size := hLay.valid.jumpOf_lt_size hp
  have hb : (F.recordAt (F.recordAt p).jump).jump < F.size :=
    hLay.valid.jumpOf_lt_size ha
  let ⟨hRecP, _, hInP⟩ := readRecordWords_spec hLay hp
  let ⟨hRecA_raw, _, hInA_raw⟩ := readRecordWords_spec hLay ha
  let ⟨hRecB_raw, _, hInB_raw⟩ := readRecordWords_spec hLay hb
  have hSzRead : readWord mem R.baseAddr = F.size := hLay.size_word
  have hNewRecEq :
      (let recP := (readRecordWords R mem p).1
       let recA := (readRecordWords R mem recP.jump).1
       let recB := (readRecordWords R mem recA.jump).1
       let len1 := recP.depth - recA.depth
       let len2 := recA.depth - recB.depth
       let j := if 0 < len1 ∧ len1 = len2 then recA.jump else p
       ({ parent := p, depth := recP.depth + 1, jump := j } : JumpRecord)) =
        F.mkAppendedRecord p := by
    dsimp only
    rw [hRecP, hRecA_raw, hRecB_raw]
    rfl
  have hMemEq :
      (appendLeafWords R mem p).1 =
        writeWord (writeRecordWords R mem F.size (F.mkAppendedRecord p)).1
          R.baseAddr (F.size + 1) := by
    unfold appendLeafWords
    dsimp only
    rw [hSzRead, hNewRecEq]
  have hNewLtSz' : F.size < (F.appendLeaf p).size := by omega
  let ⟨hSizeLtW, hParLtW_raw, hDepLtW_raw, hJmpLtW_raw⟩ :=
    record_fields_lt_pow2 hValid' hNewLtSz' hIns' R.wordCapacity
  have hRecNewF' : (F.appendLeaf p).recordAt F.size = F.mkAppendedRecord p :=
    recordAt_appendLeaf_new F p
  have hParLtW : (F.mkAppendedRecord p).parent < 2 ^ R.W := by
    rw [← hRecNewF']; exact hParLtW_raw
  have hDepLtW : (F.mkAppendedRecord p).depth < 2 ^ R.W := by
    rw [← hRecNewF']; exact hDepLtW_raw
  have hJmpLtW : (F.mkAppendedRecord p).jump < 2 ^ R.W := by
    rw [← hRecNewF']; exact hJmpLtW_raw
  have hSzPlusLtW : F.size + 1 < 2 ^ R.W := by
    rw [← hSize']; exact hSizeLtW
  have hSzWRec :
      (writeRecordWords R mem F.size (F.mkAppendedRecord p)).1.size = mem.size :=
    writeRecordWords_size R mem F.size (F.mkAppendedRecord p)
  have hSzOut : (appendLeafWords R mem p).1.size = mem.size := by
    rw [hMemEq, writeWord_size, hSzWRec]
  have hFitWRec :
      WordMemFit R.W (writeRecordWords R mem F.size (F.mkAppendedRecord p)).1 :=
    writeRecordWords_fit hLay.mem_fit hReg hSzMax hParLtW hDepLtW hJmpLtW
  have hFitOut : WordMemFit R.W (appendLeafWords R mem p).1 := by
    rw [hMemEq]
    exact hFitWRec.writeWord (by omega) hSzPlusLtW
  let ⟨hSelfP, hSelfD, hSelfJ⟩ :=
    writeRecordWords_read_self hReg hSzMax (F.mkAppendedRecord p)
  have hLay' : JumpWordLayout R (F.appendLeaf p) (appendLeafWords R mem p).1 :=
    { valid := hValid'
      inserted_le := hIns'
      region_inBounds := by rw [hSzOut]; exact hReg
      mem_fit := hFitOut
      size_word := by
        rw [hMemEq, hSize']
        exact readWord_writeWord_self (by omega)
      slot_parent := fun u hu' => by
        rw [hMemEq]
        if huOld : u < F.size then
          have hBOld := R.slot_addrs_inRegion (show u ≤ R.maxNodes by omega)
          have hDiff : ∀ a b : Nat, a < b → R.parentAddr b ≠ R.parentAddr a ∧
              R.depthAddr b ≠ R.parentAddr a ∧ R.jumpAddr b ≠ R.parentAddr a := by
            intro a b hab
            unfold JumpWordRegion.parentAddr JumpWordRegion.depthAddr JumpWordRegion.jumpAddr
              JumpWordRegion.slotAddr
            exact ⟨by omega, by omega, by omega⟩
          let ⟨hd1, hd2, hd3⟩ := hDiff u F.size huOld
          rw [readWord_writeWord_ne _ _ _ _ (by omega),
            writeRecordWords_read_other R mem F.size _ hd1 hd2 hd3,
            parentOf_appendLeaf_old F p huOld]
          exact hLay.slot_parent u huOld
        else
          have huEq : u = F.size := by omega
          subst huEq
          rw [readWord_writeWord_ne _ _ _ _ (by omega), hSelfP]
          unfold JumpForest.parentOf
          rw [recordAt_appendLeaf_new]
      slot_depth := fun u hu' => by
        rw [hMemEq]
        if huOld : u < F.size then
          have hBOld := R.slot_addrs_inRegion (show u ≤ R.maxNodes by omega)
          have hDiff : ∀ a b : Nat, a < b → R.parentAddr b ≠ R.depthAddr a ∧
              R.depthAddr b ≠ R.depthAddr a ∧ R.jumpAddr b ≠ R.depthAddr a := by
            intro a b hab
            unfold JumpWordRegion.parentAddr JumpWordRegion.depthAddr JumpWordRegion.jumpAddr
              JumpWordRegion.slotAddr
            exact ⟨by omega, by omega, by omega⟩
          let ⟨hd1, hd2, hd3⟩ := hDiff u F.size huOld
          rw [readWord_writeWord_ne _ _ _ _ (by omega),
            writeRecordWords_read_other R mem F.size _ hd1 hd2 hd3,
            depthOf_appendLeaf_old F p huOld]
          exact hLay.slot_depth u huOld
        else
          have huEq : u = F.size := by omega
          subst huEq
          rw [readWord_writeWord_ne _ _ _ _ (by omega), hSelfD]
          unfold JumpForest.depthOf
          rw [recordAt_appendLeaf_new]
      slot_jump := fun u hu' => by
        rw [hMemEq]
        if huOld : u < F.size then
          have hBOld := R.slot_addrs_inRegion (show u ≤ R.maxNodes by omega)
          have hDiff : ∀ a b : Nat, a < b → R.parentAddr b ≠ R.jumpAddr a ∧
              R.depthAddr b ≠ R.jumpAddr a ∧ R.jumpAddr b ≠ R.jumpAddr a := by
            intro a b hab
            unfold JumpWordRegion.parentAddr JumpWordRegion.depthAddr JumpWordRegion.jumpAddr
              JumpWordRegion.slotAddr
            exact ⟨by omega, by omega, by omega⟩
          let ⟨hd1, hd2, hd3⟩ := hDiff u F.size huOld
          rw [readWord_writeWord_ne _ _ _ _ (by omega),
            writeRecordWords_read_other R mem F.size _ hd1 hd2 hd3,
            jumpOf_appendLeaf_old F p huOld]
          exact hLay.slot_jump u huOld
        else
          have huEq : u = F.size := by omega
          subst huEq
          rw [readWord_writeWord_ne _ _ _ _ (by omega), hSelfJ]
          unfold JumpForest.jumpOf
          rw [recordAt_appendLeaf_new] }
  have hInReg : AllAccessesInRegion R.baseAddr R.endAddr (appendLeafWords R mem p).2 := by
    unfold appendLeafWords
    dsimp only
    rw [hSzRead]
    have hInA : AllAccessesInRegion R.baseAddr R.endAddr
        (readRecordWords R mem (readRecordWords R mem p).1.jump).2 := by
      rw [hRecP]
      exact hInA_raw
    have hInB : AllAccessesInRegion R.baseAddr R.endAddr
        (readRecordWords R mem
          (readRecordWords R mem (readRecordWords R mem p).1.jump).1.jump).2 := by
      rw [hRecP, hRecA_raw]
      exact hInB_raw
    have hInW := writeRecordWords_inRegion R mem hSzMax
      (let recP := (readRecordWords R mem p).1
       let recA := (readRecordWords R mem recP.jump).1
       let recB := (readRecordWords R mem recA.jump).1
       let len1 := recP.depth - recA.depth
       let len2 := recA.depth - recB.depth
       let j := if 0 < len1 ∧ len1 = len2 then recA.jump else p
       { parent := p, depth := recP.depth + 1, jump := j })
    have hInBase : AllAccessesInRegion R.baseAddr R.endAddr
        [WordAccess.write R.baseAddr (F.size + 1)] :=
      ⟨⟨Nat.le_refl _, (show R.baseAddr < R.endAddr by unfold JumpWordRegion.endAddr; omega)⟩, trivial⟩
    have hBase : R.baseAddr < R.endAddr := by unfold JumpWordRegion.endAddr; omega
    refine ⟨⟨Nat.le_refl _, hBase⟩, ?_⟩
    have hInTail := allAccessesInRegion_append hInP
      (allAccessesInRegion_append hInA
        (allAccessesInRegion_append hInB
          (allAccessesInRegion_append hInW hInBase)))
    simpa only [List.append_assoc] using hInTail
  refine ⟨hLay', hSzOut, rfl, hInReg, ?_⟩
  intro j hj hj' hOut
  rw [← readWord_of_lt hj', ← readWord_of_lt hj, hMemEq,
    readWord_writeWord_ne _ _ _ _ (by omega)]
  exact writeRecordWords_read_other R mem F.size _ (by omega) (by omega) (by omega)

/-! ### `EX0.3` Concrete `Array Nat` Word-Address / Read / Write Realization (Part 2/2:
    `ancestorAtDepthWords`, `decideAncestorWords`, `RecordOp` Execution, and
    Concrete `WordRamRecordBridge` Instantiation) -/

private theorem wordAccess_length_append (xs ys : List WordAccess) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil =>
      change ys.length = 0 + ys.length
      omega
  | cons _ tl ih =>
      change (tl ++ ys).length + 1 = (tl.length + 1) + ys.length
      omega

/-- Concrete word-memory traversal loop matching `JumpForest.ancestorAtDepthAux`.
    Takes the already-loaded record `recW` of `w` so each jump move performs `3` word reads
    and each parent move performs `6` word reads (matching `3 * traceReadOps.length`). -/
def ancestorAtDepthWordsAux (R : JumpWordRegion) (mem : Array Nat) :
    Nat → Nat → JumpRecord → Nat → Nat × List WordAccess
  | 0, w, _, _ => (w, [])
  | fuel + 1, w, recW, targetDepth =>
      if targetDepth < recW.depth then
        let rJ := readRecordWords R mem recW.jump
        if targetDepth ≤ rJ.1.depth then
          let res := ancestorAtDepthWordsAux R mem fuel recW.jump rJ.1 targetDepth
          (res.1, rJ.2 ++ res.2)
        else
          let rP := readRecordWords R mem recW.parent
          let res := ancestorAtDepthWordsAux R mem fuel recW.parent rP.1 targetDepth
          (res.1, rJ.2 ++ rP.2 ++ res.2)
      else
        (w, [])

theorem ancestorAtDepthWordsAux_zero (R : JumpWordRegion) (mem : Array Nat)
    (w : Nat) (recW : JumpRecord) (targetDepth : Nat) :
    ancestorAtDepthWordsAux R mem 0 w recW targetDepth = (w, []) := rfl

theorem ancestorAtDepthWordsAux_succ (R : JumpWordRegion) (mem : Array Nat)
    (fuel w : Nat) (recW : JumpRecord) (targetDepth : Nat) :
    ancestorAtDepthWordsAux R mem (fuel + 1) w recW targetDepth =
      if targetDepth < recW.depth then
        let rJ := readRecordWords R mem recW.jump
        if targetDepth ≤ rJ.1.depth then
          let res := ancestorAtDepthWordsAux R mem fuel recW.jump rJ.1 targetDepth
          (res.1, rJ.2 ++ res.2)
        else
          let rP := readRecordWords R mem recW.parent
          let res := ancestorAtDepthWordsAux R mem fuel recW.parent rP.1 targetDepth
          (res.1, rJ.2 ++ rP.2 ++ res.2)
      else
        (w, []) := rfl

/-- Concrete `Array Nat` implementation of `F.ancestorAtDepth u targetDepth`. -/
def ancestorAtDepthWords (R : JumpWordRegion) (mem : Array Nat)
    (u targetDepth : Nat) : Nat × List WordAccess :=
  let rU := readRecordWords R mem u
  let res := ancestorAtDepthWordsAux R mem (rU.1.depth - targetDepth) u rU.1 targetDepth
  (res.1, rU.2 ++ res.2)

/-- Concrete `Array Nat` implementation of `F.decideAncestor a u` (`1` depth read of `a`
    plus at most one `ancestorAtDepthWords` traversal from `u`). -/
def decideAncestorWords (R : JumpWordRegion) (mem : Array Nat)
    (a u : Nat) : Bool × List WordAccess :=
  let depthA := readWord mem (R.depthAddr a)
  let rU := readRecordWords R mem u
  if depthA ≤ rU.1.depth then
    let res := ancestorAtDepthWordsAux R mem (rU.1.depth - depthA) u rU.1 depthA
    (if res.1 = a then true else false, WordAccess.read (R.depthAddr a) :: (rU.2 ++ res.2))
  else
    (false, WordAccess.read (R.depthAddr a) :: rU.2)

private theorem ancestorAtDepthWordsAux_spec {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} (hLay : JumpWordLayout R F mem) (targetDepth : Nat) :
    ∀ (fuel w : Nat), w < F.size →
      (ancestorAtDepthWordsAux R mem fuel w (F.recordAt w) targetDepth).1 =
        F.ancestorAtDepthAux fuel w targetDepth ∧
      (ancestorAtDepthWordsAux R mem fuel w (F.recordAt w) targetDepth).2.length =
        3 * (F.movesReadOps (F.traceMovesAux fuel w targetDepth)).length ∧
      AllAccessesInRegion R.baseAddr R.endAddr
        (ancestorAtDepthWordsAux R mem fuel w (F.recordAt w) targetDepth).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro w _
      exact ⟨rfl, rfl, trivial⟩
  | succ f ih =>
      intro w hw
      rw [ancestorAtDepthWordsAux_succ, JumpForest.ancestorAtDepthAux_succ,
        JumpForest.traceMovesAux_succ]
      have hDepEq : (F.recordAt w).depth = F.depthOf w := rfl
      have hJmpEq : (F.recordAt w).jump = F.jumpOf w := rfl
      have hParEq : (F.recordAt w).parent = F.parentOf w := rfl
      if hLt : targetDepth < F.depthOf w then
        rw [hDepEq, ite_eq_left hLt, ite_eq_left hLt, ite_eq_left hLt]
        have hjSz : F.jumpOf w < F.size := hLay.valid.jumpOf_lt_size hw
        have hpSz : F.parentOf w < F.size := hLay.valid.parentOf_lt_size hw
        let ⟨hRecJ, hLenJ, hInJ⟩ := readRecordWords_spec hLay hjSz
        let ⟨hRecP, hLenP, hInP⟩ := readRecordWords_spec hLay hpSz
        dsimp only
        rw [hJmpEq, hRecJ]
        have hDepJ : (F.recordAt (F.jumpOf w)).depth = F.depthOf (F.jumpOf w) := rfl
        rw [hDepJ]
        if hJump : targetDepth ≤ F.depthOf (F.jumpOf w) then
          rw [ite_eq_left hJump]
          have hStepJ : F.stepToDepth w targetDepth = F.jumpOf w := by
            unfold JumpForest.stepToDepth
            dsimp only
            exact ite_eq_left hJump
          have hMoveJ : F.stepMoveToDepth w targetDepth = JumpMove.jump w (F.jumpOf w) := by
            unfold JumpForest.stepMoveToDepth
            dsimp only
            exact ite_eq_left hJump
          rw [hStepJ, hMoveJ, JumpForest.movesReadOps_cons]
          let ⟨hRes, hLen, hIn⟩ := ih (F.jumpOf w) hjSz
          refine ⟨hRes, ?_, ?_⟩
          · dsimp only
            rw [wordAccess_length_append, hLenJ, hLen]
            change 3 + 3 * (F.movesReadOps (F.traceMovesAux f (F.jumpOf w) targetDepth)).length =
              3 * (RecordOp.read (F.jumpOf w) ::
                F.movesReadOps (F.traceMovesAux f (F.jumpOf w) targetDepth)).length
            simp only [List.length_cons]
            omega
          · exact allAccessesInRegion_append hInJ hIn
        else
          rw [ite_eq_right hJump, hParEq, hRecP]
          have hStepP : F.stepToDepth w targetDepth = F.parentOf w := by
            unfold JumpForest.stepToDepth
            dsimp only
            exact ite_eq_right hJump
          have hMoveP :
              F.stepMoveToDepth w targetDepth = JumpMove.parent w (F.parentOf w) := by
            unfold JumpForest.stepMoveToDepth
            dsimp only
            exact ite_eq_right hJump
          rw [hStepP, hMoveP, JumpForest.movesReadOps_cons]
          let ⟨hRes, hLen, hIn⟩ := ih (F.parentOf w) hpSz
          refine ⟨hRes, ?_, ?_⟩
          · dsimp only
            rw [wordAccess_length_append, wordAccess_length_append, hLenJ, hLenP, hLen]
            change 3 + 3 + 3 * (F.movesReadOps (F.traceMovesAux f (F.parentOf w) targetDepth)).length =
              3 * (RecordOp.read (F.jumpOf w) :: RecordOp.read (F.parentOf w) ::
                F.movesReadOps (F.traceMovesAux f (F.parentOf w) targetDepth)).length
            simp only [List.length_cons]
            omega
          · exact allAccessesInRegion_append (allAccessesInRegion_append hInJ hInP) hIn
      else
        rw [hDepEq, ite_eq_right hLt, ite_eq_right hLt, ite_eq_right hLt]
        exact ⟨rfl, rfl, trivial⟩

/-- `ancestorAtDepthWords` refines `F.ancestorAtDepth u targetDepth`, stays strictly inside
    `[R.baseAddr, R.endAddr)` (`< mem.size ≤ 2 ^ R.W`), and executes at most `3 * (6 * L + 1)`
    (`≤ 1 + 3 * (6 * L + 1)`) word reads whenever `F.numInserted ≤ n` and `n + 2 ≤ 2 ^ L`. -/
theorem ancestorAtDepthWords_spec {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u n L : Nat} (hu : u < F.size)
    (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L) (targetDepth : Nat) :
    (ancestorAtDepthWords R mem u targetDepth).1 = F.ancestorAtDepth u targetDepth ∧
      (ancestorAtDepthWords R mem u targetDepth).2.length =
        3 * (F.traceReadOps u targetDepth).length ∧
      (ancestorAtDepthWords R mem u targetDepth).2.length ≤ 1 + 3 * (6 * L + 1) ∧
      AllAccessesInRegion R.baseAddr R.endAddr (ancestorAtDepthWords R mem u targetDepth).2 := by
  let ⟨hRecU, hLenU, hInU⟩ := readRecordWords_spec hLay hu
  let ⟨hRes, hAuxLen, hAuxIn⟩ :=
    ancestorAtDepthWordsAux_spec hLay targetDepth (F.depthOf u - targetDepth) u hu
  have hReadBound : (F.traceReadOps u targetDepth).length ≤ 6 * L + 1 :=
    traceReadOps_length_le hLay.valid hu hInserted hPow targetDepth
  have hExactLen :
      (ancestorAtDepthWords R mem u targetDepth).2.length =
        3 * (F.traceReadOps u targetDepth).length := by
    unfold ancestorAtDepthWords
    dsimp only
    rw [hRecU, wordAccess_length_append, hLenU]
    have hDepU : (F.recordAt u).depth = F.depthOf u := rfl
    rw [hDepU, hAuxLen]
    unfold JumpForest.traceReadOps JumpForest.traceMoves
    simp only [List.length_cons]
    omega
  refine ⟨?_, hExactLen, by omega, ?_⟩
  · unfold ancestorAtDepthWords JumpForest.ancestorAtDepth
    dsimp only
    rw [hRecU]
    exact hRes
  · unfold ancestorAtDepthWords
    dsimp only
    rw [hRecU]
    exact allAccessesInRegion_append hInU hAuxIn

/-- `decideAncestorWords` refines `F.decideAncestor a u`, stays strictly inside
    `[R.baseAddr, R.endAddr)`, and executes at most `1 + 3 * (6 * L + 1)` word reads. -/
theorem decideAncestorWords_spec {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {a u n L : Nat}
    (ha : a < F.size) (hu : u < F.size)
    (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L) :
    (decideAncestorWords R mem a u).1 = F.decideAncestor a u ∧
      (decideAncestorWords R mem a u).2.length ≤ 1 + 3 * (6 * L + 1) ∧
      AllAccessesInRegion R.baseAddr R.endAddr (decideAncestorWords R mem a u).2 := by
  let ⟨_, inv⟩ := hLay.valid.exists_forestInvariant
  have hSzPos : 0 < F.size := inv.size_pos
  have hNumEq : F.numInserted = F.size - 1 := rfl
  have hInsLe := hLay.inserted_le
  have haMax : a ≤ R.maxNodes := by omega
  have hBa := R.slot_addrs_inRegion haMax
  have hDepA : readWord mem (R.depthAddr a) = F.depthOf a := hLay.slot_depth a ha
  let ⟨hRecU, hLenU, hInU⟩ := readRecordWords_spec hLay hu
  let ⟨hRes, hAuxLen, hAuxIn⟩ :=
    ancestorAtDepthWordsAux_spec hLay (F.depthOf a) (F.depthOf u - F.depthOf a) u hu
  have hReadBound : (F.traceReadOps u (F.depthOf a)).length ≤ 6 * L + 1 :=
    traceReadOps_length_le hLay.valid hu hInserted hPow (F.depthOf a)
  unfold decideAncestorWords JumpForest.decideAncestor
  dsimp only
  rw [hDepA, hRecU]
  have hDepU : (F.recordAt u).depth = F.depthOf u := rfl
  rw [hDepU]
  if hLe : F.depthOf a ≤ F.depthOf u then
    rw [ite_eq_left hLe]
    dsimp only
    have hRes' :
        (ancestorAtDepthWordsAux R mem (F.depthOf u - F.depthOf a) u (F.recordAt u)
          (F.depthOf a)).1 = F.ancestorAtDepth u (F.depthOf a) := hRes
    rw [hRes']
    refine ⟨?_, ?_, ?_⟩
    · if hEq : F.ancestorAtDepth u (F.depthOf a) = a then
        rw [ite_eq_left hEq, ite_eq_left ⟨hLe, hEq⟩]
      else
        have hNotAnd : ¬ (F.depthOf a ≤ F.depthOf u ∧ F.ancestorAtDepth u (F.depthOf a) = a) :=
          fun h => hEq h.2
        rw [ite_eq_right hEq, ite_eq_right hNotAnd]
    · simp only [List.length_cons]
      rw [wordAccess_length_append, hLenU, hAuxLen]
      unfold JumpForest.traceReadOps JumpForest.traceMoves at hReadBound
      simp only [List.length_cons] at hReadBound
      omega
    · exact ⟨⟨(by change R.baseAddr ≤ R.depthAddr a; omega), (by change R.depthAddr a < R.endAddr; omega)⟩, allAccessesInRegion_append hInU hAuxIn⟩
  else
    have hNotAnd : ¬ (F.depthOf a ≤ F.depthOf u ∧ F.ancestorAtDepth u (F.depthOf a) = a) :=
      fun h => hLe h.1
    rw [ite_eq_right hLe, ite_eq_right hNotAnd]
    refine ⟨rfl, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [hLenU]
      omega
    · exact ⟨⟨(by change R.baseAddr ≤ R.depthAddr a; omega), (by change R.depthAddr a < R.endAddr; omega)⟩, hInU⟩

/-- Concrete word-memory executor for abstract `RecordOp` transcripts. -/
def execRecordOpWords (R : JumpWordRegion) (mem : Array Nat) :
    RecordOp → Array Nat × List WordAccess
  | RecordOp.read idx =>
      (mem, (readRecordWords R mem idx).2)
  | RecordOp.append rec =>
      let sz := readWord mem R.baseAddr
      let wRec := writeRecordWords R mem sz rec
      let mem2 := writeWord wRec.1 R.baseAddr (sz + 1)
      (mem2, WordAccess.read R.baseAddr :: (wRec.2 ++ [WordAccess.write R.baseAddr (sz + 1)]))

def execRecordOpsWords (R : JumpWordRegion) (mem : Array Nat) :
    List RecordOp → Array Nat × List WordAccess
  | [] => (mem, [])
  | op :: ops =>
      let step := execRecordOpWords R mem op
      let rest := execRecordOpsWords R step.1 ops
      (rest.1, step.2 ++ rest.2)

theorem execRecordOpsWords_nil (R : JumpWordRegion) (mem : Array Nat) :
    execRecordOpsWords R mem [] = (mem, []) := rfl

theorem execRecordOpsWords_cons (R : JumpWordRegion) (mem : Array Nat)
    (op : RecordOp) (ops : List RecordOp) :
    execRecordOpsWords R mem (op :: ops) =
      let step := execRecordOpWords R mem op
      let rest := execRecordOpsWords R step.1 ops
      (rest.1, step.2 ++ rest.2) := rfl

/-- Executing `F.appendLeafOps p` on `mem` produces the exact same memory as `appendLeafWords`
    in `14` (`3 * 3 + 5`) word accesses. -/
theorem execRecordOpsWords_appendLeafOps {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {p : Nat} (hp : p < F.size) :
    (execRecordOpsWords R mem (F.appendLeafOps p)).1 = (appendLeafWords R mem p).1 ∧
      (execRecordOpsWords R mem (F.appendLeafOps p)).2.length = 14 := by
  have ha : (F.recordAt p).jump < F.size := hLay.valid.jumpOf_lt_size hp
  have hb : (F.recordAt (F.recordAt p).jump).jump < F.size := hLay.valid.jumpOf_lt_size ha
  let ⟨hRecP, _, _⟩ := readRecordWords_spec hLay hp
  let ⟨hRecA, _, _⟩ := readRecordWords_spec hLay ha
  let ⟨hRecB, _, _⟩ := readRecordWords_spec hLay hb
  refine ⟨?_, rfl⟩
  unfold JumpForest.appendLeafOps execRecordOpsWords execRecordOpWords appendLeafWords
  dsimp only
  rw [hRecP, hRecA, hRecB]
  rfl

/-- Concrete `EX0.3` instantiation of `WordRamRecordBridge` backed by `Array Nat`
    (`wordsPerRecord := 3`, `headerWords := 1`, `costPerRead := 3`, `costPerAppend := 5`). -/
def mkJumpWordRamBridge (R : JumpWordRegion) : WordRamRecordBridge :=
  { wordWidth := R.W
    maxNodes := R.maxNodes
    wordCapacity := R.wordCapacity
    costPerRead := 3
    costPerAppend := 5
    wordsPerRecord := 3
    headerWords := 1 }

/-- End-to-end concrete `Array Nat` bridge theorem instantiating `WordRamRecordBridge`
    (`wordsPerRecord = 3`, `headerWords = 1`, `costPerRead = 3`, `costPerAppend = 5`):
    - `appendLeafWords` refines `F.appendLeaf p`, preserves `< 2 ^ R.W` word-fit and frame,
      and uses `3 * costPerRead + costPerAppend = 14` in-bounds word accesses;
    - retained region occupies `headerWords + wordsPerRecord * (maxNodes + 1)` words
      (`headerWords + wordsPerRecord * (F.numInserted + 1)` active words);
    - `ancestorAtDepthWords` and `decideAncestorWords` refine `F.ancestorAtDepth` and
      `F.decideAncestor` in `≤ 1 + (6 * ceilLog2 (R.maxNodes + 2) + 1) * costPerRead`
      in-bounds word reads. -/
theorem jumpWordRamBridge_endToEnd {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) (hRoom : F.numInserted < R.maxNodes)
    {p a u : Nat} (hp : p < F.size) (ha : a < F.size) (hu : u < F.size) (targetDepth : Nat) :
    let B := mkJumpWordRamBridge R
    let L := ceilLog2 (B.maxNodes + 2)
    JumpWordLayout R (F.appendLeaf p) (appendLeafWords R mem p).1 ∧
      (appendLeafWords R mem p).2.length = 3 * B.costPerRead + B.costPerAppend ∧
      R.endAddr = R.baseAddr + B.headerWords + B.wordsPerRecord * (B.maxNodes + 1) ∧
      (ancestorAtDepthWords R mem u targetDepth).1 = F.ancestorAtDepth u targetDepth ∧
      (ancestorAtDepthWords R mem u targetDepth).2.length ≤
        (6 * L + 1) * B.costPerRead ∧
      (decideAncestorWords R mem a u).1 = F.decideAncestor a u ∧
      (decideAncestorWords R mem a u).2.length ≤
        1 + (6 * L + 1) * B.costPerRead := by
  intro B L
  let ⟨hLay', _, hAppLen, _, _⟩ := appendLeafWords_spec hLay hRoom hp
  let ⟨hAncRes, hAncExact, _, _⟩ :=
    ancestorAtDepthWords_spec hLay hu hLay.inserted_le (pow2_ceilLog2_ge (R.maxNodes + 2))
      targetDepth
  let ⟨hDecRes, hDecLen, _⟩ :=
    decideAncestorWords_spec hLay ha hu hLay.inserted_le (pow2_ceilLog2_ge (R.maxNodes + 2))
  have hReadBound : (F.traceReadOps u targetDepth).length ≤ 6 * L + 1 :=
    traceReadOps_length_le hLay.valid hu hLay.inserted_le (pow2_ceilLog2_ge (R.maxNodes + 2))
      targetDepth
  refine ⟨hLay', ?_, rfl, hAncRes, ?_, hDecRes, ?_⟩
  · change (appendLeafWords R mem p).2.length = 14
    exact hAppLen
  · change (ancestorAtDepthWords R mem u targetDepth).2.length ≤ (6 * L + 1) * 3
    omega
  · change (decideAncestorWords R mem a u).2.length ≤ 1 + (6 * ceilLog2 (R.maxNodes + 2) + 1) * 3
    omega

end PaperB
