module

public import Lean
public import PaperB.SeedOrder
public import PaperB.ForestIntervals
public import PaperB.ExitPaths

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42
namespace ArraySweep

open PaperB PaperB.LabelledQuotient

universe u v w

/- The size proof is erased. In particular, writing one slot uses Array.set,
   not a tabulation of the whole array. -/
structure Slots (α : Type u) (n : Nat) where
  data : Array (Option α)
  size_data : data.size = n

namespace Slots

def empty (α : Type u) (n : Nat) : Slots α n :=
  ⟨Array.replicate n none, by simp⟩

def read {α : Type u} {n : Nat} (s : Slots α n) (i : Fin n) : Option α :=
  s.data[i.val]'(by simpa only [s.size_data] using i.isLt)

def write {α : Type u} {n : Nat}
    (s : Slots α n) (i : Fin n) (a : α) : Slots α n :=
  ⟨s.data.set i.val (some a) (by simpa only [s.size_data] using i.isLt),
    by simp [s.size_data]⟩

@[simp] theorem read_empty {α : Type u} {n : Nat} (i : Fin n) :
    (empty α n).read i = none := by
  simp [empty, read]

@[simp] theorem read_write_same {α : Type u} {n : Nat}
    (s : Slots α n) (i : Fin n) (a : α) :
    (s.write i a).read i = some a := by
  simp [read, write]

theorem read_write_other {α : Type u} {n : Nat}
    (s : Slots α n) (i j : Fin n) (a : α) (h : j ≠ i) :
    (s.write i a).read j = s.read j := by
  have hv : i.val ≠ j.val := fun e => h (Fin.ext e.symm)
  simp [read, write, Array.getElem_set, hv]

end Slots

structure Plan (n m : Nat) where
  rank : Fin n → Nat
  rank_inj : ∀ x y, rank x = rank y → x = y
  observe : Fin n → Fin m → Bool

namespace Plan

variable {n m : Nat}

private def pick (r : Fin n → Nat) (k : Nat) :
    List (Fin n) → Option (Fin n)
  | [] => none
  | y :: ys => if r y = k then some y else pick r k ys

private theorem pick_rank (r : Fin n → Nat) (k : Nat)
    (xs : List (Fin n)) {y : Fin n} (h : pick r k xs = some y) :
    r y = k := by
  induction xs with
  | nil => simp [pick] at h
  | cons z zs ih =>
    by_cases hz : r z = k
    · have e : z = y := by simpa [pick, hz] using h
      simpa only [e] using hz
    · exact ih (by simpa [pick, hz] using h)

private theorem pick_mem (P : Plan n m) (k : Nat) (xs : List (Fin n))
    {y : Fin n} (hy : y ∈ xs) (hk : P.rank y = k) :
    pick P.rank k xs = some y := by
  induction xs with
  | nil => simp at hy
  | cons z zs ih =>
    by_cases hz : P.rank z = k
    · have e := P.rank_inj z y (hz.trans hk.symm)
      simp [pick, e, hk]
    · have hm : y ∈ zs := by
        rcases List.mem_cons.mp hy with e | hm
        · exact (hz (by simpa only [e] using hk)).elim
        · exact hm
      simpa [pick, hz] using ih hm

def atRank (P : Plan n m) (k : Nat) : Option (Fin n) :=
  pick P.rank k (List.finRange n)

theorem atRank_iff (P : Plan n m) (k : Nat) (y : Fin n) :
    P.atRank k = some y ↔ P.rank y = k :=
  ⟨pick_rank P.rank k (List.finRange n),
    fun h => pick_mem P k (List.finRange n) (by simp) h⟩

theorem vertex_once (P : Plan n m) {k l : Nat} {y : Fin n}
    (hk : P.atRank k = some y) (hl : P.atRank l = some y) : k = l :=
  ((P.atRank_iff k y).mp hk).symm.trans ((P.atRank_iff l y).mp hl)

private def bound (r : Fin n → Nat) : List (Fin n) → Nat
  | [] => 0
  | y :: ys => max (r y + 1) (bound r ys)

private theorem lt_bound (r : Fin n → Nat) (xs : List (Fin n))
    {y : Fin n} (hy : y ∈ xs) : r y < bound r xs := by
  induction xs with
  | nil => simp at hy
  | cons z zs ih =>
    change r y < max (r z + 1) (bound r zs)
    rcases List.mem_cons.mp hy with e | hm
    · subst z
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih hm) (Nat.le_max_right _ _)

def limit (P : Plan n m) : Nat :=
  bound P.rank (List.finRange n)

theorem rank_lt_limit (P : Plan n m) (y : Fin n) : P.rank y < P.limit :=
  lt_bound P.rank (List.finRange n) (by simp)

def mapBefore (P : Plan n m) (k : Nat) (i : Fin m) : Prop :=
  ∃ y, P.rank y < k ∧ P.observe y i = true

def firstAt (P : Plan n m) (y : Fin n) (i : Fin m) : Prop :=
  P.observe y i = true ∧ ¬ P.mapBefore (P.rank y) i

theorem before_succ (P : Plan n m) (y : Fin n) (i : Fin m) :
    P.mapBefore (P.rank y + 1) i ↔
      P.mapBefore (P.rank y) i ∨ P.observe y i = true := by
  constructor
  · rintro ⟨z, hz, ho⟩
    by_cases h : P.rank z < P.rank y
    · exact Or.inl ⟨z, h, ho⟩
    · have e : z = y := P.rank_inj z y (by omega)
      exact Or.inr (by simpa only [e] using ho)
  · rintro (⟨z, hz, ho⟩ | ho)
    · exact ⟨z, by omega, ho⟩
    · exact ⟨y, Nat.lt_succ_self _, ho⟩

end Plan

structure Reads (n m : Nat) where
  installBase : Fin m → Fin n → Prop
  installMap : Fin m → Fin m → Prop
  vertexBase : Fin n → Fin n → Prop
  vertexMap : Fin n → Fin m → Prop

structure Ready {n m : Nat} (P : Plan n m) (D : Reads n m) : Prop where
  install : ∀ y i, P.firstAt y i →
    (∀ p, D.installBase i p → P.rank p < P.rank y) ∧
    (∀ j, D.installMap i j → P.mapBefore (P.rank y) j)
  vertex : ∀ y,
    (∀ z, D.vertexBase y z → P.rank z < P.rank y) ∧
    (∀ i, D.vertexMap y i →
      P.mapBefore (P.rank y) i ∨ P.observe y i = true)

/-- The executable callbacks see only dependency-indexed readers.
The installer reads the pre-vertex snapshot. The base builder reads the
same old bases, but receives the maps after this vertex's installations. -/
structure Callbacks {n m : Nat} (D : Reads n m)
    (M : Type u) (B : Type v) where
  install : (y : Fin n) → (i : Fin m) →
    ((p : Fin n) → D.installBase i p → Option B) →
    ((j : Fin m) → D.installMap i j → Option M) → M
  base : (y : Fin n) →
    ((z : Fin n) → D.vertexBase y z → Option B) →
    ((i : Fin m) → D.vertexMap y i → Option M) → B

/-- The reference values occur in the contracts, not in the driver.
For EX4.2, the vertex contract is where the incoming-occurrence union
is proved; the installer contract is separate. -/
structure Exact {n m : Nat} {M : Type u} {B : Type v} {D : Reads n m}
    (P : Plan n m) (C : Callbacks D M B)
    (wantMap : Fin m → M) (wantBase : Fin n → B) : Prop where
  install : ∀ y i rb rm, P.firstAt y i →
    (∀ p h, rb p h = some (wantBase p)) →
    (∀ j h, rm j h = some (wantMap j)) →
    C.install y i rb rm = wantMap i
  vertex : ∀ y rb rm,
    (∀ z h, rb z h = some (wantBase z)) →
    (∀ i h, rm i h = some (wantMap i)) →
    C.base y rb rm = wantBase y

structure State (n m : Nat) (M : Type u) (B : Type v) where
  maps : Slots M m
  bases : Slots B n

def Cell {α : Type u} (present : Prop) (got : Option α) (want : α) : Prop :=
  (present → got = some want) ∧ (¬ present → got = none)

structure Prefix {n m : Nat} {M : Type u} {B : Type v}
    (P : Plan n m) (wantMap : Fin m → M) (wantBase : Fin n → B)
    (k : Nat) (s : State n m M B) : Prop where
  maps : ∀ i, Cell (P.mapBefore k i) (s.maps.read i) (wantMap i)
  bases : ∀ y, Cell (P.rank y < k) (s.bases.read y) (wantBase y)

section Driver

variable {n m : Nat} {M : Type u} {B : Type v} {D : Reads n m}

def addMap (obs : Fin m → Bool) (make : Fin m → M)
    (i : Fin m) (ms : Slots M m) : Slots M m :=
  if obs i = true then
    match ms.read i with
    | none => ms.write i (make i)
    | some _ => ms
  else ms

/-- An already installed key takes the identity branch, not a write branch. -/
theorem addMap_occupied (obs : Fin m → Bool) (make : Fin m → M)
    (i : Fin m) (ms : Slots M m) {a : M} (h : ms.read i = some a) :
    addMap obs make i ms = ms := by
  simp [addMap, h]

def scanMaps (obs : Fin m → Bool) (make : Fin m → M) :
    List (Fin m) → Slots M m → Slots M m
  | [], ms => ms
  | i :: is, ms => scanMaps obs make is (addMap obs make i ms)

theorem scanMaps_read (obs : Fin m → Bool) (make : Fin m → M)
    (xs : List (Fin m)) (ms : Slots M m) (i : Fin m) :
    (scanMaps obs make xs ms).read i =
      match ms.read i with
      | some a => some a
      | none => if i ∈ xs ∧ obs i = true then some (make i) else none := by
  induction xs generalizing ms with
  | nil =>
    cases h : ms.read i <;> simp [scanMaps, h]
  | cons j js ih =>
    rw [scanMaps, ih]
    by_cases e : i = j
    · subst j
      by_cases ho : obs i = true <;>
        cases h : ms.read i <;> simp [addMap, ho, h]
    · have he : (addMap obs make j ms).read i = ms.read i := by
        by_cases ho : obs j = true
        · cases h : ms.read j <;>
            simp [addMap, ho, h, Slots.read_write_other, e]
        · simp [addMap, ho]
      rw [he]
      cases h : ms.read i <;> simp [e]

def makeMap (C : Callbacks D M B) (s : State n m M B)
    (y : Fin n) (i : Fin m) : M :=
  C.install y i (fun p _ => s.bases.read p) (fun j _ => s.maps.read j)

def stageMaps (P : Plan n m) (C : Callbacks D M B)
    (s : State n m M B) (y : Fin n) : Slots M m :=
  scanMaps (P.observe y) (makeMap C s y) (List.finRange m) s.maps

def makeBase (C : Callbacks D M B) (s : State n m M B)
    (y : Fin n) (ms : Slots M m) : B :=
  C.base y (fun z _ => s.bases.read z) (fun i _ => ms.read i)

def visit (P : Plan n m) (C : Callbacks D M B)
    (s : State n m M B) (y : Fin n) : State n m M B :=
  let ms := stageMaps P C s y
  ⟨ms, s.bases.write y (makeBase C s y ms)⟩

def step (P : Plan n m) (C : Callbacks D M B)
    (k : Nat) (s : State n m M B) : State n m M B :=
  match P.atRank k with
  | none => s
  | some y => visit P C s y

def runTo (P : Plan n m) (C : Callbacks D M B) : Nat → State n m M B
  | 0 => ⟨Slots.empty M m, Slots.empty B n⟩
  | k + 1 => step P C k (runTo P C k)

def run (P : Plan n m) (C : Callbacks D M B) : State n m M B :=
  runTo P C P.limit

theorem step_map_persistent (P : Plan n m) (C : Callbacks D M B)
    (k : Nat) (s : State n m M B) (i : Fin m) {a : M}
    (h : s.maps.read i = some a) :
    (step P C k s).maps.read i = some a := by
  cases hk : P.atRank k with
  | none => simpa [step, hk] using h
  | some y =>
    simp [step, hk, visit, stageMaps, scanMaps_read, h]

theorem runTo_map_persistent (P : Plan n m) (C : Callbacks D M B)
    {k l : Nat} (hle : k ≤ l) (i : Fin m) {a : M}
    (h : (runTo P C k).maps.read i = some a) :
    (runTo P C l).maps.read i = some a := by
  induction l with
  | zero =>
    have e : k = 0 := by omega
    simpa only [e] using h
  | succ l ih =>
    by_cases hl : k ≤ l
    · exact step_map_persistent P C l (runTo P C l) i (ih hl)
    · have e : k = l + 1 := by omega
      simpa only [e] using h

variable {P : Plan n m} {C : Callbacks D M B}
  {wantMap : Fin m → M} {wantBase : Fin n → B}

theorem stageMaps_prefix (R : Ready P D) (E : Exact P C wantMap wantBase)
    {s : State n m M B} {y : Fin n}
    (h : Prefix P wantMap wantBase (P.rank y) s) (i : Fin m) :
    Cell (P.mapBefore (P.rank y) i ∨ P.observe y i = true)
      ((stageMaps P C s y).read i) (wantMap i) := by
  have hm := h.maps i
  by_cases hp : P.mapBefore (P.rank y) i
  · rw [stageMaps, scanMaps_read, hm.1 hp]
    exact ⟨fun _ => rfl, fun hn => (hn (Or.inl hp)).elim⟩
  · rw [stageMaps, scanMaps_read, hm.2 hp]
    by_cases ho : P.observe y i = true
    · have hf : P.firstAt y i := ⟨ho, hp⟩
      have hr := R.install y i hf
      have he : makeMap C s y i = wantMap i :=
        E.install y i _ _ hf
          (fun p hd => (h.bases p).1 (hr.1 p hd))
          (fun j hd => (h.maps j).1 (hr.2 j hd))
      exact ⟨fun _ => by simp [ho, he], fun hn => (hn (Or.inr ho)).elim⟩
    · exact ⟨fun hh => (hh.elim hp ho).elim, fun _ => by simp [ho]⟩

theorem visit_prefix (R : Ready P D) (E : Exact P C wantMap wantBase)
    {s : State n m M B} {y : Fin n}
    (h : Prefix P wantMap wantBase (P.rank y) s) :
    Prefix P wantMap wantBase (P.rank y + 1) (visit P C s y) := by
  have hm := stageMaps_prefix R E h
  have hr := R.vertex y
  have hb : makeBase C s y (stageMaps P C s y) = wantBase y :=
    E.vertex y _ _
      (fun z hd => (h.bases z).1 (hr.1 z hd))
      (fun i hd => (hm i).1 (hr.2 i hd))
  constructor
  · intro i
    change Cell (P.mapBefore (P.rank y + 1) i)
      ((stageMaps P C s y).read i) (wantMap i)
    rw [P.before_succ]
    exact hm i
  · intro z
    change Cell (P.rank z < P.rank y + 1)
      ((s.bases.write y (makeBase C s y (stageMaps P C s y))).read z)
      (wantBase z)
    rw [hb]
    by_cases e : z = y
    · subst z
      rw [Slots.read_write_same]
      exact ⟨fun _ => rfl, fun hn => (hn (Nat.lt_succ_self _)).elim⟩
    · rw [Slots.read_write_other s.bases y z (wantBase y) e]
      have hne : P.rank z ≠ P.rank y := fun he => e (P.rank_inj z y he)
      exact ⟨fun hz => (h.bases z).1 (by omega),
        fun hz => (h.bases z).2 (by omega)⟩

theorem step_prefix (R : Ready P D) (E : Exact P C wantMap wantBase)
    {k : Nat} {s : State n m M B} (h : Prefix P wantMap wantBase k s) :
    Prefix P wantMap wantBase (k + 1) (step P C k s) := by
  cases hk : P.atRank k with
  | none =>
    have hn (y : Fin n) : P.rank y ≠ k := by
      intro hy
      have hs := (P.atRank_iff k y).mpr hy
      simp [hk] at hs
    have hb (y : Fin n) : P.rank y < k + 1 ↔ P.rank y < k := by
      have he := hn y
      omega
    have hm (i : Fin m) : P.mapBefore (k + 1) i ↔ P.mapBefore k i := by
      constructor <;> rintro ⟨y, hy, ho⟩
      · exact ⟨y, (hb y).mp hy, ho⟩
      · exact ⟨y, (hb y).mpr hy, ho⟩
    rw [step, hk]
    constructor
    · intro i
      rw [hm]
      exact h.maps i
    · intro y
      rw [hb]
      exact h.bases y
  | some y =>
    have hy := (P.atRank_iff k y).mp hk
    have hs : Prefix P wantMap wantBase (P.rank y) s := by
      simpa only [hy] using h
    simpa only [step, hk, hy] using visit_prefix R E hs

theorem runTo_prefix (R : Ready P D) (E : Exact P C wantMap wantBase)
    (k : Nat) : Prefix P wantMap wantBase k (runTo P C k) := by
  induction k with
  | zero =>
    constructor
    · intro i
      exact ⟨fun ⟨y, hy, _⟩ => (Nat.not_lt_zero _ hy).elim,
        fun _ => Slots.read_empty i⟩
    · intro y
      exact ⟨fun hy => (Nat.not_lt_zero _ hy).elim, fun _ => Slots.read_empty y⟩
  | succ k ih =>
    exact step_prefix R E ih

theorem run_base_exact (R : Ready P D) (E : Exact P C wantMap wantBase)
    (y : Fin n) : (run P C).bases.read y = some (wantBase y) :=
  ((runTo_prefix R E P.limit).bases y).1 (P.rank_lt_limit y)

/-- At the first observed rank the slot is empty and staging fills it.
Before that rank it was empty, and after staging every later add at that
key takes `addMap_occupied`. This applies even to a scan list with duplicates. -/
theorem first_install (R : Ready P D) (E : Exact P C wantMap wantBase)
    {y : Fin n} {i : Fin m} (hf : P.firstAt y i) :
    (runTo P C (P.rank y)).maps.read i = none ∧
    (stageMaps P C (runTo P C (P.rank y)) y).read i = some (wantMap i) := by
  have h := runTo_prefix R E (P.rank y)
  exact ⟨(h.maps i).2 hf.2, (stageMaps_prefix R E h i).1 (Or.inr hf.1)⟩

end Driver

/-! The proper-loss adapter. `SeedView` certifies the local observations,
not the result of either callback. The run never calls firstProperLossSeed. -/

abbrev Forest (H : LabelledQuotient) (m : Nat) :=
  ProperLossForestWitness H (fun K : LabelledQuotient => Fin K.vertexCount)
    (Fin m) (CutPair H)

structure SeedView {H : LabelledQuotient} {m : Nat} (F : Forest H m) where
  observe : Fin H.vertexCount → Fin m → Bool
  sound : ∀ {y i}, observe y i = true →
    ∃ A, F.nodeKey? i = some A ∧ F.ancestor i (F.label y)
  hit : ∀ {i A} (hi : F.nodeKey? i = some A),
    observe (F.firstProperLossSeed hi) i = true

namespace SeedView

variable {H : LabelledQuotient} {m : Nat} {F : Forest H m}

/-- Observe the real nodes on the label's ancestor chain, using executable
tests. An artificial root is filtered out by `real`. No seed table is input. -/
def ancestors (real : Fin m → Bool) (under : Fin m → Fin m → Bool)
    (real_ok : ∀ i, real i = true ↔ ∃ A, F.nodeKey? i = some A)
    (under_ok : ∀ i j, under i j = true ↔ F.ancestor i j) : SeedView F where
  observe y i := real i && under i (F.label y)
  sound := by
    intro y i h
    have h' : real i = true ∧ under i (F.label y) = true := by
      simpa using h
    obtain ⟨A, hA⟩ := (real_ok i).mp h'.1
    exact ⟨A, hA, (under_ok i (F.label y)).mp h'.2⟩
  hit := by
    intro i A hi
    have ha := (F.properLoss_iff_ancestor hi _).mp
      (F.firstProperLossSeed_spec hi).1
    simp [(real_ok i).mpr ⟨A, hi⟩, (under_ok i _).mpr ha]

/-- Optional label-only front end. Its extra certification is structural:
a strict descendant of a real node lies below a real immediate child.
The seed hit is then a consequence of the parent-label distinction lemma,
rather than an input to the front end. -/
def labels (real : Fin m → Bool)
    (real_ok : ∀ i, real i = true ↔ ∃ A, F.nodeKey? i = some A)
    (branch : ∀ i j A, F.nodeKey? i = some A → F.ancestor i j → i ≠ j →
      ∃ c P, F.parent c = i ∧ F.nodeKey? c = some P ∧ F.ancestor c j) :
    SeedView F where
  observe y i := real i && decide (F.label y = i)
  sound := by
    intro y i h
    have h' : real i = true ∧ F.label y = i := by simpa using h
    obtain ⟨A, hA⟩ := (real_ok i).mp h'.1
    exact ⟨A, hA, by rw [h'.2]; exact F.ancestor_refl i⟩
  hit := by
    intro i A hi
    let y := F.firstProperLossSeed hi
    have ha : F.ancestor i (F.label y) :=
      (F.properLoss_iff_ancestor hi y).mp (F.firstProperLossSeed_spec hi).1
    have he : F.label y = i := by
      by_cases e : F.label y = i
      · exact e
      · obtain ⟨c, P, hc, hP, hd⟩ := branch i (F.label y) A hi ha (Ne.symm e)
        have hA : F.nodeKey? (F.parent c) = some A := by
          simpa only [hc] using hi
        have hs : F.firstProperLossSeed hA = y := by
          apply F.distinctRanks
          have h₁ := (F.firstProperLossSeed_spec hA).2 y
            (F.firstProperLossSeed_spec hi).1
          have h₂ := (F.firstProperLossSeed_spec hi).2 (F.firstProperLossSeed hA)
            (F.firstProperLossSeed_spec hA).1
          change F.rank y ≤ F.rank (F.firstProperLossSeed hA) at h₂
          omega
        exact (F.firstParent_label_distinction hP hA (by
          rw [hs]
          exact hd)).elim
    change (real i && decide (F.label y = i)) = true
    simp [(real_ok i).mpr ⟨A, hi⟩, he]

def plan (S : SeedView F) : Plan H.vertexCount m :=
  ⟨F.rank, F.distinctRanks, S.observe⟩

theorem seed_first (S : SeedView F) {i : Fin m} {A : CutPair H}
    (hi : F.nodeKey? i = some A) :
    S.plan.atRank (F.rank (F.firstProperLossSeed hi)) =
      some (F.firstProperLossSeed hi) ∧
    S.plan.firstAt (F.firstProperLossSeed hi) i := by
  refine ⟨(S.plan.atRank_iff _ _).mpr rfl, S.hit hi, ?_⟩
  rintro ⟨z, hz, ho⟩
  obtain ⟨A', hA', ha⟩ := S.sound ho
  have e : A = A' := Option.some.inj (hi.symm.trans hA')
  subst A'
  have hle := (F.firstProperLossSeed_spec hi).2 z
    ((F.properLoss_iff_ancestor hi z).mpr ha)
  exact (Nat.not_lt_of_ge hle) hz

theorem earlier_seed (S : SeedView F) {i : Fin m} {A : CutPair H}
    (hi : F.nodeKey? i = some A) {k : Nat}
    (h : F.rank (F.firstProperLossSeed hi) < k) :
    S.plan.mapBefore k i :=
  ⟨F.firstProperLossSeed hi, h, S.hit hi⟩

end SeedView

section ForestReads

variable {H : LabelledQuotient} {m : Nat} (F : Forest H m)

def freshSource (i : Fin m) (p : Fin H.vertexCount) : Prop :=
  ∃ P B, F.nodeKey? i = some P ∧
    F.nodeKey? (F.parent i) = some B ∧ F.Fresh B P p

def onLabel (y : Fin H.vertexCount) (i : Fin m) : Prop :=
  ∃ A, F.nodeKey? i = some A ∧ F.ancestor i (F.label y)

/-- Parent-side installation can read the real parent's map and the real
maps on paths to fresh endpoints. Vertex bases may read earlier source
bases and the real maps on their own label path. -/
def forestReads : Reads H.vertexCount m where
  installBase := freshSource F
  installMap i j :=
    (j = F.parent i ∧ ∃ A, F.nodeKey? j = some A) ∨
    ∃ p, freshSource F i p ∧ onLabel F p j
  vertexBase y z := H.HasQuotientArc z y
  vertexMap := onLabel F

private theorem parent_seed_lt {i : Fin m} {P B : CutPair H}
    (hi : F.nodeKey? i = some P) (hb : F.nodeKey? (F.parent i) = some B) :
    F.rank (F.firstProperLossSeed hb) < F.rank (F.firstProperLossSeed hi) := by
  let y := F.firstProperLossSeed hi
  have hy : F.ProperLoss P y := (F.firstProperLossSeed_spec hi).1
  have hyB : F.ProperLoss B y := by
    first
    | exact F.edge_properLoss_subset hi hb y hy
    | exact F.edge_properLoss_subset i P B hi hb y hy
    | exact F.edge_properLoss_subset hi hb hy
  have hle := (F.firstProperLossSeed_spec hb).2 y hyB
  have hne : F.rank (F.firstProperLossSeed hb) ≠ F.rank y := by
    intro he
    have e : F.firstProperLossSeed hb = y := by
      apply F.distinctRanks
      exact he
    exact F.firstParent_label_distinction hi hb (by
      rw [e]
      exact (F.properLoss_iff_ancestor hi y).mp hy)
  change F.rank (F.firstProperLossSeed hb) < F.rank y
  omega

theorem forest_ready (S : SeedView F)
    (rankArc : ∀ z y, H.HasQuotientArc z y → F.rank z < F.rank y) :
    Ready S.plan (forestReads F) := by
  constructor
  · intro y i hf
    obtain ⟨P, hi, ha⟩ := S.sound hf.1
    have hle := (F.firstProperLossSeed_spec hi).2 y
      ((F.properLoss_iff_ancestor hi y).mpr ha)
    have fresh_lt {p : Fin H.vertexCount} (hp : freshSource F i p) :
        F.rank p < F.rank y := by
      obtain ⟨P', B, hi', hb, hp⟩ := hp
      exact Nat.lt_of_lt_of_le (F.freshEndpoint_dependencies hi' hb hp).2.1
        ((F.firstProperLossSeed_spec hi').2 y
          ((F.properLoss_iff_ancestor hi' y).mpr ha))
    refine ⟨fun p hp => fresh_lt hp, ?_⟩
    intro j hj
    change (j = F.parent i ∧ ∃ A, F.nodeKey? j = some A) ∨
      (∃ p, freshSource F i p ∧ onLabel F p j) at hj
    rcases hj with ⟨e, B, hb⟩ | ⟨p, hp, A, hj, haj⟩
    · subst j
      exact S.earlier_seed hb (Nat.lt_of_lt_of_le (parent_seed_lt F hi hb) hle)
    · obtain ⟨P', B, hi', hb, hp⟩ := hp
      have hs := ((F.freshEndpoint_dependencies hi' hb hp).2.2 hj haj).2
      exact S.earlier_seed hj (Nat.lt_of_lt_of_le hs
        ((F.firstProperLossSeed_spec hi').2 y
          ((F.properLoss_iff_ancestor hi' y).mpr ha)))
  · intro y
    constructor
    · exact fun z hz => rankArc z y hz
    intro i hi
    obtain ⟨A, hA, ha⟩ := hi
    have hle := (F.firstProperLossSeed_spec hA).2 y
      ((F.properLoss_iff_ancestor hA y).mpr ha)
    by_cases hlt : F.rank (F.firstProperLossSeed hA) < F.rank y
    · exact Or.inl (S.earlier_seed hA hlt)
    · have e : F.firstProperLossSeed hA = y := by
        apply F.distinctRanks
        omega
      right
      change S.observe y i = true
      simpa only [e] using S.hit hA

/-- The fresh endpoint base and every required real map are already in
the *pre-installation* snapshot of the computed sweep. -/
theorem fresh_available
    {M : Type u} {B : Type v} (S : SeedView F)
    (rankArc : ∀ z y, H.HasQuotientArc z y → F.rank z < F.rank y)
    {C : Callbacks (forestReads F) M B}
    {wantMap : Fin m → M} {wantBase : Fin H.vertexCount → B}
    (E : Exact S.plan C wantMap wantBase)
    {i : Fin m} {P A : CutPair H}
    (hi : F.nodeKey? i = some P) (ha : F.nodeKey? (F.parent i) = some A)
    {p : Fin H.vertexCount} (hp : F.Fresh A P p) :
    let k := F.rank (F.firstProperLossSeed hi)
    let s := runTo S.plan C k
    s.bases.read p = some (wantBase p) ∧
      ∀ j, onLabel F p j → s.maps.read j = some (wantMap j) := by
  dsimp only
  have h := runTo_prefix (forest_ready F S rankArc) E
    (F.rank (F.firstProperLossSeed hi))
  have hd := F.freshEndpoint_dependencies hi ha hp
  refine ⟨(h.bases p).1 hd.2.1, ?_⟩
  rintro j ⟨A', hj, hjp⟩
  exact (h.maps j).1 (S.earlier_seed hj (hd.2.2 hj hjp).2)

/-- Use the occurrence view's quotient-arc implication for `arc`.
Parallel occurrences do not need different base slots. -/
theorem occurrence_source_available
    {O : Type w} {M : Type u} {B : Type v} (S : SeedView F)
    (rankArc : ∀ z y, H.HasQuotientArc z y → F.rank z < F.rank y)
    (incoming : Fin H.vertexCount → O → Prop) (source : O → Fin H.vertexCount)
    (arc : ∀ y a, incoming y a → H.HasQuotientArc (source a) y)
    {C : Callbacks (forestReads F) M B}
    {wantMap : Fin m → M} {wantBase : Fin H.vertexCount → B}
    (E : Exact S.plan C wantMap wantBase)
    {y : Fin H.vertexCount} {a : O} (h : incoming y a) :
    (runTo S.plan C (F.rank y)).bases.read (source a) = some (wantBase (source a)) :=
  ((runTo_prefix (forest_ready F S rankArc) E (F.rank y)).bases (source a)).1
    (rankArc (source a) y (arc y a h))

end ForestReads

/-- Semantic witness for the actual proper-loss forest. This construction
is not part of the executable driver. -/
noncomputable def actualForest
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    Forest H ((buildProperLossForest H rank).realNodeCount + 1) where
  rank := rank
  distinctRanks := distinctRanks
  hasQuotientArc := H.HasQuotientArc
  mem := fun B y => B.Mem y
  lost := H.Lost
  nodeKey? := (buildProperLossForest H rank).nodeKey?
  parent := (buildProperLossForest H rank).parent
  label := (buildProperLossForest H rank).label
  ancestor := IsForestAncestor (buildProperLossForest H rank).parent
  ancestor_refl := fun _ => IsForestAncestor.refl
  real_has_properLoss := by
    intro u B hu
    exact ((buildProperLossForest_exists_node_iff rankArc flat B).mp ⟨u, hu⟩).2
  properLoss_iff_ancestor := by
    intro u B hu y
    exact buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat hu y
  edge_properLoss_subset := by
    intro u P B hu hb y hy
    exact buildProperLossForest_edge_properLoss_subset rankArc distinctRanks flat hu hb y hy
  edge_endpoints_lost := by
    intro u P B hu hb p hp
    exact buildProperLossForest_edge_endpoints_lost rankArc flat hu hb p hp
  edge_distinct_cuts := by
    intro u P B hu hb
    exact buildProperLossForest_edge_distinct_cuts rankArc flat hu hb
  properLoss_follows_endpoints := by
    intro B y b hy hb
    exact properLoss_follows_endpoints (B := B) rankArc flat hy hb
  predecessors_iff_endpoints_of_first_properLoss := by
    intro B y hy hfirst z
    exact predecessors_iff_endpoints_of_first_properLoss
      (B := B) rankArc flat hy hfirst z

end ArraySweep
end EX42
