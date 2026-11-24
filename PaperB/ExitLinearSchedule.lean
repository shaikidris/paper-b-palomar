module

public import PaperB.ExitArraySweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42.ArraySweep
universe u v w

namespace Slots
theorem eq_of_reads {α : Type u} {n : Nat} {s t : Slots α n}
    (h : ∀ i, s.read i = t.read i) : s = t := by
  have hd : s.data = t.data := by
    apply Array.ext
    · rw [s.size_data, t.size_data]
    · intro i hi _ht
      exact h ⟨i, by simpa only [s.size_data] using hi⟩
  cases s with
  | mk sd hs =>
    cases t with
    | mk td ht =>
      change sd = td at hd
      cases hd
      rfl

end Slots

def initial (n m : Nat) (M : Type u) (B : Type v) : State n m M B :=
  ⟨Slots.empty M m, Slots.empty B n⟩

structure OrderArray (n : Nat) where
  data : Array (Fin n)
  size_data : data.size = n

def OrderArray.get {n : Nat} (a : OrderArray n) (i : Fin n) : Fin n :=
  a.data[i.val]'(by simpa only [a.size_data] using i.isLt)

/--
Exact-array interface for EX4.2. The producer supplies the slot for the
first-created real/real parent edge, if any. `slot_exact` certifies both
directions: no first creation is omitted, and observations that are not
first creations do not cause writes. None of these certificates is
computed by the sweep.
-/
structure Schedule {n m : Nat} (P : Plan n m) where
  order : OrderArray n
  increasing : ∀ i j : Fin n, i.val < j.val →
    P.rank (order.get i) < P.rank (order.get j)
  covers : ∀ y : Fin n, ∃ i : Fin n, order.get i = y
  mapSlot : Slots (Fin m) n
  slot_exact : ∀ y i, mapSlot.read y = some i ↔ P.firstAt y i

namespace Schedule

variable {n m : Nat} {P : Plan n m}

abbrev vertex (S : Schedule P) (i : Fin n) : Fin n :=
  S.order.get i

theorem rank_lt_rank_iff (S : Schedule P) (a b : Fin n) :
    P.rank (S.vertex a) < P.rank (S.vertex b) ↔ a.val < b.val := by
  constructor
  · intro hr
    by_cases h : a.val < b.val
    · exact h
    · by_cases he : a.val = b.val
      · have e : a = b := Fin.ext he
        subst b
        exact (Nat.lt_irrefl _ hr).elim
      · have hba : b.val < a.val := by omega
        have hr' : P.rank (S.vertex b) < P.rank (S.vertex a) :=
          S.increasing b a hba
        exact (Nat.lt_irrefl (P.rank (S.vertex a)) (Nat.lt_trans hr hr')).elim
  · exact S.increasing a b

theorem vertex_inj (S : Schedule P) {a b : Fin n}
    (h : S.vertex a = S.vertex b) : a = b := by
  apply Fin.ext
  have h₁ : ¬ a.val < b.val := by
    intro hab
    have hr := (S.rank_lt_rank_iff a b).2 hab
    rw [h] at hr
    exact (Nat.lt_irrefl _) hr
  have h₂ : ¬ b.val < a.val := by
    intro hba
    have hr := (S.rank_lt_rank_iff b a).2 hba
    rw [h] at hr
    exact (Nat.lt_irrefl _) hr
  omega

theorem vertex_once (S : Schedule P) (y : Fin n) :
    ∃ a : Fin n, S.vertex a = y ∧
      ∀ b : Fin n, S.vertex b = y → b = a := by
  obtain ⟨a, ha⟩ := S.covers y
  exact ⟨a, ha, fun b hb => S.vertex_inj (hb.trans ha.symm)⟩

theorem install_once (S : Schedule P) {a b : Fin n} {i j : Fin m}
    (ha : S.mapSlot.read (S.vertex a) = some i)
    (hb : S.mapSlot.read (S.vertex b) = some j)
    (h : S.vertex a = S.vertex b) : a = b ∧ i = j := by
  have e := S.vertex_inj h
  subst b
  exact ⟨rfl, Option.some.inj (ha.symm.trans hb)⟩

/-- Reference cutoff after `j` indexed visits. Never evaluated by the loop. -/
def cut (S : Schedule P) (j : Nat) : Nat :=
  if h : j < n then P.rank (S.vertex ⟨j, h⟩) else P.limit

theorem cut_at (S : Schedule P) (a : Fin n) :
    S.cut a.val = P.rank (S.vertex a) := by
  cases a with
  | mk i hi => simp [cut, hi]

@[simp] theorem cut_end (S : Schedule P) : S.cut n = P.limit := by
  simp [cut]

theorem lt_cut_iff (S : Schedule P) (j : Nat) (hj : j ≤ n) (i : Fin n) :
    P.rank (S.vertex i) < S.cut j ↔ i.val < j := by
  by_cases h : j < n
  · have hc : S.cut j = P.rank (S.vertex (⟨j, h⟩ : Fin n)) :=
      S.cut_at ⟨j, h⟩
    rw [hc]
    exact S.rank_lt_rank_iff i ⟨j, h⟩
  · have e : j = n := by omega
    subst j
    rw [S.cut_end]
    exact ⟨fun _ => i.isLt, fun _ => P.rank_lt_limit _⟩

/-- Moving to the next cutoff crosses no further occupied rank. -/
theorem after_cut (S : Schedule P) (a : Fin n) (y : Fin n) :
    P.rank y < P.rank (S.vertex a) + 1 ↔ P.rank y < S.cut (a.val + 1) := by
  obtain ⟨b, hb⟩ := S.covers y
  have ha := a.isLt
  rw [← hb, S.lt_cut_iff (a.val + 1) (by omega) b]
  constructor
  · intro hr
    by_cases h : b.val < a.val + 1
    · exact h
    · have hab : a.val < b.val := by omega
      have hr' : P.rank (S.vertex a) < P.rank (S.vertex b) :=
        S.increasing a b hab
      have hle : P.rank (S.vertex a) + 1 ≤ P.rank (S.vertex b) :=
        Nat.succ_le_of_lt hr'
      exact (Nat.lt_irrefl (P.rank (S.vertex b)) (Nat.lt_of_lt_of_le hr hle)).elim
  · intro h
    by_cases he : b.val = a.val
    · have e : b = a := Fin.ext he
      rw [e]
      exact Nat.lt_succ_self _
    · have hba : b.val < a.val := by omega
      have hr : P.rank (S.vertex b) < P.rank (S.vertex a) :=
        S.increasing b a hba
      exact Nat.lt_trans hr (Nat.lt_succ_self (P.rank (S.vertex a)))

/-- Even a cutoff that is not an occupied rank separates an indexed prefix. -/
theorem exists_split (S : Schedule P) (k : Nat) :
    ∃ j : Nat, j ≤ n ∧
      ∀ a : Fin n, a.val < j ↔ P.rank (S.vertex a) < k := by
  have aux (l : Nat) (hl : l ≤ n) :
      ∃ j : Nat, j ≤ l ∧ ∀ a : Fin n, a.val < l →
        (a.val < j ↔ P.rank (S.vertex a) < k) := by
    induction l with
    | zero =>
      exact ⟨0, Nat.le_refl _, fun a ha => (Nat.not_lt_zero a.val ha).elim⟩
    | succ l ih =>
      let b : Fin n := ⟨l, by omega⟩
      by_cases hb : P.rank (S.vertex b) < k
      · refine ⟨l + 1, Nat.le_refl _, ?_⟩
        intro a ha
        refine ⟨fun _ => ?_, fun _ => ha⟩
        by_cases h : a.val < l
        · exact Nat.lt_trans (S.increasing a b h) hb
        · have e : a = b := Fin.ext (by change a.val = l; omega)
          simpa only [e] using hb
      · obtain ⟨j, hj, hs⟩ := ih (by omega)
        refine ⟨j, by omega, ?_⟩
        intro a ha
        by_cases h : a.val < l
        · exact hs a h
        · have e : a = b := Fin.ext (by change a.val = l; omega)
          have hn : ¬ P.rank (S.vertex a) < k := by simpa only [e] using hb
          exact ⟨fun hja => (h (Nat.lt_of_lt_of_le hja hj)).elim,
            fun hr => (hn hr).elim⟩
  obtain ⟨j, hj, hs⟩ := aux n (Nat.le_refl _)
  exact ⟨j, hj, fun a => hs a a.isLt⟩

/-- One order-array read and one slot-array read per iteration.
The recursion is on the number of entries, not on a numeric rank. -/
def foldFrom {A : Type w} (S : Schedule P)
    (f : A → Fin n → Option (Fin m) → A) :
    (fuel start : Nat) → start + fuel ≤ n → A → A
  | 0, _, _, acc => acc
  | fuel + 1, start, h, acc =>
    let y := S.vertex ⟨start, by omega⟩
    foldFrom S f fuel (start + 1) (by omega) (f acc y (S.mapSlot.read y))

end Schedule

section Indexed

variable {n m : Nat} {M : Type u} {B : Type v} {D : Reads n m}
  {P : Plan n m} {C : Callbacks D M B}
  {wantMap : Fin m → M} {wantBase : Fin n → B}

/-- A present slot is certified empty in the pre-vertex state.
The installer receives that old state, including its old maps. -/
def stageOne (C : Callbacks D M B) (s : State n m M B)
    (y : Fin n) (o : Option (Fin m)) : Slots M m :=
  match o with
  | none => s.maps
  | some i => s.maps.write i (makeMap C s y i)

/-- The base callback receives old bases and the newly staged maps. -/
def visitOne (C : Callbacks D M B) (s : State n m M B)
    (y : Fin n) (o : Option (Fin m)) : State n m M B :=
  let ms := stageOne C s y o
  ⟨ms, s.bases.write y (makeBase C s y ms)⟩

def runPrefix (S : Schedule P) (C : Callbacks D M B)
    (j : Nat) (hj : j ≤ n) : State n m M B :=
  S.foldFrom (visitOne C) j 0 (by simpa only [Nat.zero_add] using hj)
    (initial n m M B)

/-- Executable entry point. Neither `Plan.limit` nor `Plan.atRank` nor
`stageMaps` occurs on its execution path. -/
def runIndexed (S : Schedule P) (C : Callbacks D M B) : State n m M B :=
  runPrefix S C n (Nat.le_refl n)

/-- Equality of the actual map arrays, not just equality of wanted outputs.
This local simulation needs the presence invariant and the exact slot
contract, but does not need correctness of either callback's result. -/
theorem stageOne_eq_stageMaps (S : Schedule P)
    {s : State n m M B} {y : Fin n}
    (h : Prefix P wantMap wantBase (P.rank y) s) :
    stageOne C s y (S.mapSlot.read y) = stageMaps P C s y := by
  apply Slots.eq_of_reads
  intro i
  rw [stageMaps, scanMaps_read]
  by_cases hf : P.firstAt y i
  · have ht := (S.slot_exact y i).2 hf
    have he := (h.maps i).2 hf.2
    simp [stageOne, ht, he, hf.1]
  · have hread : (stageOne C s y (S.mapSlot.read y)).read i = s.maps.read i := by
      cases e : S.mapSlot.read y with
      | none => simp [stageOne]
      | some j =>
        have hne : i ≠ j := by
          intro hij
          subst j
          exact hf ((S.slot_exact y i).1 e)
        simpa only [stageOne, e] using
          (Slots.read_write_other s.maps j i (makeMap C s y j) hne)
    rw [hread]
    by_cases hp : P.mapBefore (P.rank y) i
    · rw [(h.maps i).1 hp]
    · have ho : P.observe y i ≠ true := fun ho => hf ⟨ho, hp⟩
      simp [(h.maps i).2 hp, ho]

theorem visitOne_eq_visit (S : Schedule P)
    {s : State n m M B} {y : Fin n}
    (h : Prefix P wantMap wantBase (P.rank y) s) :
    visitOne C s y (S.mapSlot.read y) = visit P C s y := by
  simp only [visitOne, visit, stageOne_eq_stageMaps (C := C) S h]

theorem prefix_reindex {a b : Nat} {s : State n m M B}
    (hr : ∀ y, P.rank y < a ↔ P.rank y < b)
    (h : Prefix P wantMap wantBase a s) :
    Prefix P wantMap wantBase b s := by
  constructor
  · intro i
    have hm : P.mapBefore a i ↔ P.mapBefore b i :=
      ⟨fun ⟨y, hy, ho⟩ => ⟨y, (hr y).1 hy, ho⟩,
        fun ⟨y, hy, ho⟩ => ⟨y, (hr y).2 hy, ho⟩⟩
    rw [← hm]
    exact h.maps i
  · intro y
    rw [← hr y]
    exact h.bases y

private theorem cell_eq {A : Type w} {p : Prop} {a b : Option A} {v : A}
    (ha : Cell p a v) (hb : Cell p b v) : a = b := by
  classical
  by_cases h : p
  · exact (ha.1 h).trans (hb.1 h).symm
  · exact (ha.2 h).trans (hb.2 h).symm

theorem prefix_state_eq {k : Nat} {s t : State n m M B}
    (hs : Prefix P wantMap wantBase k s)
    (ht : Prefix P wantMap wantBase k t) : s = t := by
  have hm : s.maps = t.maps :=
    Slots.eq_of_reads (fun i => cell_eq (hs.maps i) (ht.maps i))
  have hb : s.bases = t.bases :=
    Slots.eq_of_reads (fun y => cell_eq (hs.bases y) (ht.bases y))
  cases s with
  | mk sm sb =>
    cases t with
    | mk tm tb =>
      change sm = tm at hm
      change sb = tb at hb
      cases hm
      cases hb
      rfl

theorem foldFrom_prefix (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (fuel : Nat) :
    ∀ (start : Nat) (h : start + fuel ≤ n) (s : State n m M B),
      Prefix P wantMap wantBase (S.cut start) s →
      Prefix P wantMap wantBase (S.cut (start + fuel))
        (S.foldFrom (visitOne C) fuel start h s) := by
  induction fuel with
  | zero =>
    intro start h s hs
    simpa only [Schedule.foldFrom, Nat.add_zero] using hs
  | succ fuel ih =>
    intro start h s hs
    let a : Fin n := ⟨start, by omega⟩
    let y := S.vertex a
    have hc : S.cut start = P.rank y := S.cut_at a
    have hp : Prefix P wantMap wantBase (P.rank y) s := by
      simpa only [hc] using hs
    have hv : Prefix P wantMap wantBase (P.rank y + 1)
        (visitOne C s y (S.mapSlot.read y)) := by
      rw [visitOne_eq_visit S hp]
      exact visit_prefix R E hp
    have hn : Prefix P wantMap wantBase (S.cut (start + 1))
        (visitOne C s y (S.mapSlot.read y)) :=
      prefix_reindex (S.after_cut a) hv
    have hh : start + 1 + fuel ≤ n := by omega
    have he : start + 1 + fuel = start + (fuel + 1) := by omega
    simpa only [Schedule.foldFrom, he, y, a] using
      ih (start + 1) hh (visitOne C s y (S.mapSlot.read y)) hn

theorem runPrefix_prefix (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (j : Nat) (hj : j ≤ n) :
    Prefix P wantMap wantBase (S.cut j) (runPrefix S C j hj) := by
  have hz (y : Fin n) : P.rank y < 0 ↔ P.rank y < S.cut 0 := by
    obtain ⟨i, hi⟩ := S.covers y
    rw [← hi, S.lt_cut_iff 0 (Nat.zero_le n) i]
    exact ⟨fun h => (Nat.not_lt_zero _ h).elim,
      fun h => (Nat.not_lt_zero _ h).elim⟩
  have h0 : Prefix P wantMap wantBase (S.cut 0) (initial n m M B) :=
    prefix_reindex hz (runTo_prefix R E 0)
  have hh : 0 + j ≤ n := by omega
  simpa only [runPrefix, Nat.zero_add] using
    foldFrom_prefix S R E j 0 hh (initial n m M B) h0

theorem runPrefix_eq_runTo (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (j : Nat) (hj : j ≤ n) :
    runPrefix S C j hj = runTo P C (S.cut j) :=
  prefix_state_eq (runPrefix_prefix S R E j hj)
    (runTo_prefix R E (S.cut j))

/-- Agreement at any integer cutoff, including cutoffs in rank gaps. -/
theorem runPrefix_eq_runTo_of_split (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (j k : Nat) (hj : j ≤ n)
    (hs : ∀ a : Fin n, a.val < j ↔ P.rank (S.vertex a) < k) :
    runPrefix S C j hj = runTo P C k := by
  have hr (y : Fin n) : P.rank y < S.cut j ↔ P.rank y < k := by
    obtain ⟨a, ha⟩ := S.covers y
    rw [← ha, S.lt_cut_iff j hj a]
    exact hs a
  exact prefix_state_eq (prefix_reindex hr (runPrefix_prefix S R E j hj))
    (runTo_prefix R E k)

theorem reference_prefix_is_indexed (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (k : Nat) :
    ∃ (j : Nat) (hj : j ≤ n), runPrefix S C j hj = runTo P C k := by
  obtain ⟨j, hj, hs⟩ := S.exists_split k
  exact ⟨j, hj, runPrefix_eq_runTo_of_split S R E j k hj hs⟩

theorem runIndexed_eq_run (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) :
    runIndexed S C = run P C := by
  simpa only [runIndexed, run, Schedule.cut_end] using
    runPrefix_eq_runTo S R E n (Nat.le_refl n)

theorem runIndexed_base_exact (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (y : Fin n) :
    (runIndexed S C).bases.read y = some (wantBase y) := by
  rw [runIndexed_eq_run S R E]
  exact ((runTo_prefix R E P.limit).bases y).1 (P.rank_lt_limit y)

theorem runIndexed_map_exact (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (i : Fin m) :
    Cell (∃ y, P.observe y i = true)
      ((runIndexed S C).maps.read i) (wantMap i) := by
  have hm : P.mapBefore P.limit i ↔ ∃ y, P.observe y i = true :=
    ⟨fun ⟨y, _, ho⟩ => ⟨y, ho⟩,
      fun ⟨y, ho⟩ => ⟨y, P.rank_lt_limit y, ho⟩⟩
  rw [runIndexed_eq_run S R E, ← hm]
  exact (runTo_prefix R E P.limit).maps i

theorem indexed_first_install (S : Schedule P) (R : Ready P D)
    (E : Exact P C wantMap wantBase) (a : Fin n) {i : Fin m}
    (hi : S.mapSlot.read (S.vertex a) = some i) :
    let s := runPrefix S C a.val (Nat.le_of_lt a.isLt)
    s.maps.read i = none ∧
      (stageOne C s (S.vertex a) (S.mapSlot.read (S.vertex a))).read i =
        some (wantMap i) := by
  let s := runPrefix S C a.val (Nat.le_of_lt a.isLt)
  have hp : Prefix P wantMap wantBase (P.rank (S.vertex a)) s := by
    simpa only [S.cut_at a] using
      runPrefix_prefix S R E a.val (Nat.le_of_lt a.isLt)
  have hf := (S.slot_exact (S.vertex a) i).1 hi
  change s.maps.read i = none ∧
    (stageOne C s (S.vertex a) (S.mapSlot.read (S.vertex a))).read i =
      some (wantMap i)
  refine ⟨(hp.maps i).2 hf.2, ?_⟩
  rw [stageOne_eq_stageMaps S hp]
  exact (stageMaps_prefix R E hp i).1 (Or.inr hf.1)

end Indexed

section Counts

variable {n m : Nat} {M : Type u} {B : Type v} {D : Reads n m}
  {P : Plan n m}

/- The audit uses the very same indexed loop and visit body. It is not
   called by `runIndexed`. One `some` branch means exactly one installer
   call and one map write; `none` means neither. -/
structure Counts where
  rankSlots : Nat
  visits : Nat
  installs : Nat

def installCost {m : Nat} : Option (Fin m) → Nat
  | none => 0
  | some _ => 1

theorem installCost_le_one (o : Option (Fin m)) : installCost o ≤ 1 := by
  cases o with
  | none =>
    change 0 ≤ 1
    exact Nat.zero_le 1
  | some i =>
    change 1 ≤ 1
    exact Nat.le_refl 1

def Counts.charge (c : Counts) (o : Option (Fin m)) : Counts :=
  ⟨c.rankSlots + 1, c.visits + 1, c.installs + installCost o⟩

def countedVisit (C : Callbacks D M B) (acc : State n m M B × Counts)
    (y : Fin n) (o : Option (Fin m)) : State n m M B × Counts :=
  (visitOne C acc.1 y o, acc.2.charge o)

theorem foldFrom_counts (S : Schedule P) (C : Callbacks D M B) (fuel : Nat) :
    ∀ (start : Nat) (h : start + fuel ≤ n) (s : State n m M B) (c : Counts),
      let z := S.foldFrom (countedVisit C) fuel start h (s, c)
      z.1 = S.foldFrom (visitOne C) fuel start h s ∧
      z.2.rankSlots = c.rankSlots + fuel ∧
      z.2.visits = c.visits + fuel ∧
      z.2.installs ≤ c.installs + fuel := by
  induction fuel with
  | zero =>
    intro start h s c
    simp [Schedule.foldFrom]
  | succ fuel ih =>
    intro start h s c
    let a : Fin n := ⟨start, by omega⟩
    let y := S.vertex a
    let o := S.mapSlot.read y
    have ht := ih (start + 1) (by omega) (visitOne C s y o) (c.charge o)
    simp only [Schedule.foldFrom, countedVisit]
    refine ⟨ht.1, ht.2.1.trans ?_, ht.2.2.1.trans ?_, ?_⟩
    · simp only [Counts.charge]
      omega
    · simp only [Counts.charge]
      omega
    · have hcost := installCost_le_one o
      have hb := ht.2.2.2
      change _ ≤ c.installs + installCost o + fuel at hb
      exact Nat.le_trans hb (by omega)

theorem runIndexed_counts (S : Schedule P) (C : Callbacks D M B) :
    let z := S.foldFrom (countedVisit C) n 0 (by omega)
      (initial n m M B, ⟨0, 0, 0⟩)
    z.1 = runIndexed S C ∧
    z.2.rankSlots = S.order.data.size ∧
    z.2.visits = n ∧ z.2.installs ≤ n := by
  simpa only [runIndexed, runPrefix, S.order.size_data, Nat.zero_add] using
    foldFrom_counts S C n 0 (by omega) (initial n m M B) ⟨0, 0, 0⟩

end Counts

end EX42.ArraySweep
