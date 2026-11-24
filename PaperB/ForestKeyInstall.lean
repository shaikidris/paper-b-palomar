module

public import PaperB.ForestHead
public import PaperB.PairLookup
public import PaperB.Jumps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
EX2.4 — dynamic pair installation.

Place this module after the supplied declarations, or import the modules
containing those declarations before this block. The question does not give
their import paths.

The dictionary and all table capacities are fixed before the sweep. A
dictionary index is not a jump slot. Slot 0 means “not installed”; jump
node 0 is the root. No installation branch enumerates a table or resizes
an array. The write bound counts logical table/word writes, not Lean's
copy-on-write costs for arrays retained by a caller.
-/

namespace EX24

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

structure Config (H : LabelledQuotient) where
  region : JumpWordRegion
  dict : Array Key
  sorted : PairLookup.StrictSorted dict
  code : CutPair H → Key
  code_inj : ∀ {a b}, code a = code b → a = b
  vertexIndex : Vertex H → Nat
  vertexIndex_inj : ∀ {u v}, vertexIndex u = vertexIndex v → u = v
  zeroKey : CutPair H
  atDepth : JumpWordRegion → Array Nat → Nat → Nat → Nat
  ancestor : JumpWordRegion → Array Nat → Nat → Nat → Bool

structure Tables (H : LabelledQuotient) where
  mem : Array Nat
  slots : Array Nat
  back : Array (Option (CutPair H))
  next : Nat

def Tables.slotAt {H : LabelledQuotient} (t : Tables H) (i : Nat) : Nat :=
  (t.slots[i]?).getD 0

structure State (H : LabelledQuotient) where
  tables : Tables H
  labels : Array Nat

def State.labelAt {H : LabelledQuotient} (s : State H) (i : Nat) : Nat :=
  (s.labels[i]?).getD 0

def selectors {H : LabelledQuotient} (c : Config H) (s : State H) :
    Selectors H where
  label v := s.labelAt (c.vertexIndex v)
  depth n := (readRecordWords c.region s.tables.mem n).1.depth
  atDepth := c.atDepth c.region s.tables.mem
  ancestor := c.ancestor c.region s.tables.mem
  key n :=
    match s.tables.back[n]? with
    | some (some q) => q
    | _ => c.zeroKey

structure Grounded {H : LabelledQuotient} (c : Config H)
    (F : JumpForest) (t : Tables H) : Prop where
  layout : JumpWordLayout c.region F t.mem
  size_eq : F.size = t.next
  slot_size : t.slots.size = c.dict.size
  back_size : t.back.size = c.region.maxNodes + 1
  zero : t.back[0]? = some none
  forward : ∀ i, t.slotAt i ≠ 0 → ∃ q,
    (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
      t.back[t.slotAt i]? = some (some q)
  backward : ∀ n q, t.back[n]? = some (some q) →
    n < t.next ∧ n ≠ 0 ∧ ∃ i,
      (PairLookup.lookup c.dict (c.code q)).1 = some i ∧ t.slotAt i = n

def initial {H : LabelledQuotient} (c : Config H) (mem : Array Nat)
    (vertexCapacity : Nat) : State H :=
  ⟨⟨mem, Array.replicate c.dict.size 0,
      Array.replicate (c.region.maxNodes + 1) none, 1⟩,
    Array.replicate vertexCapacity 0⟩

theorem initial_grounded {H : LabelledQuotient} (c : Config H)
    {F : JumpForest} {mem : Array Nat}
    (h : JumpWordLayout c.region F mem) (hs : F.size = 1) (n : Nat) :
    Grounded c F (initial c mem n).tables := by
  refine ⟨h, hs, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · simp [initial]
  · simp [initial, getElem?_def]
  · intro i hi
    by_cases hb : i < c.dict.size <;>
      simp [initial, Tables.slotAt, getElem?_def, hb] at hi
  · intro j q hj
    by_cases hb : j < c.region.maxNodes + 1 <;>
      simp [initial, getElem?_def, hb] at hj

private theorem opt_set {α : Type} (a : Array α) (i : Nat)
    (hi : i < a.size) (v : α) (j : Nat) :
    (a.set i v hi)[j]? = if j = i then some v else a[j]? := by
  by_cases e : j = i
  · subst j
    simp [getElem?_def, Array.getElem_set, hi]
  · by_cases hj : j < a.size
    · simp [getElem?_def, Array.getElem_set, hj, e, Ne.symm e]
    · simp [getElem?_def, hj, e]

structure Installed (H : LabelledQuotient) where
  tables : Tables H
  node : Nat
  allocated : Bool
  accesses : List WordAccess

def Installed.delta {H : LabelledQuotient} (r : Installed H) : Nat :=
  if r.allocated then 1 else 0

private def isWrite : WordAccess → Bool
  | .write _ _ => true
  | _ => false

/-- One label write; on allocation, also one slot, reverse-key, and
next-slot write, plus the writes in the grounded jump trace. -/
def Installed.writes {H : LabelledQuotient} (r : Installed H) : Nat :=
  1 + 3 * r.delta + (r.accesses.filter isWrite).length

private def keep {H : LabelledQuotient} (t : Tables H) (n : Nat) :
    Installed H :=
  ⟨t, n, false, []⟩

private def grow {H : LabelledQuotient} (c : Config H) (t : Tables H)
    (p : Nat) (q : CutPair H) (i : Nat) (hi : i < t.slots.size)
    (hn : t.next < t.back.size) : Installed H :=
  let w := appendLeafWords c.region t.mem p
  ⟨⟨w.1, t.slots.set i t.next hi, t.back.set t.next (some q) hn,
       t.next + 1⟩, t.next, true, w.2⟩

/-- A request with no new pair selects its parent, including the stopped
case with parent 0. A hit on a positive slot never calls `appendLeafWords`. -/
def install {H : LabelledQuotient} (c : Config H) (t : Tables H)
    (req : ForestHead.Step H) : Option (Installed H) :=
  if req.parent < t.next then
    match req.newPair with
    | none => some (keep t req.parent)
    | some q =>
      match (PairLookup.lookup c.dict (c.code q)).1 with
      | none => none
      | some i =>
        if hi : i < t.slots.size then
          let n := t.slotAt i
          if n = 0 then
            if hn : t.next < t.back.size then
              some (grow c t req.parent q i hi hn)
            else none
          else some (keep t n)
        else none
  else none

def Selection {H : LabelledQuotient} (c : Config H) (t : Tables H)
    (req : ForestHead.Step H) (r : Installed H) : Prop :=
  match req.newPair with
  | none => r.node = req.parent ∧ r.allocated = false
  | some q => ∃ i,
      (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
      r.tables.slotAt i = r.node ∧ r.node ≠ 0 ∧
      r.tables.back[r.node]? = some (some q) ∧
      (r.allocated = true ↔ t.slotAt i = 0)

structure InstallOK {H : LabelledQuotient} (c : Config H) (F : JumpForest)
    (t : Tables H) (req : ForestHead.Step H) (r : Installed H) : Prop where
  grounded :
    Grounded c (if r.allocated then F.appendLeaf req.parent else F) r.tables
  next_eq : r.tables.next = t.next + r.delta
  node_lt : r.node < r.tables.next
  old_slot : ∀ i, t.slotAt i ≠ 0 → r.tables.slotAt i = t.slotAt i
  old_back : ∀ n, n < t.next → r.tables.back[n]? = t.back[n]?
  selection : Selection c t req r
  trace_bound : r.accesses.length ≤ 14 * r.delta
  no_allocation : r.allocated = false → r.tables = t

private theorem keep_ok {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H} {n : Nat}
    (g : Grounded c F t) (hn : n < t.next)
    (sel : Selection c t req (keep t n)) :
    InstallOK c F t req (keep t n) := by
  refine ⟨g, ?_, hn, ?_, ?_, sel, ?_, ?_⟩
  · simp [keep, Installed.delta]
  · intros
    rfl
  · intros
    rfl
  · simp [keep, Installed.delta]
  · intro _
    rfl

private theorem grow_ok {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H}
    {q : CutPair H} {i : Nat} (g : Grounded c F t)
    (hp : req.parent < t.next) (hq : req.newPair = some q)
    (hit : (PairLookup.lookup c.dict (c.code q)).1 = some i)
    (hi : i < t.slots.size) (hz : t.slotAt i = 0)
    (hn : t.next < t.back.size) :
    InstallOK c F t req (grow c t req.parent q i hi hn) := by
  let r := grow c t req.parent q i hi hn
  change InstallOK c F t req r
  have hpF : req.parent < F.size := by rw [g.size_eq]; exact hp
  have hpos : 0 < t.next := by omega
  have hcap : t.next < c.region.maxNodes + 1 := by
    simpa only [g.back_size] using hn
  have room : F.numInserted < c.region.maxNodes := by
    change F.size - 1 < c.region.maxNodes
    rw [g.size_eq]
    omega
  obtain ⟨lay, _, hlen, _, _⟩ := appendLeafWords_spec g.layout room hpF
  have hs (j : Nat) :
      r.tables.slotAt j = if j = i then t.next else t.slotAt j := by
    change ((t.slots.set i t.next hi)[j]?).getD 0 = _
    by_cases e : j = i <;> simp [opt_set, e, Tables.slotAt]
  have hb (n : Nat) :
      r.tables.back[n]? =
        if n = t.next then some (some q) else t.back[n]? := by
    exact opt_set t.back t.next hn (some q) n
  have oldSlot (j : Nat) (hj : t.slotAt j ≠ 0) :
      r.tables.slotAt j = t.slotAt j := by
    have e : j ≠ i := by
      intro e
      subst j
      exact hj hz
    rw [hs, if_neg e]
  have oldBack (n : Nat) (hn' : n < t.next) :
      r.tables.back[n]? = t.back[n]? := by
    rw [hb, if_neg (Nat.ne_of_lt hn')]
  have newSlot : r.tables.slotAt i = t.next := by simp [hs]
  have newBack : r.tables.back[t.next]? = some (some q) := by simp [hb]
  have g' : Grounded c (F.appendLeaf req.parent) r.tables := by
    refine ⟨lay, ?_, ?_, ?_, oldBack 0 hpos |>.trans g.zero, ?_, ?_⟩
    · change (F.appendLeaf req.parent).size = t.next + 1
      rw [F.size_appendLeaf req.parent, g.size_eq]
    · simpa [r, grow] using g.slot_size
    · simpa [r, grow] using g.back_size
    · intro j hj
      by_cases e : j = i
      · subst j
        exact ⟨q, hit, by rw [newSlot]; exact newBack⟩
      · have he : r.tables.slotAt j = t.slotAt j := by rw [hs, if_neg e]
        obtain ⟨k, hk, hkey⟩ := g.forward j (he ▸ hj)
        have hl := (g.backward (t.slotAt j) k hkey).1
        exact ⟨k, hk, by rw [he, oldBack _ hl]; exact hkey⟩
    · intro n k hkey
      by_cases e : n = t.next
      · subst n
        have same : q = k := Option.some.inj (Option.some.inj
          (newBack.symm.trans hkey))
        subst k
        exact ⟨Nat.lt_succ_self _, Nat.ne_of_gt hpos, i, hit, newSlot⟩
      · have hkey' : t.back[n]? = some (some k) := by
          simpa only [hb, if_neg e] using hkey
        obtain ⟨hl, hne, j, hj, hjn⟩ := g.backward n k hkey'
        have hj0 : t.slotAt j ≠ 0 := by
          rw [hjn]
          exact hne
        have hl' : n < r.tables.next := by
          change n < t.next + 1
          omega
        exact ⟨hl', hne, j, hj, (oldSlot j hj0).trans hjn⟩
  refine ⟨g', ?_, ?_, oldSlot, oldBack, ?_, ?_, ?_⟩
  · rfl
  · change t.next < t.next + 1
    exact Nat.lt_succ_self _
  · unfold Selection
    rw [hq]
    refine ⟨i, hit, newSlot, Nat.ne_of_gt hpos, newBack, ?_⟩
    change (true = true ↔ t.slotAt i = 0)
    simp [hz]
  · change (appendLeafWords c.region t.mem req.parent).2.length ≤ 14 * 1
    simp [hlen]
  · intro hfalse
    change true = false at hfalse
    cases hfalse

private theorem same_pair_of_hit {H : LabelledQuotient} (c : Config H)
    {q k : CutPair H} {i : Nat}
    (hq : (PairLookup.lookup c.dict (c.code q)).1 = some i)
    (hk : (PairLookup.lookup c.dict (c.code k)).1 = some i) : q = k := by
  obtain ⟨_, eqQ⟩ :=
    (PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted i).mp hq
  obtain ⟨_, eqK⟩ :=
    (PairLookup.lookup_eq_some_iff c.dict (c.code k) c.sorted i).mp hk
  exact c.code_inj (eqQ.symm.trans eqK)

theorem install_spec {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H}
    {r : Installed H} (g : Grounded c F t)
    (h : install c t req = some r) : InstallOK c F t req r := by
  by_cases hp : req.parent < t.next
  · cases hq : req.newPair with
    | none =>
      simp only [install, if_pos hp, hq] at h
      have er := Option.some.inj h
      subst r
      apply keep_ok g hp
      simp [Selection, hq, keep]
    | some q =>
      cases hk : (PairLookup.lookup c.dict (c.code q)).1 with
      | none => simp [install, hp, hq, hk] at h
      | some i =>
        by_cases hi : i < t.slots.size
        · by_cases hz : t.slotAt i = 0
          · by_cases hn : t.next < t.back.size
            · simp only [install, if_pos hp, hq, hk, dif_pos hi,
                if_pos hz, dif_pos hn] at h
              have er := Option.some.inj h
              subst r
              exact grow_ok g hp hq hk hi hz hn
            · simp [install, hp, hq, hk, hi, hz, hn] at h
          · simp only [install, if_pos hp, hq, hk, dif_pos hi, if_neg hz] at h
            have er := Option.some.inj h
            subst r
            obtain ⟨k, hki, hback⟩ := g.forward i hz
            have same := same_pair_of_hit c hk hki
            subst k
            apply keep_ok g (g.backward (t.slotAt i) q hback).1
            unfold Selection
            rw [hq]
            refine ⟨i, hk, rfl, hz, hback, ?_⟩
            simp [keep, hz]
        · simp [install, hp, hq, hk, hi] at h
  · simp [install, hp] at h

/-- A covered request succeeds. A full region is allowed on a reuse. -/
theorem install_exists {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H}
    (g : Grounded c F t) (hp : req.parent < t.next)
    (cover : ∀ q, req.newPair = some q → ∃ i,
      (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
      (t.slotAt i = 0 → t.next < t.back.size)) :
    ∃ r, install c t req = some r := by
  cases hq : req.newPair with
  | none =>
    exact ⟨keep t req.parent, by simp [install, hp, hq]⟩
  | some q =>
    obtain ⟨i, hk, capacity⟩ := cover q hq
    obtain ⟨hi', _⟩ :=
      (PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted i).mp hk
    have hi : i < t.slots.size := by simpa only [g.slot_size] using hi'
    by_cases hz : t.slotAt i = 0
    · have hn := capacity hz
      exact ⟨grow c t req.parent q i hi hn,
        by simp [install, hp, hq, hk, hi, hz, hn]⟩
    · exact ⟨keep t (t.slotAt i), by simp [install, hp, hq, hk, hi, hz]⟩

structure HeadResult (H : LabelledQuotient) where
  measured : Measured H
  installed : Installed H
  labels : Array Nat

def HeadResult.state {H : LabelledQuotient} (r : HeadResult H) : State H :=
  ⟨r.installed.tables, r.labels⟩

/-- Run the original kernel on the previous tables, then commit its
request and write the head's label exactly once on success. -/
def step {H : LabelledQuotient} (c : Config H) (s : State H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H)) :
    Option (HeadResult H) :=
  if hy : c.vertexIndex y < s.labels.size then
    let m := ForestHead.runHead (selectors c s) rank y xs
    (install c s.tables m.step).map fun r =>
      ⟨m, r, s.labels.set (c.vertexIndex y) r.node hy⟩
  else none

theorem step_exists {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat} {y : Vertex H}
    {xs : List (Vertex H)} (g : Grounded c F s.tables)
    (hy : c.vertexIndex y < s.labels.size)
    (hp : (ForestHead.runHead (selectors c s) rank y xs).step.parent <
      s.tables.next)
    (cover : ∀ q, (ForestHead.runHead (selectors c s) rank y xs).step.newPair =
      some q → ∃ i, (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
        (s.tables.slotAt i = 0 → s.tables.next < s.tables.back.size)) :
    ∃ r, step c s rank y xs = some r := by
  obtain ⟨a, ha⟩ := install_exists g hp cover
  exact ⟨⟨ForestHead.runHead (selectors c s) rank y xs, a,
    s.labels.set (c.vertexIndex y) a.node hy⟩, by simp [step, hy, ha]⟩

theorem step_parts {H : LabelledQuotient} {c : Config H} {s : State H}
    {rank : Vertex H → Nat} {y : Vertex H} {xs : List (Vertex H)}
    {r : HeadResult H} (h : step c s rank y xs = some r) :
    r.measured = ForestHead.runHead (selectors c s) rank y xs ∧
    install c s.tables r.measured.step = some r.installed ∧
    r.labels.size = s.labels.size ∧
    ∀ j, r.labels[j]? =
      if j = c.vertexIndex y then some r.installed.node else s.labels[j]? := by
  by_cases hy : c.vertexIndex y < s.labels.size
  · cases ha : install c s.tables (ForestHead.runHead (selectors c s) rank y xs).step with
    | none => simp [step, hy, ha] at h
    | some a =>
      simp only [step, dif_pos hy, ha, Option.map_some] at h
      have er := Option.some.inj h
      subst r
      exact ⟨rfl, ha, by simp, opt_set s.labels (c.vertexIndex y) hy a.node⟩
  · simp [step, hy] at h

private theorem trace_writes_le (l : List WordAccess) :
    (l.filter isWrite).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : isWrite a <;> simp [h] <;> omega

/-- At most one new node and at most 18 logical writes: one label,
three installation-table/counter writes, and at most 14 writes
(conservatively counting every grounded jump access as a write). -/
theorem step_spec {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat} {y : Vertex H}
    {xs : List (Vertex H)} {r : HeadResult H}
    (g : Grounded c F s.tables) (h : step c s rank y xs = some r) :
    InstallOK c F s.tables r.measured.step r.installed ∧
    r.state.tables.next = s.tables.next + r.installed.delta ∧
    r.installed.delta ≤ 1 ∧ r.installed.writes ≤ 18 ∧
    (r.installed.allocated = false → r.installed.writes = 1) := by
  have ok := install_spec g (step_parts h).2.1
  have hd : r.installed.delta ≤ 1 := by
    cases ha : r.installed.allocated <;> simp [Installed.delta, ha]
  have ht := ok.trace_bound
  have hw := trace_writes_le r.installed.accesses
  refine ⟨ok, ok.next_eq, hd, ?_, ?_⟩
  · unfold Installed.writes
    omega
  · intro ha
    have hz : r.installed.delta = 0 := by simp [Installed.delta, ha]
    unfold Installed.writes
    omega

theorem previous_label {H : LabelledQuotient} {c : Config H} {s : State H}
    {rank : Vertex H → Nat} {y u : Vertex H} {xs : List (Vertex H)}
    {r : HeadResult H} (h : step c s rank y xs = some r) (hne : u ≠ y) :
    (selectors c r.state).label u = (selectors c s).label u := by
  have hi : c.vertexIndex u ≠ c.vertexIndex y :=
    fun e => hne (c.vertexIndex_inj e)
  change (r.labels[c.vertexIndex u]?).getD 0 =
    (s.labels[c.vertexIndex u]?).getD 0
  rw [(step_parts h).2.2.2 (c.vertexIndex u), if_neg hi]

/-- The supplied Ready hypothesis concerns the pre-step selectors. This
proves the request semantics; it does not infer Ready for the next head.
In particular, reusing a node does not overwrite its original parent.
A decoded-view invariant for installed labels must justify that an old
node for a repeated key already represents the requested chain. -/
theorem step_request_semantics {H : LabelledQuotient}
    {c : Config H} {s : State H} {rank : Vertex H → Nat}
    {y : Vertex H} {xs : List (Vertex H)} {r : HeadResult H}
    (h : step c s rank y xs = some r)
    (view : Nat → List (CutPair H)) (T : TestSpec y xs)
    (rootView : view 0 = [])
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (ready : ∀ m, y ≠ H.root → H.hasQuotientArcBool H.root y = false →
      maxByRank rank (preds H y) = some m →
      H.HasQuotientArc m y ∧ Ready (selectors c s) view rank y m xs) :
    decode view r.measured.step = sweepChain H rank y := by
  rw [(step_parts h).1]
  exact runHead_semantics (selectors c s) view rank y xs T rootView rankArc ready

/-- The successful install branches always write one label. Only the
fresh branch writes four jump words, two table slots and the next counter. -/
theorem install_writes_exact {H : LabelledQuotient}
    {c : Config H} {t : Tables H} {req : ForestHead.Step H} {out : Installed H}
    (run : install c t req = some out) :
    out.writes = 1 + 7 * out.delta := by
  by_cases hp : req.parent < t.next
  · cases pair : req.newPair with
    | none =>
      simp only [install, ite_eq_left hp, pair, Option.some.injEq] at run
      subst out
      rfl
    | some q =>
      cases hit : (PairLookup.lookup c.dict (c.code q)).1 with
      | none => simp [install, hp, pair, hit] at run
      | some i =>
        by_cases hi : i < t.slots.size
        · by_cases fresh : t.slotAt i = 0
          · by_cases room : t.next < t.back.size
            · simp only [install, ite_eq_left hp, pair, hit, dite_eq_left hi,
                ite_eq_left fresh, dite_eq_left room, Option.some.injEq] at run
              subst out
              rfl
            · simp [install, hp, pair, hit, hi, fresh, room] at run
          · simp only [install, ite_eq_left hp, pair, hit, dite_eq_left hi,
              ite_eq_right fresh, Option.some.injEq] at run
            subst out
            rfl
        · simp [install, hp, pair, hit, hi] at run
  · simp [install, hp] at run

end EX24
