module

public import PaperB.ForestPreparedHead
public import PaperB.PairDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestDictionary

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.PairLookup EX24

/-- The executable interface is a direct row read. Exactness is erased. -/
structure Rows (H : LabelledQuotient) where
  row : Vertex H → List (Vertex H)
  spec : ∀ y : Vertex H, TestSpec y (row y)

def collectFrom {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) (ys : List (Vertex H)) : List Key :=
  ys.filterMap fun y => (preparedKey H (rows.row y)).map code

theorem mem_collectFrom {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) (ys : List (Vertex H)) (k : Key) :
    k ∈ collectFrom rows code ys ↔
      ∃ y ∈ ys, ∃ q : CutPair H,
        preparedKey H (rows.row y) = some q ∧ code q = k := by
  rw [collectFrom, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    cases hq : preparedKey H (rows.row y) with
    | none => simp [hq] at h
    | some q =>
      have he : some (code q) = some k := by
        simpa only [hq, Option.map_some] using h
      exact ⟨y, hy, q, hq, Option.some.inj he⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨y, hy, by simp only [hq, Option.map_some]⟩

private theorem filterMap_length_bound {α β : Type}
    (f : α → Option β) (xs : List α) :
    (xs.filterMap f).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases hf : f x with
    | none =>
      simp only [List.filterMap, hf, List.length_cons]
      exact Nat.le_succ_of_le ih
    | some b =>
      simp only [List.filterMap, hf, List.length_cons]
      exact Nat.succ_le_succ ih

/-- Collection uses vertex enumeration, not sweep order. -/
def collect {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) : List Key :=
  collectFrom rows code (List.finRange H.vertexCount)

/-- The prepared row test emits at most one key per vertex. Reserve
that many accumulator slots before visiting the first row. -/
def collectReserved {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) : List Key :=
  List.filterMapTR.go (fun y => (preparedKey H (rows.row y)).map code)
    (List.finRange H.vertexCount) (Array.emptyWithCapacity H.vertexCount)

@[csimp] theorem collect_csimp : @collect = @collectReserved := by
  funext H rows code
  unfold collect collectFrom collectReserved
  rw [List.filterMap_eq_filterMapTR]
  rfl

theorem mem_collect {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) (k : Key) :
    k ∈ collect rows code ↔
      ∃ (y : Vertex H) (q : CutPair H),
        preparedKey H (rows.row y) = some q ∧ code q = k := by
  unfold collect
  rw [mem_collectFrom]
  constructor
  · rintro ⟨y, _, q, hq, hk⟩
    exact ⟨y, q, hq, hk⟩
  · rintro ⟨y, q, hq, hk⟩
    exact ⟨y, by simp, q, hq, hk⟩

theorem collect_length_le {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) :
    (collect rows code).length ≤ H.vertexCount := by
  have h := filterMap_length_bound
    (fun y : Vertex H => (preparedKey H (rows.row y)).map code)
    (List.finRange H.vertexCount)
  simpa [collect, collectFrom] using h

def dictionary {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) : Array Key :=
  PaperB.PairLookup.KeyMerge.dictionary (collect rows code)

theorem dictionary_spec {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) :
    StrictSorted (dictionary rows code) ∧
      (∀ k : Key, k ∈ (dictionary rows code).toList ↔
        ∃ (y : Vertex H) (q : CutPair H),
          preparedKey H (rows.row y) = some q ∧ code q = k) ∧
      (dictionary rows code).size ≤ H.vertexCount := by
  have hd := PaperB.PairLookup.KeyMerge.dictionary_spec (collect rows code)
  refine ⟨hd.1, fun k => (hd.2 k).trans (mem_collect rows code k), ?_⟩
  have hb := (PaperB.PairLookup.KeyMerge.build_spec (collect rows code)).length_le
  have hs : (dictionary rows code).size ≤ (collect rows code).length := by
    simpa [dictionary, PaperB.PairLookup.KeyMerge.dictionary] using hb
  exact Nat.le_trans hs (collect_length_le rows code)

theorem dictionary_comparisons_log {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) :
    (PaperB.PairLookup.KeyMerge.build (collect rows code)).comparisons ≤
      2 * (collect rows code).length *
        PaperB.PairLookup.KeyMerge.ceilBinaryLog (collect rows code).length :=
  PaperB.PairLookup.KeyMerge.build_comparisons_log (collect rows code)

private theorem plan_key {H : LabelledQuotient}
    {rank : Vertex H → Nat} {y : Vertex H} {xs : List (Vertex H)}
    {m : Vertex H} {key : Option (CutPair H)}
    (h : planPrepared rank y xs = some (m, key)) :
    key = preparedKey H xs := by
  unfold planPrepared at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hm : maxByRank rank xs with
      | none => simp [hm] at h
      | some u =>
        have he : some (u, preparedKey H xs) = some (m, key) := by
          simpa only [hm, Option.map_some] using h
        exact (congrArg (fun p : Vertex H × Option (CutPair H) => p.2)
          (Option.some.inj he)).symm

/-- A stopped head requests no pair. An active head forwards its planned
key unchanged. Neither row exactness nor a rank property is needed here. -/
theorem preparedKey_of_newPair {H : LabelledQuotient}
    {S : Selectors H} {rank : Vertex H → Nat} {y : Vertex H}
    {xs : List (Vertex H)} {q : CutPair H}
    (h : (runPrepared S rank y xs).step.newPair = some q) :
    preparedKey H xs = some q := by
  cases hp : planPrepared rank y xs with
  | none =>
    have hn : (stopped (H := H)).step.newPair = some q := by
      simpa only [runPrepared, hp] using h
    change (none : Option (CutPair H)) = some q at hn
    cases hn
  | some p =>
    rcases p with ⟨m, key⟩
    have ha : (active S xs m key).step.newPair = some q := by
      simpa only [runPrepared, hp] using h
    change key = some q at ha
    exact (plan_key hp).symm.trans ha

theorem newPair_mem_dictionary {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) {S : Selectors H} {rank : Vertex H → Nat}
    {y : Vertex H} {q : CutPair H}
    (h : (runPrepared S rank y (rows.row y)).step.newPair = some q) :
    code q ∈ (dictionary rows code).toList :=
  ((dictionary_spec rows code).2.1 (code q)).mpr
    ⟨y, q, preparedKey_of_newPair h, rfl⟩

/-- The head uses the supplied sweep rank. Its installation and label
write are those of the original step, and every requested key is covered. -/
theorem stepPrepared_dictionary_parts {H : LabelledQuotient}
    (rows : Rows H) {c : Config H} {s : State H}
    {rank : Vertex H → Nat} {y : Vertex H} {r : HeadResult H}
    (hd : c.dict = dictionary rows c.code)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b)
    (h : stepPrepared c s rank y (rows.row y) = some r) :
    r.measured = runPrepared (selectors c s) rank y (rows.row y) ∧
      install c s.tables r.measured.step = some r.installed ∧
      r.labels.size = s.labels.size ∧
      (∀ j, r.labels[j]? =
        if j = c.vertexIndex y then some r.installed.node else s.labels[j]?) ∧
      (∀ q : CutPair H, r.measured.step.newPair = some q →
        preparedKey H (rows.row y) = some q ∧ c.code q ∈ c.dict.toList) := by
  have hl : step c s rank y (rows.row y) = some r :=
    (stepPrepared_eq_step c s rank y (rows.row y) (rows.spec y) inj).symm.trans h
  obtain ⟨hm, hi, hs, hw⟩ := step_parts hl
  have hm' : r.measured = runPrepared (selectors c s) rank y (rows.row y) :=
    hm.trans (runPrepared_eq_runHead (selectors c s) rank y (rows.row y)
      (rows.spec y) inj).symm
  refine ⟨hm', hi, hs, hw, ?_⟩
  intro q hq
  rw [hm'] at hq
  exact ⟨preparedKey_of_newPair hq, hd.symm ▸ newPair_mem_dictionary rows c.code hq⟩

/-- Success bridge for the install interface. Lookup completeness is stated
on dictionary members, separately from the capacity needed for an empty
slot. The per-head coverage premise of `step_exists` is derived here. -/
theorem stepPrepared_dictionary_exists {H : LabelledQuotient}
    (rows : Rows H) {c : Config H} {s : State H} {F : JumpForest}
    {rank : Vertex H → Nat} {y : Vertex H}
    (hd : c.dict = dictionary rows c.code)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b)
    (g : Grounded c F s.tables)
    (hy : c.vertexIndex y < s.labels.size)
    (hp : (runPrepared (selectors c s) rank y (rows.row y)).step.parent <
      s.tables.next)
    (lookupComplete : ∀ k : Key, k ∈ c.dict.toList →
      ∃ i, (PairLookup.lookup c.dict k).1 = some i)
    (room : ∀ (k : Key) (i : Nat), k ∈ c.dict.toList →
      (PairLookup.lookup c.dict k).1 = some i →
      s.tables.slotAt i = 0 → s.tables.next < s.tables.back.size) :
    ∃ r, stepPrepared c s rank y (rows.row y) = some r := by
  have he := runPrepared_eq_runHead (selectors c s) rank y (rows.row y)
    (rows.spec y) inj
  have hp' : (runHead (selectors c s) rank y (rows.row y)).step.parent <
      s.tables.next := by
    rw [← he]
    exact hp
  have cover : ∀ q : CutPair H,
      (runHead (selectors c s) rank y (rows.row y)).step.newPair = some q →
        ∃ i, (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
          (s.tables.slotAt i = 0 → s.tables.next < s.tables.back.size) := by
    intro q hq
    have hq' : (runPrepared (selectors c s) rank y (rows.row y)).step.newPair =
        some q := by
      rw [he]
      exact hq
    have hk : c.code q ∈ c.dict.toList :=
      hd.symm ▸ newPair_mem_dictionary rows c.code hq'
    obtain ⟨i, hi⟩ := lookupComplete (c.code q) hk
    exact ⟨i, hi, room (c.code q) i hk hi⟩
  obtain ⟨r, hr⟩ := step_exists g hy hp' cover
  exact ⟨r, (stepPrepared_eq_step c s rank y (rows.row y) (rows.spec y) inj).trans hr⟩

end PaperB.ForestDictionary
