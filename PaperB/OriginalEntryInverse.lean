module

public import PaperB.OriginalStaticFull
public import PaperB.StaticLinearHead
public import PaperB.ExitLCABridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.OriginalEntryInverse

open PaperB.LabelledQuotient
open PackedStaticLayout StaticLinearHead
open PaperB.ExitMap PaperB.EX44 PaperB.EX16Assembly PaperB.StaticHeadSweep PaperB.Digraph

variable {g : Digraph} {r : Fin g.vertexCount}

/-- The scatter reads the installed packed column, not a rebuilt column. -/
def packedEntry (q : OriginalReader g r) :=
  q.reader.layout.endpoints.entry

theorem packedEntry_exact (q : OriginalReader g r) (x : Fin q.count) :
    (packedEntry q).read x = (entryColumn q.input).read x := by
  first
  | rfl
  | unfold packedEntry
    rw [q.reader.layout_exact] <;> rfl
  | change q.reader.entry x = _
    have ht := q.reader.input_ok
    refine (q.reader.entry_exact x).trans ?_
    symm
    first
    | rfl
    | simp [entryColumn] <;> done
    | exact?
    | simp [entryColumn] <;> exact?

theorem packedEntry_lt (q : OriginalReader g r) (x : Fin q.count) :
    (packedEntry q).read x < q.count := by
  rw [packedEntry_exact q x]
  exact StaticLinearHead.entry_lt q.input q.reader.input_ok x

def entryRank (q : OriginalReader g r) (x : Fin q.count) : Fin q.count :=
  StaticLinearHead.rank (packedEntry q) (packedEntry_lt q) x

theorem entryRank_val (q : OriginalReader g r) (x : Fin q.count) :
    (entryRank q x).val = q.reader.entry x := rfl

theorem entryRank_spec (q : OriginalReader g r) (x : Fin q.count) :
    entryRank q x =
      StaticLinearHead.rank (entryColumn q.input)
        (StaticLinearHead.entry_lt q.input q.reader.input_ok) x :=
  Fin.ext (packedEntry_exact q x)

theorem entryRank_injective (q : OriginalReader g r) :
    Function.Injective (entryRank q) := by
  intro a b h
  apply StaticLinearHead.rank_injective q.input q.reader.input_ok
  simpa only [entryRank_spec q a, entryRank_spec q b] using h

theorem preorder_at_entryRank (q : OriginalReader g r) (x : Fin q.count) :
    (preorderSpec q.input)[(entryRank q x).val]'(by
      rw [preorder_length q.input q.reader.input_ok]
      exact (entryRank q x).isLt) = x := by
  let atRank (i : Fin q.count) : Fin q.count :=
    (preorderSpec q.input)[i.val]'(by
      rw [preorder_length q.input q.reader.input_ok]
      exact i.isLt)
  change atRank (entryRank q x) = x
  rw [entryRank_spec q x]
  exact preorder_get_entry q.input q.reader.input_ok x

/-- Build once and retain the slots. Endpoint queries take this stored index,
so neither endpoint query reruns the scatter. -/
structure Index (q : OriginalReader g r) where
  slots : Slots q.count (Fin q.count)
  read_rank : ∀ x, slots.read (entryRank q x) = x

def build (q : OriginalReader g r) : Index q where
  slots :=
    (StaticLinearHead.inverseSlots q.input.root
      (packedEntry q) (packedEntry_lt q)).slots
  read_rank x :=
    StaticLinearHead.inverse_read q.input.root
      (packedEntry q) (packedEntry_lt q)
      (fun {_ _} h => entryRank_injective q h) x

theorem inverse_size (q : OriginalReader g r) :
    (build q).slots.data.size = q.count :=
  (build q).slots.len

theorem inverse_read_endpoint (q : OriginalReader g r) (x : Fin q.count) :
    (build q).slots.read
      ⟨q.reader.layout.endpoints.entry.read x, packedEntry_lt q x⟩ = x :=
  (build q).read_rank x

/-- One bounds check and, on a hit, one read from the retained inverse. -/
def readEndpoint {q : OriginalReader g r} (I : Index q)
    (k : Nat) : Option (Fin q.count) :=
  if h : k < q.count then some (I.slots.read ⟨k, h⟩) else none

theorem readEndpoint_entry {q : OriginalReader g r} (I : Index q)
    (x : Fin q.count) :
    readEndpoint I (q.reader.entry x) = some x := by
  change readEndpoint I ((packedEntry q).read x) = some x
  unfold readEndpoint
  rw [dif_pos (packedEntry_lt q x)]
  exact congrArg some (I.read_rank x)

/-- A lookup in the original-ID index followed by a packed entry read. -/
def originalRank (q : OriginalReader g r) (v : Fin g.vertexCount) :
    Option Nat :=
  (q.ids.find v).map (fun x => q.reader.entry x)

theorem originalRank_of_find (q : OriginalReader g r)
    {v : Fin g.vertexCount} {x : Fin q.count}
    (h : q.ids.find v = some x) :
    originalRank q v = some (q.reader.entry x) := by
  simp [originalRank, h]

theorem originalRank_reachable (q : OriginalReader g r)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
    originalRank q v =
      some ((entryColumn q.input).read (q.slot v hv)) :=
  (originalRank_of_find q (q.find_slot v hv)).trans
    (congrArg some (packedEntry_exact q (q.slot v hv)))

theorem originalRank_roundTrip {q : OriginalReader g r} (I : Index q)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
    (originalRank q v).bind (readEndpoint I) = some (q.slot v hv) := by
  rw [originalRank_of_find q (q.find_slot v hv)]
  exact readEndpoint_entry I (q.slot v hv)

def toSpan {q : OriginalReader g r} (I : Index q) :
    Interval → Option (Fin q.count × Fin q.count)
  | .empty => none
  | .span lo hi => do
      let a ← readEndpoint I lo
      let b ← readEndpoint I hi
      return (a, b)

theorem toSpan_at_entries {q : OriginalReader g r} (I : Index q)
    (a b : Fin q.count) :
    toSpan I (.span (q.reader.entry a) (q.reader.entry b)) = some (a, b) := by
  simp only [toSpan, readEndpoint_entry] <;> rfl

private theorem summary_has_extrema (xs : List Nat) (hne : xs ≠ []) :
    ∃ lo hi, ExitSummary.summary xs = .span lo hi ∧ lo ∈ xs ∧ hi ∈ xs ∧
      ∀ k ∈ xs, lo ≤ k ∧ k ≤ hi := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    by_cases h : xs = []
    · subst xs
      refine ⟨x, x, by simp [ExitSummary.singleton], by simp, by simp, ?_⟩
      intro k hk
      have he : k = x := by simpa using hk
      subst k
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨a, b, hab, ha, hb, hbounds⟩ := ih h
      refine ⟨min x a, max x b, ?_, ?_, ?_, ?_⟩
      · simp [hab, ExitSummary.singleton, Interval.join]
      · rw [Nat.min_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr ha)
      · rw [Nat.max_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr hb)
      · intro k hk
        rcases List.mem_cons.mp hk with he | hk
        · subst k
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega
        · obtain ⟨hl, hh⟩ := hbounds k hk
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega

/-- The nonempty result contains actual held witnesses. The computed interval
stores their exact entry ranks, and those ranks bound every witness in `X`.
The list and its summary occur only in the proof. -/
theorem witnessOrder {q : OriginalReader g r} (I : Index q)
    {α : Type} (ts : List α) (key : α → Nat) (X : Fin q.count → Prop)
    (s : Interval) (hs : s = ExitSummary.summary (ts.map key))
    (hne : ts ≠ [])
    (lift : ∀ t ∈ ts, ∃ x, X x ∧ key t = q.reader.entry x)
    (cover : ∀ x, X x → ∃ t ∈ ts, key t = q.reader.entry x) :
    ∃ a b, X a ∧ X b ∧
      s = .span (q.reader.entry a) (q.reader.entry b) ∧
      toSpan I s = some (a, b) ∧
      ∀ x, X x → q.reader.entry a ≤ q.reader.entry x ∧
        q.reader.entry x ≤ q.reader.entry b := by
  have hm : ts.map key ≠ [] := by
    intro he
    apply hne
    cases ts with
    | nil => rfl
    | cons t rest => simp at he
  obtain ⟨lo, hi, hspan, hlo, hhi, hbounds⟩ :=
    summary_has_extrema (ts.map key) hm
  obtain ⟨u, hu, hlu⟩ := List.mem_map.mp hlo
  obtain ⟨v, hv, hhv⟩ := List.mem_map.mp hhi
  obtain ⟨a, ha, hka⟩ := lift u hu
  obtain ⟨b, hb, hkb⟩ := lift v hv
  have hab : s = .span (q.reader.entry a) (q.reader.entry b) := by
    rw [hs, hspan, ← hlu, ← hhv, hka, hkb]
  refine ⟨a, b, ha, hb, hab, hab ▸ toSpan_at_entries I a b, ?_⟩
  intro x hx
  obtain ⟨t, ht, hkt⟩ := cover x hx
  have h := hbounds (key t) (List.mem_map.mpr ⟨t, ht, rfl⟩)
  simpa only [← hlu, ← hhv, hka, hkb, hkt] using h

theorem computedSpan_exact {q : OriginalReader g r} (I : Index q)
    {α : Type} (ts : List α) (key : α → Nat) (X : Fin q.count → Prop)
    (s : Interval) (hs : s = ExitSummary.summary (ts.map key))
    (lift : ∀ t ∈ ts, ∃ x, X x ∧ key t = q.reader.entry x)
    (cover : ∀ x, X x → ∃ t ∈ ts, key t = q.reader.entry x) :
    SpanExact (fun x => q.reader.entry x) X (toSpan I s) := by
  by_cases hne : ts = []
  · subst ts
    rw [hs, List.map_nil, ExitSummary.summary_nil]
    change ∀ x, ¬ X x
    intro x hx
    obtain ⟨t, ht, _⟩ := cover x hx
    simpa using ht
  · obtain ⟨a, b, ha, hb, _, hout, horder⟩ :=
      witnessOrder I ts key X s hs hne lift cover
    rw [hout]
    exact ⟨ha, hb, horder⟩

theorem heldSpan_exact {q : OriginalReader g r} (I : Index q)
    (ts : List (Fin q.count)) (s : Interval)
    (hs : s = ExitSummary.summary (ts.map fun x => q.reader.entry x)) :
    SpanExact (fun x => q.reader.entry x) (fun x => x ∈ ts) (toSpan I s) :=
  computedSpan_exact I ts (fun x => q.reader.entry x) (fun x => x ∈ ts)
    s hs (fun x hx => ⟨x, hx, rfl⟩) (fun x hx => ⟨x, hx, rfl⟩)

/-- The default in the specification is never used on a tail: reachability
gives a `find` hit. At query time `toSpan` takes only the stored inverse and
the already-computed interval; it does not traverse `ts` or call `find`. -/
theorem originalSpan_exact {q : OriginalReader g r} (I : Index q)
    (ts : List (Fin g.vertexCount))
    (reach : ∀ v ∈ ts, g.InitiallyReachable r v) (s : Interval)
    (hs : s = ExitSummary.summary
      (ts.map fun v => (originalRank q v).getD 0)) :
    SpanExact (fun x => q.reader.entry x)
      (fun x => q.ids.originals.read x ∈ ts) (toSpan I s) := by
  refine computedSpan_exact I ts (fun v => (originalRank q v).getD 0)
    (fun x => q.ids.originals.read x ∈ ts) s hs ?_ ?_
  · intro v hv
    refine ⟨q.slot v (reach v hv), ?_, ?_⟩
    · rw [q.original_at_slot v (reach v hv)]
      exact hv
    · exact congrArg (fun o : Option Nat => o.getD 0)
        (originalRank_of_find q (q.find_slot v (reach v hv)))
  · intro x hx
    refine ⟨q.ids.originals.read x, hx, ?_⟩
    exact congrArg (fun o : Option Nat => o.getD 0)
      (originalRank_of_find q (q.ids.slot_of_original x))

end PaperB.OriginalEntryInverse
