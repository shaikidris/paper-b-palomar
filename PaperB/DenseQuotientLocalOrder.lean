module

public import PaperB.Kahn
public import PaperB.KahnInverse
public import PaperB.DenseQuotientRows
public import PaperB.StaticOracleTree
public import PaperB.SharedLocalOrder

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseQuotientLocalOrder

open EX51
open PaperB.DenseQuotientRows PaperB.EX16Assembly
open EX51.LocalSchedule
  (Slot Choice Entry Tag Schedule OneAt raw raw_spec schedule schedule_row
    schedule_increasing)

set_option autoImplicit false

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)
variable {buckets : PaperB.ForestLayout.ChildLists q.count} (rows : Layout buckets)
variable (childOK : ∀ u c : Fin q.count,
  Occurs buckets u (.inr c) ↔ c ≠ q.input.root ∧ q.input.parent.read c = u)

def rootSlot (c : Fin q.count) : Slot rows.length :=
  ⟨c, rows.encode c ⟨.inl c, rfl⟩⟩

def childSlot (c : Fin q.count) (hc : c ≠ q.input.root) : Slot rows.length :=
  let p := q.input.parent.read c
  ⟨p, rows.encode p ⟨.inr c, (childOK p c).mpr ⟨hc, rfl⟩⟩⟩

/-- One shared ID lookup per input vertex. Child slots use the layout's inverse
lookup, not a search in the owner's row. -/
def pick (z : Fin g.vertexCount) : Choice rows.length :=
  match q.ids.find z with
  | none => ⟨none, none⟩
  | some c =>
      ⟨some (rootSlot q rows c),
        if hc : c ≠ q.input.root then some (childSlot q rows childOK c hc)
        else none⟩

variable (order : Array (Fin g.vertexCount))

/-- Consume the supplied Kahn ID array in its original order. -/
def build : Schedule rows.length :=
  schedule (pick q rows childOK) order.toList

theorem at_most_two (z : Fin g.vertexCount) (n : Nat) :
    (raw (pick q rows childOK) n [z]).1.length ≤ 2 := by
  simpa using (raw_spec (pick q rows childOK) [z] n).2

theorem one_at
    (noSelf : ∀ c : Fin q.count, c ≠ q.input.root → q.input.parent.read c ≠ c)
    (z : Fin g.vertexCount) (u : Fin q.count) :
    OneAt (pick q rows childOK z) u := by
  cases hf : q.ids.find z with
  | none => simp [OneAt, pick, hf]
  | some c =>
      by_cases hc : c ≠ q.input.root
      · unfold OneAt
        rintro ⟨hr, hp⟩
        have h₁ : c = u := by simpa [pick, hf, rootSlot] using hr
        have h₂ : q.input.parent.read c = u := by
          simpa [pick, hf, hc, childSlot] using hp
        exact noSelf c hc (h₂.trans h₁.symm)
      · simp [OneAt, pick, hf, hc]

theorem stable (u : Fin q.count) :
    (build q rows childOK order).rows.row u =
      (raw (pick q rows childOK) 0 order.toList).1.filter
        (fun e => decide (e.owner = u)) :=
  schedule_row (pick q rows childOK) order.toList u

theorem increasing
    (noSelf : ∀ c : Fin q.count, c ≠ q.input.root → q.input.parent.read c ≠ c)
    (u : Fin q.count) :
    (((build q rows childOK order).rows.row u).map (fun e => e.source)).Pairwise
      (· < ·) :=
  schedule_increasing (pick q rows childOK) order.toList u
    (fun z _ => one_at q rows childOK noSelf z u)

variable (rank : Fin g.vertexCount → Nat)

/-- These laws are used only in proofs. In particular `build` does not read
ranks or probe the original translation in reverse. -/
structure Laws : Prop where
  rankAt : ∀ (i : Nat) (hi : i < order.toList.length),
    rank (order.toList[i]'hi) = i
  retained : ∀ c : Fin q.count, q.ids.originals.read c ∈ order.toList
  find_iff : ∀ (z : Fin g.vertexCount) (c : Fin q.count),
    q.ids.find z = some c ↔ q.ids.originals.read c = z

private theorem raw_cons {α : Type} {B : Nat} {L : Fin B → Nat}
    (p : α → Choice L) (n : Nat) (a : α) (xs : List α) :
    (raw p n (a :: xs)).1 = (raw p n [a]).1 ++ (raw p (n + 1) xs).1 := by
  simp only [raw, List.append_nil]

private theorem raw_mem_rank {α : Type} {B : Nat} {L : Fin B → Nat}
    (p : α → Choice L) (rk : α → Nat) (xs : List α) (n : Nat)
    (hr : ∀ (i : Nat) (hi : i < xs.length), rk (xs[i]'hi) = n + i)
    (e : Entry L) :
    e ∈ (raw p n xs).1 ↔ ∃ a ∈ xs, e ∈ (raw p (rk a) [a]).1 := by
  induction xs generalizing n with
  | nil => simp [raw]
  | cons a xs ih =>
      have ha : rk a = n := by
        have h0 := hr 0 (by simp)
        change rk a = n + 0 at h0
        simpa only [Nat.add_zero] using h0
      have ht (i : Nat) (hi : i < xs.length) :
          rk (xs[i]'hi) = (n + 1) + i := by
        have hb : i + 1 < (a :: xs).length := by
          simpa only [List.length_cons] using Nat.succ_lt_succ hi
        have hn : n + (i + 1) = (n + 1) + i := by omega
        simpa only [List.getElem_cons_succ, hn] using hr (i + 1) hb
      rw [raw_cons, List.mem_append, ih (n + 1) ht]
      constructor
      · rintro (he | ⟨z, hz, he⟩)
        · exact ⟨a, by simp, by simpa only [ha] using he⟩
        · exact ⟨z, List.mem_cons.mpr (Or.inr hz), he⟩
      · rintro ⟨z, hz, he⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl (by simpa only [ha] using he)
        · exact Or.inr ⟨z, hz, he⟩

private def entry {B : Nat} {L : Fin B → Nat}
    (s : Slot L) (tag : Tag) (n : Nat) : Entry L :=
  ⟨s.owner, s.index, tag, n⟩

def rootEntry (c : Fin q.count) (n : Nat) : Entry rows.length :=
  entry (rootSlot q rows c) .root n

def childEntry (c : Fin q.count) (hc : c ≠ q.input.root) (n : Nat) :
    Entry rows.length :=
  entry (childSlot q rows childOK c hc) .child n

private theorem singleton_iff (z : Fin g.vertexCount) (n : Nat)
    (e : Entry rows.length) :
    e ∈ (raw (pick q rows childOK) n [z]).1 ↔
      ∃ c, q.ids.find z = some c ∧
        (e = rootEntry q rows c n ∨
          ∃ hc : c ≠ q.input.root, e = childEntry q rows childOK c hc n) := by
  let P (c : Fin q.count) : Prop :=
    e = rootEntry q rows c n ∨
      ∃ hc : c ≠ q.input.root, e = childEntry q rows childOK c hc n
  change _ ↔ ∃ c, q.ids.find z = some c ∧ P c
  cases hf : q.ids.find z with
  | none =>
      simp only [raw, pick, hf]
      change e ∈ ([] : List (Entry rows.length)) ↔ _
      simp
  | some c =>
      simp only [raw, pick, hf]
      have hx : (∃ d, some c = some d ∧ P d) ↔ P c := by
        constructor
        · rintro ⟨d, hd, h⟩
          have hcd := Option.some.inj hd
          subst d
          exact h
        · exact fun h => ⟨c, rfl, h⟩
      rw [hx]
      by_cases hc : c ≠ q.input.root
      · rw [dif_pos hc]
        change e ∈ [rootEntry q rows c n, childEntry q rows childOK c hc n] ↔ P c
        simp only [List.mem_cons, List.not_mem_nil, or_false, P]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨hc, h⟩
        · rintro (h | ⟨_, h⟩)
          · exact Or.inl h
          · exact Or.inr h
      · rw [dif_neg hc]
        change e ∈ [rootEntry q rows c n] ↔ P c
        simp only [List.mem_cons, List.not_mem_nil, or_false, P]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hd, _⟩)
          · exact h
          · exact (hc hd).elim

/-- Exact records, including their tags, encoded slots, and Kahn positions. -/
theorem row_entry_iff (laws : Laws q order rank) (u : Fin q.count)
    (e : Entry rows.length) :
    e ∈ (build q rows childOK order).rows.row u ↔
      e = rootEntry q rows u (rank (q.ids.originals.read u)) ∨
        ∃ (c : Fin q.count) (hc : c ≠ q.input.root),
          q.input.parent.read c = u ∧
          e = childEntry q rows childOK c hc (rank (q.ids.originals.read c)) := by
  rw [stable, List.mem_filter, decide_eq_true_eq]
  rw [raw_mem_rank (pick q rows childOK) rank order.toList 0
    (fun i hi => by simpa only [Nat.zero_add] using laws.rankAt i hi) e]
  constructor
  · rintro ⟨⟨z, _, hz⟩, hu⟩
    obtain ⟨c, hf, he⟩ := (singleton_iff q rows childOK z (rank z) e).mp hz
    have ho := (laws.find_iff z c).mp hf
    subst z
    rcases he with h | ⟨hc, h⟩
    · subst e
      change c = u at hu
      subst c
      exact Or.inl rfl
    · subst e
      exact Or.inr ⟨c, hc, hu, rfl⟩
  · rintro (h | ⟨c, hc, hp, h⟩)
    · subst e
      refine ⟨⟨q.ids.originals.read u, laws.retained u, ?_⟩, rfl⟩
      exact (singleton_iff q rows childOK _ _ _).mpr
        ⟨u, (laws.find_iff _ u).mpr rfl, Or.inl rfl⟩
    · subst e
      refine ⟨⟨q.ids.originals.read c, laws.retained c, ?_⟩, hp⟩
      exact (singleton_iff q rows childOK _ _ _).mpr
        ⟨c, (laws.find_iff _ c).mpr rfl, Or.inr ⟨hc, rfl⟩⟩

def keyOf (e : Entry rows.length) : Key q.count :=
  rows.key e.owner e.slot

private theorem rootEntry_key (c : Fin q.count) (n : Nat) :
    keyOf q rows (rootEntry q rows c n) = .inl c :=
  congrArg Subtype.val (rows.decode_encode c ⟨.inl c, rfl⟩)

private theorem childEntry_key (c : Fin q.count) (hc : c ≠ q.input.root) (n : Nat) :
    keyOf q rows (childEntry q rows childOK c hc n) = .inr c :=
  congrArg Subtype.val (rows.decode_encode (q.input.parent.read c)
    ⟨.inr c, (childOK _ c).mpr ⟨hc, rfl⟩⟩)


private abbrev actual (u : Fin q.count) :=
  (build q rows childOK order).rows.row u

private theorem rowOwner (u : Fin q.count) (e : Entry rows.length)
    (he : e ∈ actual q rows childOK order u) : e.owner = u := by
  change e ∈ (build q rows childOK order).rows.row u at he
  rw [stable, List.mem_filter, decide_eq_true_eq] at he
  exact he.2

private def ownedSlot (u : Fin q.count) (e : Entry rows.length)
    (h : e.owner = u) : Fin (rows.length u) :=
  ⟨e.slot.val, by rw [← h]; exact e.slot.isLt⟩

private theorem ownedSlot_key (u : Fin q.count) (e : Entry rows.length)
    (h : e.owner = u) :
    rows.key u (ownedSlot q rows u e h) = keyOf q rows e := by
  subst u
  rfl

def slotRank (u : Fin q.count) (i : Fin (rows.length u)) : Nat :=
  rank (q.ids.originals.read (Sum.elim id id (rows.key u i)))

private theorem aligned (laws : Laws q order rank) (u : Fin q.count)
    (e : Entry rows.length) (he : e ∈ actual q rows childOK order u) :
    slotRank q rows rank u
      (ownedSlot q rows u e (rowOwner q rows childOK order u e he)) = e.source := by
  unfold slotRank
  rw [ownedSlot_key]
  rcases (row_entry_iff q rows childOK order rank laws u e).mp he with h | ⟨c, hc, _, h⟩
  · rw [h, rootEntry_key] <;> rfl
  · rw [h, childEntry_key] <;> rfl

private theorem actual_cover (laws : Laws q order rank) (u : Fin q.count)
    (i : Fin (rows.length u)) :
    ∃ e, ∃ he : e ∈ actual q rows childOK order u,
      ownedSlot q rows u e (rowOwner q rows childOK order u e he) = i := by
  have hd : Occurs buckets u (rows.key u i) := (rows.decode u i).property
  cases hk : rows.key u i with
  | inl d =>
      have hu := ((rows.key_is_root_iff u d i).mp hk).2
      subst d
      let e := rootEntry q rows u (rank (q.ids.originals.read u))
      have he := (row_entry_iff q rows childOK order rank laws u e).mpr (Or.inl rfl)
      refine ⟨e, he, rows.key_injective u ?_⟩
      exact (ownedSlot_key q rows u e _).trans ((rootEntry_key q rows u _).trans hk.symm)
  | inr c =>
      obtain ⟨hc, hp⟩ := (childOK u c).mp (by simpa only [hk] using hd)
      let e := childEntry q rows childOK c hc (rank (q.ids.originals.read c))
      have he := (row_entry_iff q rows childOK order rank laws u e).mpr
        (Or.inr ⟨c, hc, hp, rfl⟩)
      refine ⟨e, he, rows.key_injective u ?_⟩
      exact (ownedSlot_key q rows u e _).trans
        ((childEntry_key q rows childOK c hc _).trans hk.symm)

private def project {α β : Type} {P : α → Prop} (f : ∀ a, P a → β) :
    (xs : List α) → (∀ a ∈ xs, P a) → List β
  | [], _ => []
  | a :: xs, h =>
      f a (h a (List.mem_cons.mpr (Or.inl rfl))) ::
        project f xs (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))

private theorem project_mem {α β : Type} {P : α → Prop} (f : ∀ a, P a → β)
    (xs : List α) (h : ∀ a ∈ xs, P a) (a : α) (ha : a ∈ xs) :
    f a (h a ha) ∈ project f xs h := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
      simp only [project, List.mem_cons]
      rcases List.mem_cons.mp ha with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (ih _ hb)

private theorem map_project {α β γ : Type} {P : α → Prop}
    (f : ∀ a, P a → β) (s : α → γ) (t : β → γ)
    (xs : List α) (h : ∀ a ∈ xs, P a)
    (H : ∀ a (ha : a ∈ xs), t (f a (h a ha)) = s a) :
    (project f xs h).map t = xs.map s := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [project, List.map_cons]
      rw [H a (List.mem_cons.mpr (Or.inl rfl))]
      exact congrArg (List.cons (s a))
        (ih _ (fun b hb => H b (List.mem_cons.mpr (Or.inr hb))))

def extractSlots (s : Schedule rows.length) (u : Fin q.count)
    (owns : ∀ e ∈ s.rows.row u, e.owner = u) : Array (Fin (rows.length u)) :=
  (project (ownedSlot q rows u) (s.rows.row u) owns).toArray

def slotArray (u : Fin q.count) : Array (Fin (rows.length u)) :=
  extractSlots q rows (build q rows childOK order) u (rowOwner q rows childOK order u)

def slotArrays : Array (Σ u : Fin q.count, Array (Fin (rows.length u))) :=
  let s := build q rows childOK order
  Array.ofFn (fun u : Fin q.count => ⟨u, extractSlots q rows s u
    (rowOwner q rows childOK order u)⟩)

private theorem slotArray_list (u : Fin q.count) :
    (slotArray q rows childOK order u).toList =
      project (ownedSlot q rows u) (actual q rows childOK order u)
        (rowOwner q rows childOK order u) := by
  simp [slotArray, extractSlots]

theorem slotArray_mem (laws : Laws q order rank) (u : Fin q.count)
    (i : Fin (rows.length u)) : i ∈ (slotArray q rows childOK order u).toList := by
  obtain ⟨e, he, hi⟩ := actual_cover q rows childOK order rank laws u i
  rw [slotArray_list, ← hi]
  exact project_mem _ _ _ e he

theorem slotArray_covers (laws : Laws q order rank) (u : Fin q.count)
    (i : Fin (rows.length u)) :
    ∃ (j : Nat) (hj : j < (slotArray q rows childOK order u).size),
      (slotArray q rows childOK order u)[j]'hj = i := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp
    (slotArray_mem q rows childOK order rank laws u i)
  exact ⟨j, by simpa using hj, by simpa using he⟩

variable (noSelf : ∀ c : Fin q.count, c ≠ q.input.root → q.input.parent.read c ≠ c)

include noSelf in
theorem slotArray_increasing (laws : Laws q order rank) (u : Fin q.count) :
    ((slotArray q rows childOK order u).toList.map (slotRank q rows rank u)).Pairwise
      (· < ·) := by
  rw [slotArray_list, map_project _ (fun e => e.source) _ _ _
    (aligned q rows childOK order rank laws u)]
  exact increasing q rows childOK order noSelf u

include noSelf in
theorem slotArray_nodup (laws : Laws q order rank) (u : Fin q.count) :
    (slotArray q rows childOK order u).toList.Nodup := by
  have h := List.pairwise_map.mp (slotArray_increasing q rows childOK order rank noSelf laws u)
  apply h.imp
  intro a b hab he
  subst b
  exact (Nat.lt_irrefl _) hab

private theorem pullSlot {α : Type} (a : α) (ys : List α) (ha : a ∈ ys) :
    ∃ zs, ys.Perm (a :: zs) := by
  induction ys with
  | nil => cases ha
  | cons b ys ih =>
      rcases List.mem_cons.mp ha with rfl | ht
      · exact ⟨ys, List.Perm.refl _⟩
      · obtain ⟨zs, hp⟩ := ih ht
        exact ⟨b :: zs, (List.Perm.cons b hp).trans (by
          first | exact List.Perm.swap a b zs | exact List.Perm.swap b a zs)⟩

private theorem coverPerm {α : Type} (xs ys : List α) (hx : xs.Nodup)
    (hy : ys.Nodup) (H : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact .nil
      | cons a ys => exact False.elim (List.not_mem_nil ((H a).mpr (by simp)))
  | cons a xs ih =>
      obtain ⟨zs, hp⟩ := pullSlot a ys ((H a).mp (by simp))
      have hz := List.nodup_cons.mp (hp.nodup_iff.mp hy)
      have ht := List.nodup_cons.mp hx
      refine (List.Perm.cons a (ih zs ht.2 hz.2 ?_)).trans hp.symm
      intro b
      by_cases h : b = a
      · subst b
        exact iff_of_false ht.1 hz.1
      · simpa only [List.mem_cons, h, false_or] using (H b).trans hp.mem_iff

include noSelf in
theorem slotArray_perm (laws : Laws q order rank) (u : Fin q.count) :
    (slotArray q rows childOK order u).toList.Perm (List.finRange (rows.length u)) := by
  have hm (i : Fin (rows.length u)) : i ∈ List.finRange (rows.length u) := by
    exact List.mem_iff_getElem.mpr ⟨i.val, by simpa using i.isLt, by simp⟩
  apply coverPerm _ _ (slotArray_nodup q rows childOK order rank noSelf laws u)
  · first
    | exact List.nodup_finRange _
    | change List.Pairwise (· ≠ ·) _
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij he
      have hv := congrArg Fin.val he
      simp at hv <;> omega
  · exact fun i => ⟨fun _ => hm i, fun _ => slotArray_mem q rows childOK order rank laws u i⟩

include noSelf in
theorem slotArray_size (laws : Laws q order rank) (u : Fin q.count) :
    (slotArray q rows childOK order u).size = rows.length u := by
  simpa using (slotArray_perm q rows childOK order rank noSelf laws u).length_eq

open Kahn StaticLinearHead StaticHeadSweep

structure BoundKahnOrder (graph : Digraph) where
  result : Kahn.Result graph.vertexCount
  size_eq : result.order.size = graph.vertexCount
  top : graph.IsTopologicalList result.order.toList
  slots : Slots graph.vertexCount (Fin graph.vertexCount)
  slots_eq : slots = (KahnInverse.build result.order size_eq).slots

private theorem topOrderSize (xs : Array (Fin g.vertexCount))
    (ht : g.IsTopologicalList xs.toList) : xs.size = g.vertexCount := by
  have hn : (List.ofFn (id : Fin g.vertexCount → Fin g.vertexCount)).Nodup := by
    change List.Pairwise (· ≠ ·) _
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn, id_eq]
    intro he
    have hij' : i = j := congrArg Fin.val he
    omega
  have hp := (List.perm_ext_iff_of_nodup ht.1 hn).2
    (fun v => ⟨fun _ => List.mem_ofFn.mpr ⟨v, rfl⟩, fun _ => ht.2.1 v⟩)
  simpa using hp.length_eq

def BoundKahnOrder.ofResult (res : Kahn.Result g.vertexCount)
    (ht : g.IsTopologicalList res.order.toList) : BoundKahnOrder g :=
  let hs := topOrderSize res.order ht
  let inverse := KahnInverse.build res.order hs
  ⟨res, hs, ht, inverse.slots, rfl⟩

def BoundKahnOrder.ofRun (hacyc : g.IsAcyclic) : BoundKahnOrder g :=
  let res := Kahn.run g
  BoundKahnOrder.ofResult res (Kahn.run_isTopologicalList g hacyc)

def BoundKahnOrder.rankRead (b : BoundKahnOrder g) (v : Fin g.vertexCount) : Nat :=
  (b.slots.read v).val

theorem BoundKahnOrder.laws (b : BoundKahnOrder g) :
    Laws q b.result.order b.rankRead := by
  constructor
  · intro i hi
    let j : Fin g.vertexCount := ⟨i, by simpa [b.size_eq] using hi⟩
    have he := congrArg Fin.val
      (KahnInverse.rank_vertexAt b.result.order b.size_eq b.top.1 j)
    simpa only [BoundKahnOrder.rankRead, b.slots_eq, KahnInverse.rank,
      KahnInverse.vertexAt, Array.getElem_toList, j] using he
  · intro c
    exact b.top.2.1 (q.ids.originals.read c)
  · exact q.find_eq_some_iff_original

private theorem checkedNoSelf (c : Fin q.count) (hc : c ≠ q.input.root) :
    q.input.parent.read c ≠ c := by
  intro he
  have hok := q.reader.input_ok
  obtain ⟨d, hd⟩ : ∃ d : Fin q.count → Nat,
      d c = d (q.input.parent.read c) + 1 := by
    first
    | exact ⟨_, hok.depth_step c hc⟩
    | exact ⟨_, hok.1.depth_step c hc⟩
    | exact ⟨_, hok.tree.depth_step c hc⟩
  rw [he] at hd
  omega

structure KahnLocals where
  bound : BoundKahnOrder g
  arrays : Array (Σ u : Fin q.count, Array (Fin (rows.length u)))
  arrays_eq : arrays = slotArrays q rows childOK bound.result.order

def KahnLocals.prepare (b : BoundKahnOrder g) : KahnLocals q rows childOK :=
  let arrays := slotArrays q rows childOK b.result.order
  ⟨b, arrays, rfl⟩

theorem KahnLocals.size (p : KahnLocals q rows childOK) :
    p.arrays.size = q.count := by
  simp [p.arrays_eq, slotArrays]

theorem KahnLocals.get_eq (p : KahnLocals q rows childOK) (u : Fin q.count) :
    p.arrays[u.val]'(by simpa only [KahnLocals.size q rows childOK p] using u.isLt) =
      ⟨u, slotArray q rows childOK p.bound.result.order u⟩ := by
  rcases p with ⟨b, a, ha⟩
  subst a
  simp [slotArrays, slotArray, Array.getElem_ofFn]

theorem KahnLocals.increasing (p : KahnLocals q rows childOK) (u : Fin q.count) :
    let e := p.arrays[u.val]'(by
      simpa only [KahnLocals.size q rows childOK p] using u.isLt)
    (e.2.toList.map (slotRank q rows p.bound.rankRead e.1)).Pairwise (· < ·) := by
  dsimp only
  rw [KahnLocals.get_eq q rows childOK p u]
  exact slotArray_increasing q rows childOK p.bound.result.order p.bound.rankRead
    (checkedNoSelf q) (BoundKahnOrder.laws q p.bound) u

theorem KahnLocals.covers (p : KahnLocals q rows childOK) (u : Fin q.count) :
    let e := p.arrays[u.val]'(by
      simpa only [KahnLocals.size q rows childOK p] using u.isLt)
    ∀ i : Fin (rows.length e.1), ∃ (j : Nat) (hj : j < e.2.size), e.2[j]'hj = i := by
  dsimp only
  rw [KahnLocals.get_eq q rows childOK p u]
  exact slotArray_covers q rows childOK p.bound.result.order p.bound.rankRead
    (BoundKahnOrder.laws q p.bound) u

end PaperB.DenseQuotientLocalOrder
