module

public import PaperB.ForestIncomingRaw
public import PaperB.ForestIncomingEpoch
public import PaperB.ForestExactDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestIncomingPrep

open StaticHeadSweep (Slots)
open ForestIncoming (Rows run run_spec testSpec rawVisits)
open ForestIncomingRaw (Entry Prepared arcHead prepare row row_eq mem_row
  supplied length_supplied rawTotal rawTotal_prepare)

private theorem heads_nodup (n : Nat) : (List.finRange n).Nodup := by
  first | exact List.nodup_finRange n | exact List.nodup_finRange | (simp; done) | exact?

def sources (H : LabelledQuotient) (p : Prepared H) : Rows H.vertexCount :=
  (List.finRange H.vertexCount).foldl
    (fun s y => s.write y ((row H p y).map Prod.fst))
    (Slots.fill H.vertexCount [])

private theorem fold_read {n : Nat} (f : Fin n → List (Fin n))
    (ys : List (Fin n)) (s : Rows n) (y : Fin n) :
    (ys.foldl (fun a z => a.write z (f z)) s).read y =
      if y ∈ ys then f y else s.read y := by
  induction ys generalizing s with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : y ∈ zs
    · have hy : y ∈ z :: zs := List.Mem.tail z h
      rw [ite_eq_left h, ite_eq_left hy]
    · by_cases e : y = z
      · subst z
        rw [ite_eq_right h, ite_eq_left (show y ∈ y :: zs from List.Mem.head _)] <;> simp
      · have hn : y ∉ z :: zs := fun hm => (List.mem_cons.mp hm).elim e h
        rw [ite_eq_right h, ite_eq_right hn, Slots.read_write_other s z y (f z) e]

theorem source_row (H : LabelledQuotient) (p : Prepared H) (y : Fin H.vertexCount) :
    (sources H p).read y = (row H p y).map Prod.fst := by
  rw [sources, fold_read,
    ite_eq_left (show y ∈ List.finRange H.vertexCount from by simp)]

theorem mem_source (H : LabelledQuotient) (u y : Fin H.vertexCount) :
    u ∈ (sources H (prepare H)).read y ↔
      ∃ a ∈ H.outArcs u, arcHead a = y := by
  rw [source_row, List.mem_map]
  constructor
  · rintro ⟨⟨v, a⟩, ha, hv⟩
    change v = u at hv
    subst v
    exact ⟨a, (mem_row H u y a).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(u, a), (mem_row H u y a).mpr ha, rfl⟩

/-- The erased bridge to the quotient adjacency predicate. -/
def Cover (H : LabelledQuotient) : Prop :=
  ∀ u y : Fin H.vertexCount,
    (∃ a ∈ H.outArcs u, arcHead a = y) ↔ H.HasQuotientArc u y

structure Built (H : LabelledQuotient) where
  labels : Prepared H
  raw : Rows H.vertexCount
  tests : ForestDictionary.Rows H
  visits : Nat

def build (H : LabelledQuotient) (cover : Cover H) : Built H :=
  let p := prepare H
  let s := sources H p
  let ys := List.finRange H.vertexCount
  let d := run s ys
  ⟨p, s, ⟨d.rows.read, fun y =>
    testSpec s ys (heads_nodup _) y (by simp [ys])
      (fun u => (mem_source H u y).trans (cover u y))⟩, d.visits⟩

private theorem sum_bump {n : Nat} (w : Fin n → Nat) (z : Fin n)
    (ys : List (Fin n)) (hd : ys.Nodup) :
    (ys.map (fun y => w y + (if z = y then 1 else 0))).sum =
      (ys.map w).sum + (if z ∈ ys then 1 else 0) := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    have hn := List.nodup_cons.mp hd
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    rw [ih hn.2]
    by_cases e : z = y
    · subst z
      simp [hn.1] <;> omega
    · simp [e, Nat.add_assoc]

private theorem bucket_mass {α : Type} {n : Nat} (key : α → Fin n)
    (ys : List (Fin n)) (hd : ys.Nodup) (hall : ∀ y, y ∈ ys) (xs : List α) :
    (ys.map (fun y => (xs.filter (fun a => decide (key a = y))).length)).sum =
      xs.length := by
  induction xs with
  | nil =>
    have hz : ∀ zs : List (Fin n), (zs.map (fun _ => (0 : Nat))).sum = 0 := by
      intro zs
      induction zs <;> simp [*]
    exact hz ys
  | cons a xs ih =>
    have he : (fun y => ((a :: xs).filter (fun b => decide (key b = y))).length) =
        (fun y => (xs.filter (fun b => decide (key b = y))).length +
          (if key a = y then 1 else 0)) := by
      funext y
      by_cases h : key a = y <;> simp [h]
    rw [he, sum_bump _ _ _ hd, ite_eq_left (hall _), ih, List.length_cons]

/-- Cost specification: one `Prod.fst` application per input cell of each map.
`build` does not run this length sum. -/
def mapCalls (H : LabelledQuotient) (p : Prepared H) : Nat :=
  ((List.finRange H.vertexCount).map fun y => (row H p y).length).sum

theorem mapCalls_prepare (H : LabelledQuotient) :
    mapCalls H (prepare H) = (supplied H).length := by
  simp only [mapCalls, row_eq]
  exact bucket_mass (fun e : Entry H => arcHead e.2) _
    (heads_nodup _) (fun y => by simp) (supplied H)

private theorem visits_sum {n : Nat} (s : Rows n) (ys : List (Fin n)) :
    rawVisits s ys = (ys.map fun y => (s.read y).length).sum := by
  induction ys <;> simp [rawVisits, *]

theorem visits_eq_mapCalls (H : LabelledQuotient) (cover : Cover H) :
    (build H cover).visits = mapCalls H (build H cover).labels := by
  change (run (sources H (prepare H)) (List.finRange H.vertexCount)).visits =
    mapCalls H (prepare H)
  rw [(run_spec _ _ (heads_nodup H.vertexCount)).2.2, visits_sum]
  simp only [mapCalls, source_row, List.length_map]

theorem visits_supplied (H : LabelledQuotient) (cover : Cover H) :
    (build H cover).visits = (supplied H).length := by
  rw [visits_eq_mapCalls]
  exact mapCalls_prepare H

theorem visits_rawTotal (H : LabelledQuotient) (cover : Cover H) :
    (build H cover).visits = rawTotal H (build H cover).labels := by
  change (build H cover).visits = rawTotal H (prepare H)
  rw [visits_supplied, length_supplied, rawTotal_prepare]

private theorem remove_one {α : Type} (x : α) (xs : List α) (hx : x ∈ xs) :
    ∃ zs : List α, zs.length + 1 = xs.length ∧
      ∀ z, z ≠ x → z ∈ xs → z ∈ zs := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with e | h
    · subst a
      exact ⟨xs, rfl, fun z hn hz => (List.mem_cons.mp hz).resolve_left hn⟩
    · obtain ⟨zs, hl, hm⟩ := ih h
      refine ⟨a :: zs, ?_, ?_⟩
      · simp only [List.length_cons]
        rw [← hl]
      · intro z hn hz
        rcases List.mem_cons.mp hz with e | hz
        · exact List.mem_cons.mpr (Or.inl e)
        · exact List.Mem.tail a (hm z hn hz)

private theorem length_le {α : Type} (xs zs : List α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, x ∈ zs) : xs.length ≤ zs.length := by
  induction xs generalizing zs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    obtain ⟨bs, hb, hc⟩ := remove_one a zs (hm a (List.Mem.head _))
    have hd := List.nodup_cons.mp hn
    have hp := ih bs hd.2 (fun u hu =>
      hc u (fun e => hd.1 (e ▸ hu)) (hm u (List.Mem.tail a hu)))
    rw [← hb]
    exact Nat.succ_le_succ hp

private theorem sum_le {α : Type} (f g : α → Nat) (ys : List α)
    (h : ∀ y, f y ≤ g y) : (ys.map f).sum ≤ (ys.map g).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (h y) ih

theorem testLengths_le (H : LabelledQuotient) (cover : Cover H) :
    ((List.finRange H.vertexCount).map fun y => ((build H cover).tests.row y).length).sum
      ≤ (supplied H).length := by
  rw [← mapCalls_prepare H]
  unfold mapCalls
  apply sum_le
  intro y
  have hg := (run_spec (sources H (prepare H)) _ (heads_nodup H.vertexCount)).2.1
    y (by simp)
  simpa only [build, source_row, List.length_map] using
    length_le _ _ hg.1 (fun u hu => (hg.2 u).mp hu)

end PaperB.ForestIncomingPrep
