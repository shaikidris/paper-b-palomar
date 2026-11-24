module

public import PaperB.ForestHead
public import PaperB.StaticHeadSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestIncoming

open PaperB.StaticHeadSweep (Slots)

variable {N : Nat}

abbrev Marks (N : Nat) := Slots N (Option (Fin N))
abbrev Rows (N : Nat) := Slots N (List (Fin N))

def Ready (past : List (Fin N)) (a : Marks N) : Prop :=
  ∀ u y, a.read u = some y → y ∈ past

structure RowResult (N : Nat) where
  marks : Marks N
  row : List (Fin N)
  visits : Nat

/-- Emit by cons, so the row is in reverse first-occurrence order. -/
def scan (y : Fin N) (todo : List (Fin N)) (a : Marks N)
    (out : List (Fin N)) (n : Nat) : RowResult N :=
  match todo with
  | [] => ⟨a, out, n⟩
  | u :: us =>
    if a.read u = some y then scan y us a out (n + 1)
    else scan y us (a.write u (some y)) (u :: out) (n + 1)
termination_by structural todo

private theorem scan_spec (y : Fin N) (todo past : List (Fin N))
    (a : Marks N) (out : List (Fin N)) (n : Nat)
    (hr : Ready (y :: past) a) (hd : out.Nodup)
    (hs : ∀ v, a.read v = some y ↔ v ∈ out) :
    let r := scan y todo a out n
    Ready (y :: past) r.marks ∧ r.row.Nodup ∧
      (∀ v, v ∈ r.row ↔ v ∈ todo ∨ v ∈ out) ∧ r.visits = n + todo.length := by
  induction todo generalizing a out n with
  | nil =>
    refine ⟨hr, hd, ?_, ?_⟩
    · intro v
      simp [scan]
    · simp [scan]
  | cons u us ih =>
    by_cases h : a.read u = some y
    · obtain ⟨hr', hd', hm, hn⟩ := ih a out (n + 1) hr hd hs
      simp only [scan, ite_eq_left h]
      refine ⟨hr', hd', ?_, ?_⟩
      · intro v
        rw [hm, List.mem_cons, or_assoc]
        constructor
        · exact Or.inr
        · rintro (rfl | hv)
          · exact Or.inr ((hs _).mp h)
          · exact hv
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hn
    · let b := a.write u (some y)
      have hb : Ready (y :: past) b := by
        intro v z hz
        by_cases e : v = u
        · subst v
          have hz' : some y = some z := by simpa [b] using hz
          exact List.mem_cons.mpr (Or.inl (Option.some.inj hz').symm)
        · exact hr v z (by
            simpa only [b, Slots.read_write_other a u v (some y) e] using hz)
      have hb' : ∀ v, b.read v = some y ↔ v ∈ u :: out := by
        intro v
        by_cases e : v = u
        · subst v
          simp [b]
        · simpa only [b, Slots.read_write_other a u v (some y) e,
            List.mem_cons, e, false_or] using hs v
      have hu : (u :: out).Nodup :=
        List.nodup_cons.mpr ⟨fun hu => h ((hs u).mpr hu), hd⟩
      obtain ⟨hr', hd', hm, hn⟩ := ih b (u :: out) (n + 1) hb hu hb'
      simp only [scan, ite_eq_right h]
      refine ⟨hr', hd', ?_, ?_⟩
      · intro v
        rw [hm]
        simp only [List.mem_cons, or_assoc, or_left_comm]
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hn

theorem row_spec (y : Fin N) (raw past : List (Fin N)) (a : Marks N)
    (n : Nat) (hr : Ready past a) (hy : y ∉ past) :
    let r := scan y raw a [] n
    Ready (y :: past) r.marks ∧ r.row.Nodup ∧
      (∀ u, u ∈ r.row ↔ u ∈ raw) ∧ r.visits = n + raw.length := by
  have hs : ∀ u, a.read u = some y ↔ u ∈ ([] : List (Fin N)) := by
    intro u
    exact ⟨fun h => (hy (hr u y h)).elim, fun h => by cases h⟩
  simpa only [List.not_mem_nil, or_false] using
    scan_spec y raw past a [] n (fun u z h => List.Mem.tail y (hr u z h))
      (by simp) hs

structure Result (N : Nat) where
  marks : Marks N
  rows : Rows N
  visits : Nat

def sweep (raw : Rows N) (ys : List (Fin N)) (a : Marks N)
    (out : Rows N) (n : Nat) : Result N :=
  match ys with
  | [] => ⟨a, out, n⟩
  | y :: rest =>
    let r := scan y (raw.read y) a [] n
    sweep raw rest r.marks (out.write y r.row) r.visits
termination_by structural ys

/-- Cost specification only; `run` does not compute these lengths. -/
def rawVisits (raw : Rows N) : List (Fin N) → Nat
  | [] => 0
  | y :: ys => (raw.read y).length + rawVisits raw ys

def Good (raw out : Rows N) (ys : List (Fin N)) : Prop :=
  ∀ y ∈ ys, (out.read y).Nodup ∧ ∀ u, u ∈ out.read y ↔ u ∈ raw.read y

theorem sweep_spec (raw : Rows N) (ys past : List (Fin N))
    (a : Marks N) (out : Rows N) (n : Nat) (hd : ys.Nodup)
    (hf : ∀ y ∈ ys, y ∉ past) (hr : Ready past a) (hg : Good raw out past) :
    let r := sweep raw ys a out n
    Ready (ys ++ past) r.marks ∧ Good raw r.rows (ys ++ past) ∧
      r.visits = n + rawVisits raw ys := by
  induction ys generalizing past a out n with
  | nil =>
    refine ⟨hr, hg, ?_⟩
    simp [sweep, rawVisits]
  | cons y ys ih =>
    let r := scan y (raw.read y) a [] n
    let b := out.write y r.row
    obtain ⟨hr', hd', hm, hn⟩ := row_spec y (raw.read y) past a n hr
      (hf y (List.Mem.head _))
    have hg' : Good raw b (y :: past) := by
      intro v hv
      by_cases e : v = y
      · subst v
        simpa [b, r] using And.intro hd' hm
      · simpa only [b, Slots.read_write_other out y v r.row e] using
          hg v ((List.mem_cons.mp hv).resolve_left e)
    have hf' : ∀ v ∈ ys, v ∉ y :: past := by
      intro v hv hv'
      rcases List.mem_cons.mp hv' with e | hp
      · subst v
        exact (List.nodup_cons.mp hd).1 hv
      · exact hf v (List.Mem.tail y hv) hp
    obtain ⟨hR, hG, hN⟩ :=
      ih (y :: past) r.marks b r.visits (List.nodup_cons.mp hd).2 hf' hr' hg'
    have hp (v : Fin N) : v ∈ ys ++ (y :: past) ↔ v ∈ (y :: ys) ++ past := by
      simp only [List.mem_append, List.mem_cons, or_assoc, or_left_comm]
    refine ⟨fun u v h => (hp v).mp (hR u v h), fun v h => hG v ((hp v).mpr h), ?_⟩
    change (sweep raw ys r.marks b r.visits).visits = _
    have hc : r.visits = n + (raw.read y).length := hn
    rw [hN, hc, rawVisits, Nat.add_assoc]

/-- Initialize one stamp array and thread it through every supplied head. -/
def run (raw : Rows N) (ys : List (Fin N)) : Result N :=
  sweep raw ys (Slots.fill N none) (Slots.fill N []) 0

theorem run_spec (raw : Rows N) (ys : List (Fin N)) (hd : ys.Nodup) :
    Ready ys (run raw ys).marks ∧ Good raw (run raw ys).rows ys ∧
      (run raw ys).visits = rawVisits raw ys := by
  have hr : Ready [] (Slots.fill N (none : Option (Fin N))) := by
    intro u z h
    simp [Slots.read, Slots.fill] at h
  simp only [run]
  simpa only [List.append_nil, Nat.zero_add] using
    sweep_spec raw ys [] _ _ 0 hd (fun _ _ h => by cases h) hr
      (fun _ h => by cases h)

theorem testSpec {H : LabelledQuotient} (raw : Rows H.vertexCount)
    (ys : List (ForestHead.Vertex H)) (hd : ys.Nodup)
    (y : ForestHead.Vertex H) (hy : y ∈ ys)
    (cover : ∀ u, u ∈ raw.read y ↔ H.HasQuotientArc u y) :
    ForestHead.TestSpec (H := H) y ((run raw ys).rows.read y) := by
  obtain ⟨hn, hm⟩ := (run_spec raw ys hd).2.1 y hy
  exact ⟨hn, fun u => (hm u).trans (cover u)⟩

end PaperB.ForestIncoming
