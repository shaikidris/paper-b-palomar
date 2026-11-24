module

public import PaperB.ArcBuckets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX51

namespace LocalSchedule

universe u
variable {B : Nat} {L : Fin B → Nat} {α : Type u}

inductive Tag where
  | root | child

structure Slot (L : Fin B → Nat) where
  owner : Fin B
  index : Fin (L owner)

structure Choice (L : Fin B → Nat) where
  root : Option (Slot L)
  child : Option (Slot L)

structure Entry (L : Fin B → Nat) where
  owner : Fin B
  slot : Fin (L owner)
  tag : Tag
  source : Nat

private def piece (tag : Tag) (n : Nat) : Option (Slot L) → List (Entry L)
  | none => []
  | some s => [⟨s.owner, s.index, tag, n⟩]

private def block (c : Choice L) (n : Nat) : List (Entry L) :=
  piece .root n c.root ++ piece .child n c.child

/-- The second component charges one visit in each input cons branch. -/
def raw (pick : α → Choice L) : Nat → List α → List (Entry L) × Nat
  | _, [] => ([], 0)
  | n, a :: xs =>
      let here := block (pick a) n
      let tail := raw pick (n + 1) xs
      (here ++ tail.1, tail.2 + 1)

theorem raw_spec (pick : α → Choice L) (xs : List α) (n : Nat) :
    (raw pick n xs).2 = xs.length ∧
      (raw pick n xs).1.length ≤ 2 * xs.length := by
  induction xs generalizing n with
  | nil => simp [raw]
  | cons a xs ih =>
      obtain ⟨hv, hb⟩ := ih (n + 1)
      have hc : (block (pick a) n).length ≤ 2 := by
        cases pick a with
        | mk r c => cases r <;> cases c <;> simp [block, piece]
      simp only [raw, List.length_append, List.length_cons]
      exact ⟨congrArg (fun k : Nat => k + 1) hv, by omega⟩

structure Schedule (L : Fin B → Nat) where
  rows : EX51.Rows B (Entry L)
  work : EX51.Work
  visits : Nat

def schedule (pick : α → Choice L) (xs : List α) : Schedule L :=
  let r := raw pick 0 xs
  let g := EX51.groupMap (fun e : Entry L => e.owner) id r.1
  ⟨g.1, g.2, r.2⟩

theorem schedule_work (pick : α → Choice L) (xs : List α) :
    let m := (raw pick 0 xs).1.length
    (schedule pick xs).visits = xs.length ∧
      (schedule pick xs).work = ⟨B, m, m, m, B⟩ := by
  exact ⟨(raw_spec pick xs 0).1,
    EX51.groupMap_work (fun e : Entry L => e.owner) id (raw pick 0 xs).1⟩

theorem schedule_row (pick : α → Choice L) (xs : List α) (j : Fin B) :
    (schedule pick xs).rows.row j =
      (raw pick 0 xs).1.filter (fun e => decide (e.owner = j)) := by
  exact EX51.group_row (fun e : Entry L => e.owner) (raw pick 0 xs).1 j

/-- The root and child slots are not both owned by `j`. -/
def OneAt (c : Choice L) (j : Fin B) : Prop :=
  ¬ (c.root.map (fun s => s.owner) = some j ∧
     c.child.map (fun s => s.owner) = some j)

private def positions (j : Fin B) (es : List (Entry L)) : List Nat :=
  (es.filter (fun e => decide (e.owner = j))).map (fun e => e.source)

private theorem positions_append (j : Fin B) (xs ys : List (Entry L)) :
    positions j (xs ++ ys) = positions j xs ++ positions j ys := by
  simp only [positions, List.filter_append, List.map_append]

private theorem piece_positions (j : Fin B) (tag : Tag) (n : Nat)
    (s : Option (Slot L)) :
    positions j (piece tag n s) =
      if s.map (fun a => a.owner) = some j then [n] else [] := by
  cases s with
  | none => simp [positions, piece]
  | some s => by_cases h : s.owner = j <;> simp [positions, piece, h]

private theorem block_positions (c : Choice L) (j : Fin B) (n : Nat)
    (h : OneAt c j) :
    positions j (block c n) = [] ∨ positions j (block c n) = [n] := by
  simp only [block, positions_append, piece_positions]
  unfold OneAt at h
  by_cases hr : c.root.map (fun s => s.owner) = some j <;>
    by_cases hc : c.child.map (fun s => s.owner) = some j
  · exact (h ⟨hr, hc⟩).elim
  all_goals simp [hr, hc]

private theorem positions_spec (pick : α → Choice L) (j : Fin B)
    (xs : List α) (n : Nat) (h : ∀ a ∈ xs, OneAt (pick a) j) :
    let ps := positions j (raw pick n xs).1
    ps.Pairwise (· < ·) ∧ ∀ m ∈ ps, n ≤ m := by
  induction xs generalizing n with
  | nil => simp [raw, positions]
  | cons a xs ih =>
      obtain ⟨ht, hlo⟩ := ih (n + 1)
        (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))
      have ha : OneAt (pick a) j := h a (by simp)
      rcases block_positions (pick a) j n ha with he | he
      · simp only [raw, positions_append, he, List.nil_append]
        exact ⟨ht, fun m hm => Nat.le_trans (Nat.le_succ n) (hlo m hm)⟩
      · simp only [raw, positions_append, he, List.cons_append, List.nil_append]
        refine ⟨List.Pairwise.cons ?_ ht, ?_⟩
        · intro m hm
          have hl := hlo m hm
          omega
        · intro m hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Nat.le_refl _
          · exact Nat.le_trans (Nat.le_succ n) (hlo m hm)

theorem schedule_increasing (pick : α → Choice L) (xs : List α) (j : Fin B)
    (h : ∀ a ∈ xs, OneAt (pick a) j) :
    (((schedule pick xs).rows.row j).map (fun e => e.source)).Pairwise (· < ·) := by
  rw [schedule_row]
  exact (positions_spec pick j xs 0 h).1

end LocalSchedule

end EX51
