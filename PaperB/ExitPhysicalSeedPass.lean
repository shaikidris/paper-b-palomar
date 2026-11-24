module

public import PaperB.ExitPhysicalOneSlot
public import PaperB.ExitPhysicalPass

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option maxHeartbeats 2000000

namespace PaperB.ExitPhysicalSeedPass

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot

/-- Designation and agreement with the logical forest are separate obligations. -/
structure SeedCertificate (F : JumpForest) (ref : Store) (slots u : Nat) : Prop where
  bound : u < slots
  designated : SeedSlot F u
  read_eq : ref u = seedRecord

abbrev Seed (F : JumpForest) (ref : Store) (slots : Nat) :=
  {u : Nat // SeedCertificate F ref slots u}

variable {bits words slots : Nat} {F : JumpForest} {ref : Store}
variable (tags : TagsFit bits) (base : Word bits)
variable (layout : Layout base words slots)
variable (fit : (storedCodec tags).valid seedRecord)

private def writeSeed (bank : WriteResult bits words) (s : Seed F ref slots) :
    WriteResult bits words :=
  seedWrite tags base layout bank s.val s.property.bound s.property.designated fit

/-- Fold over the supplied seed IDs, threading the preallocated bank without a
reset. The certificates and distinctness proof are erased. One fit proof
suffices because every slot receives the same record. -/
def run (seeds : List (Seed F ref slots)) (bank : WriteResult bits words)
    (_distinct : (seeds.map Subtype.val).Nodup) : WriteResult bits words :=
  seeds.foldl (writeSeed tags base layout fit) bank

private theorem tail_nodup {s : Seed F ref slots} {ss : List (Seed F ref slots)}
    (h : ((s :: ss).map Subtype.val).Nodup) : (ss.map Subtype.val).Nodup := by
  change (s.val :: ss.map Subtype.val).Nodup at h
  exact (List.nodup_cons.mp h).2

/-- Publish exactly the union of the old occupied slots and the supplied IDs,
with every published slot agreeing with `ref`. -/
theorem run_exact (seeds : List (Seed F ref slots)) :
    ∀ (bank : WriteResult bits words) (distinct : (seeds.map Subtype.val).Nodup)
      (occ : Nat → Prop) {old : Store},
      OccupiedExact tags base layout bank occ old →
      (∀ u, occ u → old u = ref u) →
      OccupiedExact tags base layout (run tags base layout fit seeds bank distinct)
        (fun u => occ u ∨ u ∈ seeds.map Subtype.val) ref := by
  induction seeds with
  | nil =>
      intro bank distinct occ old hex hread u hu
      have ho : occ u := by simpa using hu
      obtain ⟨hb, he⟩ := hex u ho
      exact ⟨hb, he.trans (hread u ho)⟩
  | cons s ss ih =>
      intro bank distinct occ old hex hread u hu
      let next := writeSeed tags base layout fit bank s
      have he := seedWrite_exact tags base layout bank s.val s.property.bound
        s.property.designated fit hex
      have hn : OccupiedExact tags base layout next
          (fun v => occ v ∨ v = s.val) ref := by
        intro v hv
        obtain ⟨hb, hr⟩ := he v hv
        refine ⟨hb, hr.trans ?_⟩
        change (if v = s.val then seedRecord else old v) = ref v
        by_cases hs : v = s.val
        · rw [if_pos hs, hs]
          exact s.property.read_eq.symm
        · rw [if_neg hs]
          exact hread v (Or.resolve_right hv hs)
      have hocc : (occ u ∨ u = s.val) ∨ u ∈ ss.map Subtype.val := by
        change occ u ∨ u ∈ (s :: ss).map Subtype.val at hu
        simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with ho | hs | ht
        · exact Or.inl (Or.inl ho)
        · exact Or.inl (Or.inr hs)
        · exact Or.inr ht
      exact ih next (tail_nodup distinct) (fun v => occ v ∨ v = s.val)
        (old := ref) hn (fun _ _ => rfl) u hocc

theorem run_writes (seeds : List (Seed F ref slots)) :
    ∀ (bank : WriteResult bits words) (distinct : (seeds.map Subtype.val).Nodup),
      (run tags base layout fit seeds bank distinct).writes =
        bank.writes + 18 * seeds.length := by
  induction seeds with
  | nil =>
      intro bank distinct
      simp [run]
  | cons s ss ih =>
      intro bank distinct
      let next := writeSeed tags base layout fit bank s
      have hw : next.writes = bank.writes + 18 :=
        seedWrite_writes tags base layout bank s.val s.property.bound
          s.property.designated fit
      calc
        (run tags base layout fit (s :: ss) bank distinct).writes =
            next.writes + 18 * ss.length :=
          ih next (tail_nodup distinct)
        _ = bank.writes + 18 * (s :: ss).length := by
          rw [hw, List.length_cons]
          omega

/-- Every cell outside all selected seed blocks keeps its original word. -/
theorem run_cell_outside (seeds : List (Seed F ref slots)) (cell : Nat) (hc : cell < words) :
    ∀ (bank : WriteResult bits words) (distinct : (seeds.map Subtype.val).Nodup),
      (∀ s ∈ seeds, cell < base.val + 18 * s.val ∨
        base.val + 18 * s.val + 18 ≤ cell) →
      (run tags base layout fit seeds bank distinct).mem[cell]'(
        (run tags base layout fit seeds bank distinct).lt_size hc) =
        bank.mem[cell]'(bank.lt_size hc) := by
  induction seeds with
  | nil =>
      intro bank distinct hout
      rfl
  | cons s ss ih =>
      intro bank distinct hout
      let next := writeSeed tags base layout fit bank s
      have ht := ih next (tail_nodup distinct)
        (fun t hm => hout t (List.mem_cons.mpr (Or.inr hm)))
      have hs : next.mem[cell]'(next.lt_size hc) = bank.mem[cell]'(bank.lt_size hc) :=
        seedWrite_cell_outside tags base layout bank s.val s.property.bound
          s.property.designated fit cell hc (hout s (by simp))
      simp only [run, List.foldl_cons] at ht ⊢
      exact Eq.trans ht hs

/-- In particular, a depth column laid out before the slot bank is unchanged. -/
theorem run_depth_cell (seeds : List (Seed F ref slots)) (bank : WriteResult bits words)
    (distinct : (seeds.map Subtype.val).Nodup)
    {depthBase : Word bits} {depthWords i : Nat}
    (hBefore : depthBase.val + depthWords ≤ base.val) (hi : i < depthWords) :
    (run tags base layout fit seeds bank distinct).mem[depthBase.val + i]'(
      (run tags base layout fit seeds bank distinct).lt_size
        (layout.depthCell_before_slot (depthBase := depthBase) hBefore hi 0).1) =
      bank.mem[depthBase.val + i]'(bank.lt_size
        (layout.depthCell_before_slot (depthBase := depthBase) hBefore hi 0).1) := by
  exact run_cell_outside tags base layout fit seeds (depthBase.val + i)
    (layout.depthCell_before_slot (depthBase := depthBase) hBefore hi 0).1 bank distinct
    (fun s _ =>
      Or.inl (layout.depthCell_before_slot (depthBase := depthBase) hBefore hi s.val).2)

end PaperB.ExitPhysicalSeedPass
