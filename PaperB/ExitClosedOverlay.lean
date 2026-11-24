module

public import PaperB.ExitPartialOccupancy
public import PaperB.ExitSingleMap

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute.StoredExit

open PaperB.ExitPhysicalOneSlot (Job)
open PaperB.Machine (Word)
open PaperB.StoredPacking
open PaperB.ExitMap.Retention
open CheckedFold

/-- Frame a path without changing its endpoint or its map. Closure is needed
only for parent pointers, since those are the pointers a `ParentPath` reads. -/
theorem parentPath_frame_on_live
    {old read : Store} {rank rank' : Nat → Nat} {live : Nat → Prop}
    (closed : ∀ u, live u → live (old u).parent)
    (read_eq : ∀ u, live u → read u = old u)
    (rank_eq : ∀ u, live u → rank' u = rank u)
    {u v : Nat} {m : Map} (path : ParentPath old rank u v m) :
    live u → ParentPath read rank' u v m ∧ live v := by
  induction path with
  | nil u =>
      intro hu
      exact ⟨ParentPath.nil u, hu⟩
  | @cons u a m down tail ih =>
      intro hu
      have hp := closed u hu
      have he := read_eq u hu
      obtain ⟨tail', ha⟩ := ih hp
      have down' : rank' (read u).parent < rank' u := by
        rw [he, rank_eq _ hp, rank_eq _ hu]
        exact down
      have tail'' : ParentPath read rank' (read u).parent a m := by
        simpa only [he] using tail'
      exact ⟨by simpa only [he] using ParentPath.cons u down' tail'', ha⟩

/-- The map certificates that accompany the decoded reader contract.
`DecodedOccupied` itself does not assert that a decoded map is a path map. -/
structure ExactLiveHops (read : Store) (rank : Nat → Nat)
    (live : Nat → Prop) : Prop where
  parent_path : ∀ u, live u →
    ParentPath read rank u (read u).parent (read u).parentMap
  jump_path : ∀ u, live u → JumpOK read rank u

theorem ExactLiveHops.frame_on_live
    {old read : Store} {rank rank' : Nat → Nat} {live : Nat → Prop}
    (hops : ExactLiveHops old rank live)
    (closed : ∀ u, live u → live (old u).parent)
    (read_eq : ∀ u, live u → read u = old u)
    (rank_eq : ∀ u, live u → rank' u = rank u) :
    ExactLiveHops read rank' live where
  parent_path := by
    intro u hu
    simpa only [read_eq u hu] using
      (parentPath_frame_on_live closed read_eq rank_eq
        (hops.parent_path u hu) hu).1
  jump_path := by
    intro u hu
    simpa only [JumpOK, read_eq u hu] using
      (parentPath_frame_on_live closed read_eq rank_eq
        (hops.jump_path u hu) hu).1

private theorem parentPath_one_stored_hop
    {read : Store} {rank : Nat → Nat} {u : Nat}
    (down : rank (read u).parent < rank u) :
    ParentPath read rank u (read u).parent (read u).parentMap := by
  have castMap {m : Map}
      (p : ParentPath read rank u (read u).parent m)
      (hm : m = (read u).parentMap) :
      ParentPath read rank u (read u).parent (read u).parentMap :=
    hm ▸ p
  refine castMap (ParentPath.cons (read := read) (rank := rank) u down
    (ParentPath.nil (read := read) (rank := rank) (read u).parent)) ?_
  first
  | rfl
  | (simp; done)
  | exact?
  | simpa [Map.comp, Map.identity]

section Overlay

variable {bits : Nat} {mem : Array (Word bits)}
  {R : Region bits mem.size} {F : JumpForest} {old : Store}
  {tags : TagsFit bits} {live : Nat → Prop}

theorem DecodedOccupied.overlay_eq_on_live
    (ok : DecodedOccupied mem R F old tags live)
    (j : Job) (slot_eq : j.slot = F.size) :
    ∀ u, live u → j.overlay old u = old u := by
  intro u hu
  have hne : u ≠ j.slot := by
    rw [slot_eq]
    exact Nat.ne_of_lt (ok.live_lt_size u hu)
  simp only [Job.overlay, if_neg hne]

/-- The isolated step needs only the old live path certificates. In the skew
case the second certificate is at the jump read from the old parent record. -/
theorem DecodedOccupied.overlay_hops_exact
    (ok : DecodedOccupied mem R F old tags live)
    (hops : ExactLiveHops old F.depthOf live)
    (j : Job) (slot_eq : j.slot = F.size) (hp : live j.parent)
    (jump_eq : j.jump = (F.mkAppendedRecord j.parent).jump)
    (rank : Nat → Nat)
    (rank_eq : ∀ u, live u → rank u = F.depthOf u)
    (down : rank j.parent < rank j.slot) :
    (j.overlay old j.slot).parent = (F.mkAppendedRecord j.parent).parent ∧
    (j.overlay old j.slot).jump = (F.mkAppendedRecord j.parent).jump ∧
    ExactLiveHops (j.overlay old) rank (j.occupy live) ∧
    ParentPath (j.overlay old) rank j.slot j.parent j.edge := by
  have closed : ∀ u, live u → live (old u).parent := by
    intro u hu
    rw [ok.parent_eq u hu]
    exact ok.parent_live u hu
  have hpj : live (old j.parent).jump := by
    rw [ok.jump_eq j.parent hp]
    exact ok.jump_live j.parent hp
  have ranked : ExactLiveHops old rank live :=
    hops.frame_on_live closed (fun _ _ => rfl) rank_eq
  have framed : ExactLiveHops (j.overlay old) rank live :=
    hops.frame_on_live closed (ok.overlay_eq_on_live j slot_eq) rank_eq
  have built :
      (j.overlay old j.slot).parent = (F.mkAppendedRecord j.parent).parent ∧
      (j.overlay old j.slot).jump = (F.mkAppendedRecord j.parent).jump ∧
      JumpOK (j.overlay old) rank j.slot := by
    have overlay_eq : j.overlay old = (fun u => if u = F.size then
        buildOneSlot old j.parent j.jump j.edge else old u) := by
      funext u
      simp only [Job.overlay, slot_eq]
    simpa only [overlay_eq, slot_eq] using
      (buildOneSlot_exact F j.parent j.parent j.jump old rank j.edge
        rfl jump_eq
        (fun _ => ok.jump_eq j.parent hp)
        (fun _ => ok.jump_eq (old j.parent).jump hpj)
        (by simpa only [slot_eq] using down)
        (fun _ => ranked.jump_path j.parent hp)
        (fun _ => ranked.jump_path (old j.parent).jump hpj))
  have parent_new : (j.overlay old j.slot).parent = j.parent := built.1
  have map_new : (j.overlay old j.slot).parentMap = j.edge := by
    by_cases h : j.jump = j.parent
    · simp [Job.overlay, buildOneSlot, h, Stored.parentOnly]
    · simp [Job.overlay, buildOneSlot, h, Stored.skew]
  have edge_path : ParentPath (j.overlay old) rank j.slot j.parent j.edge := by
    have h := parentPath_one_stored_hop
      (read := j.overlay old) (rank := rank) (u := j.slot)
      (by simpa only [parent_new] using down)
    simpa only [parent_new, map_new] using h
  refine ⟨built.1, built.2.1, ?_, edge_path⟩
  constructor
  · intro u hu
    change live u ∨ u = j.slot at hu
    rcases hu with hu | rfl
    · exact framed.parent_path u hu
    · simpa only [parent_new, map_new] using edge_path
  · intro u hu
    change live u ∨ u = j.slot at hu
    rcases hu with hu | rfl
    · exact framed.jump_path u hu
    · exact built.2.2

/-- Extend the actual decoded reader contract after one isolated write.
The physical premises are readback at the bounded new slot and read
preservation at old live slots. No read of another dead slot is specified. -/
theorem DecodedOccupied.extend_isolated_overlay
    (ok : DecodedOccupied mem R F old tags live)
    (hops : ExactLiveHops old F.depthOf live)
    {mem' : Array (Word bits)} {R' : Region bits mem'.size} {G : JumpForest}
    (j : Job) (slot_eq : j.slot = F.size) (slot_bound : j.slot < R'.slots)
    (hp : live j.parent)
    (jump_eq : j.jump = (F.mkAppendedRecord j.parent).jump)
    (valid' : ValidJumpForest G) (size_eq : G.size = F.size + 1)
    (depth_old : ∀ u, live u → G.depthOf u = F.depthOf u)
    (parent_old : ∀ u, live u → G.parentOf u = F.parentOf u)
    (jump_old : ∀ u, live u → G.jumpOf u = F.jumpOf u)
    (parent_new : G.parentOf j.slot = (F.mkAppendedRecord j.parent).parent)
    (jump_new : G.jumpOf j.slot = (F.mkAppendedRecord j.parent).jump)
    (down : G.depthOf j.parent < G.depthOf j.slot)
    (depth_frame : ∀ u, live u → depthAt mem' R' u = depthAt mem R u)
    (record_frame : ∀ u, live u →
      recordAt mem' R' tags u = recordAt mem R tags u)
    (depth_written : depthAt mem' R' j.slot = G.depthOf j.slot)
    (record_written : recordAt mem' R' tags j.slot =
      buildOneSlot old j.parent j.jump j.edge) :
    DecodedOccupied mem' R' G (j.overlay old) tags (j.occupy live) ∧
    ExactLiveHops (j.overlay old) G.depthOf (j.occupy live) := by
  obtain ⟨hparent, hjump, hops', _⟩ :=
    ok.overlay_hops_exact hops j slot_eq hp jump_eq G.depthOf depth_old down
  have hread := ok.overlay_eq_on_live j slot_eq
  have hj_live : live (F.mkAppendedRecord j.parent).jump := by
    change live (if
      0 < F.depthOf j.parent - F.depthOf (F.jumpOf j.parent) ∧
        F.depthOf j.parent - F.depthOf (F.jumpOf j.parent) =
          F.depthOf (F.jumpOf j.parent) - F.depthOf (F.jumpOf (F.jumpOf j.parent))
      then F.jumpOf (F.jumpOf j.parent) else j.parent)
    split
    · exact ok.jump_live _ (ok.jump_live _ hp)
    · exact hp
  refine ⟨?_, hops'⟩
  change DecodedOccupied mem' R' G (j.overlay old) tags
    (fun u => live u ∨ u = j.slot)
  refine
    { size_le := by omega
      valid := valid'
      live_lt_size := ?_
      depth_exact := ?_
      record_exact := ?_
      parent_eq := ?_
      jump_eq := ?_
      parent_live := ?_
      jump_live := ?_ }
  · intro u hu
    rcases hu with hu | rfl
    · have hlt := ok.live_lt_size u hu
      omega
    · omega
  · intro u hu
    rcases hu with hu | rfl
    · exact (depth_frame u hu).trans
        ((ok.depth_exact u hu).trans (depth_old u hu).symm)
    · exact depth_written
  · intro u hu
    rcases hu with hu | rfl
    · rw [hread u hu]
      exact (record_frame u hu).trans (ok.record_exact u hu)
    · simpa [Job.overlay] using record_written
  · intro u hu
    rcases hu with hu | rfl
    · rw [hread u hu, ok.parent_eq u hu, parent_old u hu]
    · exact hparent.trans parent_new.symm
  · intro u hu
    rcases hu with hu | rfl
    · rw [hread u hu, ok.jump_eq u hu, jump_old u hu]
    · exact hjump.trans jump_new.symm
  · intro u hu
    rcases hu with hu | rfl
    · exact Or.inl (by rw [parent_old u hu]; exact ok.parent_live u hu)
    · exact Or.inl (by rw [parent_new]; exact hp)
  · intro u hu
    rcases hu with hu | rfl
    · exact Or.inl (by rw [jump_old u hu]; exact ok.jump_live u hu)
    · exact Or.inl (by rw [jump_new]; exact hj_live)

end Overlay

end PaperB.ExitMap.JumpMapRoute.StoredExit
