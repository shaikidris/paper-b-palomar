module

public import PaperB.ExitPriorBase
public import PaperB.ExitPhysicalOneSlot
public import PaperB.ExitArraySweep
public import PaperB.StaticHeadSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Replacement for `PaperB/ExitPartialOccupancy.lean`.
The packed invariant implies the decoded invariant. Both use the same
fused-fold proof; the physical writer only needs the decoded invariant.
-/

namespace PaperB.ExitMap.JumpMapRoute.StoredExit

open PaperB.Machine (Word)
open PaperB.StoredPacking
open PaperB.ExitMap.Retention
open CheckedFold
open PriorBase (run accumulated)
open PaperB.BuiltExit (zero)

/-- A partially filled arena. Dead slots and spare capacity are unconstrained. -/
structure PartialOccupied {bits endpoints : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
    (w : Width bits (max R.slots endpoints)) (live : Nat → Prop) : Prop where
  size_le : F.size ≤ R.slots
  valid : ValidJumpForest F
  live_lt_size : ∀ u, live u → u < F.size
  depth : ∀ v : Fin R.slots, live v.val →
    (mem[(R.depthAddr v).val]'(R.depthMem v)).val = F.depthOf v.val
  parent_eq : ∀ u, live u → (ref u).parent = F.parentOf u
  jump_eq : ∀ u, live u → (ref u).jump = F.jumpOf u
  parent_live : ∀ u, live u → live (F.parentOf u)
  jump_live : ∀ u, live u → live (F.jumpOf u)
  maps : ∀ v : Fin R.slots, live v.val →
    MapBound endpoints (ref v.val).parentMap ∧ MapBound endpoints (ref v.val).jumpMap
  packed : ∀ (v : Fin R.slots), live v.val →
    ∀ (hr : (storedCodec w.tags).valid (ref v.val)) (i : Fin 18),
      mem[R.base.val + 18 * v.val + i.val]'(by
        have hm := R.recordMem v
        have hi := i.isLt
        omega) = (storedCodec w.tags).encode (ref v.val) hr i

/-- The live query view requires exact reader results, not canonical encodings. -/
structure DecodedOccupied {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
    (tags : TagsFit bits) (live : Nat → Prop) : Prop where
  size_le : F.size ≤ R.slots
  valid : ValidJumpForest F
  live_lt_size : ∀ u, live u → u < F.size
  depth_exact : ∀ u, live u → depthAt mem R u = F.depthOf u
  record_exact : ∀ u, live u → recordAt mem R tags u = ref u
  parent_eq : ∀ u, live u → (ref u).parent = F.parentOf u
  jump_eq : ∀ u, live u → (ref u).jump = F.jumpOf u
  parent_live : ∀ u, live u → live (F.parentOf u)
  jump_live : ∀ u, live u → live (F.jumpOf u)

section Exact

variable {bits endpoints : Nat} {mem : Array (Word bits)}
  {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
  {w : Width bits (max R.slots endpoints)} {tags : TagsFit bits}
  {live : Nat → Prop}

theorem depth_exact_live (ok : PartialOccupied mem R F ref w live) {u : Nat}
    (hu : live u) : depthAt mem R u = F.depthOf u := by
  have h : u < R.slots := Nat.lt_of_lt_of_le (ok.live_lt_size u hu) ok.size_le
  simpa only [depthAt, dif_pos h] using ok.depth ⟨u, h⟩ hu

theorem record_exact_live (ok : PartialOccupied mem R F ref w live) {u : Nat}
    (hu : live u) : recordAt mem R w.tags u = ref u := by
  have hF := ok.live_lt_size u hu
  have h : u < R.slots := Nat.lt_of_lt_of_le hF ok.size_le
  let v : Fin R.slots := ⟨u, h⟩
  have hp : (ref u).parent < R.slots := by
    rw [ok.parent_eq u hu]
    exact Nat.lt_of_lt_of_le (ok.valid.parentOf_lt_size hF) ok.size_le
  have hj : (ref u).jump < R.slots := by
    rw [ok.jump_eq u hu]
    exact Nat.lt_of_lt_of_le (ok.valid.jumpOf_lt_size hF) ok.size_le
  have hm := ok.maps v hu
  have hr := stored_fits w (ref u) hp hj hm.1 hm.2
  rw [recordAt, dif_pos h]
  exact readStoredAt_exact w.tags mem R.base u (R.recordAddr v)
    (R.recordMem v) (ref u) hr (ok.packed v hu hr)

theorem PartialOccupied.toDecoded (ok : PartialOccupied mem R F ref w live) :
    DecodedOccupied mem R F ref w.tags live where
  size_le := ok.size_le
  valid := ok.valid
  live_lt_size := ok.live_lt_size
  depth_exact := fun _ hu => depth_exact_live ok hu
  record_exact := fun _ hu => record_exact_live ok hu
  parent_eq := ok.parent_eq
  jump_eq := ok.jump_eq
  parent_live := ok.parent_live
  jump_live := ok.jump_live

private theorem aux_exact_live (ok : DecodedOccupied mem R F ref tags live)
    (d budget : Nat) {u : Nat} {acc : Map} {steps : Nat} (hu : live u) :
    foldFusedAux (depthAt mem R) (recordAt mem R tags) d budget u acc steps =
      foldFusedAux F.depthOf ref d budget u acc steps := by
  conv => lhs; rw [foldFusedAux]
  conv => rhs; rw [foldFusedAux]
  rw [ok.depth_exact u hu]
  by_cases h : steps < budget ∧ d < F.depthOf u
  · have hj : live (ref u).jump := by
      rw [ok.jump_eq u hu]
      exact ok.jump_live u hu
    have hp : live (ref u).parent := by
      rw [ok.parent_eq u hu]
      exact ok.parent_live u hu
    have he : selectAtDepth (depthAt mem R) d (recordAt mem R tags u) =
        selectAtDepth F.depthOf d (ref u) := by
      rw [ok.record_exact u hu]
      simp only [selectAtDepth, ok.depth_exact (ref u).jump hj]
    have hv : live (selectAtDepth F.depthOf d (ref u)).dst := by
      by_cases ht : d ≤ F.depthOf (ref u).jump
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hj
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hp
    simp only [dif_pos h, he]
    exact aux_exact_live ok d budget hv
  · simp only [dif_neg h]
termination_by budget - steps
decreasing_by
  have hb := h.1
  omega

theorem DecodedOccupied.foldStored_exact_live
    (ok : DecodedOccupied mem R F ref tags live) {u : Nat}
    (hu : live u) (d : Nat) :
    foldStored mem R tags u d = foldFused F ref u d := by
  change foldFusedAux (depthAt mem R) (recordAt mem R tags) d
      (depthAt mem R u - d) u Map.identity 0 =
    foldFusedAux F.depthOf ref d (F.depthOf u - d) u Map.identity 0
  rw [ok.depth_exact u hu]
  exact aux_exact_live ok d (F.depthOf u - d) hu

theorem DecodedOccupied.foldStored_steps_le_live
    (ok : DecodedOccupied mem R F ref tags live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R tags u d).steps ≤ 3 * ceilLog2 (n + 2) := by
  rw [ok.foldStored_exact_live hu d]
  exact foldFused_steps_le route ok.valid (ok.live_lt_size u hu) hn d

theorem DecodedOccupied.run_exact_fold_live
    (ok : DecodedOccupied mem R F ref tags live) {u : Nat}
    (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) :
    run mem R tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d))
        ((prior[v.val]'(v.isLt)).getD zero) := by
  simp only [run, ok.foldStored_exact_live hu d]

theorem DecodedOccupied.run_exact_base_live
    (ok : DecodedOccupied mem R F ref tags live) {u : Nat}
    (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) (seed : Values)
    (hbase : prior[v.val]'(v.isLt) = some seed) :
    run mem R tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d)) seed := by
  simp only [ok.run_exact_fold_live hu d prior v, hbase, Option.getD]

/-- Charge the initial depth lookup and the one prior-base read separately
from the packed worker. -/
theorem DecodedOccupied.run_read_charge_live
    (ok : DecodedOccupied mem R F ref tags live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3 := by
  obtain ⟨c, hc, hwords⟩ := foldStored_wordReads mem R tags u d
  have hsteps := ok.foldStored_steps_le_live route hu hn d
  exact ⟨c, hc, hwords, by omega⟩

theorem foldStored_exact_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat) :
    foldStored mem R w.tags u d = foldFused F ref u d :=
  ok.toDecoded.foldStored_exact_live hu d

theorem foldStored_steps_le_live (ok : PartialOccupied mem R F ref w live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R w.tags u d).steps ≤ 3 * ceilLog2 (n + 2) :=
  ok.toDecoded.foldStored_steps_le_live route hu hn d

theorem run_exact_fold_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) :
    run mem R w.tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d))
        ((prior[v.val]'(v.isLt)).getD zero) :=
  ok.toDecoded.run_exact_fold_live hu d prior v

theorem run_exact_base_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) (seed : Values)
    (hbase : prior[v.val]'(v.isLt) = some seed) :
    run mem R w.tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d)) seed :=
  ok.toDecoded.run_exact_base_live hu d prior v seed hbase

theorem run_read_charge_live (ok : PartialOccupied mem R F ref w live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R w.tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R w.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3 :=
  ok.toDecoded.run_read_charge_live route hu hn d

end Exact

section Physical

variable {bits words : Nat} {bank : PaperB.ExitStoredWrite.WriteResult bits words}
  {R : Region bits bank.mem.size} {F : JumpForest}
  {ref : Nat → CheckedFold.Stored} {tags : TagsFit bits} {live : Nat → Prop}
  {layout : PaperB.ExitPhysicalOneSlot.Layout R.base words R.slots}

/-- `OccupiedExact` supplies record reads from this very bank, with the
region's packed base and capacity. Exact words at the read-only depth
addresses are a separate premise, not a consequence of the writer invariant. -/
theorem DecodedOccupied.ofOccupiedExact
    (occupied : PaperB.ExitPhysicalOneSlot.OccupiedExact
      tags R.base layout bank live ref)
    (hsize : F.size ≤ R.slots) (hvalid : ValidJumpForest F)
    (hlive : ∀ u, live u → u < F.size)
    (hdepth : ∀ v : Fin R.slots, live v.val →
      (bank.mem[(R.depthAddr v).val]'(R.depthMem v)).val = F.depthOf v.val)
    (hparent : ∀ u, live u → (ref u).parent = F.parentOf u)
    (hjump : ∀ u, live u → (ref u).jump = F.jumpOf u)
    (hparentLive : ∀ u, live u → live (F.parentOf u))
    (hjumpLive : ∀ u, live u → live (F.jumpOf u)) :
    DecodedOccupied bank.mem R F ref tags live where
  size_le := hsize
  valid := hvalid
  live_lt_size := hlive
  depth_exact := by
    intro u hu
    have h : u < R.slots := Nat.lt_of_lt_of_le (hlive u hu) hsize
    simpa only [depthAt, dif_pos h] using hdepth ⟨u, h⟩ hu
  record_exact := by
    intro u hu
    obtain ⟨h, hread⟩ := occupied u hu
    rw [recordAt, dif_pos h]
    simpa only [PaperB.ExitPhysicalOneSlot.readSlot] using hread
  parent_eq := hparent
  jump_eq := hjump
  parent_live := hparentLive
  jump_live := hjumpLive

end Physical

section PriorSlots

open PaperB.BuiltExit

/-- Rewrap the existing array. The sweep has already supplied the `Option`
layer, so neither an array copy nor an element conversion is needed. -/
@[inline] def priorSlotsView {N : Nat} (s : EX42.ArraySweep.Slots Values N) :
    StaticHeadSweep.Slots N (Option Values) :=
  ⟨s.data, s.size_data⟩

theorem priorSlotsView_data {N : Nat} (s : EX42.ArraySweep.Slots Values N) :
    (priorSlotsView s).data = s.data :=
  rfl

theorem priorSlotsView_read {N : Nat} (s : EX42.ArraySweep.Slots Values N)
    (v : Fin N) :
    (priorSlotsView s).read v = s.read v :=
  rfl

/-- The callback's index is the caller's index with the array-size proof. -/
@[inline] def priorCellIndex {N : Nat}
    (prior : StaticHeadSweep.Slots N (Option Values)) (v : Fin N) :
    Fin prior.data.size :=
  ⟨v.val, by simpa only [prior.len] using v.isLt⟩

theorem priorCellIndex_val {N : Nat}
    (prior : StaticHeadSweep.Slots N (Option Values)) (v : Fin N) :
    (priorCellIndex prior v).val = v.val :=
  rfl

/-- The actual callback, unfolded: its prior-base operand comes from one
`Option Values` cell at `v`. The packed fold does not take the prior array. -/
theorem run_at_prior_slot {bits N : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits)
    (prior : StaticHeadSweep.Slots N (Option Values)) (v : Fin N) (u d : Nat) :
    PriorBase.run mem R tags prior.data (priorCellIndex prior v) u d =
      Map.eval (accumulated (foldStored mem R tags u d))
        ((prior.read v).getD zero) :=
  rfl

theorem DecodedOccupied.run_exact_arraySweep_live
    {bits N : Nat} {mem : Array (Word bits)} {R : Region bits mem.size}
    {F : JumpForest} {ref : Nat → CheckedFold.Stored} {tags : TagsFit bits}
    {live : Nat → Prop} (ok : DecodedOccupied mem R F ref tags live)
    {u : Nat} (hu : live u) (d : Nat)
    (prior : EX42.ArraySweep.Slots Values N) (v : Fin N) (seed : Values)
    (hbase : prior.read v = some seed) :
    PriorBase.run mem R tags (priorSlotsView prior).data
        (priorCellIndex (priorSlotsView prior) v) u d =
      Map.eval (accumulated (foldFused F ref u d)) seed := by
  simp only [run_at_prior_slot, ok.foldStored_exact_live hu d,
    priorSlotsView_read, hbase, Option.getD]

/-- End-to-end exactness and read charge for the callback on the writer's
bank and the sweep's existing prior-base array. -/
theorem run_physical_exact_toll_live
    {bits words N : Nat} {bank : PaperB.ExitStoredWrite.WriteResult bits words}
    {R : Region bits bank.mem.size} {F : JumpForest}
    {ref : Nat → CheckedFold.Stored} {tags : TagsFit bits} {live : Nat → Prop}
    {layout : PaperB.ExitPhysicalOneSlot.Layout R.base words R.slots}
    (occupied : PaperB.ExitPhysicalOneSlot.OccupiedExact
      tags R.base layout bank live ref)
    (hsize : F.size ≤ R.slots) (hvalid : ValidJumpForest F)
    (hlive : ∀ u, live u → u < F.size)
    (hdepth : ∀ v : Fin R.slots, live v.val →
      (bank.mem[(R.depthAddr v).val]'(R.depthMem v)).val = F.depthOf v.val)
    (hparent : ∀ u, live u → (ref u).parent = F.parentOf u)
    (hjump : ∀ u, live u → (ref u).jump = F.jumpOf u)
    (hparentLive : ∀ u, live u → live (F.parentOf u))
    (hjumpLive : ∀ u, live u → live (F.jumpOf u))
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat)
    (prior : EX42.ArraySweep.Slots Values N) (v : Fin N) (seed : Values)
    (hbase : prior.read v = some seed) :
    (PriorBase.run bank.mem R tags (priorSlotsView prior).data
        (priorCellIndex (priorSlotsView prior) v) u d =
      Map.eval (accumulated (foldFused F ref u d)) seed) ∧
    (∃ c, WordCharge (depthAt bank.mem R) (recordAt bank.mem R tags) d
        (depthAt bank.mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored bank.mem R tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3) := by
  have ok : DecodedOccupied bank.mem R F ref tags live :=
    DecodedOccupied.ofOccupiedExact occupied hsize hvalid hlive hdepth
      hparent hjump hparentLive hjumpLive
  exact ⟨ok.run_exact_arraySweep_live hu d prior v seed hbase,
    ok.run_read_charge_live route hu hn d⟩

end PriorSlots

end PaperB.ExitMap.JumpMapRoute.StoredExit
