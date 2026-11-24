module

public import PaperB.FusedJumpMaps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute.PackedExit
open PaperB.ExitMap.CheckedFold
open JumpForest

/-- Pass the packed map-record getter, with its map region fixed, as
`getOccupied`. Its behavior outside occupied slots is immaterial. The worker
receives the actual depth reader and getter, not the specification forest. -/
@[inline] def foldPacked (R : JumpWordRegion) (mem : Array Nat)
    (getOccupied : Array Nat → Store) (u d : Nat) : Result :=
  let depth : Nat → Nat := fun v => readWord mem (R.depthAddr v)
  foldFusedAux depth (getOccupied mem) d (depth u - d) u Map.identity 0

private theorem aux_eq {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} {raw ref : Store} (layout : JumpWordLayout R F mem)
    (record_eq : ∀ v, v < F.size → raw v = ref v)
    (parent_eq : ∀ v, v < F.size → (ref v).parent = F.parentOf v)
    (jump_eq : ∀ v, v < F.size → (ref v).jump = F.jumpOf v)
    (d budget fuel u : Nat) (acc : Map) (steps : Nat)
    (hf : budget - steps = fuel) (hu : u < F.size) :
    foldFusedAux (fun v => readWord mem (R.depthAddr v)) raw d budget u acc steps =
      foldFusedAux F.depthOf ref d budget u acc steps := by
  induction fuel generalizing u acc steps with
  | zero =>
    have hb : ¬ steps < budget := by omega
    conv => lhs; rw [foldFusedAux]
    conv => rhs; rw [foldFusedAux]
    simp [hb]
  | succ fuel ih =>
    have hb : steps < budget := by omega
    have hd := layout.slot_depth u hu
    conv => lhs; rw [foldFusedAux]
    conv => rhs; rw [foldFusedAux]
    by_cases hl : d < F.depthOf u
    · have hj : (ref u).jump < F.size := by
        rw [jump_eq u hu]
        exact layout.valid.jumpOf_lt_size hu
      have hp : (ref u).parent < F.size := by
        rw [parent_eq u hu]
        exact layout.valid.parentOf_lt_size hu
      have hs :
          selectAtDepth (fun v => readWord mem (R.depthAddr v)) d (raw u) =
            selectAtDepth F.depthOf d (ref u) := by
        rw [record_eq u hu]
        simp only [selectAtDepth, layout.slot_depth _ hj]
      have hv : (selectAtDepth F.depthOf d (ref u)).dst < F.size := by
        by_cases h : d ≤ F.depthOf (ref u).jump
        · simpa [selectAtDepth, Stored.select, h] using hj
        · simpa [selectAtDepth, Stored.select, h] using hp
      have hg : steps < budget ∧ d < F.depthOf u := ⟨hb, hl⟩
      have hn : budget - (steps + 1) = fuel := by omega
      simp only [hd, dite_eq_left hg, hs]
      exact ih _ _ _ hn hv
    · simp [hd, hb, hl]

/-- Agreement covers the entire result. All record and target hypotheses are
restricted to occupied indices, including those used at recursive calls. -/
theorem foldPacked_eq_foldFused {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} (layout : JumpWordLayout R F mem)
    (getOccupied : Array Nat → Store) (ref : Store)
    (record_eq : ∀ v, v < F.size → getOccupied mem v = ref v)
    (parent_eq : ∀ v, v < F.size → (ref v).parent = F.parentOf v)
    (jump_eq : ∀ v, v < F.size → (ref v).jump = F.jumpOf v)
    {u : Nat} (hu : u < F.size) (d : Nat) :
    foldPacked R mem getOccupied u d = foldFused F ref u d := by
  change foldFusedAux (fun v => readWord mem (R.depthAddr v))
      (getOccupied mem) d (readWord mem (R.depthAddr u) - d) u Map.identity 0 =
    foldFusedAux F.depthOf ref d (F.depthOf u - d) u Map.identity 0
  rw [layout.slot_depth u hu]
  exact aux_eq layout record_eq parent_eq jump_eq d _ _ u Map.identity 0
    (Nat.sub_zero _) hu

/-- Proof-only upper charges for the worker. A halt can probe the current
depth once. A hop probes the current and jump depths once each and calls
the record getter once. `C` is the charge for that one getter call. -/
inductive ReadCharge (depth : Nat → Nat) (read : Store)
    (d budget C : Nat) : Result → Nat → Prop where
  | halt (s : Result) (h : ¬ (s.steps < budget ∧ d < depth s.stop)) :
      ReadCharge depth read d budget C s 1
  | hop (s : Result) (h : s.steps < budget ∧ d < depth s.stop) {q : Nat}
      (tail : ReadCharge depth read d budget C
        (let e := selectAtDepth depth d (read s.stop)
         ⟨e.dst, Map.compose s.composed e.map, s.steps + 1⟩) q) :
      ReadCharge depth read d budget C s (C + 2 + q)

private theorem aux_charge (depth : Nat → Nat) (read : Store)
    (d budget C : Nat) (s : Result) :
    ∃ k, (foldFusedAux depth read d budget s.stop s.composed s.steps).steps =
        s.steps + k ∧ ReadCharge depth read d budget C s (1 + (C + 2) * k) := by
  by_cases h : s.steps < budget ∧ d < depth s.stop
  · let e := selectAtDepth depth d (read s.stop)
    let t : Result := ⟨e.dst, Map.compose s.composed e.map, s.steps + 1⟩
    obtain ⟨k, hk, hc⟩ := aux_charge depth read d budget C t
    refine ⟨k + 1, ?_, ?_⟩
    · rw [foldFusedAux_registers depth read d budget s, if_pos h]
      calc
        _ = t.steps + k := hk
        _ = s.steps + (k + 1) := by
          change s.steps + 1 + k = s.steps + (k + 1)
          omega
    · have hh : ReadCharge depth read d budget C s (C + 2 + (1 + (C + 2) * k)) :=
        .hop s h hc
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hh
  · refine ⟨0, ?_, ?_⟩
    · rw [foldFusedAux_registers depth read d budget s, if_neg h, Nat.add_zero]
    · simpa only [Nat.mul_zero, Nat.add_zero] using
        (ReadCharge.halt (depth := depth) (read := read) (d := d)
          (budget := budget) (C := C) s h)
termination_by budget - s.steps
decreasing_by
  have hb := h.1
  change budget - (s.steps + 1) < budget - s.steps
  omega

/-- The worker charges at most `C + 2` reads per taken hop and one at halt.
Budget initialization adds one depth read, for a total upper charge of
`2 + (C + 2) * result.steps`. Use `C = 1` to count a packed record access as
one operation, or the getter's fixed word-read bound to count word reads. -/
theorem foldPacked_readCharge (R : JumpWordRegion) (mem : Array Nat)
    (getOccupied : Array Nat → Store) (u d C : Nat) :
    let depth : Nat → Nat := fun v => readWord mem (R.depthAddr v)
    ReadCharge depth (getOccupied mem) d (depth u - d) C
      ⟨u, Map.identity, 0⟩ (1 + (C + 2) * (foldPacked R mem getOccupied u d).steps) := by
  let depth : Nat → Nat := fun v => readWord mem (R.depthAddr v)
  obtain ⟨k, hk, hc⟩ :=
    aux_charge depth (getOccupied mem) d (depth u - d) C ⟨u, Map.identity, 0⟩
  change (foldPacked R mem getOccupied u d).steps = 0 + k at hk
  rw [Nat.zero_add] at hk
  rw [hk]
  exact hc

end PaperB.ExitMap.JumpMapRoute.PackedExit
