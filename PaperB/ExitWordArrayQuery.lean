module

public import PaperB.ExitPackedFused
public import PaperB.ExitStoredCodec

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute.StoredExit

open PaperB.Machine (Word)
open PaperB.StoredPacking
open PaperB.ExitMap.Retention
open CheckedFold

structure Region (bits words : Nat) where
  slots : Nat
  depthAddr : Fin slots → Word bits
  depthMem : ∀ v, (depthAddr v).val < words
  base : Word bits
  recordAddr : ∀ v : Fin slots, base.val + 18 * v.val + 18 ≤ 2 ^ bits
  recordMem : ∀ v : Fin slots, base.val + 18 * v.val + 18 ≤ words

@[inline] def depthAt {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (u : Nat) : Nat :=
  if hu : u < R.slots then
    (mem[(R.depthAddr ⟨u, hu⟩).val]'(R.depthMem ⟨u, hu⟩)).val
  else 0

@[inline] def recordAt {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits) (u : Nat) : CheckedFold.Stored :=
  if hu : u < R.slots then
    readStoredAt tags mem R.base u (R.recordAddr ⟨u, hu⟩) (R.recordMem ⟨u, hu⟩)
  else ⟨0, 0, Map.identity, Map.identity⟩

@[inline] def foldStored {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits) (u d : Nat) :=
  let depth := depthAt mem R
  foldFusedAux depth (recordAt mem R tags) d (depth u - d) u Map.identity 0

structure Occupied {bits endpoints : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
    (w : Width bits (max R.slots endpoints)) : Prop where
  size_eq : R.slots = F.size
  valid : ValidJumpForest F
  depth : ∀ v : Fin R.slots,
    (mem[(R.depthAddr v).val]'(R.depthMem v)).val = F.depthOf v.val
  parent_eq : ∀ u, u < F.size → (ref u).parent = F.parentOf u
  jump_eq : ∀ u, u < F.size → (ref u).jump = F.jumpOf u
  maps : ∀ v : Fin R.slots,
    MapBound endpoints (ref v.val).parentMap ∧ MapBound endpoints (ref v.val).jumpMap
  packed : ∀ (v : Fin R.slots) (hr : (storedCodec w.tags).valid (ref v.val))
      (i : Fin 18),
    mem[R.base.val + 18 * v.val + i.val]'(by
      have hm := R.recordMem v
      have hi := i.isLt
      omega) = (storedCodec w.tags).encode (ref v.val) hr i

section Exact

variable {bits endpoints : Nat} {mem : Array (Word bits)}
  {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
  {w : Width bits (max R.slots endpoints)}

private theorem depth_exact (ok : Occupied mem R F ref w) {u : Nat}
    (hu : u < F.size) : depthAt mem R u = F.depthOf u := by
  have h : u < R.slots := ok.size_eq.symm ▸ hu
  simpa only [depthAt, dif_pos h] using ok.depth ⟨u, h⟩

private theorem record_exact (ok : Occupied mem R F ref w) {u : Nat}
    (hu : u < F.size) : recordAt mem R w.tags u = ref u := by
  have h : u < R.slots := ok.size_eq.symm ▸ hu
  let v : Fin R.slots := ⟨u, h⟩
  have hp : (ref u).parent < R.slots := by
    rw [ok.parent_eq u hu, ok.size_eq]
    exact ok.valid.parentOf_lt_size hu
  have hj : (ref u).jump < R.slots := by
    rw [ok.jump_eq u hu, ok.size_eq]
    exact ok.valid.jumpOf_lt_size hu
  have hr := stored_fits w (ref u) hp hj (ok.maps v).1 (ok.maps v).2
  rw [recordAt, dif_pos h]
  exact readStoredAt_exact w.tags mem R.base u (R.recordAddr v)
    (R.recordMem v) (ref u) hr (ok.packed v hr)

private theorem aux_exact (ok : Occupied mem R F ref w)
    (d budget u : Nat) (acc : Map) (steps : Nat) (hu : u < F.size) :
    foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget u acc steps =
      foldFusedAux F.depthOf ref d budget u acc steps := by
  conv => lhs; rw [foldFusedAux]
  conv => rhs; rw [foldFusedAux]
  rw [depth_exact ok hu]
  by_cases h : steps < budget ∧ d < F.depthOf u
  · have hj : (ref u).jump < F.size := by
      rw [ok.jump_eq u hu]
      exact ok.valid.jumpOf_lt_size hu
    have hp : (ref u).parent < F.size := by
      rw [ok.parent_eq u hu]
      exact ok.valid.parentOf_lt_size hu
    have he : selectAtDepth (depthAt mem R) d (recordAt mem R w.tags u) =
        selectAtDepth F.depthOf d (ref u) := by
      rw [record_exact ok hu]
      simp only [selectAtDepth, depth_exact ok hj]
    have hv : (selectAtDepth F.depthOf d (ref u)).dst < F.size := by
      by_cases ht : d ≤ F.depthOf (ref u).jump
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hj
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hp
    simp only [dif_pos h, he]
    exact aux_exact ok d budget _ _ (steps + 1) hv
  · simp only [dif_neg h]
termination_by budget - steps
decreasing_by
  have hb := h.1
  omega

theorem foldStored_exact (ok : Occupied mem R F ref w) {u : Nat}
    (hu : u < F.size) (d : Nat) :
    foldStored mem R w.tags u d = foldFused F ref u d := by
  change foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d
      (depthAt mem R u - d) u Map.identity 0 =
    foldFusedAux F.depthOf ref d (F.depthOf u - d) u Map.identity 0
  rw [depth_exact ok hu]
  exact aux_exact ok d _ u Map.identity 0 hu

theorem foldStored_steps_le (ok : Occupied mem R F ref w) (route : StoreOK F ref)
    {u n : Nat} (hu : u < F.size) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R w.tags u d).steps ≤ 3 * ceilLog2 (n + 2) := by
  rw [foldStored_exact ok hu d]
  exact foldFused_steps_le route ok.valid hu hn d

end Exact

/-- Worker upper charges: one depth probe at halt, or one current-depth
probe, one 18-word record read, and one jump-depth probe per hop. -/
inductive WordCharge (depth : Nat → Nat) (read : Nat → CheckedFold.Stored)
    (d budget : Nat) : Nat → Nat → Nat → Prop where
  | halt {u k : Nat} (h : ¬ (k < budget ∧ d < depth u)) :
      WordCharge depth read d budget u k 1
  | hop {u k c : Nat} (h : k < budget ∧ d < depth u)
      (tail : WordCharge depth read d budget
        (selectAtDepth depth d (read u)).dst (k + 1) c) :
      WordCharge depth read d budget u k (20 + c)

private theorem worker_charge (depth : Nat → Nat) (read : Nat → CheckedFold.Stored)
    (d budget u : Nat) (acc : Map) (k : Nat) :
    ∃ n, (foldFusedAux depth read d budget u acc k).steps = k + n ∧
      WordCharge depth read d budget u k (1 + 20 * n) := by
  by_cases h : k < budget ∧ d < depth u
  · let e := selectAtDepth depth d (read u)
    obtain ⟨n, hn, hc⟩ :=
      worker_charge depth read d budget e.dst (Map.compose acc e.map) (k + 1)
    refine ⟨n + 1, ?_, ?_⟩
    · rw [foldFusedAux, dif_pos h]
      change (foldFusedAux depth read d budget e.dst
        (Map.compose acc e.map) (k + 1)).steps = k + (n + 1)
      omega
    · rw [show 1 + 20 * (n + 1) = 20 + (1 + 20 * n) by omega]
      exact WordCharge.hop h hc
  · refine ⟨0, ?_, WordCharge.halt h⟩
    rw [foldFusedAux, dif_neg h, Nat.add_zero]
termination_by budget - k
decreasing_by
  have hb := h.1
  omega

/-- Budget initialization adds one word read to the worker charge. -/
theorem foldStored_wordReads {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits) (u d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R tags u d).steps + 2 := by
  obtain ⟨n, hn, hc⟩ := worker_charge (depthAt mem R) (recordAt mem R tags)
    d (depthAt mem R u - d) u Map.identity 0
  change (foldStored mem R tags u d).steps = 0 + n at hn
  exact ⟨1 + 20 * n, hc, by omega⟩

end PaperB.ExitMap.JumpMapRoute.StoredExit
