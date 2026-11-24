module

public import PaperB.RamExitSummarySweepROM
public import PaperB.RamExitSummarySweepCount
public import PaperB.RamExitSummarySweepBRun
public import PaperB.RamExitSummarySweepARun
public import PaperB.RamExitSummaryStage3

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (encodeBackPair encodeBackPair_eq_iff ofOrderedReader)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open PaperB.Exit.OrderedReaderResult
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

variable {bits : Nat}

def ramBankRegion (mem : Array (Word bits)) (N : Nat)
    (hFitMem : 19 * N ≤ mem.size) (hFitBits : 19 * N ≤ 2 ^ bits) :
    Region bits mem.size where
  slots := N
  depthAddr v := ⟨v.val, by have := v.isLt; omega⟩
  depthMem v := by have := v.isLt; dsimp only; omega
  base := ⟨N, by have := Nat.two_pow_pos bits; omega⟩
  recordAddr v := by have := v.isLt; dsimp only; omega
  recordMem v := by have := v.isLt; dsimp only; omega

section ActualOutputBridges

private theorem mapWordsAt_encode {bits : Nat} (hTag : TagsFit bits)
    {mem : Array (Word bits)} {addr : Nat} {m : Map}
    (hm : MapBound (2 ^ bits) m) (hMem : addr + 8 ≤ mem.size)
    (hM : MapWordsAt mem addr m) (k : Fin 8) :
    mem[addr + k.val]'(by have := k.isLt; omega) =
      (mapCodec hTag).encode m (mapValid_of_mapBound hTag hm) k := by
  have hk : addr + k.val < mem.size := by have := k.isLt; omega
  have h := (mapWordsAt_encode_iff hTag mem addr m hm).mp hM k
  rw [Array.getElem?_eq_getElem hk] at h
  exact Option.some.inj h

theorem packed_of_storedWords {bits : Nat} (hTag : TagsFit bits)
    {mem : Array (Word bits)} {base v : Nat} {r : CheckedFold.Stored}
    (hp : r.parent < 2 ^ bits) (hj : r.jump < 2 ^ bits)
    (hpm : MapBound (2 ^ bits) r.parentMap) (hjm : MapBound (2 ^ bits) r.jumpMap)
    (hr : (storedCodec hTag).valid r)
    (hMem : base + 18 * v + 18 ≤ mem.size)
    (h0 : (mem[base + 18 * v]?).map Fin.val = some r.parent)
    (h1 : (mem[base + 18 * v + 1]?).map Fin.val = some r.jump)
    (hPM : MapWordsAt mem (base + 18 * v + 2) r.parentMap)
    (hJM : MapWordsAt mem (base + 18 * v + 10) r.jumpMap) (i : Fin 18) :
    mem[base + 18 * v + i.val]'(by have := i.isLt; omega) =
      (storedCodec hTag).encode r hr i := by
  have hIrr : (storedCodec hTag).encode r hr i =
      (storedCodec hTag).encode r (storedValid_of_bounds hTag hp hj hpm hjm) i := rfl
  rw [hIrr, storedCodec_encode_at hTag r hp hj hpm hjm i]
  by_cases hi0 : i.val = 0
  · rw [dite_eq_left hi0]
    apply Fin.ext
    have hEq := h0
    rw [Array.getElem?_eq_getElem (by omega), Option.map_some] at hEq
    simpa only [hi0, Nat.add_zero] using Option.some.inj hEq
  · rw [dite_eq_right hi0]
    by_cases hi1 : i.val = 1
    · rw [dite_eq_left hi1]
      apply Fin.ext
      have hEq := h1
      rw [Array.getElem?_eq_getElem (by omega), Option.map_some] at hEq
      simpa only [hi1] using Option.some.inj hEq
    · rw [dite_eq_right hi1]
      by_cases hi10 : i.val < 10
      · rw [dite_eq_left hi10]
        have hEq : base + 18 * v + i.val = (base + 18 * v + 2) + (i.val - 2) := by omega
        have hM := mapWordsAt_encode hTag hpm (by omega) hPM ⟨i.val - 2, by omega⟩
        simpa only [hEq] using hM
      · rw [dite_eq_right hi10]
        have hEq : base + 18 * v + i.val = (base + 18 * v + 10) + (i.val - 10) := by omega
        have hM := mapWordsAt_encode hTag hjm (by omega) hJM ⟨i.val - 10, by have := i.isLt; omega⟩
        simpa only [hEq] using hM

theorem sealedPlaced_of_valuesWords {bits endpoints : Nat}
    (wFit : Width bits endpoints) {mem : Array (Word bits)} {pBase : Nat}
    (prior : Array (Option Values)) (hb : SealedPriorBase.BaseBound endpoints prior)
    (hMem : pBase + 6 * prior.size ≤ mem.size)
    (hVals : ∀ y : Fin prior.size,
      ValuesWordsAt mem (pBase + 6 * y.val) ((prior[y.val]'(y.isLt)).getD BuiltExit.zero)) :
    ∀ j : Fin (6 * prior.size),
      mem[pBase + j.val]'(by have := j.isLt; omega) =
        (SealedPriorBase.serialize wFit prior hb)[j.val]'(by
          simpa only [SealedPriorBase.seal_size] using j.isLt) := by
  intro j
  let v : Fin prior.size := ⟨j.val / 6, by have := j.isLt; omega⟩
  have hkLt : j.val % 6 < 6 := Nat.mod_lt _ (by decide)
  have hMod : 6 * v.val + j.val % 6 = j.val := by dsimp only [v]; omega
  simp only [SealedPriorBase.serialize, Array.getElem_ofFn]
  change mem[pBase + j.val]'_ =
    if hk : j.val % 6 < 3 then
      (intervalCodec wFit.tags).encode ((prior[v.val]'(v.isLt)).getD BuiltExit.zero).x0
        (rankBound_mono wFit.ranks (hb v).1) ⟨j.val % 6, hk⟩
    else
      (intervalCodec wFit.tags).encode ((prior[v.val]'(v.isLt)).getD BuiltExit.zero).x1
        (rankBound_mono wFit.ranks (hb v).2) ⟨j.val % 6 - 3, by omega⟩
  by_cases hk : j.val % 6 < 3
  · rw [dite_eq_left hk]
    have h := (intervalWordsAt_encode_iff wFit.tags mem (pBase + 6 * v.val) _
      (rankBound_mono wFit.ranks (hb v).1)).mp (hVals v).1 ⟨j.val % 6, hk⟩
    rw [show pBase + 6 * v.val + j.val % 6 = pBase + j.val by omega,
      Array.getElem?_eq_getElem (by have := j.isLt; omega)] at h
    exact Option.some.inj h
  · rw [dite_eq_right hk]
    have h := (intervalWordsAt_encode_iff wFit.tags mem (pBase + 6 * v.val + 3) _
      (rankBound_mono wFit.ranks (hb v).2)).mp (hVals v).2 ⟨j.val % 6 - 3, by omega⟩
    have hh : pBase + 6 * v.val + 3 + (j.val % 6 - 3) = pBase + j.val := by omega
    rw [hh, Array.getElem?_eq_getElem (by have := j.isLt; omega)] at h
    exact Option.some.inj h

end ActualOutputBridges

end PaperB.RamProgram.ExitSummaryBuild
