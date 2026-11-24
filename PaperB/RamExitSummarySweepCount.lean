module

public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepARun
public import PaperB.RamExitSummaryStage3

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

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

section ListSumHelpers

private theorem nodup_map_sum_le (f : Nat → Nat) :
    ∀ (l1 l2 : List Nat), l1.Nodup → (∀ x ∈ l1, x ∈ l2) →
      (l1.map f).sum ≤ (l2.map f).sum
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l2 := hsub a List.mem_cons_self
    have hih := nodup_map_sum_le f t (l2.erase a) hnd.2 (fun x hx =>
      (List.mem_erase_of_ne (fun he : x = a => hnd.1 (he ▸ hx))).mpr
        (hsub x (List.mem_cons_of_mem a hx)))
    have her : (l2.map f).sum = f a + ((l2.erase a).map f).sum := by
      clear hih hnd hsub
      induction l2 with
      | nil => simp at ha
      | cons b bs ihb =>
        simp only [List.mem_cons] at ha
        by_cases hab : b = a
        · subst hab; simp [List.erase_cons_head]
        · have hbs : a ∈ bs := ha.elim (fun h => absurd h.symm hab) id
          rw [List.erase_cons]
          split
          · next he => exact absurd (eq_of_beq he) hab
          · simp only [List.map_cons, List.sum_cons]
            rw [ihb hbs]; omega
    simp only [List.map_cons, List.sum_cons, her]
    omega

private theorem list_sum_map_range (H : LabelledQuotient) :
    ∀ k : Nat, ((List.range k).map (degIn H)).sum = prefixIn H k
  | 0 => rfl
  | k + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
      list_sum_map_range H k, prefixIn]

def remDegIn (H : LabelledQuotient) (orderKahn : Array (Vertex H))
    (sizeKahn : orderKahn.size = H.vertexCount) (idx : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 =>
    (if h : idx < H.vertexCount then
      degIn H (orderedVertexAt orderKahn sizeKahn ⟨idx, h⟩).val
     else 0) + remDegIn H orderKahn sizeKahn (idx + 1) rem

private theorem remDegIn_eq_drop_sum (H : LabelledQuotient)
    (orderKahn : Array (Vertex H)) (sizeKahn : orderKahn.size = H.vertexCount) :
    ∀ (rem idx : Nat), idx + rem ≤ H.vertexCount →
      remDegIn H orderKahn sizeKahn idx rem =
        ((((List.finRange H.vertexCount).drop idx).take rem).map
          (fun i => degIn H (orderedVertexAt orderKahn sizeKahn i).val)).sum
  | 0, _, _ => by simp [remDegIn]
  | rem + 1, idx, hLe => by
    have hIdx : idx < H.vertexCount := by omega
    have hDrop : (List.finRange H.vertexCount).drop idx =
        ⟨idx, hIdx⟩ :: (List.finRange H.vertexCount).drop (idx + 1) := by
      have hLt : idx < (List.finRange H.vertexCount).length := by simp [hIdx]
      rw [← List.getElem_cons_drop hLt, List.getElem_finRange]
      rfl
    rw [remDegIn, dite_eq_left hIdx, hDrop, List.take_succ_cons, List.map_cons, List.sum_cons,
      remDegIn_eq_drop_sum H orderKahn sizeKahn rem (idx + 1) (by omega)]

theorem remDegIn_le_arcCount {H : LabelledQuotient}
    (orderKahn : Array (Vertex H)) (sizeKahn : orderKahn.size = H.vertexCount)
    (hNd : orderKahn.toList.Nodup) :
    remDegIn H orderKahn sizeKahn 0 H.vertexCount ≤ H.arcCount := by
  have hEq : remDegIn H orderKahn sizeKahn 0 H.vertexCount =
      (orderKahn.toList.map (fun y : Vertex H => degIn H y.val)).sum := by
    rw [remDegIn_eq_drop_sum H orderKahn sizeKahn H.vertexCount 0 (by simp),
      List.drop_zero, List.take_of_length_le (by simp)]
    congr 1
    exact List.ext_getElem (by simp [sizeKahn]) (fun k hk1 hk2 => by
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk,
        Array.getElem_toList]
      rfl)
  rw [hEq]
  let l1 := orderKahn.toList.map (Fin.val (n := H.vertexCount))
  have hNdMap : ∀ l : List (Vertex H), l.Nodup → (l.map Fin.val).Nodup := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      intro hnd
      simp only [List.nodup_cons, List.map_cons] at hnd ⊢
      refine ⟨fun hm => hnd.1 ?_, ih hnd.2⟩
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
      rw [← Fin.ext heq]
      exact hb
  have hNdVal : l1.Nodup := hNdMap orderKahn.toList hNd
  have hMap1 : (orderKahn.toList.map (fun y : Vertex H => degIn H y.val)).sum =
      (l1.map (degIn H)).sum := by
    dsimp only [l1]; rw [List.map_map]; rfl
  have hSub : ∀ x ∈ l1, x ∈ List.range H.vertexCount := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr y.isLt
  rw [hMap1]
  have hSumLe := nodup_map_sum_le (degIn H) l1 (List.range H.vertexCount) hNdVal hSub
  rw [list_sum_map_range, prefixIn_vertexCount] at hSumLe
  exact hSumLe

def remBucketsLen (buckets : Nat → List Nat) (idx : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => (buckets idx).length + remBucketsLen buckets (idx + 1) rem

private theorem remBucketsLen_eq_flatMap (buckets : Nat → List Nat) :
    ∀ (rem idx : Nat),
      remBucketsLen buckets idx rem =
        (((List.range rem).map (fun j => idx + j)).flatMap buckets).length
  | 0, _ => by simp [remBucketsLen]
  | rem + 1, idx => by
    have hSh : (List.range (rem + 1)).map (fun j => idx + j) =
        idx :: (List.range rem).map (fun j => (idx + 1) + j) := by
      rw [List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      dsimp only [Function.comp_def]
      omega
    rw [remBucketsLen, hSh, List.flatMap_cons, List.length_append,
      remBucketsLen_eq_flatMap buckets rem (idx + 1)]

theorem remBucketsLen_le_next {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (rankKahn : Vertex H → Nat) (buckets : Nat → List Nat)
    (hSpec : ∀ tr < H.vertexCount, (buckets tr).Nodup ∧ ∀ w ∈ buckets tr,
      w < r.out.tables.next ∧
      ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
        max (rankKahn P.fst) (rankKahn P.snd) = tr) :
    remBucketsLen buckets 0 H.vertexCount ≤ r.out.tables.next := by
  rw [remBucketsLen_eq_flatMap]
  have hMapId : (List.range H.vertexCount).map (fun j => 0 + j) = List.range H.vertexCount := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    simp
  rw [hMapId]
  let flat := (List.range H.vertexCount).flatMap buckets
  have hFlatNd : flat.Nodup := by
    dsimp only [flat]
    have hGen : ∀ l : List Nat, l.Nodup → (∀ tr ∈ l, tr < H.vertexCount) →
        (l.flatMap buckets).Nodup := by
      intro l
      induction l with
      | nil => intro _ _; simp
      | cons a t ih =>
        intro hnd hlt
        rw [List.nodup_cons] at hnd
        rw [List.flatMap_cons, List.nodup_append]
        refine ⟨(hSpec a (hlt a List.mem_cons_self)).1,
          ih hnd.2 (fun tr htr => hlt tr (List.mem_cons_of_mem a htr)), ?_⟩
        intro w hwa w' hw' hEq
        subst w'
        obtain ⟨tr, htrT, hwTr⟩ := List.mem_flatMap.mp hw'
        obtain ⟨_, Pa, hBa, hTrA⟩ := (hSpec a (hlt a List.mem_cons_self)).2 w hwa
        obtain ⟨_, P2, hB2, hTr2⟩ := (hSpec tr (hlt tr (List.mem_cons_of_mem a htrT))).2 w hwTr
        have hPEq : Pa = P2 := Option.some.inj (Option.some.inj (hBa.symm.trans hB2))
        have hEqTr : a = tr := by rw [← hTrA, ← hTr2, hPEq]
        exact hnd.1 (hEqTr ▸ htrT)
    exact hGen (List.range H.vertexCount) List.nodup_range (fun _ hm => List.mem_range.mp hm)
  have hSub : ∀ w ∈ flat, w ∈ List.range r.out.tables.next := by
    intro w hw
    obtain ⟨tr, htr, hwTr⟩ := List.mem_flatMap.mp hw
    exact List.mem_range.mpr ((hSpec tr (List.mem_range.mp htr)).2 w hwTr).1
  have hLen1 : flat.length = (flat.map (fun _ => 1)).sum := by
    clear hFlatNd hSub
    induction flat with
    | nil => simp
    | cons _ _ ih => simp [ih, Nat.add_comm]
  have hLen2 : (List.range r.out.tables.next).length =
      ((List.range r.out.tables.next).map (fun _ => 1)).sum := by
    clear hFlatNd hSub hLen1
    induction List.range r.out.tables.next with
    | nil => simp
    | cons _ _ ih => simp [ih, Nat.add_comm]
  rw [hLen1, ← List.length_range (n := r.out.tables.next), hLen2]
  exact nodup_map_sum_le (fun _ => 1) flat (List.range r.out.tables.next) hFlatNd hSub

end ListSumHelpers

end PaperB.RamProgram.ExitSummaryBuild
