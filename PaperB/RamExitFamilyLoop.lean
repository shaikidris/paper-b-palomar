module

public import PaperB.RamExitFamilyLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-!
EX5.1 Exit-Summary Family Loop (`PaperB.RamExitFamilyLoop`):
Fixed 16-register Word-RAM program `exitFamilyLoopProgram` consuming the output of
`prefixAndForestLoopProgram` (`StaticTreeSlice`, `qStartFn`, `countingSortedArcs`,
and `OwnerForestPackedRecordAt`), invoking lifted 15-register `exitSummaryBuildProgram`
on reusable scratch `[exitSubInBase, exitSubWorkBase)` for every large quotient
(`3 ≤ n_d`), copying `[exitDepth (N_d), exitStored (18*N_d), exitPrior (6*n_d)]`
into `exitArenaBase`, writing `[ep0, ep1, ep2]` at `exitPtrsBase + 3*d` (or `[0,0,0]`
for small quotients `n_d < 3`), and halting in `SealedPackEntryRegs` +
`SealedDisjointLayout` + `OwnerExitArenaAt` for `RamSealedPacker`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex)
open PaperB.RamForestProgram.Finish (packedPayload)
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.ExitMap.JumpMapRoute (foldFusedAux)
open PaperB.ForestSlimIndex
open PaperB.Digraph (lemma22ExitTails mem_lemma22ExitTails)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamFamilyForestLoop
open PaperB.RamQuotientEmitter
open PaperB.RamDataSliceAdapter
open PaperB.RamStaticReaderBridge
open PaperB.RetainedProperLoss
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.RamSealedPacker
open PaperB.RamProgram.ExitSummaryBuild
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)
open PaperB.Digraph (dominates_refl dominates_reachable_predecessor_of_ne rank_lt_of_strict_dominator)
open PaperB.Exit.OrderedReaderResult (exitDenseOwnerSlots_read exitDenseOwnerCell exitTransferDrivers)
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase (RouteSlotEdges route_parentPath)

section MathBridges

private theorem idxOf_getElem_nodup_fin {α : Type _} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf (l[i]'hi) = i := by
  have hlt : l.idxOf (l[i]'hi) < l.length :=
    List.idxOf_lt_length_of_mem (List.getElem_mem hi)
  have hEq : l[l.idxOf (l[i]'hi)]'hlt = l[i]'hi := List.getElem_idxOf hlt
  have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
  by_cases hne : l.idxOf (l[i]'hi) = i
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with h1 | h3
    · exact False.elim (hPw _ _ hlt hi h1 hEq)
    · exact False.elim (hPw _ _ hi hlt h3 hEq.symm)

theorem denseRank_emittedArc {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {ea : EmittedArc dense.length} (hea : ea ∈ S.emittedArcs d)
    (hEnt : ea.tailEntry < dense.length) :
    denseRank S (dense[(S.denseOfEntry ⟨ea.tailEntry, hEnt⟩).val]'(S.denseOfEntry ⟨ea.tailEntry, hEnt⟩).isLt) =
      ea.tailEntry := by
  unfold StaticTreeSlice.emittedArcs StaticTreeSlice.allEmittedArcs at hea
  obtain ⟨hmAll, _⟩ := List.mem_filter.mp hea
  obtain ⟨uDense, _, heU⟩ := List.mem_flatMap.mp hmAll
  unfold StaticTreeSlice.emitForU at heU
  obtain ⟨vOrig, _, hvEq⟩ := List.mem_filterMap.mp heU
  by_cases hv : dense.idxOf vOrig < dense.length
  · simp only [dite_eq_left hv, Option.some.injEq] at hvEq
    let vDense : Fin dense.length := ⟨dense.idxOf vOrig, hv⟩
    have heaEq : ea = S.emittedArc uDense vDense := hvEq.symm
    have hEntEq : ea.tailEntry = S.entry uDense := by rw [heaEq]; rfl
    have huD : S.denseOfEntry ⟨ea.tailEntry, hEnt⟩ = uDense := by
      apply Fin.ext
      have hsub : (⟨ea.tailEntry, hEnt⟩ : Fin dense.length) =
          ⟨S.entry uDense, Nat.lt_of_lt_of_le (S.entry_lt_stop uDense).1 (S.entry_lt_stop uDense).2⟩ :=
        Fin.ext hEntEq
      rw [hsub, S.denseOfEntry_entry uDense]
    rw [huD]
    unfold denseRank
    have hvMem : dense[uDense.val]'uDense.isLt ∈ dense := List.getElem_mem uDense.isLt
    rw [dite_eq_left hvMem]
    have hIdx : (⟨dense.idxOf (dense[uDense.val]'uDense.isLt),
        List.idxOf_lt_length_of_mem hvMem⟩ : Fin dense.length) = uDense :=
      Fin.ext (idxOf_getElem_nodup_fin S.nodup uDense.isLt)
    rw [hIdx, ← hEntEq]
  · simp [hv] at hvEq

theorem denseRank_lt_vertexCount {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (v : Fin g.vertexCount) :
    denseRank S v < g.vertexCount := by
  unfold denseRank
  by_cases hv : v ∈ dense
  · rw [dite_eq_left hv]
    let u := S.entry ⟨dense.idxOf v, List.idxOf_lt_length_of_mem hv⟩
    have hu : S.entry ⟨dense.idxOf v, List.idxOf_lt_length_of_mem hv⟩ < dense.length :=
      Nat.lt_of_lt_of_le (S.entry_lt_stop _).1 (S.entry_lt_stop _).2
    have hLen := S.length_le
    omega
  · rw [dite_eq_right hv]
    exact Fin.pos r

theorem supplied_reverse_ramQuotient_eq_full {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    ((PaperB.ForestIncomingRaw.supplied (S.ramQuotient d)).reverse).map
        (fun e => (e.1.val, (PaperB.ForestIncomingRaw.arcHead e.2).val, denseRank S e.2.origTail)) =
      (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).map
        (fun ea => (ea.srcLocal, ea.headLocal, ea.tailEntry)) := by
  have foldCons_supplied : ∀ (H : LabelledQuotient),
      (PaperB.ForestIncomingRaw.supplied H).reverse =
        (List.finRange H.vertexCount).flatMap
          (fun u : Fin H.vertexCount => (H.outArcs u).map (fun a => (u, a))) := by
    intro H
    have hFold : ∀ (us : List (Fin H.vertexCount))
        (acc : List (PaperB.ForestIncomingRaw.Entry H)),
        (us.foldl (fun acc u => (H.outArcs u).foldl (fun es a => (u, a) :: es) acc) acc).reverse =
          acc.reverse ++ us.flatMap (fun u => (H.outArcs u).map (fun a => (u, a))) := by
      intro us
      induction us with
      | nil => intro acc; simp
      | cons u us ih =>
        intro acc
        simp only [List.foldl_cons, ih]
        have hPush : ((H.outArcs u).foldl (fun es a => (u, a) :: es) acc).reverse =
            acc.reverse ++ (H.outArcs u).map (fun a => (u, a)) := by
          have hRev : ∀ (xs : List (QuotientArc H.origVertexCount H.vertexCount))
              (acc' : List (PaperB.ForestIncomingRaw.Entry H)),
              (xs.foldl (fun es a => (u, a) :: es) acc') =
                xs.reverse.map (fun a => (u, a)) ++ acc' := by
            intro xs
            induction xs with
            | nil => intro _; simp
            | cons x xs ihx =>
              intro acc'
              simp only [List.foldl_cons, ihx, List.reverse_cons, List.map_append,
                List.map_singleton, List.append_assoc, List.singleton_append]
          rw [hRev, List.reverse_append, List.map_reverse, List.reverse_reverse]
        rw [hPush, List.append_assoc, List.flatMap_cons]
    exact hFold (List.finRange H.vertexCount) []
  rw [foldCons_supplied (S.ramQuotient d)]
  unfold countingSortedArcs
  rw [List.map_flatMap, List.map_flatMap]
  congr 1
  funext u
  simp only [List.map_map, Function.comp_def]
  have hHeadEq : ∀ a : QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount,
      PaperB.ForestIncomingRaw.arcHead a = a.head := fun a => by cases a; rfl
  simp only [hHeadEq]
  have hOut : (S.ramQuotient d).outArcs u =
      (S.emittedArcs d).filterMap (fun ea =>
        if ea.srcLocal == u.val then
          if hHead : ea.headLocal < 1 + (S.childSlice d).length then
            if hEnt : ea.tailEntry < dense.length then
              let uD := S.denseOfEntry ⟨ea.tailEntry, hEnt⟩
              some (⟨⟨ea.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩ :
                QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount)
            else none
          else none
        else none) := by
    simp [LabelledQuotient.outArcs, StaticTreeSlice.ramQuotient]
  rw [hOut]
  suffices ∀ l : List (EmittedArc dense.length),
      (∀ ea ∈ l, ea ∈ S.emittedArcs d) →
      (l.filterMap (fun ea =>
        if ea.srcLocal == u.val then
          if hHead : ea.headLocal < 1 + (S.childSlice d).length then
            if hEnt : ea.tailEntry < dense.length then
              let uD := S.denseOfEntry ⟨ea.tailEntry, hEnt⟩
              some (⟨⟨ea.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩ :
                QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount)
            else none
          else none
        else none)).map (fun a => (u.val, a.head.val, denseRank S a.origTail)) =
      (l.filter (fun ea => ea.srcLocal == u.val)).map
        (fun ea => (ea.srcLocal, ea.headLocal, ea.tailEntry)) from
    this (S.emittedArcs d) (fun _ h => h)
  intro l hl
  induction l with
  | nil => rfl
  | cons ea xs ih =>
    have hea : ea ∈ S.emittedArcs d := hl ea List.mem_cons_self
    have hBnd := S.emittedArc_bounds d hea
    have hxs' := ih (fun x hx => hl x (List.mem_cons_of_mem ea hx))
    by_cases hsrc : (ea.srcLocal == u.val) = true
    · have hsrcEq : ea.srcLocal = u.val := beq_iff_eq.mp hsrc
      have hRank : denseRank S (dense[(S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩).val]'
          (S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩).isLt) = ea.tailEntry :=
        denseRank_emittedArc S d hea hBnd.2.2.2
      simp only [List.filterMap_cons, List.filter_cons, ite_eq_left hsrc,
        dite_eq_left hBnd.2.2.1, dite_eq_left hBnd.2.2.2, hsrcEq, beq_self_eq_true,
        ite_true, List.map_cons, Fin.val_mk, hRank, hxs']
    · simp only [List.filterMap_cons, List.filter_cons, ite_eq_right hsrc, hxs']

theorem exitBuildInput_of_staged {bits inCap workCap : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : workCap ≤ 2 ^ bits}
    {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {pH : PaperB.ForestDictionary.Rows (S.ramQuotient d)}
    {dataH : Array (Vertex (S.ramQuotient d))}
    {sizeH : dataH.size = (S.ramQuotient d).vertexCount}
    {rankH : Vertex (S.ramQuotient d) → Nat}
    {hlarge : 3 ≤ (S.ramQuotient d).vertexCount}
    (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
    {hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits}
    (subIn : Input (RamForestProgram.layout bits inCap workCap hsi hsw))
    (hCap : 4 + (S.ramQuotient d).vertexCount + 4 * ordResH.out.tables.next +
        3 * (S.ramQuotient d).arcCount ≤ inCap)
    (hVertexLe : (S.ramQuotient d).vertexCount ≤ g.vertexCount)
    (h0 : (subIn.words[0]?).map Fin.val = some (S.ramQuotient d).vertexCount)
    (h1 : (subIn.words[1]?).map Fin.val = some (S.ramQuotient d).arcCount)
    (h2 : (subIn.words[2]?).map Fin.val = some ordResH.out.tables.next)
    (h3 : (subIn.words[3]?).map Fin.val = some g.vertexCount)
    (hLab : ∀ y : Fin (S.ramQuotient d).vertexCount,
      (subIn.words[4 + y.val]?).map Fin.val = ((packWordColumns ordResH hWidth).labels[y.val]?).map Fin.val)
    (hBF : ∀ u : Fin ordResH.out.tables.next,
      (subIn.words[4 + (S.ramQuotient d).vertexCount + u.val]?).map Fin.val =
        ((packWordColumns ordResH hWidth).back.tagAndFirst[u.val]?).map Fin.val)
    (hBS : ∀ u : Fin ordResH.out.tables.next,
      (subIn.words[4 + (S.ramQuotient d).vertexCount + ordResH.out.tables.next + u.val]?).map Fin.val =
        ((packWordColumns ordResH hWidth).back.second[u.val]?).map Fin.val)
    (hEnt : ∀ u : Fin ordResH.out.tables.next,
      (subIn.words[4 + (S.ramQuotient d).vertexCount + 2 * ordResH.out.tables.next + u.val]?).map Fin.val =
        ((packWordColumns ordResH hWidth).entry[u.val]?).map Fin.val)
    (hStp : ∀ u : Fin ordResH.out.tables.next,
      (subIn.words[4 + (S.ramQuotient d).vertexCount + 3 * ordResH.out.tables.next + u.val]?).map Fin.val =
        ((packWordColumns ordResH hWidth).stop[u.val]?).map Fin.val)
    (hArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (subIn.words[4 + (S.ramQuotient d).vertexCount + 4 * ordResH.out.tables.next + p]?).map Fin.val =
        some ea.srcLocal ∧
      (subIn.words[4 + (S.ramQuotient d).vertexCount + 4 * ordResH.out.tables.next +
          (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal ∧
      (subIn.words[4 + (S.ramQuotient d).vertexCount + 4 * ordResH.out.tables.next +
          2 * (S.emittedArcs d).length + p]?).map Fin.val = some ea.tailEntry) :
    ExitBuildInput subIn (S.ramQuotient d) ordResH (denseRank S) g.vertexCount := by
  let H := S.ramQuotient d
  let s := ofOrderedReader ordResH
  have hWord : H.vertexCount < 2 ^ bits := by
    change 1 + 18 * H.vertexCount < 2 ^ bits at hWidth
    omega
  have hArcEq : H.arcCount = (S.emittedArcs d).length := ramQuotient_arcCount_eq S d
  have hNodeEq : nodeCount (orderedConfig pH hlarge) ordResH.out = ordResH.out.tables.next :=
    nodeCount_eq_next ordResH.index.ok
  refine
    { cap_ge := hCap
      hdr_n := h0
      hdr_m := h1
      hdr_NH := h2
      hdr_nGlobal := h3
      hRank_lt := fun x => denseRank_lt_vertexCount S x
      hVertex_le_nGlobal := hVertexLe
      labels_at := fun y => ?_
      back_at := fun u => ?_
      fEntry_at := fun u => ?_
      fStop_at := fun u => ?_
      qSrc_at := fun e => ?_
      qHead_at := fun e => ?_
      qTailRank_at := fun e => ?_ }
  · have hLabEq := hLab y
    have hLtLab : y.val < s.labels.size := by
      have hSz : s.labels.size = H.vertexCount := ordResH.index.ok.1
      rw [hSz]; exact y.isLt
    have hPackLab : ((packWordColumns ordResH hWidth).labels[y.val]?).map Fin.val =
        some (s.labels[y.val]'hLtLab) :=
      (BoundedScalarArray.getElem?_pack_map_val s.labels _ _ y.val).trans
        (getElem?_pos s.labels y.val hLtLab)
    have hSel : s.labels[y.val]'hLtLab = (selectors (orderedConfig pH hlarge) ordResH.out).label y := by
      have hl := labelAt_eq ordResH y
      have hVIdx : (orderedConfig pH hlarge).vertexIndex y = y.val := rfl
      rw [hVIdx] at hl
      change (s.labels[y.val]?).getD 0 = _ at hl
      rw [getElem?_pos s.labels y.val hLtLab, Option.getD_some] at hl
      exact hl.trans (ordResH.index.label_val y)
    rw [hLabEq, hPackLab, hSel]
  · obtain ⟨_, _, hG, _, _⟩ := ordResH.index.ok.2.2
    have hNLe : ordResH.out.tables.next ≤ H.vertexCount + 1 := by
      rw [← hNodeEq]; exact nodeCount_le ordResH.index.ok
    have huBack : u.val < ordResH.out.tables.back.size := by
      have hBSz : s.back.size = H.vertexCount + 1 := hG.back_size
      change u.val < s.back.size
      omega
    have huSBack : u.val < s.back.size := huBack
    cases hb : ordResH.out.tables.back[u.val]'huBack with
    | none =>
      refine ⟨none, getElem?_pos ordResH.out.tables.back u.val huBack ▸ congrArg some hb, ?_, ?_⟩
      · have hRead := packBackWords_read_option s hWord u.val
        have hs1 := (packBackWords_size s hWord).1
        have hs2 := (packBackWords_size s hWord).2
        have hSBack : s.back[u.val]? = some none :=
          (getElem?_pos ordResH.out.tables.back u.val huBack).trans (congrArg some hb)
        rw [hSBack, Option.map_some] at hRead
        unfold BackWords.read at hRead
        rw [getElem?_pos _ _ (hs1.symm ▸ huSBack), getElem?_pos _ _ (hs2.symm ▸ huSBack)] at hRead
        have hEq := Option.some.inj hRead
        rw [hBF u, getElem?_pos _ _ (by change u.val < (packBackWords s _).tagAndFirst.size; rw [hs1]; exact huSBack),
          Option.map_some]
        exact congrArg (fun p => some p.1) hEq
      · have hRead := packBackWords_read_option s hWord u.val
        have hs1 := (packBackWords_size s hWord).1
        have hs2 := (packBackWords_size s hWord).2
        have hSBack : s.back[u.val]? = some none :=
          (getElem?_pos ordResH.out.tables.back u.val huBack).trans (congrArg some hb)
        rw [hSBack, Option.map_some] at hRead
        unfold BackWords.read at hRead
        rw [getElem?_pos _ _ (hs1.symm ▸ huSBack), getElem?_pos _ _ (hs2.symm ▸ huSBack)] at hRead
        have hEq := Option.some.inj hRead
        rw [hBS u, getElem?_pos _ _ (by change u.val < (packBackWords s _).second.size; rw [hs2]; exact huSBack),
          Option.map_some]
        exact congrArg (fun p => some p.2) hEq
    | some P =>
      refine ⟨some P, getElem?_pos ordResH.out.tables.back u.val huBack ▸ congrArg some hb, ?_, ?_⟩
      · have hRead := packBackWords_read_option s hWord u.val
        have hs1 := (packBackWords_size s hWord).1
        have hs2 := (packBackWords_size s hWord).2
        have hSBack : s.back[u.val]? = some (some P) :=
          (getElem?_pos ordResH.out.tables.back u.val huBack).trans (congrArg some hb)
        rw [hSBack, Option.map_some] at hRead
        unfold BackWords.read at hRead
        rw [getElem?_pos _ _ (hs1.symm ▸ huSBack), getElem?_pos _ _ (hs2.symm ▸ huSBack)] at hRead
        have hEq := Option.some.inj hRead
        rw [hBF u, getElem?_pos _ _ (by change u.val < (packBackWords s _).tagAndFirst.size; rw [hs1]; exact huSBack),
          Option.map_some]
        exact congrArg (fun p => some p.1) hEq
      · have hRead := packBackWords_read_option s hWord u.val
        have hs1 := (packBackWords_size s hWord).1
        have hs2 := (packBackWords_size s hWord).2
        have hSBack : s.back[u.val]? = some (some P) :=
          (getElem?_pos ordResH.out.tables.back u.val huBack).trans (congrArg some hb)
        rw [hSBack, Option.map_some] at hRead
        unfold BackWords.read at hRead
        rw [getElem?_pos _ _ (hs1.symm ▸ huSBack), getElem?_pos _ _ (hs2.symm ▸ huSBack)] at hRead
        have hEq := Option.some.inj hRead
        rw [hBS u, getElem?_pos _ _ (by change u.val < (packBackWords s _).second.size; rw [hs2]; exact huSBack),
          Option.map_some]
        exact congrArg (fun p => some p.2) hEq
  · have hEntSz : s.entry.size = ordResH.out.tables.next := by
      rw [← hNodeEq]; exact ordResH.index.reader.layout.endpoints.entry.len
    have huLt : u.val < s.entry.size := hEntSz.symm ▸ u.isLt
    have hPackEnt : ((packWordColumns ordResH hWidth).entry[u.val]?).map Fin.val =
        some (s.entry[u.val]'huLt) :=
      (BoundedScalarArray.getElem?_pack_map_val s.entry _ _ u.val).trans
        (getElem?_pos s.entry u.val huLt)
    have hReadEnt : s.entry[u.val]'huLt =
        ordResH.index.reader.entry (Fin.cast hNodeEq.symm u) := by
      change ordResH.index.reader.layout.endpoints.entry.data[u.val]'huLt =
        ordResH.index.reader.entry (Fin.cast hNodeEq.symm u)
      rfl
    rw [hEnt u, hPackEnt, hReadEnt]
  · have hStpSz : s.stop.size = ordResH.out.tables.next := by
      rw [← hNodeEq]; exact ordResH.index.reader.layout.endpoints.stop.len
    have huLt : u.val < s.stop.size := hStpSz.symm ▸ u.isLt
    have hPackStp : ((packWordColumns ordResH hWidth).stop[u.val]?).map Fin.val =
        some (s.stop[u.val]'huLt) :=
      (BoundedScalarArray.getElem?_pack_map_val s.stop _ _ u.val).trans
        (getElem?_pos s.stop u.val huLt)
    have hReadStp : s.stop[u.val]'huLt =
        ordResH.index.reader.stop (Fin.cast hNodeEq.symm u) := by
      change ordResH.index.reader.layout.endpoints.stop.data[u.val]'huLt =
        ordResH.index.reader.stop (Fin.cast hNodeEq.symm u)
      rfl
    rw [hStp u, hPackStp, hReadStp]
  · have hp : e.val < (S.emittedArcs d).length := hArcEq ▸ e.isLt
    have hMapEq := supplied_reverse_ramQuotient_eq_full S d
    have hLenSup : e.val < (PaperB.ForestIncomingRaw.supplied H).reverse.length := by
      rw [List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
        PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
      exact e.isLt
    have hLenSort : e.val < (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).length := by
      rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp
    have hElem := congrArg (fun xs => xs[e.val]?) hMapEq
    rw [List.getElem?_map, List.getElem?_map, getElem?_pos _ e.val hLenSup,
      getElem?_pos _ e.val hLenSort, Option.map_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hElem
    change _ = some (PaperB.RamForestProgram.ArcParents.rawOccurrence H e).1.val
    rw [show (PaperB.RamForestProgram.ArcParents.rawOccurrence H e).1.val = _ from hElem.1]
    exact (hArcs e.val hp).1
  · have hp : e.val < (S.emittedArcs d).length := hArcEq ▸ e.isLt
    have hMapEq := supplied_reverse_ramQuotient_eq_full S d
    have hLenSup : e.val < (PaperB.ForestIncomingRaw.supplied H).reverse.length := by
      rw [List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
        PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
      exact e.isLt
    have hLenSort : e.val < (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).length := by
      rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp
    have hElem := congrArg (fun xs => xs[e.val]?) hMapEq
    rw [List.getElem?_map, List.getElem?_map, getElem?_pos _ e.val hLenSup,
      getElem?_pos _ e.val hLenSort, Option.map_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hElem
    change _ = some (PaperB.RamForestProgram.ArcParents.rawHead H e).val
    rw [show (PaperB.RamForestProgram.ArcParents.rawHead H e).val = _ from congrArg Prod.fst hElem.2]
    exact (congrArg (fun k => (subIn.words[4 + H.vertexCount + 4 * ordResH.out.tables.next + k + e.val]?).map Fin.val) hArcEq).trans
      (hArcs e.val hp).2.1
  · have hp : e.val < (S.emittedArcs d).length := hArcEq ▸ e.isLt
    have hMapEq := supplied_reverse_ramQuotient_eq_full S d
    have hLenSup : e.val < (PaperB.ForestIncomingRaw.supplied H).reverse.length := by
      rw [List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
        PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
      exact e.isLt
    have hLenSort : e.val < (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).length := by
      rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp
    have hElem := congrArg (fun xs => xs[e.val]?) hMapEq
    rw [List.getElem?_map, List.getElem?_map, getElem?_pos _ e.val hLenSup,
      getElem?_pos _ e.val hLenSort, Option.map_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hElem
    change _ = some (denseRank S (PaperB.RamForestProgram.ArcParents.rawOccurrence H e).2.origTail)
    rw [show denseRank S (PaperB.RamForestProgram.ArcParents.rawOccurrence H e).2.origTail = _ from congrArg Prod.snd hElem.2]
    exact (congrArg (fun k => (subIn.words[4 + H.vertexCount + 4 * ordResH.out.tables.next + 2 * k + e.val]?).map Fin.val) hArcEq).trans
      (hArcs e.val hp).2.2

theorem childSlice_length_le {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (S.childSlice d).length ≤ dense.length - 1 := by
  have hLen : (S.childSlice d).length = S.childStart (d.val + 1) - S.childStart d.val := by
    simp [StaticTreeSlice.childSlice]
  have h1 := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
  rw [S.childStart_end] at h1
  omega

theorem ramQuotient_vertexCount_le {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (S.ramQuotient d).vertexCount ≤ g.vertexCount := by
  have hC := childSlice_length_le S d
  have hD := S.length_le
  have hdPos : 0 < dense.length := Nat.lt_of_le_of_lt (Nat.zero_le _) d.isLt
  change 1 + (S.childSlice d).length ≤ g.vertexCount
  omega

theorem ramQuotient_arcCount_le {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (S.ramQuotient d).arcCount ≤ g.arcCount := by
  rw [ramQuotient_arcCount_eq S d]
  have hSucc : qStartFn S (d.val + 1) = qStartFn S d.val + (S.emittedArcs d).length :=
    qStartFn_succ S d.isLt
  have hLe := qStartFn_le_arcCount S (d.val + 1)
  omega

private theorem avoidPath_snoc {V : Type _} {edge : V → V → Prop} {failed : V → Prop}
    {a b c : V} (p : AvoidPath edge failed a b) (hbc : edge b c) (hc : ¬ failed c) :
    AvoidPath edge failed a c := by
  revert hbc hc
  induction p with
  | refl x hx => intro hbc hc; exact AvoidPath.step x c c hx hbc (AvoidPath.refl c hc)
  | step x w y hx hxw _ ih => intro hbc hc; exact AvoidPath.step x w c hx hxw (ih hbc hc)

private theorem avoidPath_trans {V : Type _} {edge : V → V → Prop} {failed : V → Prop}
    {a b c : V} (p : AvoidPath edge failed a b) (q : AvoidPath edge failed b c) :
    AvoidPath edge failed a c := by
  revert q
  induction p with
  | refl _ _ => intro q; exact q
  | step x w y hx hxw _ ih => intro q; exact AvoidPath.step x w c hx hxw (ih q)

private theorem suffix_from_dom {g : Digraph} {P : Fin g.vertexCount → Prop}
    (d₀ : Fin g.vertexCount) :
    ∀ {a y : Fin g.vertexCount}, y ≠ d₀ → g.SurvivingPath P a y →
      AvoidPath g.HasArc (fun z => P z ∨ z = d₀) a y ∨
      (¬ P d₀ ∧ ∃ w : Fin g.vertexCount, g.HasArc d₀ w ∧
        AvoidPath g.HasArc (fun z => P z ∨ z = d₀) w y) := by
  intro a y hyd p
  revert hyd
  induction p with
  | refl x hx =>
    intro hyd
    exact Or.inl (AvoidPath.refl x (fun h => h.elim hx hyd))
  | step x w z hx hxw _ ih =>
    intro hyd
    rcases ih hyd with hRest | hRight
    · by_cases hxd : x = d₀
      · subst hxd
        exact Or.inr ⟨hx, w, hxw, hRest⟩
      · exact Or.inl (AvoidPath.step x w z (fun h => h.elim hx hxd) hxw hRest)
    · exact Or.inr hRight

private theorem avoid_dom_of_avoid_vertex {g : Digraph} (r u₀ : Fin g.vertexCount) :
    ∀ {a y : Fin g.vertexCount},
      AvoidPath g.HasArc (fun z => z = u₀) r a →
      AvoidPath g.HasArc (fun z => z = u₀) a y →
      AvoidPath g.HasArc (fun z => g.Dominates r u₀ z) a y := by
  intro a y hPref p
  revert hPref
  induction p with
  | refl x _ => intro hPref; exact AvoidPath.refl x (fun hd => hd hPref)
  | step x w y _ hxw rest ih =>
    intro hPref
    have hwAlive : w ≠ u₀ := by
      cases rest with
      | refl _ h => exact h
      | step _ _ _ h _ _ => exact h
    exact AvoidPath.step x w y (fun hd => hd hPref) hxw
      (ih (avoidPath_snoc hPref hxw hwAlive))

private theorem dom_along_suffix {g : Digraph} {r d₀ y : Fin g.vertexCount}
    {P : Fin g.vertexCount → Prop} (hDomY : g.Dominates r d₀ y) :
    ∀ {w : Fin g.vertexCount}, AvoidPath g.HasArc (fun z => P z ∨ z = d₀) w y →
      g.Dominates r d₀ w := by
  intro w p hp
  have hWy : AvoidPath g.HasArc (fun z => z = d₀) w y :=
    AvoidPath.mono p (fun _ hz => Or.inr hz)
  exact hDomY (avoidPath_trans hp hWy)

private theorem childSlice_same_dom {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c₁ c₂ : Fin dense.length)
    (hc₁ : c₁ ∈ S.childSlice d) (hc₂ : c₂ ∈ S.childSlice d)
    {x : Fin dense.length}
    (h1 : g.Dominates r (dense[c₁.val]'c₁.isLt) (dense[x.val]'x.isLt))
    (h2 : g.Dominates r (dense[c₂.val]'c₂.isLt) (dense[x.val]'x.isLt)) :
    c₁ = c₂ := by
  have hi1 := (S.dominates_iff_interval c₁ x).mp h1
  have hi2 := (S.dominates_iff_interval c₂ x).mp h2
  rcases Nat.lt_trichotomy (S.entry c₁) (S.entry c₂) with hLt | hEq | hGt
  · have hDisj := S.child_interval_disjoint acyc d c₁ c₂ hc₁ hc₂ hLt
    omega
  · have hLt1 : S.entry c₁ < dense.length :=
      Nat.lt_of_lt_of_le (S.entry_lt_stop c₁).1 (S.entry_lt_stop c₁).2
    have hLt2 : S.entry c₂ < dense.length :=
      Nat.lt_of_lt_of_le (S.entry_lt_stop c₂).1 (S.entry_lt_stop c₂).2
    have h1' := S.denseOfEntry_entry c₁ hLt1
    have h2' := S.denseOfEntry_entry c₂ hLt2
    rw [← h1', ← h2']
    congr 1
    exact Fin.ext hEq
  · have hDisj := S.child_interval_disjoint acyc d c₂ c₁ hc₂ hc₁ hGt
    omega

private theorem srcLocal_eq_of_child_dom {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c x : Fin dense.length) (hc : c ∈ S.childSlice d)
    (hdx : g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt))
    (hcx : g.Dominates r (dense[c.val]'c.isLt) (dense[x.val]'x.isLt)) :
    S.srcLocalOf d x = (S.childSlice d).idxOf c + 1 := by
  rcases S.srcLocalOf_spec acyc d x hdx with ⟨hxd, _⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
  · subst x
    exfalso
    obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
    have hcPos' : 0 < c.val := Nat.pos_of_ne_zero hcPos
    have himm := S.domParent_spec c hcPos'
    rw [hcP] at himm
    have hcNeD : c ≠ d := by rw [← hcP]; exact (S.domParent_ne_self c hcPos').symm
    have hcdNe : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := fun e => hcNeD (S.dense_injective e)
    obtain ⟨rank, progress⟩ := acyc
    have hlt1 := rank_lt_of_strict_dominator progress (S.reach_mem c.val c.isLt) himm.2.1 hcdNe.symm
    have hlt2 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hcx hcdNe
    omega
  · have hEqC : c = c' := childSlice_same_dom S acyc d c c' hc hc'Mem hcx hc'Dom
    rw [hc'Idx, hEqC]

private theorem selfSlot_eq_of_child {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d) :
    S.selfSlotFn c = (S.childSlice d).idxOf c + 1 := by
  obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
  unfold StaticTreeSlice.selfSlotFn
  rw [dite_eq_right hcPos]
  dsimp only
  rw [hcP]

private theorem ramQuotient_arc_of_step {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d wDense midDense : Fin dense.length)
    (hArc : g.HasArc (dense[wDense.val]'wDense.isLt) (dense[midDense.val]'midDense.isLt))
    (hDomW : g.Dominates r (dense[d.val]'d.isLt) (dense[wDense.val]'wDense.isLt))
    (hDomMid : g.Dominates r (dense[d.val]'d.isLt) (dense[midDense.val]'midDense.isLt))
    (hMidNeD : midDense ≠ d)
    (hLocNe : S.srcLocalOf d wDense ≠ S.srcLocalOf d midDense) :
    (S.ramQuotient d).HasQuotientArc
      ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
      ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩ := by
  rcases S.srcLocalOf_spec acyc d midDense hDomMid with ⟨hm, _⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
  · exact False.elim (hMidNeD hm)
  · have hMidEqC' : midDense = c' := Classical.byContradiction fun hNe => by
      have hMidNeOrig : dense[midDense.val]'midDense.isLt ≠ dense[c'.val]'c'.isLt :=
        fun e => hNe (S.dense_injective e)
      have hDomW_c' : g.Dominates r (dense[c'.val]'c'.isLt) (dense[wDense.val]'wDense.isLt) :=
        dominates_reachable_predecessor_of_ne hArc (S.reach_mem wDense.val wDense.isLt) hMidNeOrig hc'Dom
      have hSrcW := srcLocal_eq_of_child_dom S acyc d c' wDense hc'Mem hDomW hDomW_c'
      exact hLocNe (hSrcW.trans hc'Idx.symm)
    subst hMidEqC'
    obtain ⟨_, hc'P⟩ := (S.mem_childSlice_iff d midDense).mp hc'Mem
    have hSelf : S.selfSlotFn midDense = S.srcLocalOf d midDense :=
      (selfSlot_eq_of_child S d midDense hc'Mem).trans hc'Idx.symm
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    let locMid : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩
    refine ⟨⟨locMid, dense[wDense.val]'wDense.isLt⟩, ?_, rfl⟩
    rw [S.mem_outArcs_ramQuotient_iff d locW ⟨locMid, dense[wDense.val]'wDense.isLt⟩]
    exact ⟨wDense, midDense, hArc, hc'P, rfl, hSelf, rfl⟩

private theorem ramQuotient_surviving_of_suffix_aux {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d)
    (failedG : Fin g.vertexCount → Prop)
    (failedQ : Fin (S.ramQuotient d).vertexCount → Prop)
    (hNoFail : ∀ x : Fin dense.length,
      g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt) →
      ¬ failedG (dense[x.val]'x.isLt) →
      ¬ failedQ ⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩)
    (hDomC : g.Dominates r (dense[d.val]'d.isLt) (dense[c.val]'c.isLt))
    {w y : Fin g.vertexCount}
    (p : AvoidPath g.HasArc (fun z => failedG z ∨ z = dense[d.val]'d.isLt) w y) :
    y = dense[c.val]'c.isLt →
    ∀ (wDense : Fin dense.length), dense[wDense.val]'wDense.isLt = w →
      g.Dominates r (dense[d.val]'d.isLt) w →
      (S.ramQuotient d).SurvivingPath failedQ
        ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
        ⟨(S.childSlice d).idxOf c + 1, by
          have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩ := by
  let vLocal : Fin (S.ramQuotient d).vertexCount :=
    ⟨(S.childSlice d).idxOf c + 1, by
      have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩
  have hSrcC : S.srcLocalOf d c = vLocal.val := srcLocal_eq_of_child_dom S acyc d c c hc hDomC dominates_refl
  induction p with
  | refl x hx =>
    intro hy wDense hwEq hDomW
    have hwc : wDense = c := S.dense_injective (hwEq.trans hy)
    subst hwc
    have hxAlive : ¬ failedG (dense[wDense.val]'wDense.isLt) := fun h => hx (hwEq ▸ Or.inl h)
    have hQAlive : ¬ failedQ ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩ :=
      hNoFail wDense hDomC hxAlive
    have hLocEq : (⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩ :
        Fin (S.ramQuotient d).vertexCount) = vLocal := Fin.ext hSrcC
    rw [hLocEq] at hQAlive ⊢
    exact AvoidPath.refl vLocal hQAlive
  | step x mid z hx hxw rest ih =>
    intro hz wDense hwEq hDomW
    have hxAlive : ¬ failedG (dense[wDense.val]'wDense.isLt) := fun h => hx (hwEq ▸ Or.inl h)
    have hMidReach : g.InitiallyReachable r mid :=
      Digraph.initiallyReachable_extend (hwEq ▸ S.reach_mem wDense.val wDense.isLt) (hwEq ▸ hxw)
    obtain ⟨mi, hmiLt, hmiEq⟩ := List.mem_iff_getElem.mp (S.mem_reach mid hMidReach)
    let midDense : Fin dense.length := ⟨mi, hmiLt⟩
    have hDomMid : g.Dominates r (dense[d.val]'d.isLt) mid := dom_along_suffix hDomC (hz ▸ rest)
    have hRestQ := ih hz midDense hmiEq hDomMid
    have hMidNeD : midDense ≠ d := by
      intro hEq
      have hDead : failedG mid ∨ mid = dense[d.val]'d.isLt :=
        Or.inr (hmiEq.symm.trans (congrArg (fun z : Fin dense.length => dense[z.val]'z.isLt) hEq))
      cases rest with
      | refl _ hal => exact hal hDead
      | step _ _ _ hal _ _ => exact hal hDead
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    let locMid : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩
    by_cases hLocEq : locW = locMid
    · change (S.ramQuotient d).SurvivingPath failedQ locMid vLocal at hRestQ
      rw [← hLocEq] at hRestQ
      exact hRestQ
    · have hLocNe : S.srcLocalOf d wDense ≠ S.srcLocalOf d midDense := fun e => hLocEq (Fin.ext e)
      have harcQ := ramQuotient_arc_of_step S acyc d wDense midDense
        (by dsimp only [midDense]; rw [hwEq, hmiEq]; exact hxw)
        (hwEq ▸ hDomW) (hmiEq ▸ hDomMid) hMidNeD hLocNe
      have hQAlive : ¬ failedQ locW := hNoFail wDense (hwEq ▸ hDomW) hxAlive
      exact AvoidPath.step locW locMid vLocal hQAlive harcQ hRestQ

private theorem ramQuotient_surviving_of_g_path {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d)
    (failedG : Fin g.vertexCount → Prop)
    (failedQ : Fin (S.ramQuotient d).vertexCount → Prop)
    (hNoFail : ∀ x : Fin dense.length,
      g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt) →
      ¬ failedG (dense[x.val]'x.isLt) →
      ¬ failedQ ⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩)
    (pG : g.SurvivingPath failedG r (dense[c.val]'c.isLt)) :
    (S.ramQuotient d).SurvivingPath failedQ (S.ramQuotient d).root
      ⟨(S.childSlice d).idxOf c + 1, by
        have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩ := by
  obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
  have hcPos' : 0 < c.val := Nat.pos_of_ne_zero hcPos
  have himm := S.domParent_spec c hcPos'
  rw [hcP] at himm
  have hcNeD : c ≠ d := by rw [← hcP]; exact (S.domParent_ne_self c hcPos').symm
  have hcdNe : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := fun e => hcNeD (S.dense_injective e)
  rcases suffix_from_dom (dense[d.val]'d.isLt) hcdNe pG with hAvoidD | ⟨hNotFailD, w, harcDW, pSuf⟩
  · exfalso
    exact himm.2.1 (AvoidPath.mono hAvoidD (fun _ hz => Or.inr hz))
  · have hwReach : g.InitiallyReachable r w :=
      Digraph.initiallyReachable_extend (S.reach_mem d.val d.isLt) harcDW
    obtain ⟨wi, hwiLt, hwiEq⟩ := List.mem_iff_getElem.mp (S.mem_reach w hwReach)
    let wDense : Fin dense.length := ⟨wi, hwiLt⟩
    have hDomW : g.Dominates r (dense[d.val]'d.isLt) w := dom_along_suffix himm.2.1 pSuf
    have hSufQ := ramQuotient_surviving_of_suffix_aux S acyc d c hc failedG failedQ hNoFail
      himm.2.1 pSuf rfl wDense hwiEq hDomW
    have hWNeD : wDense ≠ d := by
      intro hEq
      have hDead : failedG w ∨ w = dense[d.val]'d.isLt :=
        Or.inr (hwiEq.symm.trans (congrArg (fun z : Fin dense.length => dense[z.val]'z.isLt) hEq))
      cases pSuf with
      | refl _ hal => exact hal hDead
      | step _ _ _ hal _ _ => exact hal hDead
    let locD : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d d, S.srcLocalOf_lt d d⟩
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    have hLocDEq : locD = (S.ramQuotient d).root := by
      apply Fin.ext
      change S.srcLocalOf d d = 0
      unfold StaticTreeSlice.srcLocalOf
      simp
    rw [← hLocDEq]
    by_cases hLocEq : locD = locW
    · rw [hLocEq]; exact hSufQ
    · have hLocNe : S.srcLocalOf d d ≠ S.srcLocalOf d wDense := fun e => hLocEq (Fin.ext e)
      have harcQ := ramQuotient_arc_of_step S acyc d d wDense
        (by dsimp only [wDense]; rw [hwiEq]; exact harcDW) dominates_refl (hwiEq ▸ hDomW) hWNeD hLocNe
      have hQAlive : ¬ failedQ locD := hNoFail d dominates_refl hNotFailD
      exact AvoidPath.step locD locW _ hQAlive harcQ hSufQ

theorem ramQuotient_isFlat_of_slice
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d : Fin dense.length) :
    (S.ramQuotient d).IsFlat := by
  have hChildOfNonroot : ∀ x : Fin (S.ramQuotient d).vertexCount,
      x ≠ (S.ramQuotient d).root →
      ∃ hx : x.val - 1 < (S.childSlice d).length,
        let c := (S.childSlice d)[x.val - 1]'hx
        x = ⟨(S.childSlice d).idxOf c + 1, by
          have hIdxLt : (S.childSlice d).idxOf c < (S.childSlice d).length :=
            List.idxOf_lt_length_of_mem (List.getElem_mem hx)
          change _ < 1 + (S.childSlice d).length
          omega⟩ := by
    intro x hxNe
    have hxPos : 0 < x.val := Nat.pos_of_ne_zero (fun e => hxNe (Fin.ext e))
    have hxLt : x.val - 1 < (S.childSlice d).length := by
      have := x.isLt
      change x.val < 1 + (S.childSlice d).length at this
      omega
    refine ⟨hxLt, ?_⟩
    dsimp only
    have hIdxEq := idxOf_getElem_nodup_fin (S.childSlice_nodup d) hxLt
    apply Fin.ext
    dsimp only
    omega
  constructor
  · intro v
    by_cases hv : v = (S.ramQuotient d).root
    · rw [hv]; exact AvoidPath.refl _ not_false
    · obtain ⟨hvLt, hvEq⟩ := hChildOfNonroot v hv
      rw [hvEq]
      exact ramQuotient_surviving_of_g_path S acyc d ((S.childSlice d)[v.val - 1]'hvLt)
        (List.getElem_mem hvLt) (fun _ => False) (fun _ => False)
        (fun _ _ _ => not_false) (S.reach_mem _ _)
  · intro u v hu hvu
    by_cases hv : v = (S.ramQuotient d).root
    · rw [hv]; exact AvoidPath.refl _ hu.symm
    · obtain ⟨huLt, huEq⟩ := hChildOfNonroot u hu
      obtain ⟨hvLt, hvEq⟩ := hChildOfNonroot v hv
      let uChild := (S.childSlice d)[u.val - 1]'huLt
      let vChild := (S.childSlice d)[v.val - 1]'hvLt
      have huMem : uChild ∈ S.childSlice d := List.getElem_mem huLt
      have hvMem : vChild ∈ S.childSlice d := List.getElem_mem hvLt
      have huvChild : uChild ≠ vChild := by
        intro hEq
        apply hvu
        rw [hvEq, huEq]
        congr 1
        simp only [uChild, vChild] at hEq
        rw [hEq]
      have hNotDomUV : ¬ g.Dominates r (dense[uChild.val]'uChild.isLt) (dense[vChild.val]'vChild.isLt) := by
        intro hDom
        obtain ⟨hvPos, hvP⟩ := (S.mem_childSlice_iff d vChild).mp hvMem
        obtain ⟨huPos, huP⟩ := (S.mem_childSlice_iff d uChild).mp huMem
        have himmV := S.domParent_spec vChild (Nat.pos_of_ne_zero hvPos)
        rw [hvP] at himmV
        have himmU := S.domParent_spec uChild (Nat.pos_of_ne_zero huPos)
        rw [huP] at himmU
        have huvOrig : dense[uChild.val]'uChild.isLt ≠ dense[vChild.val]'vChild.isLt :=
          fun e => huvChild (S.dense_injective e)
        have hDomUD := himmV.2.2 (dense[uChild.val]'uChild.isLt) huvOrig hDom
        have huNeD : uChild ≠ d := by
          rw [← huP]; exact (S.domParent_ne_self uChild (Nat.pos_of_ne_zero huPos)).symm
        have huOrigD : dense[uChild.val]'uChild.isLt ≠ dense[d.val]'d.isLt :=
          fun e => huNeD (S.dense_injective e)
        obtain ⟨rank, progress⟩ := acyc
        have hlt1 := rank_lt_of_strict_dominator progress (S.reach_mem uChild.val uChild.isLt) himmU.2.1 huOrigD.symm
        have hlt2 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hDomUD huOrigD
        omega
      have hpAvoidU : AvoidPath g.HasArc (fun z => z = dense[uChild.val]'uChild.isLt) r
          (dense[vChild.val]'vChild.isLt) :=
        Classical.byContradiction fun hDom => hNotDomUV hDom
      have hRNeU : r ≠ dense[uChild.val]'uChild.isLt := by
        obtain ⟨huPos, _⟩ := (S.mem_childSlice_iff d uChild).mp huMem
        intro e
        have : (⟨0, S.qPos⟩ : Fin dense.length) = uChild := S.dense_injective (S.head_eq.trans e)
        have : 0 = uChild.val := congrArg Fin.val this
        omega
      have hpG := avoid_dom_of_avoid_vertex r (dense[uChild.val]'uChild.isLt)
        (AvoidPath.refl r hRNeU) hpAvoidU
      rw [hvEq]
      refine ramQuotient_surviving_of_g_path S acyc d vChild hvMem
        (fun z => g.Dominates r (dense[uChild.val]'uChild.isLt) z) (fun z => z = u)
        ?_ hpG
      intro x hdx hxNotDom hEqU
      apply hxNotDom
      have hLocVal : S.srcLocalOf d x = (S.childSlice d).idxOf uChild + 1 := by
        have h1 : (⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩ : Fin (S.ramQuotient d).vertexCount).val = u.val :=
          congrArg Fin.val hEqU
        have h2 : u.val = (S.childSlice d).idxOf uChild + 1 := by
          have := congrArg Fin.val huEq
          simpa only using this
        exact h1.trans h2
      rcases S.srcLocalOf_spec acyc d x hdx with ⟨_, h0⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
      · omega
      · have hc'Eq : c' = uChild := by
          rw [hc'Idx] at hLocVal
          have hIdxEq : (S.childSlice d).idxOf c' = (S.childSlice d).idxOf uChild := by omega
          have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hc'Mem)
          have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem huMem)
          have hGet : (S.childSlice d)[(S.childSlice d).idxOf c']'(List.idxOf_lt_length_of_mem hc'Mem) =
              (S.childSlice d)[(S.childSlice d).idxOf uChild]'(List.idxOf_lt_length_of_mem huMem) := by
            congr 1
          exact h1.symm.trans (hGet.trans h2)
        rwa [← hc'Eq]

private theorem packWordColumns_sizes {bits : Nat} {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pH : PaperB.ForestDictionary.Rows H} {dataH : Array (Vertex H)}
    {sizeH : dataH.size = H.vertexCount} {rankH : Vertex H → Nat}
    {hlarge : 3 ≤ H.vertexCount}
    (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits) :
    (packWordColumns ordResH hWidth).dictionary.size =
      1 + 3 * ((((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0) ∧
    (packWordColumns ordResH hWidth).back.tagAndFirst.size = H.vertexCount + 1 ∧
    (packWordColumns ordResH hWidth).back.second.size = H.vertexCount + 1 ∧
    (packWordColumns ordResH hWidth).labels.size = H.vertexCount ∧
    (packWordColumns ordResH hWidth).entry.size = ordResH.out.tables.next ∧
    (packWordColumns ordResH hWidth).stop.size = ordResH.out.tables.next ∧
    ordResH.out.tables.next ≤ H.vertexCount + 1 ∧
    (packWordColumns ordResH hWidth).wordCount ≤ 19 * H.vertexCount := by
  let w := packWordColumns ordResH hWidth
  let D := ((w.dictionary[0]?).map Fin.val).getD 0
  let s := ofOrderedReader ordResH
  have fitS : H.vertexCount < 2 ^ bits := by omega
  obtain ⟨_, _, G, _, _⟩ := ordResH.index.ok.2.2
  have hRowCnt : FlatPairDictionary.rowCount w.dictionary = s.dict.size :=
    FlatPairDictionary.rowCount_serialize s (dictionary_fits ordResH hWidth)
  have hDEq : D = s.dict.size := hRowCnt
  have hRet : w.dictionary.size = 1 + s.dict.size + s.dict.size + s.slots.size :=
    FlatPairDictionary.retained_words s (dictionary_fits ordResH hWidth)
  have hSlotSz : s.slots.size = s.dict.size := G.slot_size
  have hDictSz : w.dictionary.size = 1 + 3 * D := by omega
  have hBackSz := packBackWords_size s fitS
  have hSBackSz : s.back.size = H.vertexCount + 1 := G.back_size
  have hLabSz : w.labels.size = H.vertexCount := by
    dsimp only [w, packWordColumns]
    rw [BoundedScalarArray.size_pack]
    exact ordResH.index.ok.1
  have hNodeEq : nodeCount (orderedConfig pH hlarge) ordResH.out = ordResH.out.tables.next :=
    nodeCount_eq_next ordResH.index.ok
  have hEntSz : w.entry.size = ordResH.out.tables.next := by
    dsimp only [w, packWordColumns]
    rw [BoundedScalarArray.size_pack, ← hNodeEq]
    exact ordResH.index.reader.layout.endpoints.entry.len
  have hStpSz : w.stop.size = ordResH.out.tables.next := by
    dsimp only [w, packWordColumns]
    rw [BoundedScalarArray.size_pack, ← hNodeEq]
    exact ordResH.index.reader.layout.endpoints.stop.len
  have hNextLe : ordResH.out.tables.next ≤ H.vertexCount + 1 := by
    rw [← hNodeEq]; exact nodeCount_le ordResH.index.ok
  have hWcLe1 : w.wordCount ≤ 1 + 18 * H.vertexCount := packWordColumns_count_le ordResH hWidth
  have hWcLe : w.wordCount ≤ 19 * H.vertexCount := by omega
  have hBF : w.back.tagAndFirst.size = H.vertexCount + 1 := hBackSz.1.trans hSBackSz
  have hBS : w.back.second.size = H.vertexCount + 1 := hBackSz.2.trans hSBackSz
  exact ⟨hDictSz, hBF, hBS, hLabSz, hEntSz, hStpSz, hNextLe, hWcLe⟩

private theorem sub_self {bits : Nat} (xs : Array (Word bits)) :
    ∀ (k : Nat) (hk : k < xs.size), xs[0 + k]? = some (xs[k]'hk) := by
  intro k hk
  rw [Nat.zero_add]
  exact getElem?_pos xs k hk

private theorem sub_left {bits : Nat} {A B xs : Array (Word bits)} {off : Nat}
    (hOff : off + xs.size ≤ A.size)
    (hSub : ∀ (k : Nat) (hk : k < xs.size), A[off + k]? = some (xs[k]'hk)) :
    ∀ (k : Nat) (hk : k < xs.size), (A ++ B)[off + k]? = some (xs[k]'hk) := by
  intro k hk
  rw [Array.getElem?_append_left (by omega)]
  exact hSub k hk

private theorem sub_right {bits : Nat} {A B xs : Array (Word bits)} {off : Nat}
    (hOff : A.size ≤ off)
    (hSub : ∀ (k : Nat) (hk : k < xs.size), B[(off - A.size) + k]? = some (xs[k]'hk)) :
    ∀ (k : Nat) (hk : k < xs.size), (A ++ B)[off + k]? = some (xs[k]'hk) := by
  intro k hk
  rw [Array.getElem?_append_right (by omega), show off + k - A.size = (off - A.size) + k by omega]
  exact hSub k hk

private theorem slice_of_payload {bits : Nat} {data P xs : Array (Word bits)} {fp0 off : Nat}
    (hFit : fp0 + P.size ≤ data.size)
    (hPay : ∀ k < P.size, data[fp0 + k]? = P[k]?)
    (hOff : off + xs.size ≤ P.size)
    (hSub : ∀ (k : Nat) (hk : k < xs.size), P[off + k]? = some (xs[k]'hk)) :
    SliceAt data (fp0 + off) xs := by
  refine ⟨by omega, fun k hk => ?_⟩
  rw [show fp0 + off + k = fp0 + (off + k) by omega, hPay (off + k) (by omega)]
  exact hSub k hk

private theorem packedPayload_slices {bits : Nat} (w : WordColumns bits)
    {data : Array (Word bits)} {fp0 : Nat}
    (hFit : fp0 + w.wordCount ≤ data.size)
    (hPay : ∀ k < w.wordCount, data[fp0 + k]? = (RamForestProgram.Finish.packedPayload w)[k]?) :
    SliceAt data fp0 w.dictionary ∧
    SliceAt data (fp0 + w.dictionary.size) w.back.tagAndFirst ∧
    SliceAt data (fp0 + w.dictionary.size + w.back.tagAndFirst.size) w.back.second ∧
    SliceAt data (fp0 + w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size) w.labels ∧
    SliceAt data (fp0 + w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size +
      w.labels.size) w.entry ∧
    SliceAt data (fp0 + w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size +
      w.labels.size + w.entry.size) w.stop := by
  have hPsz : (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++
      w.stop).size = w.wordCount := by
    simp only [Array.size_append, WordColumns.wordCount]
  have hFit' : fp0 + (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++
      w.stop).size ≤ data.size := by rw [hPsz]; exact hFit
  have hPay' : ∀ k < (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++
      w.stop).size, data[fp0 + k]? = (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++
        w.labels ++ w.entry ++ w.stop)[k]? :=
    fun k hk => hPay k (by rw [← hPsz]; exact hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := slice_of_payload (xs := w.dictionary) (off := 0) hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_left (by simp only [Array.size_append]; omega)
        (sub_left (by simp only [Array.size_append]; omega)
          (sub_left (by simp only [Array.size_append]; omega)
            (sub_left (by simp only [Array.size_append]; omega)
              (sub_left (by omega) (sub_self w.dictionary))))))
    simpa only [Nat.add_zero] using h
  · exact slice_of_payload (xs := w.back.tagAndFirst) hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_left (by simp only [Array.size_append]; omega)
        (sub_left (by simp only [Array.size_append]; omega)
          (sub_left (by simp only [Array.size_append]; omega)
            (sub_left (by simp only [Array.size_append]; omega)
              (sub_right (Nat.le_refl _) (by rw [Nat.sub_self]; exact sub_self w.back.tagAndFirst))))))
  · have h := slice_of_payload (xs := w.back.second) (off := w.dictionary.size + w.back.tagAndFirst.size) hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_left (by simp only [Array.size_append]; omega)
        (sub_left (by simp only [Array.size_append]; omega)
          (sub_left (by simp only [Array.size_append]; omega)
            (sub_right (by simp only [Array.size_append]; omega)
              (by simp only [Array.size_append, Nat.sub_self]; exact sub_self w.back.second)))))
    simpa only [Nat.add_assoc] using h
  · have h := slice_of_payload
      (xs := w.labels) (off := w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size) hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_left (by simp only [Array.size_append]; omega)
        (sub_left (by simp only [Array.size_append]; omega)
          (sub_right (by simp only [Array.size_append]; omega)
            (by simp only [Array.size_append, Nat.sub_self]; exact sub_self w.labels))))
    simpa only [Nat.add_assoc] using h
  · have h := slice_of_payload
      (xs := w.entry) (off := w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size)
      hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_left (by simp only [Array.size_append]; omega)
        (sub_right (by simp only [Array.size_append]; omega)
          (by simp only [Array.size_append, Nat.sub_self]; exact sub_self w.entry)))
    simpa only [Nat.add_assoc] using h
  · have h := slice_of_payload
      (xs := w.stop) (off := w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size +
        w.entry.size) hFit' hPay'
      (by simp only [Array.size_append]; omega)
      (sub_right (by simp only [Array.size_append]; omega)
        (by simp only [Array.size_append, Nat.sub_self]; exact sub_self w.stop))
    simpa only [Nat.add_assoc] using h

private theorem wordColumns_labelAt_eq {bits : Nat} {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pH : PaperB.ForestDictionary.Rows H} {dataH : Array (Vertex H)}
    {sizeH : dataH.size = H.vertexCount} {rankH : Vertex H → Nat}
    {hlarge : 3 ≤ H.vertexCount}
    (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits) (y : Fin H.vertexCount) :
    (packWordColumns ordResH hWidth).labelAt y.val =
      (selectors (orderedConfig pH hlarge) ordResH.out).label y := by
  let s := ofOrderedReader ordResH
  have hLtLab : y.val < s.labels.size := by
    have hSz : s.labels.size = H.vertexCount := ordResH.index.ok.1
    rw [hSz]; exact y.isLt
  have hPackLab : ((packWordColumns ordResH hWidth).labels[y.val]?).map Fin.val =
      some (s.labels[y.val]'hLtLab) :=
    (BoundedScalarArray.getElem?_pack_map_val s.labels _ _ y.val).trans
      (getElem?_pos s.labels y.val hLtLab)
  unfold WordColumns.labelAt
  rw [hPackLab, Option.getD_some]
  have hl := labelAt_eq ordResH y
  have hVIdx : (orderedConfig pH hlarge).vertexIndex y = y.val := rfl
  rw [hVIdx] at hl
  change (s.labels[y.val]?).getD 0 = _ at hl
  rw [getElem?_pos s.labels y.val hLtLab, Option.getD_some] at hl
  exact hl.trans (ordResH.index.label_val y)

private theorem checkedHit_some_facts {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pH : PaperB.ForestDictionary.Rows H} {dataH : Array (Vertex H)}
    {sizeH : dataH.size = H.vertexCount} {rankH : Vertex H → Nat}
    {hlarge : 3 ≤ H.vertexCount}
    {ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge}
    {entryRank : Fin H.origVertexCount → Nat}
    {rArcH : ∀ u v : Vertex H, H.HasQuotientArc u v → rankH u < rankH v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H pH dataH sizeH rankH hlarge ordResH entryRank rArcH flat bits endpoints)
    (P : CutPair H) (aNode : Nat) (hHit : checkedHit ordResH P = some aNode) :
    aNode < C.built.bundle.F.size ∧
    aNode < ordResH.out.tables.next ∧
    ∃ aF : Fin C.built.bundle.F.size, aF.val = aNode ∧
      (buildProperLossForest H rankH).nodeKey? (C.built.bundle.E.image aF) = some P ∧
      C.built.bundle.F.depthOf (C.built.slotOf P) = C.built.bundle.F.depthOf aNode := by
  have hBack : ordResH.out.tables.back[aNode]? = some (some P) :=
    (checked_iff_back ordResH P aNode).mp hHit
  have hPhys : physicalPairSlot? (orderedConfig pH hlarge) ordResH.out.tables P = some aNode :=
    (physicalPairSlot?_eq_some_iff C.built.bundle.G P aNode).mpr hBack
  obtain ⟨aF, haF, hNode⟩ := (C.built.bundle.hSlot P aNode).mp hPhys
  have hMod : C.built.model = actualModel C.built.bundle entryRank rArcH flat := C.built.model_eq
  have hKey : ∃ a : Fin (C.built.model.forest.realNodeCount + 1),
      C.built.model.forest.nodeKey? a = some P ∧
      C.built.model.forest.depth a = (buildProperLossForest H rankH).depth (C.built.bundle.E.image aF) := by
    rw [hMod]
    exact ⟨C.built.bundle.E.image aF, hNode, rfl⟩
  obtain ⟨a, ha, hda⟩ := hKey
  have hSlotDep : C.built.bundle.F.depthOf (C.built.slotOf P) = C.built.model.forest.depth a :=
    C.built.slot_depth_eq ha
  have hEmbDep := C.built.bundle.E.depth_eq aF
  have hRecSpec := (readRecordWords_spec C.built.bundle.G.layout aF.isLt).1
  have hSelDep : (selectors (orderedConfig pH hlarge) ordResH.out).depth aF.val =
      C.built.bundle.F.depthOf aF.val :=
    congrArg JumpRecord.depth hRecSpec
  have hDepEq : C.built.bundle.F.depthOf (C.built.slotOf P) = C.built.bundle.F.depthOf aNode := by
    rw [hSlotDep, hda, ← hEmbDep, hSelDep, haF]
  have hNext : aNode < ordResH.out.tables.next := by
    rw [← C.built.bundle.G.size_eq, ← haF]; exact aF.isLt
  exact ⟨haF ▸ aF.isLt, hNext, aF, haF, hNode, hDepEq⟩

private def relocateRegion {bits subSize dataSize : Nat}
    (Rsub : Region bits subSize) (ep0 ep1 : Nat)
    (hData : dataSize ≤ 2 ^ bits)
    (hDep : ∀ x : Fin Rsub.slots, ep0 + x.val < dataSize)
    (hRec : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < dataSize)
    (hBase : ep1 < dataSize) : Region bits dataSize where
  slots := Rsub.slots
  depthAddr := fun x => ⟨ep0 + x.val, Nat.lt_of_lt_of_le (hDep x) hData⟩
  depthMem := fun x => hDep x
  base := ⟨ep1, Nat.lt_of_lt_of_le hBase hData⟩
  recordAddr := fun v => Nat.le_trans (Nat.succ_le_of_lt (hRec v)) hData
  recordMem := fun v => Nat.succ_le_of_lt (hRec v)

private theorem occupied_relocate {bits : Nat}
    {subMem data : Array (Word bits)} {ep0 ep1 : Nat}
    (Rsub : Region bits subMem.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
    {endpoints : Nat} (wFit : Width bits (max Rsub.slots endpoints))
    (hOcc : Occupied subMem Rsub F ref wFit)
    (hSubDep : ∀ x : Fin Rsub.slots, (Rsub.depthAddr x).val = x.val)
    (hSubBase : Rsub.base.val = Rsub.slots)
    (hData : data.size ≤ 2 ^ bits)
    (hDep : ∀ x : Fin Rsub.slots, ep0 + x.val < data.size)
    (hRec : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < data.size)
    (hBase : ep1 < data.size) (hep1 : ep1 = ep0 + Rsub.slots)
    (hCopy : ∀ k < 19 * Rsub.slots, data[ep0 + k]? = subMem[k]?) :
    Occupied data (relocateRegion Rsub ep0 ep1 hData hDep hRec hBase) F ref wFit := by
  have hGet : ∀ k < 19 * Rsub.slots,
      ∀ (h1 : ep0 + k < data.size) (h2 : k < subMem.size),
        data[ep0 + k]'h1 = subMem[k]'h2 := by
    intro k hk h1 h2
    apply Option.some.inj
    rw [← Array.getElem?_eq_getElem h1, ← Array.getElem?_eq_getElem h2]
    exact hCopy k hk
  refine
    { size_eq := hOcc.size_eq
      valid := hOcc.valid
      depth := fun v => by
        have hv : v.val < Rsub.slots := v.isLt
        have hEq := hGet v.val (by omega) (hDep v) (by
          have hm := Rsub.depthMem v
          rwa [hSubDep v] at hm)
        have hOld :
            some (subMem[(Rsub.depthAddr v).val]'(Rsub.depthMem v)) =
              some (subMem[v.val]'(by have hm := Rsub.depthMem v; rwa [hSubDep v] at hm)) := by
          rw [← Array.getElem?_eq_getElem, ← Array.getElem?_eq_getElem, hSubDep v]
        exact (congrArg Fin.val (hEq.trans (Option.some.inj hOld).symm)).trans (hOcc.depth v)
      parent_eq := hOcc.parent_eq
      jump_eq := hOcc.jump_eq
      maps := hOcc.maps
      packed := fun v hr i => by
        have hi := i.isLt
        have hv : v.val < Rsub.slots := v.isLt
        have hk : Rsub.slots + 18 * v.val + i.val < 19 * Rsub.slots := by omega
        have hEq := hGet (Rsub.slots + 18 * v.val + i.val) hk
          (by have := hRec v; omega)
          (by have := Rsub.recordMem v; rw [hSubBase] at this; omega)
        have hSubPack := hOcc.packed v hr i
        change data[ep1 + 18 * v.val + i.val]'_ = _
        have hAddr : ep1 + 18 * v.val + i.val = ep0 + (Rsub.slots + 18 * v.val + i.val) := by omega
        have hSubAddr : Rsub.base.val + 18 * v.val + i.val = Rsub.slots + 18 * v.val + i.val := by omega
        have hOpt :
            data[ep1 + 18 * v.val + i.val]? =
              subMem[Rsub.base.val + 18 * v.val + i.val]? := by
          rw [hAddr, hSubAddr]
          exact hCopy _ hk
        have hWord :
            data[ep1 + 18 * v.val + i.val]'(by have := hRec v; omega) =
              subMem[Rsub.base.val + 18 * v.val + i.val]'(by have := Rsub.recordMem v; omega) :=
          Option.some.inj (by
            rw [← Array.getElem?_eq_getElem, ← Array.getElem?_eq_getElem]
            exact hOpt)
        exact hWord.trans hSubPack }

private theorem placed_relocate {bits endpoints : Nat}
    {subMem data : Array (Word bits)} {ep2 ep2Sub : Nat}
    {prior : Array (Option Values)} {hb : SealedPriorBase.BaseBound endpoints prior}
    (wFit : Width bits endpoints)
    (sealSub : SealedPriorBase.BaseView prior.size subMem.size)
    (hSubStart : sealSub.start = ep2Sub)
    (hPlaced : SealedPriorBase.Placed wFit prior hb subMem sealSub)
    (sealData : SealedPriorBase.BaseView prior.size data.size)
    (hDatStart : sealData.start = ep2)
    (hCopy : ∀ j < 6 * prior.size, data[ep2 + j]? = subMem[ep2Sub + j]?) :
    SealedPriorBase.Placed wFit prior hb data sealData := by
  intro j
  have hj := j.isLt
  have h1 : sealData.start + j.val < data.size := by have := sealData.fits; omega
  have h2 : sealSub.start + j.val < subMem.size := by have := sealSub.fits; omega
  have hEq : data[sealData.start + j.val]'h1 = subMem[sealSub.start + j.val]'h2 := by
    apply Option.some.inj
    rw [← Array.getElem?_eq_getElem h1, ← Array.getElem?_eq_getElem h2, hDatStart, hSubStart]
    exact hCopy j.val hj
  exact hEq.trans (hPlaced j)

private theorem depthAt_relocate {bits : Nat} {subMem data : Array (Word bits)} {ep0 ep1 : Nat}
    (Rsub : Region bits subMem.size)
    (hSubDep : ∀ x : Fin Rsub.slots, (Rsub.depthAddr x).val = x.val)
    (hData : data.size ≤ 2 ^ bits)
    (hDep : ∀ x : Fin Rsub.slots, ep0 + x.val < data.size)
    (hRec : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < data.size)
    (hBase : ep1 < data.size)
    (hCopy : ∀ k < 19 * Rsub.slots, data[ep0 + k]? = subMem[k]?) (a : Nat) :
    depthAt data (relocateRegion Rsub ep0 ep1 hData hDep hRec hBase) a = depthAt subMem Rsub a := by
  by_cases ha : a < Rsub.slots
  · have h1 := hDep ⟨a, ha⟩
    have h2 : (Rsub.depthAddr ⟨a, ha⟩).val < subMem.size := Rsub.depthMem ⟨a, ha⟩
    dsimp only [depthAt, relocateRegion]
    simp only [dite_eq_left ha]
    apply congrArg Fin.val
    apply Option.some.inj
    rw [← Array.getElem?_eq_getElem h1, ← Array.getElem?_eq_getElem h2, hSubDep ⟨a, ha⟩]
    exact hCopy a (by omega)
  · dsimp only [depthAt, relocateRegion]
    simp only [dite_eq_right ha]

private theorem recordAt_relocate {bits : Nat} {subMem data : Array (Word bits)} {ep0 ep1 : Nat}
    (Rsub : Region bits subMem.size) (tags : TagsFit bits)
    (hSubBase : Rsub.base.val = Rsub.slots)
    (hData : data.size ≤ 2 ^ bits)
    (hDep : ∀ x : Fin Rsub.slots, ep0 + x.val < data.size)
    (hRec : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < data.size)
    (hBase : ep1 < data.size) (hep1 : ep1 = ep0 + Rsub.slots)
    (hCopy : ∀ k < 19 * Rsub.slots, data[ep0 + k]? = subMem[k]?) (a : Nat) :
    recordAt data (relocateRegion Rsub ep0 ep1 hData hDep hRec hBase) tags a =
      recordAt subMem Rsub tags a := by
  by_cases ha : a < Rsub.slots
  · dsimp only [recordAt, relocateRegion]
    simp only [dite_eq_left ha]
    unfold PaperB.StoredPacking.readStoredAt PaperB.StoredPacking.readStoredBlockAt
    congr 1
    funext i
    simp only [PaperB.StoredPacking.stored_offset_no_wrap]
    have hi := i.isLt
    have h1 : ep1 + 18 * a + i.val < data.size := by
      have hb : ep1 + 18 * a + 17 < data.size := hRec ⟨a, ha⟩
      omega
    have h2 : Rsub.base.val + 18 * a + i.val < subMem.size := by
      have hb : Rsub.base.val + 18 * a + 18 ≤ subMem.size := Rsub.recordMem ⟨a, ha⟩
      omega
    apply Option.some.inj
    rw [← Array.getElem?_eq_getElem h1, ← Array.getElem?_eq_getElem h2,
      show ep1 + 18 * a + i.val = ep0 + (Rsub.slots + 18 * a + i.val) by omega, hSubBase]
    exact hCopy (Rsub.slots + 18 * a + i.val) (by omega)
  · dsimp only [recordAt, relocateRegion]
    simp only [dite_eq_right ha]

private theorem foldStored_relocate {bits : Nat} {subMem data : Array (Word bits)} {ep0 ep1 : Nat}
    (Rsub : Region bits subMem.size) (tags : TagsFit bits)
    (hSubDep : ∀ x : Fin Rsub.slots, (Rsub.depthAddr x).val = x.val)
    (hSubBase : Rsub.base.val = Rsub.slots)
    (hData : data.size ≤ 2 ^ bits)
    (hDep : ∀ x : Fin Rsub.slots, ep0 + x.val < data.size)
    (hRec : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < data.size)
    (hBase : ep1 < data.size) (hep1 : ep1 = ep0 + Rsub.slots)
    (hCopy : ∀ k < 19 * Rsub.slots, data[ep0 + k]? = subMem[k]?) (u d : Nat) :
    foldStored data (relocateRegion Rsub ep0 ep1 hData hDep hRec hBase) tags u d =
      foldStored subMem Rsub tags u d := by
  have hD := depthAt_relocate Rsub hSubDep hData hDep hRec hBase hCopy
  have hR := recordAt_relocate Rsub tags hSubBase hData hDep hRec hBase hep1 hCopy
  simp only [foldStored, funext hD, funext hR]

private theorem summary_has_extrema_local (xs : List Nat) (hne : xs ≠ []) :
    ∃ lo hi, ExitSummary.summary xs = .span lo hi ∧ lo ∈ xs ∧ hi ∈ xs ∧
      ∀ k ∈ xs, lo ≤ k ∧ k ≤ hi := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    by_cases h : xs = []
    · subst xs
      refine ⟨x, x, by simp [ExitSummary.singleton], by simp, by simp, ?_⟩
      intro k hk
      have he : k = x := by simpa using hk
      subst k
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨a, b, hab, ha, hb, hbounds⟩ := ih h
      refine ⟨min x a, max x b, ?_, ?_, ?_, ?_⟩
      · simp [hab, ExitSummary.singleton, Interval.join]
      · rw [Nat.min_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr ha)
      · rw [Nat.max_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr hb)
      · intro k hk
        rcases List.mem_cons.mp hk with he | hk
        · subst k
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega
        · obtain ⟨hl, hh⟩ := hbounds k hk
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega

private theorem summary_map_eq_of_mem_iff_local {α : Type _}
    (xs ys : List α) (f : α → Nat) (hmem : ∀ x, x ∈ xs ↔ x ∈ ys) :
    ExitSummary.summary (xs.map f) = ExitSummary.summary (ys.map f) := by
  by_cases hx : xs = []
  · have hy : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y _ =>
        have hIn : y ∈ xs := (hmem y).mpr (List.mem_cons.mpr (Or.inl rfl))
        rw [hx] at hIn
        cases hIn
    rw [hx, hy]
  · have hy : ys ≠ [] := by
      intro hNil
      cases xs with
      | nil => exact hx rfl
      | cons x _ =>
        have hIn : x ∈ ys := (hmem x).mp (List.mem_cons.mpr (Or.inl rfl))
        rw [hNil] at hIn
        cases hIn
    have hmx : xs.map f ≠ [] := by cases xs <;> simp at hx ⊢
    have hmy : ys.map f ≠ [] := by cases ys <;> simp at hy ⊢
    obtain ⟨lox, hix, hsx, hlox, hhix, hbx⟩ := summary_has_extrema_local (xs.map f) hmx
    obtain ⟨loy, hiy, hsy, hloy, hhiy, hby⟩ := summary_has_extrema_local (ys.map f) hmy
    obtain ⟨ax, hax, eax⟩ := List.mem_map.mp hlox
    obtain ⟨bx, hbxm, ebx⟩ := List.mem_map.mp hhix
    obtain ⟨ay, hay, eay⟩ := List.mem_map.mp hloy
    obtain ⟨by_, hbym, eby⟩ := List.mem_map.mp hhiy
    have hloxInY : lox ∈ ys.map f := eax ▸ List.mem_map.mpr ⟨ax, (hmem ax).mp hax, rfl⟩
    have hhixInY : hix ∈ ys.map f := ebx ▸ List.mem_map.mpr ⟨bx, (hmem bx).mp hbxm, rfl⟩
    have hloyInX : loy ∈ xs.map f := eay ▸ List.mem_map.mpr ⟨ay, (hmem ay).mpr hay, rfl⟩
    have hhiyInX : hiy ∈ xs.map f := eby ▸ List.mem_map.mpr ⟨by_, (hmem by_).mpr hbym, rfl⟩
    have hl1 := (hby lox hloxInY).1
    have hl2 := (hbx loy hloyInX).1
    have hh1 := (hby hix hhixInY).2
    have hh2 := (hbx hiy hhiyInX).2
    rw [hsx, hsy]
    have hlo : lox = loy := Nat.le_antisymm hl2 hl1
    have hhi : hix = hiy := Nat.le_antisymm hh1 hh2
    rw [hlo, hhi]

private theorem model_ref_x0_x1 {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pH : PaperB.ForestDictionary.Rows H} {dataH : Array (Vertex H)}
    {sizeH : dataH.size = H.vertexCount} {rankH : Vertex H → Nat}
    {hlarge : 3 ≤ H.vertexCount}
    {ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge}
    {entryRank : Fin H.origVertexCount → Nat}
    {rArcH : ∀ u v : Vertex H, H.HasQuotientArc u v → rankH u < rankH v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H pH dataH sizeH rankH hlarge ordResH entryRank rArcH flat bits endpoints)
    (P : CutPair H) (y : Vertex H) :
    (C.built.model.ref P y).x0 = ExitSummary.summary ((lemma22ExitTails H P P.fst y).map entryRank) ∧
    (C.built.model.ref P y).x1 = ExitSummary.summary ((lemma22ExitTails H P P.snd y).map entryRank) := by
  have hMod : C.built.model = actualModel C.built.bundle entryRank rArcH flat := C.built.model_eq
  have hRefEq : ∀ j : Fin 2,
      Two.get (C.built.model.ref P y) j =
        ExitSummary.summary
          ((lemma22ExitTails H P (C.built.model.endpoint P j) y).map C.built.model.rank) := by
    intro j
    have hj : Two.get (C.built.model.ref P y) j =
        ExitSummary.summary
          (List.map C.built.model.rank (C.built.model.tails P (C.built.model.endpoint P j) y)) := by
      rcases j with ⟨_ | _ | j, hj⟩
      · rfl
      · rfl
      · omega
    rw [hj]
    apply summary_map_eq_of_mem_iff_local
    intro x
    have hMemEnd : P.Mem (C.built.model.endpoint P j) := C.built.model.endpoint_mem P j
    exact (C.built.model.tails_iff P (C.built.model.endpoint P j) y x hMemEnd).trans
      mem_lemma22ExitTails.symm
  have hRankEq : C.built.model.rank = entryRank := by rw [hMod]; rfl
  have hEnd0 : C.built.model.endpoint P 0 = P.fst := by rw [hMod]; rfl
  have hEnd1 : C.built.model.endpoint P 1 = P.snd := by rw [hMod]; rfl
  constructor
  · have h0 := hRefEq 0
    rw [Two.get_zero, hRankEq, hEnd0] at h0
    exact h0
  · have h1 := hRefEq 1
    rw [Two.get_one, hRankEq, hEnd1] at h1
    exact h1

private theorem anc_of_root {H : LabelledQuotient} {rank : Vertex H → Nat}
    {x z : Fin ((buildProperLossForest H rank).realNodeCount + 1)}
    (h : IsForestAncestor (buildProperLossForest H rank).parent x z) :
    z = (buildProperLossForest H rank).rootNode →
    x = (buildProperLossForest H rank).rootNode := by
  induction h with
  | refl => intro hz; exact hz
  | step k _ ih =>
    intro hk
    rw [hk, buildProperLossForest_parent_root H rank] at ih
    exact ih rfl

private theorem parentPath_rank_le_local {read : Store} {rank : Nat → Nat}
    {u a : Nat} {m : Map} (hp : ParentPath read rank u a m) :
    rank a ≤ rank u := by
  induction hp with
  | nil _ => exact Nat.le_refl _
  | cons _ down _ ih => exact Nat.le_trans ih (Nat.le_of_lt down)

theorem ownerExitArenaAt_of_built {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {forestPtrsBase forestArenaBase forestUsed exitPtrsBase exitArenaBase exitUsed : Nat}
    {data subMem : Array (Word bits)}
    (hLarge : 3 ≤ 1 + (S.childSlice d).length)
    (flat : (S.ramQuotient d).IsFlat)
    (hVertexLe : (S.ramQuotient d).vertexCount ≤ g.vertexCount)
    (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
    (dataH : Array (Vertex (S.ramQuotient d)))
    (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
    (rankH : Vertex (S.ramQuotient d) → Nat)
    (incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
      rankH (orderedVertexAt dataH sizeH i) < rankH (orderedVertexAt dataH sizeH j))
    (covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
      orderedVertexAt dataH sizeH i = v)
    (rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v →
      rankH u < rankH v)
    (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hLarge)
    (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits)
    {ptrBase : Nat}
    (hfaLo : forestArenaBase ≤ ptrBase)
    (hfaHi : ptrBase + (packWordColumns ordResH hWidth).wordCount ≤ forestArenaBase + forestUsed)
    (hfp0 : (data[forestPtrsBase + 6 * d.val]?).map Fin.val = some ptrBase)
    (hfp1 : (data[forestPtrsBase + 6 * d.val + 1]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0)))
    (hfp2 : (data[forestPtrsBase + 6 * d.val + 2]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0) +
        (1 + (S.childSlice d).length + 1)))
    (hfp3 : (data[forestPtrsBase + 6 * d.val + 3]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0) +
        2 * (1 + (S.childSlice d).length + 1)))
    (hfp4 : (data[forestPtrsBase + 6 * d.val + 4]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0) +
        2 * (1 + (S.childSlice d).length + 1) + (1 + (S.childSlice d).length)))
    (hfp5 : (data[forestPtrsBase + 6 * d.val + 5]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((packWordColumns ordResH hWidth).dictionary[0]?).map Fin.val).getD 0) +
        2 * (1 + (S.childSlice d).length + 1) + (1 + (S.childSlice d).length) +
        (packWordColumns ordResH hWidth).entry.size))
    (hPay : ∀ k < (packWordColumns ordResH hWidth).wordCount,
      data[ptrBase + k]? = (RamForestProgram.Finish.packedPayload (packWordColumns ordResH hWidth))[k]?)
    (hPtrDataFit : ptrBase + (packWordColumns ordResH hWidth).wordCount ≤ data.size)
    {ep0 ep1 ep2 : Nat}
    (hep0 : (data[exitPtrsBase + 3 * d.val]?).map Fin.val = some ep0)
    (hep1 : (data[exitPtrsBase + 3 * d.val + 1]?).map Fin.val = some ep1)
    (hep2 : (data[exitPtrsBase + 3 * d.val + 2]?).map Fin.val = some ep2)
    (hEA_lo : exitArenaBase ≤ ep0)
    (h10 : ep1 = ep0 + ordResH.out.tables.next)
    (h21 : ep2 = ep1 + 18 * ordResH.out.tables.next)
    (hEA_hi : ep2 + 6 * (1 + (S.childSlice d).length) ≤ exitArenaBase + exitUsed)
    (hDataWordFit : data.size ≤ 2 ^ bits)
    (hDataFit : ep2 + 6 * (1 + (S.childSlice d).length) ≤ data.size)
    {endpoints : Nat}
    (C : ActualSealedContract (S.ramQuotient d) pH dataH sizeH rankH hLarge ordResH
      (denseRank S) rArcH flat bits endpoints)
    (hSubFitR : 19 * ordResH.out.tables.next ≤ subMem.size)
    (hSubBits : 19 * ordResH.out.tables.next ≤ 2 ^ bits)
    (hSubMem : ∀ k < 19 * ordResH.out.tables.next + 6 * (1 + (S.childSlice d).length),
      data[ep0 + k]? = subMem[k]?)
    (hOccSub : Occupied subMem (ramBankRegion subMem ordResH.out.tables.next hSubFitR hSubBits)
      C.built.bundle.F C.built.ref C.wFit)
    (hDecSub : DecodedOccupied subMem (ramBankRegion subMem ordResH.out.tables.next hSubFitR hSubBits)
      C.built.bundle.F C.built.ref C.wFit.tags C.built.live)
    (hSealFit : 19 * ordResH.out.tables.next + 6 * C.built.bases.data.size ≤ subMem.size)
    (hPlacedSub : SealedPriorBase.Placed C.wFit C.built.bases.data
      (fun v => ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
        rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩)
      subMem ⟨19 * ordResH.out.tables.next, hSealFit⟩) :
    OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed data := by
  let H := S.ramQuotient d
  let n_d := 1 + (S.childSlice d).length
  let N := ordResH.out.tables.next
  have hN : N = ordResH.out.tables.next := rfl
  have hnd : n_d = 1 + (S.childSlice d).length := rfl
  have hHV : H.vertexCount = 1 + (S.childSlice d).length := rfl
  let Rsub := ramBankRegion subMem N hSubFitR hSubBits
  let wCols := packWordColumns ordResH hWidth
  let DW := ((wCols.dictionary[0]?).map Fin.val).getD 0
  have hSizes := packWordColumns_sizes ordResH hWidth
  rcases hSizes with ⟨hwDict, hwBF, hwBS, hwLab, hwEnt, hwStp, hNextLe, hwCntLe⟩
  change wCols.dictionary.size = 1 + 3 * DW at hwDict
  change wCols.back.tagAndFirst.size = H.vertexCount + 1 at hwBF
  change wCols.back.second.size = H.vertexCount + 1 at hwBS
  change wCols.labels.size = H.vertexCount at hwLab
  change wCols.entry.size = N at hwEnt
  change wCols.stop.size = N at hwStp
  change N ≤ H.vertexCount + 1 at hNextLe
  change wCols.wordCount ≤ 19 * H.vertexCount at hwCntLe
  let fp0 := ptrBase
  let fp1 := fp0 + wCols.dictionary.size
  let fp2 := fp1 + wCols.back.tagAndFirst.size
  let fp3 := fp2 + wCols.back.second.size
  let fp4 := fp3 + wCols.labels.size
  let fp5 := fp4 + wCols.entry.size
  have hSlices := packedPayload_slices wCols hPtrDataFit hPay
  rcases hSlices with ⟨hSl0, hSl1, hSl2, hSl3, hSl4, hSl5⟩
  have hDict0Pos : 0 < wCols.dictionary.size := by omega
  have hDataFp0 : ((data[fp0]?).map Fin.val).getD 0 = DW := by
    have h0 := hSl0.2 0 hDict0Pos
    rw [Nat.add_zero] at h0
    dsimp only [DW, fp0]
    rw [h0, getElem?_pos wCols.dictionary 0 hDict0Pos]
  have e0 : fp0 = ptrBase := rfl
  have e1 : fp1 = fp0 + (1 + 3 * DW) := congrArg (fp0 + ·) hwDict
  have e2 : fp2 = fp1 + (H.vertexCount + 1) := congrArg (fp1 + ·) hwBF
  have e3 : fp3 = fp2 + (H.vertexCount + 1) := congrArg (fp2 + ·) hwBS
  have e4 : fp4 = fp3 + H.vertexCount := congrArg (fp3 + ·) hwLab
  have e5 : fp5 = fp4 + wCols.entry.size := rfl
  have hfp1' : (data[forestPtrsBase + 6 * d.val + 1]?).map Fin.val = some fp1 := by
    rw [show fp1 = ptrBase + (1 + 3 * DW) by omega]; exact hfp1
  have hfp2' : (data[forestPtrsBase + 6 * d.val + 2]?).map Fin.val = some fp2 := by
    rw [show fp2 = ptrBase + (1 + 3 * DW) + (1 + (S.childSlice d).length + 1) by omega]
    exact hfp2
  have hfp3' : (data[forestPtrsBase + 6 * d.val + 3]?).map Fin.val = some fp3 := by
    rw [show fp3 = ptrBase + (1 + 3 * DW) + 2 * (1 + (S.childSlice d).length + 1) by omega]
    exact hfp3
  have hfp4' : (data[forestPtrsBase + 6 * d.val + 4]?).map Fin.val = some fp4 := by
    rw [show fp4 = ptrBase + (1 + 3 * DW) + 2 * (1 + (S.childSlice d).length + 1) +
      (1 + (S.childSlice d).length) by omega]
    exact hfp4
  have hfp5' : (data[forestPtrsBase + 6 * d.val + 5]?).map Fin.val = some fp5 := by
    rw [show fp5 = ptrBase + (1 + 3 * DW) + 2 * (1 + (S.childSlice d).length + 1) +
      (1 + (S.childSlice d).length) + wCols.entry.size by omega]
    exact hfp5
  have hWcSum : fp5 + wCols.stop.size = fp0 + wCols.wordCount := by
    dsimp only [fp5, fp4, fp3, fp2, fp1, fp0]
    unfold WordColumns.wordCount; omega
  have hDepBnd : ∀ x : Fin Rsub.slots, ep0 + x.val < data.size := fun x => by
    have := x.isLt; change x.val < N at this; omega
  have hRecBnd : ∀ v : Fin Rsub.slots, ep1 + 18 * v.val + 17 < data.size := fun v => by
    have := v.isLt; change v.val < N at this; omega
  have hBaseBnd : ep1 < data.size := by omega
  let Rdata := relocateRegion Rsub ep0 ep1 hDataWordFit hDepBnd hRecBnd hBaseBnd
  have hRsubMemCopy : ∀ k < 19 * Rsub.slots, data[ep0 + k]? = subMem[k]? := fun k hk =>
    hSubMem k (by change k < 19 * N at hk; omega)
  have okData : Occupied data Rdata C.built.bundle.F C.built.ref C.wFit :=
    occupied_relocate Rsub C.built.bundle.F C.built.ref C.wFit hOccSub (fun _ => rfl) rfl
      hDataWordFit hDepBnd hRecBnd hBaseBnd h10 hRsubMemCopy
  let prior := C.built.bases.data
  let hbMax : SealedPriorBase.BaseBound (max Rdata.slots endpoints) prior := fun v =>
    ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
      rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩
  have hPriorSz : prior.size = n_d := C.built.bases.size_data
  let Bdata : SealedPriorBase.BaseView prior.size data.size := ⟨ep2, by omega⟩
  have hPlacedData : SealedPriorBase.Placed C.wFit prior hbMax data Bdata := by
    apply placed_relocate (ep2Sub := 19 * N) C.wFit ⟨19 * N, hSealFit⟩ rfl hPlacedSub Bdata rfl
    intro j hj
    rw [show ep2 + j = ep0 + (19 * N + j) by omega]
    exact hSubMem (19 * N + j) (by rw [hPriorSz] at hj; omega)
  dsimp only [OwnerExitArenaAt]
  rw [dite_eq_left hLarge]
  refine ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, Rdata, C.built.bundle.F,
    C.built.ref, C.wFit, okData,
    prior, hbMax, Bdata, hPlacedData, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
    incH, covH, rArcH, hfp0, hfp1', hfp2', hfp3', hfp4', hfp5',
    by rw [hDataFp0]; exact e1,
    e2, e3, e4, e5,
    by rw [hDataFp0]; exact hwDict,
    hwBF, hwBS, hwLab, hwStp.trans hwEnt.symm, by rw [hwEnt]; exact hNextLe, hwCntLe,
    hfaLo, by rw [hWcSum]; exact hfaHi,
    hSl0, hSl1, hSl2, hSl3, hSl4, hSl5,
    packWordColumns_dictionary_represents ordResH hWidth,
    fun a v => packWordColumns_known ordResH hWidth a v,
    fun j P => packBackWords_matches (ofOrderedReader ordResH) (by omega) j P,
    fun _ => rfl,
    fun y => ?_,
    fun P hCan aNode hHit => ?_,
    hep0, hep1, hep2,
    hEA_lo, by rw [hwEnt]; omega,
    by omega, by rw [hwEnt]; omega,
    by omega, hEA_hi,
    by show Rdata.slots = wCols.entry.size; exact hwEnt.symm,
    hPriorSz, rfl, rfl, fun _ => rfl,
    fun P hCan aNode hHit y hProp => ?_⟩
  · have hLabEq : wCols.labelAt y.val = (selectors (orderedConfig pH hLarge) ordResH.out).label y :=
      wordColumns_labelAt_eq ordResH hWidth y
    have hLabLt := C.built.bundle.E.label_lt y True.intro
    rw [hLabEq]
    exact ⟨hLabLt, Nat.lt_of_lt_of_eq hLabLt (C.built.bundle.G.size_eq.trans hwEnt.symm)⟩
  · obtain ⟨h3, hNx, _⟩ := checkedHit_some_facts C P aNode hHit
    have h1 : aNode < wCols.entry.size := by rw [hwEnt]; exact hNx
    have h2 : aNode < wCols.stop.size := by rw [hwStp]; exact hNx
    have h4 : aNode < wCols.back.tagAndFirst.size := by rw [hwBF]; omega
    have h5 : aNode < wCols.back.second.size := by rw [hwBS]; omega
    exact ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨_, haLtN, aF, _, hNodeP, hDepEq⟩ := checkedHit_some_facts C P aNode hHit
    let W := actualModel C.built.bundle (denseRank S) rArcH flat
    have hMod : C.built.model = W := C.built.model_eq
    have hAnc : IsForestAncestor (buildProperLossForest H rankH).parent
        (C.built.bundle.E.image aF) ((buildProperLossForest H rankH).label y) :=
      (buildProperLossForest_properLoss_iff_of_node rArcH C.built.bundle.distinctRanks flat hNodeP y).mp hProp
    have hLabelNE : (buildProperLossForest H rankH).label y ≠
        (buildProperLossForest H rankH).rootNode := by
      intro hRoot
      have hRootAnc := anc_of_root hAnc hRoot
      rw [hRootAnc, buildProperLossForest_nodeKey?_root] at hNodeP
      cases hNodeP
    obtain ⟨Acut, hLabKey⟩ : ∃ Acut : CutPair H,
        (buildProperLossForest H rankH).nodeKey? ((buildProperLossForest H rankH).label y) =
          some Acut := by
      cases hq : (buildProperLossForest H rankH).nodeKey? ((buildProperLossForest H rankH).label y) with
      | some Acut => exact ⟨Acut, rfl⟩
      | none =>
        exact (hLabelNE (buildProperLossForest_nodeKey?_inj H rankH
          (hq.trans (buildProperLossForest_nodeKey?_root H rankH).symm))).elim
    have hOwnEq : W.owner y = W.forest.nodeKey? (W.forest.label y) := by
      rw [← hMod]
      exact C.built.owner_eq y
    have hOwnW : W.owner y = some Acut := hOwnEq.trans hLabKey
    have hOwnC : C.built.model.owner y = some Acut := by rw [hMod]; exact hOwnW
    obtain ⟨u0, hu0Read, hu0Slot⟩ := C.built.slot_key_at y Acut hOwnC
    have hu0Sel : u0.val = (selectors (orderedConfig pH hLarge) ordResH.out).label y := by
      rw [exitDenseOwnerSlots_read ordResH C.built.bundle.E y] at hu0Read
      dsimp only [exitDenseOwnerCell] at hu0Read
      split at hu0Read
      · cases hu0Read
      · exact (congrArg Fin.val (Option.some.inj hu0Read)).symm
    have hUEq : wCols.labelAt y.val = C.built.slotOf Acut := by
      have hLabEq : wCols.labelAt y.val = (selectors (orderedConfig pH hLarge) ordResH.out).label y :=
        wordColumns_labelAt_eq ordResH hWidth y
      rw [hLabEq, ← hu0Sel, hu0Slot]
    have huLiveA : C.built.live (C.built.slotOf Acut) := by
      rw [← hu0Slot]
      exact C.built.all_live u0.val u0.isLt
    have haSub : aNode < Rsub.slots := haLtN
    have hDepthDataSub : depthAt data Rdata aNode = depthAt subMem Rsub aNode :=
      depthAt_relocate Rsub (fun _ => rfl) hDataWordFit hDepBnd hRecBnd hBaseBnd hRsubMemCopy aNode
    have hAtSub : depthAt subMem Rsub aNode = C.built.bundle.F.depthOf aNode := by
      simp only [depthAt, dite_eq_left haSub]
      exact hOccSub.depth ⟨aNode, haSub⟩
    have hDepthEq : depthAt data Rdata aNode = C.built.bundle.F.depthOf (C.built.slotOf P) := by
      rw [hDepthDataSub, hAtSub, hDepEq]
    have hFoldEq : foldStored data Rdata C.wFit.tags (wCols.labelAt y.val) (depthAt data Rdata aNode) =
        foldStored subMem Rsub C.wFit.tags (C.built.slotOf Acut)
          (C.built.bundle.F.depthOf (C.built.slotOf P)) := by
      rw [foldStored_relocate Rsub C.wFit.tags (fun _ => rfl) rfl hDataWordFit hDepBnd hRecBnd hBaseBnd
        h10 hRsubMemCopy, hUEq, hDepthEq]
    refine ⟨?_, fun hPr => ?_⟩
    · have hStp := live_foldStored_steps_le hDecSub C.built.liveOK huLiveA
        (bundle_numInserted_le C.built.bundle) (C.built.bundle.F.depthOf (C.built.slotOf P))
      have hCeil : ceilLog2 (H.vertexCount + 2) ≤ ceilLog2 (g.vertexCount + 2) :=
        ceilLog2_le_iff.mpr (Nat.le_trans (Nat.add_le_add_right hVertexLe 2)
          (ceilLog2_le_iff.mp (Nat.le_refl _)))
      change (foldStored data Rdata C.wFit.tags (wCols.labelAt y.val) (depthAt data Rdata aNode)).steps ≤ _
      rw [hFoldEq]
      exact Nat.le_trans hStp (Nat.mul_le_mul_left 3 hCeil)
    · have facts : BuiltExit.RouteForestFacts W.forest :=
        BuiltExit.RouteForestFacts.of_build rArcH C.built.bundle.distinctRanks flat
      have hLive : BuiltExit.RoutePathEdgeLive W (fun _ => True) (C.built.bundle.E.image aF) y :=
        BuiltExit.RoutePathEdgeLive.of_driverCoverage
          (fun k {_ _} hk hp => actualModel_driverCoverage C.built.bundle (denseRank S) rArcH flat hk hp)
          (fun _ _ _ => True.intro)
      obtain ⟨rt⟩ := BuiltExit.Route.nonempty_of_forestAncestor facts hOwnEq hNodeP hAnc hLive
      let q : BuiltExit.Query W (fun _ => True) (fun _ => True) P y := ⟨True.intro, rt⟩
      let rb : BuiltExit.BaseReader (fun _ : Fin H.vertexCount => True) :=
        fun z _ => some (W.wantBase z)
      let rm : BuiltExit.MapReader (fun _ : Fin (exitTransferDrivers ordResH).size => True) :=
        fun i _ => some (W.wantMap i)
      have hEdgesW : @RouteSlotEdges H (exitTransferDrivers ordResH).size W (fun _ => True)
          (fun i _ => some (W.wantMap i)) C.built.slotOf C.built.bundle.F C.built.ref := by
        simpa only [hMod] using C.built.edges
      let dSlot := C.built.bundle.F.depthOf (C.built.slotOf P)
      have hPath : ParentPath C.built.ref C.built.bundle.F.depthOf
          (C.built.slotOf Acut) (C.built.slotOf P) (q.route.actual rm) :=
        route_parentPath q.route hEdgesW hOwnW
      have hDepthLe : dSlot ≤ C.built.bundle.F.depthOf (C.built.slotOf Acut) :=
        parentPath_rank_le_local hPath
      have hSlotLt : C.built.slotOf Acut < C.built.bundle.F.size := by
        rw [← hu0Slot]; exact u0.isLt
      have hDepthAnc : C.built.bundle.F.depthOf
          (C.built.bundle.F.ancestorAtDepth (C.built.slotOf Acut) dSlot) = dSlot :=
        (C.built.bundle.G.layout.valid.ancestorAtDepth_spec hSlotLt hDepthLe).2.2
      let vPr : Fin prior.size := ⟨y.val, hPr⟩
      have hBase : prior[vPr.val]'vPr.isLt = rb y q.readOK := by
        have hb := C.built.bases_exact y
        dsimp only [vPr, rb, prior]
        change C.built.bases.data[y.val]'_ = some (W.wantBase y)
        rw [← hMod]
        exact hb
      have hRunSub : PriorBase.run subMem Rsub C.wFit.tags prior vPr
            (C.built.slotOf Acut) dSlot = q.run rb rm :=
        live_run_eq_query_of_route q rb rm C.built.slotOf hOwnW hEdgesW hDecSub
          C.built.liveOK huLiveA dSlot hDepthAnc rfl prior vPr hBase
      have hQuery : q.run rb rm = W.ref P y := by
        change Map.eval (rt.actual rm) ((rb y True.intro).getD BuiltExit.zero) = W.ref P y
        exact rt.actual_exact rm (fun _ _ => rfl)
      have hRunData : PriorBase.run data Rdata C.wFit.tags prior vPr
            (wCols.labelAt y.val) (depthAt data Rdata aNode) = C.built.model.ref P y := by
        unfold PriorBase.run
        rw [hFoldEq, hMod]
        exact hRunSub.trans hQuery
      have hRefs := model_ref_x0_x1 C P y
      exact ⟨(congrArg (fun v => v.x0) hRunData).trans hRefs.1,
        (congrArg (fun v => v.x1) hRunData).trans hRefs.2⟩

def exitUsedPrefix {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (k : Nat) : Nat :=
  (List.range k).foldl
    (fun acc j =>
      if h : j < dense.length then
        if 3 ≤ 1 + (S.childSlice ⟨j, h⟩).length then
          acc + 47 * (S.childSlice ⟨j, h⟩).length
        else acc
      else acc)
    0

theorem exitUsedPrefix_zero {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    exitUsedPrefix S 0 = 0 := rfl

theorem exitUsedPrefix_succ {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) {k : Nat} (hk : k < dense.length) :
    exitUsedPrefix S (k + 1) =
      exitUsedPrefix S k +
        (if 3 ≤ 1 + (S.childSlice ⟨k, hk⟩).length then
          47 * (S.childSlice ⟨k, hk⟩).length
        else 0) := by
  unfold exitUsedPrefix
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, dite_eq_left hk]
  split <;> omega

theorem exitUsedPrefix_le_48n {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) {k : Nat} (hk : k ≤ dense.length) :
    exitUsedPrefix S k ≤ 48 * g.vertexCount := by
  have hMono : ∀ a b, a ≤ b → exitUsedPrefix S a ≤ exitUsedPrefix S b := by
    intro a b hab
    have hDiff : ∀ t, exitUsedPrefix S a ≤ exitUsedPrefix S (a + t) := by
      intro t
      induction t with
      | zero => exact Nat.le_refl _
      | succ t ih =>
        refine Nat.le_trans ih ?_
        unfold exitUsedPrefix
        rw [← Nat.add_assoc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        split <;> (try split) <;> omega
    simpa only [Nat.add_sub_cancel' hab] using hDiff (b - a)
  have hFold : ∀ (l : List Nat) (a b : Nat),
      a ≤ 47 * b →
      l.foldl (fun acc j =>
        if h : j < dense.length then
          if 3 ≤ 1 + (S.childSlice ⟨j, h⟩).length then
            acc + 47 * (S.childSlice ⟨j, h⟩).length
          else acc
        else acc) a ≤
      47 * l.foldl (fun acc j =>
        if h : j < dense.length then acc + (S.childSlice ⟨j, h⟩).length else acc) b := by
    intro l
    induction l with
    | nil => intro a b hab; exact hab
    | cons x xs ih =>
      intro a b hab
      simp only [List.foldl_cons]
      apply ih
      by_cases hx : x < dense.length
      · rw [dite_eq_left hx, dite_eq_left hx]
        split
        · rw [Nat.mul_add]; omega
        · rw [Nat.mul_add]; omega
      · rw [dite_eq_right hx, dite_eq_right hx]; exact hab
  have hAll : exitUsedPrefix S dense.length ≤ 47 * (dense.length - 1) := by
    rw [← sum_childSlice_length S]
    exact hFold (List.range dense.length) 0 0 (Nat.le_refl _)
  have hDense := S.length_le
  have := hMono k dense.length hk
  omega

end MathBridges

end PaperB.RamExitFamilyLoop
