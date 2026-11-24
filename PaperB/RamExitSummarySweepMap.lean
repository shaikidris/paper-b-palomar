module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepArc

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-! Root and top-level seeds and the parent-map value installed by the sweep. -/

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

/-! ### 10. Mathematical & Contract Bridges for Stage 4 (`Step 4A` & `Step 4B`) -/

section Stage4MathBridges

open PaperB.Jumps
open PaperB.EX24.FinalDFS
open _root_.EX24.PreStep

theorem actualOld_seed {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {flat : H.IsFlat}
    {increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j)}
    {covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    (B := buildActualSweepBundle H flat increasing covers rankArc r) :
    ∀ k u, (u = 0 ∨ B.F.parentOf u = 0) →
      actualOld B increasing covers entryRank rankArc flat k u = seedRecord := by
  intro k
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    unfold actualOld
    by_cases hk : k < H.vertexCount
    · rw [dite_eq_left hk]
      let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
      cases ho : S.mapSlot.read (S.vertex ⟨k, hk⟩) with
      | none => exact ih u hu
      | some i =>
        dsimp only
        unfold Job.overlay actualPacking
        dsimp only
        have hd : (exitTransferDrivers r)[i.val]'i.isLt ∈ exitTransferDrivers r :=
          Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
        obtain ⟨_, _, _, _, _, _, _, hpNe, _, _, _, _, _⟩ :=
          bundle_drivers_provenance B hd
        have hPhys : B.F.parentOf (actualDriverAddress r i).val ≠ 0 := by
          have hlt : (actualDriverAddress r i).val < B.F.size := by
            rw [B.G.size_eq]; exact (actualDriverAddress r i).isLt
          have hP : actualPhysicalParent r (actualDriverAddress r i).val =
              B.F.parentOf (actualDriverAddress r i).val := by
            unfold actualPhysicalParent
            rw [(readRecordWords_spec B.G.layout hlt).1] <;> rfl
          rw [← hP]
          change actualPhysicalParent r (exitTransferDrivers r)[i.val].address ≠ 0
          exact hpNe
        have hNe : u ≠ (actualDriverAddress r i).val := by
          intro hEq
          rw [hEq] at hu
          rcases hu with hz | hpz
          · rw [hz, (validJumpForest_root_zero B.G.layout.valid).1] at hPhys
            exact hPhys rfl
          · exact hPhys hpz
        change (if u = (actualDriverAddress r i).val then _ else
          actualOld B increasing covers entryRank rankArc flat k u) = seedRecord
        rw [ite_eq_right hNe]
        exact ih u hu
    · rw [dite_eq_right hk]; exact ih u hu

theorem step4B_wantMap {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    {bits endpoints : Nat}
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (wFit : Width bits (max r.out.tables.next endpoints))
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    (rankKahn : Vertex H → Nat)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (idx : Nat)
    {ref : Store} {w : Nat} {Pc : CutPair H} :
    let C := buildActualSealedContract H flat increasing covers rankArc r entryRank hRank wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    (∀ u, liveBefore flat increasing covers rankArc r rankKahn idx u → ref u = C.built.ref u) →
    w < r.out.tables.next →
    0 < B.F.parentOf w →
    r.out.tables.back[w]? = some (some Pc) →
    max (rankKahn Pc.fst) (rankKahn Pc.snd) = idx →
    let pN := B.F.parentOf w
    ∃ (Pp : CutPair H) (i : Fin (exitTransferDrivers r).size),
      r.out.tables.back[pN]? = some (some Pp) ∧
      C.built.slotOf (C.built.model.child i) = w ∧
      C.built.model.child i = Pc ∧
      C.built.model.parent i = Pp ∧
      liveBefore flat increasing covers rankArc r rankKahn idx pN ∧
      let freshFn := fun (z : Vertex H) =>
        if z.val = Pp.fst.val ∨ z.val = Pp.snd.val then zero
        else
          let vz := (selectors (orderedConfig p large) r.out).label z
          Map.eval (foldFused B.F ref vz (B.F.depthOf pN)).composed (C.built.model.wantBase z)
      let c := vjoin (freshFn Pc.fst) (freshFn Pc.snd)
      let mkSlot := fun (s : Vertex H) =>
        if s.val = Pc.fst.val then some (0 : Fin 2)
        else if s.val = Pc.snd.val then some 1
        else none
      let pm : Map := ⟨⟨c.x0, mkSlot Pp.fst⟩, ⟨c.x1, mkSlot Pp.snd⟩⟩
      pm = C.built.model.wantMap i := by
  intro C B hRefLive hwLt hParPos hBackW hTrW pN
  let W := actualModel B entryRank rankArc flat
  have hMod : C.built.model = W := C.built.model_eq
  have hwPos : 0 < w := by
    refine Classical.byContradiction fun hw0 => ?_
    have hz : w = 0 := by omega
    rw [hz, (validJumpForest_root_zero B.G.layout.valid).1] at hParPos
    omega
  have hwF : w < B.F.size := B.G.size_eq.symm ▸ hwLt
  have hpF : pN < B.F.size := B.G.layout.valid.parentOf_lt_size hwF
  have hpLt : pN < r.out.tables.next := B.G.size_eq ▸ hpF
  let wF : Fin B.F.size := ⟨w, hwF⟩
  let pF : Fin B.F.size := ⟨pN, hpF⟩
  have hPcKey : (buildProperLossForest H rank).nodeKey? (B.E.image wF) = some Pc :=
    Option.some.inj ((B.E.back_eq wF).symm.trans hBackW)
  have hPpKey : ∃ Pp, (buildProperLossForest H rank).nodeKey? (B.E.image pF) = some Pp := by
    cases hk : (buildProperLossForest H rank).nodeKey? (B.E.image pF) with
    | some Pp => exact ⟨Pp, rfl⟩
    | none =>
      exfalso
      have h0 : 0 < B.F.size := B.G.size_eq.symm ▸ (B_next_pos flat increasing covers rankArc r).1
      have hR := buildProperLossForest_nodeKey?_inj H rank
        (hk.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      rw [← B.E.root_eq h0] at hR
      have hZero := congrArg Fin.val (B.E.injective hR)
      change pN = 0 at hZero
      exact (Nat.ne_of_gt hParPos) hZero
  obtain ⟨Pp, hPpKey⟩ := hPpKey
  have hBackP : r.out.tables.back[pN]? = some (some Pp) :=
    (B.E.back_eq pF).trans (congrArg some hPpKey)
  have hUpEq : B.up wF = pF := Fin.ext (B.hUp wF)
  have hPpPar : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent (B.E.image wF)) = some Pp := by
    rw [← B.E.parent_eq wF, hUpEq]; exact hPpKey
  obtain ⟨i, hiEdge⟩ := actualModel_driverCoverage B entryRank rankArc flat hPcKey hPpPar
  have hChildI : W.child i = Pc := by
    have h1 := W.childKey i
    rw [hiEdge] at h1
    change (buildProperLossForest H rank).nodeKey? (B.E.image wF) = _ at h1
    rw [hPcKey] at h1
    exact Option.some.inj h1.symm
  have hParentI : W.parent i = Pp := by
    have h1 := W.parentKey i
    rw [hiEdge] at h1
    change (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).parent (B.E.image wF)) = _ at h1
    rw [hPpPar] at h1
    exact Option.some.inj h1.symm
  have hSlotW : C.built.slotOf (C.built.model.child i) = w := by
    rw [hMod, hChildI]
    change (physicalPairSlot? (orderedConfig p large) r.out.tables Pc).getD 0 = w
    rw [(B.hSlot Pc w).mpr ⟨wF, rfl, hPcKey⟩]; rfl
  obtain ⟨Pc', Pp', hBackW', hBackP', hLtTr⟩ :=
    trigger_parent_lt_child flat increasing covers rankArc r rankKahn rankArcKahn hwPos hwLt hParPos
  have hPcEq : Pc' = Pc := Option.some.inj (Option.some.inj (hBackW'.symm.trans hBackW))
  have hPpEq : Pp' = Pp := Option.some.inj (Option.some.inj (hBackP'.symm.trans hBackP))
  subst Pc'
  subst Pp'
  have hLiveP : liveBefore flat increasing covers rankArc r rankKahn idx pN :=
    ⟨hpLt, Or.inr (Or.inr ⟨Pp, hBackP, hTrW ▸ hLtTr⟩)⟩
  have hFreshEq : ∀ k : Fin 2,
      (let z := if k.val = 0 then Pc.fst else Pc.snd
       if z.val = Pp.fst.val ∨ z.val = Pp.snd.val then zero
       else
         let vz := (selectors (orderedConfig p large) r.out).label z
         Map.eval (foldFused B.F ref vz (B.F.depthOf pN)).composed (C.built.model.wantBase z)) =
      W.refFresh i k := by
    intro k
    let z := W.endpoint (W.child i) k
    have hzEq : z = (if k.val = 0 then Pc.fst else Pc.snd) := by
      dsimp only [z]; rw [hChildI]
      rcases fin2_cases k with rfl | rfl <;> rfl
    rw [← hzEq]
    have hSlotIff : W.slot (W.parent i) z = none ↔ ¬ (z.val = Pp.fst.val ∨ z.val = Pp.snd.val) := by
      rw [W.slot_none, hParentI]
      constructor
      · intro hMem hEq
        apply hMem
        rcases hEq with h1 | h2
        · exact Or.inl (Fin.ext h1)
        · exact Or.inr (Fin.ext h2)
      · intro hNe hMem
        apply hNe
        rcases (W.mem_iff Pp z).mp hMem with ⟨j, hj⟩
        rcases fin2_cases j with rfl | rfl
        · exact Or.inl (congrArg Fin.val hj.symm)
        · exact Or.inr (congrArg Fin.val hj.symm)
    by_cases hMem : z.val = Pp.fst.val ∨ z.val = Pp.snd.val
    · rw [ite_eq_left hMem]
      have hSome : W.slot (W.parent i) z ≠ none := fun hn => (hSlotIff.mp hn) hMem
      unfold BuiltExit.Model.refFresh
      rw [ite_eq_right hSome]
    · rw [ite_eq_right hMem]
      have hNone : W.slot (W.parent i) z = none := hSlotIff.mpr hMem
      unfold BuiltExit.Model.refFresh
      rw [ite_eq_left hNone]
      have hNotMem : ¬ Pp.Mem z := (hParentI ▸ (W.slot_none (W.parent i) z).mp hNone)
      have hLost : H.Lost Pp z := buildProperLossForest_edge_endpoints_lost rankArc flat
        (hChildI ▸ W.childKey i) (hParentI ▸ W.parentKey i) z (hChildI ▸ W.endpoint_mem (W.child i) k)
      have hProp : H.ProperLoss Pp z := ⟨hLost, hNotMem⟩
      have hvzLt : (selectors (orderedConfig p large) r.out).label z < r.out.tables.next :=
        B.G.size_eq ▸ B.E.label_lt z True.intro
      have hvzPos : 0 < (selectors (orderedConfig p large) r.out).label z := by
        have hOwnP' : (buildProperLossForest H rank).nodeKey? (B.E.image pF) = some Pp := hPpKey
        have hpPos : 0 < pN := hParPos
        have hTest := (properLoss_iff_ramTest flat increasing covers rankArc r hpPos hpLt hOwnP' z).mp hProp
        exact hTest.1
      obtain ⟨Az, hOwnZ, hBackZ, _, _⟩ :=
        owner_eq_some_of_label_pos flat increasing covers rankArc r entryRank z hvzPos
      have hRkZLe : rankKahn z ≤ idx := by
        rw [← hTrW, hzEq]
        rcases fin2_cases k with rfl | rfl
        · exact Nat.le_max_left _ _
        · exact Nat.le_max_right _ _
      have hTrZ : max (rankKahn Az.fst) (rankKahn Az.snd) < idx :=
        Nat.lt_of_lt_of_le (trigger_lt_properLoss flat rankKahn rankArcKahn (W.ownerProper z Az hOwnZ)) hRkZLe
      have hLiveZ : liveBefore flat increasing covers rankArc r rankKahn idx
          ((selectors (orderedConfig p large) r.out).label z) :=
        ⟨hvzLt, Or.inr (Or.inr ⟨Az, hBackZ, hTrZ⟩)⟩
      have hClosed := liveBefore_parent_and_jump flat increasing covers rankArc r rankKahn rankArcKahn idx
      let live := liveBefore flat increasing covers rankArc r rankKahn idx
      have hAll (w : Nat) (hw : live w) : C.built.live w :=
        C.built.all_live w (B.G.size_eq.symm ▸ hw.1)
      have hPar (w : Nat) (hw : live w) : (C.built.ref w).parent = B.F.parentOf w :=
        C.built.liveOK.parent_eq w (hAll w hw)
      have hOldHops : ExactLiveHops C.built.ref B.F.depthOf live :=
        ⟨fun w hw => C.built.liveOK.hops.parent_path w (hAll w hw),
         fun w hw => C.built.liveOK.hops.jump_path w (hAll w hw)⟩
      have hOKLive : LiveStoreOK B.F ref live := {
        live_lt := fun w hw => B.G.size_eq.symm ▸ hw.1
        parent_eq := fun w hw => by rw [hRefLive w hw, hPar w hw]
        jump_eq := fun w hw => by
          rw [hRefLive w hw]
          exact C.built.liveOK.jump_eq w (hAll w hw)
        parent_live := fun w hw => (hClosed w hw).1
        jump_live := fun w hw => (hClosed w hw).2
        parent_down := fun w hw => C.built.liveOK.parent_down w (hAll w hw)
        hops := hOldHops.frame_on_live
          (fun w hw => by rw [hPar w hw]; exact (hClosed w hw).1)
          hRefLive (fun _ _ => rfl) }
      let rb : BuiltExit.BaseReader (fun _ : Fin H.vertexCount => True) := fun qz _ => some (W.wantBase qz)
      let rm : BuiltExit.MapReader (fun _ : Fin (exitTransferDrivers r).size => True) := fun qm _ => some (W.wantMap qm)
      have hFacts : BuiltExit.RouteForestFacts W.forest :=
        BuiltExit.RouteForestFacts.of_build rankArc B.distinctRanks flat
      have hOwnEqW : ∀ qz, W.owner qz = W.forest.nodeKey? (W.forest.label qz) :=
        exitDenseOwnerKey?_eq_canonical r B.E
      have hLiveRt : BuiltExit.RoutePathEdgeLive W (fun _ => True) (B.E.image pF) z :=
        BuiltExit.RoutePathEdgeLive.of_driverCoverage
          (fun k0 {_ _} hk0 hp0 => actualModel_driverCoverage B entryRank rankArc flat hk0 hp0)
          (fun _ _ _ => True.intro)
      have hAncZ : IsForestAncestor W.forest.parent (B.E.image pF) (W.forest.label z) :=
        (buildProperLossForest_properLoss_iff_of_node rankArc B.distinctRanks flat hPpKey z).mp hProp
      obtain ⟨rt⟩ := BuiltExit.Route.nonempty_of_forestAncestor hFacts (hOwnEqW z) hPpKey hAncZ hLiveRt
      let q : BuiltExit.Query W (fun _ => True) (fun _ => True) Pp z := ⟨True.intro, rt⟩
      have hSlotZEq : C.built.slotOf Az = (selectors (orderedConfig p large) r.out).label z := by
        obtain ⟨zF, hzF, hzVal⟩ := C.built.slot_key_at z Az (by rw [hMod]; exact hOwnZ)
        rw [exitDenseOwnerSlots_read] at hzF
        dsimp only [exitDenseOwnerCell] at hzF
        rw [ite_eq_right (Nat.ne_of_gt hvzPos)] at hzF
        exact hzVal.symm.trans (congrArg Fin.val (Option.some.inj hzF).symm)
      have hSlotPEq : C.built.slotOf Pp = pN := by
        change (physicalPairSlot? (orderedConfig p large) r.out.tables Pp).getD 0 = pN
        rw [(B.hSlot Pp pN).mpr ⟨pF, rfl, hPpKey⟩]; rfl
      have hEdgesW : @RouteSlotEdges H (exitTransferDrivers r).size W (fun _ => True) rm
          C.built.slotOf B.F C.built.ref := by
        change @RouteSlotEdges H (exitTransferDrivers r).size W (fun _ => True)
          (fun i _ => some (W.wantMap i)) C.built.slotOf C.built.bundle.F C.built.ref
        simpa only [hMod] using C.built.edges
      have hPathC : ParentPath C.built.ref B.F.depthOf ((selectors (orderedConfig p large) r.out).label z)
          pN (q.route.actual rm) := by
        rw [← hSlotZEq, ← hSlotPEq]
        exact route_parentPath q.route hEdgesW hOwnZ
      have hPathRef : ParentPath ref B.F.depthOf ((selectors (orderedConfig p large) r.out).label z)
          pN (q.route.actual rm) :=
        parentPath_transport (fun v hv => (hRefLive v hv).symm)
          (fun v hv => (hClosed v hv).1)
          (fun v hv => C.built.decoded.parent_eq v (C.built.all_live v (B.G.size_eq.symm ▸ hv.1)))
          hPathC hLiveZ
      have hDepthLe : B.F.depthOf pN ≤ B.F.depthOf ((selectors (orderedConfig p large) r.out).label z) :=
        hPathRef.rank_le
      have hDepthAnc : B.F.depthOf (B.F.ancestorAtDepth ((selectors (orderedConfig p large) r.out).label z)
          (B.F.depthOf pN)) = B.F.depthOf pN :=
        (B.G.layout.valid.ancestorAtDepth_spec (B.G.size_eq.symm ▸ hvzLt) hDepthLe).2.2
      have hAccEq := live_accumulated_foldFused_of_path hOKLive hLiveZ hPathRef hDepthAnc
      have hComposed : (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label z)
          (B.F.depthOf pN)).composed = q.route.actual rm := hAccEq
      change Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label z)
          (B.F.depthOf pN)).composed (C.built.model.wantBase z) = W.ref (W.parent i) z
      rw [hComposed, hMod, hParentI]
      have hRunEx : q.run rb rm = W.ref Pp z := q.run_exact rb rm (fun _ _ => rfl) (fun _ _ => rfl)
      rw [← hRunEx]
      unfold BuiltExit.Query.run
      simp only [rb, Option.getD_some]
  refine ⟨Pp, i, hBackP, hSlotW, by rw [hMod]; exact hChildI, by rw [hMod]; exact hParentI, hLiveP, ?_⟩
  have hMkSlot : ∀ s : Vertex H,
      (if s.val = Pc.fst.val then some (0 : Fin 2)
       else if s.val = Pc.snd.val then some 1
       else none) = W.slot (W.child i) s := by
    intro s
    rw [hChildI]
    unfold BuiltExit.Model.slot
    have h0 : W.endpoint Pc 0 = Pc.fst := rfl
    have h1 : W.endpoint Pc 1 = Pc.snd := rfl
    rw [h0, h1]
    by_cases h1e : s.val = Pc.fst.val
    · rw [ite_eq_left h1e, ite_eq_left (Fin.ext h1e.symm)]
    · have h1n : Pc.fst ≠ s := fun he => h1e (congrArg Fin.val he.symm)
      rw [ite_eq_right h1e, ite_eq_right h1n]
      by_cases h2e : s.val = Pc.snd.val
      · rw [ite_eq_left h2e, ite_eq_left (Fin.ext h2e.symm)]
      · have h2n : Pc.snd ≠ s := fun he => h2e (congrArg Fin.val he.symm)
        rw [ite_eq_right h2e, ite_eq_right h2n]
  have h0 : (if Pc.fst.val = Pp.fst.val ∨ Pc.fst.val = Pp.snd.val then zero
      else Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label Pc.fst)
        (B.F.depthOf pN)).composed (C.built.model.wantBase Pc.fst)) = W.refFresh i 0 := hFreshEq 0
  have h1 : (if Pc.snd.val = Pp.fst.val ∨ Pc.snd.val = Pp.snd.val then zero
      else Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label Pc.snd)
        (B.F.depthOf pN)).composed (C.built.model.wantBase Pc.snd)) = W.refFresh i 1 := hFreshEq 1
  have hEnd0 : W.endpoint (W.parent i) 0 = Pp.fst := by rw [hParentI]; rfl
  have hEnd1 : W.endpoint (W.parent i) 1 = Pp.snd := by rw [hParentI]; rfl
  dsimp only
  rw [h0, h1, hMod, hMkSlot Pp.fst, hMkSlot Pp.snd]
  unfold BuiltExit.Model.wantMap BuiltExit.Model.pack
  change _ = (⟨⟨(vjoin (W.refFresh i 0) (W.refFresh i 1)).x0,
    W.slot (W.child i) (W.endpoint (W.parent i) 0)⟩,
    ⟨(vjoin (W.refFresh i 0) (W.refFresh i 1)).x1,
    W.slot (W.child i) (W.endpoint (W.parent i) 1)⟩⟩ : Map)
  rw [hEnd0, hEnd1]


end Stage4MathBridges

end PaperB.RamProgram.ExitSummaryBuild
