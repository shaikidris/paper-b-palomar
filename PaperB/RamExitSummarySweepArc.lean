module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepLive

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-! Incoming-arc contributions and the wanted base of a sweep vertex. -/

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

noncomputable def ramArcStep {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (F : JumpForest) (ref : Store) (ownerSlot ownerD : Nat) (Bcut : CutPair H)
    (baseFn : Vertex H → Values) (acc : Values) (e : Nat) : Values :=
  if he : e < H.arcCount then
    let occ := rawOccurrence H ⟨e, he⟩
    let u := occ.1
    let rTail := entryRank occ.2.origTail
    let v := (selectors (orderedConfig p large) r.out).label u
    if u.val = Bcut.fst.val then ⟨Interval.join acc.x0 (.span rTail rTail), acc.x1⟩
    else if u.val = Bcut.snd.val then ⟨acc.x0, Interval.join acc.x1 (.span rTail rTail)⟩
    else if hv : v < r.out.tables.next then
      let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
        (nodeCount_eq_next r.index.ok).symm
      if hOwn : ownerSlot < r.out.tables.next then
        if 0 < v ∧
           r.index.reader.entry (Fin.cast hN ⟨ownerSlot, hOwn⟩) ≤
             r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) ∧
           r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) <
             r.index.reader.stop (Fin.cast hN ⟨ownerSlot, hOwn⟩) then
          vjoin acc (Map.eval (foldFused F ref v ownerD).composed (baseFn u))
        else acc
      else acc
    else acc
  else acc

private noncomputable def ramArcContribution {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (F : JumpForest) (ref : Store) (ownerSlot ownerD : Nat) (Bcut : CutPair H)
    (baseFn : Vertex H → Values) (e : Nat) : Values :=
  (if he : e < H.arcCount then
        let occ := rawOccurrence H ⟨e, he⟩
        let u := occ.1
        let rTail := entryRank occ.2.origTail
        let v := (selectors (orderedConfig p large) r.out).label u
        if u.val = Bcut.fst.val then ⟨.span rTail rTail, .empty⟩
        else if u.val = Bcut.snd.val then ⟨.empty, .span rTail rTail⟩
        else if hv : v < r.out.tables.next then
          let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
            (nodeCount_eq_next r.index.ok).symm
          if hOwn : ownerSlot < r.out.tables.next then
            if 0 < v ∧
               r.index.reader.entry (Fin.cast hN ⟨ownerSlot, hOwn⟩) ≤
                 r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) ∧
               r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) <
                 r.index.reader.stop (Fin.cast hN ⟨ownerSlot, hOwn⟩) then
              Map.eval (foldFused F ref v ownerD).composed (baseFn u)
            else zero
          else zero
        else zero
      else zero)

private theorem ramArcStep_eq_vjoin {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (F : JumpForest) (ref : Store) (ownerSlot ownerD : Nat) (Bcut : CutPair H)
    (baseFn : Vertex H → Values) (acc : Values) (e : Nat) :
    ramArcStep r entryRank F ref ownerSlot ownerD Bcut baseFn acc e =
      vjoin acc (ramArcContribution r entryRank F ref ownerSlot ownerD Bcut baseFn e) := by
  unfold ramArcStep ramArcContribution
  split
  · dsimp only
    split
    · apply values_ext
      · rfl
      · exact (intervalJoin_empty_right acc.x1).symm
    · split
      · apply values_ext
        · exact (intervalJoin_empty_right acc.x0).symm
        · rfl
      · split
        · split
          · split
            · rfl
            · exact (vjoin_empty_zero acc).symm
          · exact (vjoin_empty_zero acc).symm
        · exact (vjoin_empty_zero acc).symm
  · exact (vjoin_empty_zero acc).symm

theorem wantBase_eq_ramArcStep_foldl {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    (y : Vertex H)
    {ownerSlot : Nat} (hOwnPos : 0 < ownerSlot)
    (hOwnEq : (selectors (orderedConfig p large) r.out).label y = ownerSlot)
    {Bcut : CutPair H}
    (hNode : (buildProperLossForest H rank).nodeKey?
      ((buildActualSweepBundle H flat increasing covers rankArc r).E.image
        ⟨ownerSlot, hOwnEq ▸ (buildActualSweepBundle H flat increasing covers rankArc r).E.label_lt y True.intro⟩) =
      some Bcut)
    {ref : Store} {baseFn : Vertex H → Values}
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank hRank wFit hLayout
    (hRefLive : ∀ u, liveBefore flat increasing covers rankArc r rankKahn (rankKahn y) u →
      ref u = C.built.ref u) →
    (hBasePred : ∀ u : Vertex H, rankKahn u < rankKahn y →
      baseFn u = C.built.model.wantBase u) →
    (inArcsPrefix H H.arcCount y.val).foldl
        (ramArcStep r entryRank (buildActualSweepBundle H flat increasing covers rankArc r).F
          ref ownerSlot ((buildActualSweepBundle H flat increasing covers rankArc r).F.depthOf ownerSlot)
          Bcut baseFn) zero =
      C.built.model.wantBase y := by
  intro C hRefLive hBasePred
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  let W := actualModel B entryRank rankArc flat
  have hMod : C.built.model = W := C.built.model_eq
  have hOwnW : W.owner y = some Bcut := by
    change exitDenseOwnerKey? r y = some Bcut
    rw [exitDenseOwnerKey?_eq_canonical r B.E y]
    have hLab : (buildProperLossForest H rank).label y =
        B.E.image ⟨ownerSlot, hOwnEq ▸ B.E.label_lt y True.intro⟩ := by
      rw [← B.E.label_eq y True.intro]
      congr 1; apply Fin.ext; exact hOwnEq
    rw [hLab]; exact hNode
  have hWantY : C.built.model.wantBase y = W.ref Bcut y := by
    rw [hMod]; unfold BuiltExit.Model.wantBase; rw [hOwnW]
  rw [hWantY]
  let I := (actualKernel B entryRank rankArc flat).site y Bcut hOwnW
  have hItems : I.items.map BuiltExit.Item.arc = ForestIncomingRaw.row H (ForestIncomingRaw.prepare H) y := I.keep
  let rb : BuiltExit.BaseReader (fun _ : Fin H.vertexCount => True) := fun z _ => some (W.wantBase z)
  let rm : BuiltExit.MapReader (fun _ : Fin (exitTransferDrivers r).size => True) := fun i _ => some (W.wantMap i)
  have hSite : I.run rb rm = W.ref Bcut y :=
    I.run_exact (W.ownerProper y Bcut hOwnW) rb rm (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← hSite]
  unfold BuiltExit.Site.run
  let contribution := ramArcContribution r entryRank B.F ref ownerSlot
    (B.F.depthOf ownerSlot) Bcut baseFn
  have hFoldRewrite : ∀ (xs : List Nat) (init : Values),
      xs.foldl (ramArcStep r entryRank B.F ref ownerSlot (B.F.depthOf ownerSlot) Bcut baseFn) init =
        xs.foldl (fun acc e => vjoin acc (contribution e)) init := by
    intro xs
    induction xs with
    | nil => intro init; rfl
    | cons e es ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ramArcStep_eq_vjoin, ih]
  rw [hFoldRewrite]
  have hOwnLt : ownerSlot < r.out.tables.next := hOwnEq ▸ B.G.size_eq ▸ B.E.label_lt y True.intro
  have hMatchOne : ∀ (e : Nat) (heIn : e ∈ inArcsPrefix H H.arcCount y.val)
      (t : BuiltExit.Item W Bcut (fun _ => True) (fun _ => True)),
      (rawOccurrence H ⟨e, inArcsPrefix_lt H H.arcCount y.val e heIn⟩ = t.arc) →
      contribution e = t.action.run rb rm := by
    intro e heIn t htArc
    have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount y.val e heIn
    have hHd : rawHead H ⟨e, heLt⟩ = y := incomingArc_head heIn _
    unfold contribution ramArcContribution
    rw [dite_eq_left heLt]
    dsimp only
    let occ := rawOccurrence H ⟨e, heLt⟩
    let u := occ.1
    have hSrcEq : W.source t.arc = u := by
      change t.arc.1 = occ.1; rw [← htArc]
    have hTailEq : W.physicalTail t.arc = occ.2.origTail := by
      change t.arc.2.origTail = occ.2.origTail; rw [← htArc]
    have hArcH : H.HasQuotientArc u y :=
      (rawOccurrence_membership H u y).mp ⟨⟨e, heLt⟩, rfl, hHd⟩
    have hRkU : rankKahn u < rankKahn y := rankArcKahn u y hArcH
    cases t.action with
    | direct hMem =>
      have hMemU : Bcut.Mem u := hSrcEq ▸ hMem
      rcases (W.mem_iff Bcut u).mp hMemU with ⟨j, hj⟩
      have hEnds0 : W.endpoint Bcut 0 = Bcut.fst := rfl
      have hEnds1 : W.endpoint Bcut 1 = Bcut.snd := rfl
      change _ = BuiltExit.tab (fun k => if W.source t.arc = W.endpoint Bcut k
        then PaperB.ExitSummary.singleton (W.rank (W.physicalTail t.arc)) else .empty)
      rw [hSrcEq, hTailEq]
      rcases fin2_cases j with rfl | rfl
      · change W.endpoint Bcut 0 = u at hj
        rw [hEnds0] at hj
        have hFst : u = Bcut.fst := hj.symm
        have hSnd : u ≠ Bcut.snd := fun h => Bcut.ne (hFst.symm.trans h)
        rw [ite_eq_left (congrArg Fin.val hFst)]
        apply values_ext
        · change _ = if u = W.endpoint Bcut 0 then PaperB.ExitSummary.singleton (W.rank occ.2.origTail) else Interval.empty
          rw [hEnds0, ite_eq_left hFst]
          rfl
        · change _ = if u = W.endpoint Bcut 1 then PaperB.ExitSummary.singleton (W.rank occ.2.origTail) else Interval.empty
          rw [hEnds1, ite_eq_right hSnd]
      · change W.endpoint Bcut 1 = u at hj
        rw [hEnds1] at hj
        have hSnd : u = Bcut.snd := hj.symm
        have hFst : u ≠ Bcut.fst := fun h => Bcut.ne (h.symm.trans hSnd)
        rw [ite_eq_right (fun h => hFst (Fin.ext h)), ite_eq_left (congrArg Fin.val hSnd)]
        apply values_ext
        · change _ = if u = W.endpoint Bcut 0 then PaperB.ExitSummary.singleton (W.rank occ.2.origTail) else Interval.empty
          rw [hEnds0, ite_eq_right hFst]
        · change _ = if u = W.endpoint Bcut 1 then PaperB.ExitSummary.singleton (W.rank occ.2.origTail) else Interval.empty
          rw [hEnds1, ite_eq_left hSnd]
          rfl
    | skip hNotMem hNotProp =>
      have hNotMemU : ¬ Bcut.Mem u := hSrcEq ▸ hNotMem
      have hNotPropU : ¬ H.ProperLoss Bcut u := hSrcEq ▸ hNotProp
      have hNeFst : u.val ≠ Bcut.fst.val := fun he => hNotMemU ((Fin.ext he : u = Bcut.fst) ▸ Or.inl rfl)
      have hNeSnd : u.val ≠ Bcut.snd.val := fun he => hNotMemU ((Fin.ext he : u = Bcut.snd) ▸ Or.inr rfl)
      rw [ite_eq_right hNeFst, ite_eq_right hNeSnd]
      have hvLt : (selectors (orderedConfig p large) r.out).label u < r.out.tables.next :=
        B.G.size_eq ▸ B.E.label_lt u True.intro
      rw [dite_eq_left hvLt, dite_eq_left hOwnLt]
      have hTestFalse : ¬ (0 < (selectors (orderedConfig p large) r.out).label u ∧
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
            r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨_, hvLt⟩) ∧
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨_, hvLt⟩) <
            r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) := by
        intro hT
        exact hNotPropU ((properLoss_iff_ramTest flat increasing covers rankArc r hOwnPos hOwnLt hNode u).mpr hT)
      rw [ite_eq_right hTestFalse]; rfl
    | lift hProp q =>
      have hPropU : H.ProperLoss Bcut u := hSrcEq ▸ hProp
      have hNeFst : u.val ≠ Bcut.fst.val := fun he => hPropU.2 ((Fin.ext he : u = Bcut.fst) ▸ Or.inl rfl)
      have hNeSnd : u.val ≠ Bcut.snd.val := fun he => hPropU.2 ((Fin.ext he : u = Bcut.snd) ▸ Or.inr rfl)
      rw [ite_eq_right hNeFst, ite_eq_right hNeSnd]
      have hvLt : (selectors (orderedConfig p large) r.out).label u < r.out.tables.next :=
        B.G.size_eq ▸ B.E.label_lt u True.intro
      rw [dite_eq_left hvLt, dite_eq_left hOwnLt]
      have hTestTrue := (properLoss_iff_ramTest flat increasing covers rankArc r hOwnPos hOwnLt hNode u).mp hPropU
      rw [ite_eq_left hTestTrue]
      change _ = q.run rb rm
      have hvPos : 0 < (selectors (orderedConfig p large) r.out).label u := hTestTrue.1
      obtain ⟨Au, hOwnU, hBackU, _, _⟩ :=
        owner_eq_some_of_label_pos flat increasing covers rankArc r entryRank u hvPos
      have hTrU : max (rankKahn Au.fst) (rankKahn Au.snd) < rankKahn y :=
        Nat.lt_trans (trigger_lt_properLoss flat rankKahn rankArcKahn (W.ownerProper u Au hOwnU)) hRkU
      have hLiveV : liveBefore flat increasing covers rankArc r rankKahn (rankKahn y)
          ((selectors (orderedConfig p large) r.out).label u) :=
        ⟨hvLt, Or.inr (Or.inr ⟨Au, hBackU, hTrU⟩)⟩
      have hClosed := liveBefore_parent_and_jump flat increasing covers rankArc r rankKahn rankArcKahn (rankKahn y)
      let live := liveBefore flat increasing covers rankArc r rankKahn (rankKahn y)
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
      have hSlotUEq : C.built.slotOf Au = (selectors (orderedConfig p large) r.out).label u := by
        obtain ⟨uF, huF, huVal⟩ := C.built.slot_key_at u Au (by rw [hMod]; exact hOwnU)
        rw [exitDenseOwnerSlots_read] at huF
        dsimp only [exitDenseOwnerCell] at huF
        rw [ite_eq_right (Nat.ne_of_gt hvPos)] at huF
        have hU : uF.val = (selectors (orderedConfig p large) r.out).label u :=
          congrArg Fin.val (Option.some.inj huF).symm
        exact huVal.symm.trans hU
      have hSlotBEq : C.built.slotOf Bcut = ownerSlot := by
        obtain ⟨yF, hyF, hyVal⟩ := C.built.slot_key_at y Bcut (by rw [hMod]; exact hOwnW)
        rw [exitDenseOwnerSlots_read] at hyF
        dsimp only [exitDenseOwnerCell] at hyF
        rw [ite_eq_right (fun h => (Nat.ne_of_gt hOwnPos) (hOwnEq.symm.trans h))] at hyF
        have hY : yF.val = ownerSlot :=
          (congrArg Fin.val (Option.some.inj hyF).symm).trans hOwnEq
        exact hyVal.symm.trans hY
      have hEdgesW : @RouteSlotEdges H (exitTransferDrivers r).size W (fun _ => True) rm
          C.built.slotOf B.F C.built.ref := by
        change @RouteSlotEdges H (exitTransferDrivers r).size W (fun _ => True)
          (fun i _ => some (W.wantMap i)) C.built.slotOf C.built.bundle.F C.built.ref
        simpa only [hMod] using C.built.edges
      have hPathC : ParentPath C.built.ref B.F.depthOf ((selectors (orderedConfig p large) r.out).label u)
          ownerSlot (q.route.actual rm) := by
        rw [← hSlotUEq, ← hSlotBEq]
        have hOwnQ : W.owner (W.source t.arc) = some Au := by rw [hSrcEq]; exact hOwnU
        exact route_parentPath q.route hEdgesW hOwnQ
      have hPathRef : ParentPath ref B.F.depthOf ((selectors (orderedConfig p large) r.out).label u)
          ownerSlot (q.route.actual rm) :=
        parentPath_transport (fun z hz => (hRefLive z hz).symm)
          (fun z hz => (hClosed z hz).1)
          (fun z hz => C.built.decoded.parent_eq z (C.built.all_live z (B.G.size_eq.symm ▸ hz.1)))
          hPathC hLiveV
      have hDepthLe : B.F.depthOf ownerSlot ≤ B.F.depthOf ((selectors (orderedConfig p large) r.out).label u) :=
        hPathRef.rank_le
      have hDepthAnc : B.F.depthOf (B.F.ancestorAtDepth ((selectors (orderedConfig p large) r.out).label u)
          (B.F.depthOf ownerSlot)) = B.F.depthOf ownerSlot :=
        (B.G.layout.valid.ancestorAtDepth_spec (B.G.size_eq.symm ▸ hvLt) hDepthLe).2.2
      have hAccEq := live_accumulated_foldFused_of_path hOKLive hLiveV hPathRef hDepthAnc
      have hBaseU : baseFn u = W.wantBase u := by
        rw [← hMod]; exact hBasePred u hRkU
      have hComposed : (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label u)
          (B.F.depthOf ownerSlot)).composed = q.route.actual rm := hAccEq
      change Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label u)
          (B.F.depthOf ownerSlot)).composed (baseFn u) = q.run rb rm
      rw [hComposed, hBaseU]
      unfold BuiltExit.Query.run
      simp only [rb, Option.getD_some, hSrcEq]
  apply foldl_vjoin_eq_of_image
  constructor
  · intro e heIn
    have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount y.val e heIn
    have hMemRow : rawOccurrence H ⟨e, heLt⟩ ∈ ForestIncomingRaw.row H (ForestIncomingRaw.prepare H) y :=
      (rawOccurrence_in_row_iff H y _ _).mpr ⟨e, heIn, heLt, rfl⟩
    rw [← hItems] at hMemRow
    obtain ⟨t, htMem, htEq⟩ := List.mem_map.mp hMemRow
    exact ⟨t, htMem, hMatchOne e heIn t htEq.symm⟩
  · intro t htMem
    have hMemRow : t.arc ∈ ForestIncomingRaw.row H (ForestIncomingRaw.prepare H) y := by
      rw [← hItems]; exact List.mem_map.mpr ⟨t, htMem, rfl⟩
    obtain ⟨e, heIn, heLt, heOcc⟩ := (rawOccurrence_in_row_iff H y t.arc.1 t.arc.2).mp hMemRow
    exact ⟨e, heIn, (hMatchOne e heIn t heOcc).symm⟩


end Stage4MathBridges

end PaperB.RamProgram.ExitSummaryBuild
