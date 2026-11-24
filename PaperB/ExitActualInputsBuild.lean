module

public import PaperB.ExitActualCompactSchedule
public import PaperB.ExitActualOrientation
public import PaperB.ExitActualOwnerColumn
public import PaperB.ExitConcreteDepthContract
public import PaperB.ExitIncomingLaw
public import PaperB.ExitCanonicalBank
public import PaperB.ExitPhysicalSeedPass
public import PaperB.ExitLiveForestRoutes
public import PaperB.ExitRouteStoredBridge
public import PaperB.ExitClosedOverlay
public import PaperB.ExitPrefixOccupancy
public import PaperB.ExitCompactMapBefore
public import PaperB.ExitEventPrefixRank
public import PaperB.ExitEarlierCreator
public import PaperB.ExitPublishedSlotChronology
public import PaperB.ExitValidParentOrder
public import PaperB.ExitPhysicalPrefixLive
public import PaperB.GenericRawExitModel
public import PaperB.ForestPhysicalReflection
public import PaperB.ForestActualFull
public import PaperB.JumpRegionInit

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ExitActualContract

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.ForestHead
open PaperB.EX24.FinalDFS
open PaperB.Jumps
open PaperB.BuiltExit
open PaperB.BuiltExit.PackedRuntime
open PaperB.BuiltExit.PackedRuntime.DirectIntegration
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.StoredPacking
open PaperB.ExitStoredWrite
open PaperB.ExitPhysicalBankLayout
open PaperB.ExitPhysicalDepthColumn
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalSeedPass
open PaperB.Exit.OrderedReaderResult
open PaperB.OrderedFreshHeads
open EX42.ArraySweep
open EX42.ArraySweep.Packed
open _root_.EX24
open _root_.EX24.PreStep
open _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex

/-! ### 1. Non-vacuous live-bounded `LiveStoreOK` bridge (avoids uninhabited `∀ u` in `StoreOK`) -/

section LiveStoreBridge

/-- Live-restricted store invariant matching `ExactLiveHops` and `DecodedOccupied`.
Unlike `StoreOK`, this does not assert `ParentPath` at out-of-range indices `u ≥ F.size`. -/
structure LiveStoreOK (F : JumpForest) (read : Store) (live : Nat → Prop) : Prop where
  live_lt : ∀ u, live u → u < F.size
  parent_eq : ∀ u, live u → (read u).parent = F.parentOf u
  jump_eq : ∀ u, live u → (read u).jump = F.jumpOf u
  parent_live : ∀ u, live u → live (F.parentOf u)
  jump_live : ∀ u, live u → live (F.jumpOf u)
  parent_down : ∀ u, live u → 0 < F.depthOf u →
    F.depthOf (F.parentOf u) < F.depthOf u
  hops : ExactLiveHops read F.depthOf live

private theorem live_selectAtDepth_eq_traceSelect
    {F : JumpForest} {read : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F read live) {u : Nat} (hu : live u) (d : Nat) :
    selectAtDepth F.depthOf d (read u) =
      (read u).select (kind (F.stepMoveToDepth u d)) := by
  by_cases h : d ≤ F.depthOf (F.jumpOf u) <;>
    simp [selectAtDepth, JumpForest.stepMoveToDepth, kind, ok.jump_eq u hu, h]

private theorem live_traceSelect_dst
    {F : JumpForest} {read : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F read live) {u : Nat} (hu : live u) (d : Nat) :
    ((read u).select (kind (F.stepMoveToDepth u d))).dst =
      F.stepToDepth u d := by
  by_cases h : d ≤ F.depthOf (F.jumpOf u) <;>
    simp [JumpForest.stepMoveToDepth, JumpForest.stepToDepth, kind,
      Stored.select, ok.jump_eq u hu, ok.parent_eq u hu, h]

private theorem live_stepToDepth_live
    {F : JumpForest} {read : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F read live) {u : Nat} (hu : live u) (d : Nat) :
    live (F.stepToDepth u d) := by
  dsimp only [JumpForest.stepToDepth]
  split
  · exact ok.jump_live u hu
  · exact ok.parent_live u hu

private theorem live_foldFusedAux_eq_foldAux {F : JumpForest} {read : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F read live)
    (d budget fuel u : Nat) (hu : live u) (acc : Map) (steps : Nat)
    (hf : budget - steps = fuel) :
    foldFusedAux F.depthOf read d budget u acc steps =
      foldAux kind read (F.traceMovesAux fuel u d) u acc steps := by
  induction fuel generalizing u acc steps with
  | zero =>
    have hg : ¬ (steps < budget ∧ d < F.depthOf u) := by omega
    conv => lhs; rw [foldFusedAux]
    conv => rhs; rw [JumpForest.traceMovesAux_zero]
    simp only [dite_eq_right hg, foldAux]
  | succ fuel ih =>
    conv => lhs; rw [foldFusedAux]
    conv => rhs; rw [JumpForest.traceMovesAux_succ]
    by_cases hl : d < F.depthOf u
    · have hb : steps < budget := by omega
      have hg : steps < budget ∧ d < F.depthOf u := ⟨hb, hl⟩
      have hn : budget - (steps + 1) = fuel := by omega
      simp only [dite_eq_left hg, ite_eq_left hl, foldAux,
        live_selectAtDepth_eq_traceSelect ok hu d, live_traceSelect_dst ok hu d]
      exact ih (F.stepToDepth u d) (live_stepToDepth_live ok hu d) _ (steps + 1) hn
    · have hg : ¬ (steps < budget ∧ d < F.depthOf u) := fun h => hl h.2
      simp only [dite_eq_right hg, ite_eq_right hl, foldAux]

theorem live_foldFused_eq_foldTrace {F : JumpForest} {read : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F read live)
    {u : Nat} (hu : live u) (d : Nat) :
    foldFused F read u d = foldTrace F read u d := by
  unfold foldFused foldTrace fold JumpForest.traceMoves
  exact live_foldFusedAux_eq_foldAux ok d (F.depthOf u - d)
    (F.depthOf u - d) u hu Map.identity 0 (Nat.sub_zero _)

private theorem live_follows_checked {F : JumpForest} {read : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F read live)
    {u a : Nat} {ms : List JumpMove} (hu : live u) (h : Follows F u ms a) :
    Checked kind read F.depthOf u ms a := by
  induction h with
  | nil u => exact Checked.nil u
  | @parent u ms a liveD tail ih =>
    have down : F.depthOf (read u).parent < F.depthOf u := by
      rw [ok.parent_eq u hu]
      exact ok.parent_down u hu liveD
    have dst :
        (selectMove (read u) (JumpMove.parent u (F.parentOf u))).dst =
          F.parentOf u :=
      ok.parent_eq u hu
    have ht : Checked kind read F.depthOf
        (selectMove (read u) (JumpMove.parent u (F.parentOf u))).dst ms a := by
      simpa only [dst] using ih (ok.parent_live u hu)
    exact Checked.cons u (JumpMove.parent u (F.parentOf u)) (parent_segment down) ht
  | @jump u ms a tail ih =>
    have dst :
        (selectMove (read u) (JumpMove.jump u (F.jumpOf u))).dst =
          F.jumpOf u :=
      ok.jump_eq u hu
    have ht : Checked kind read F.depthOf
        (selectMove (read u) (JumpMove.jump u (F.jumpOf u))).dst ms a := by
      simpa only [dst] using ih (ok.jump_live u hu)
    exact Checked.cons u (JumpMove.jump u (F.jumpOf u))
      (jump_segment (ok.hops.jump_path u hu)) ht

theorem live_foldTrace_spec {F : JumpForest} {read : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F read live)
    {u : Nat} (hu : live u) (d : Nat) :
    let r := foldTrace F read u d
    r.stop = F.ancestorAtDepth u d ∧
      ParentPath read F.depthOf u (F.ancestorAtDepth u d) r.composed ∧
      r.steps = (F.traceMoves u d).length := by
  have hchk : Checked kind read F.depthOf u (F.traceMoves u d) (F.ancestorAtDepth u d) :=
    live_follows_checked ok hu (traceMoves_follows F u d)
  obtain ⟨hs, m, hp, hm⟩ := foldAux_spec hchk Map.identity 0
  have hc : (foldTrace F read u d).composed = m :=
    hm.trans (identity_compose m)
  refine ⟨hs, ?_, fold_steps kind read u (F.traceMoves u d)⟩
  simpa only [hc] using hp

theorem live_foldTrace_exact {F : JumpForest} {read : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F read live)
    {u : Nat} (hu : live u) {d : Nat} {m : Map}
    (reference : ParentPath read F.depthOf u (F.ancestorAtDepth u d) m) :
    (foldTrace F read u d).stop = F.ancestorAtDepth u d ∧
      (foldTrace F read u d).composed = m :=
  fold_exact (live_follows_checked ok hu (traceMoves_follows F u d)) reference

theorem live_accumulated_foldFused_of_path {F : JumpForest} {ref : Store}
    {live : Nat → Prop} (ok : LiveStoreOK F ref live)
    {u a d : Nat} (hu : live u) {p : Map} (hp : ParentPath ref F.depthOf u a p)
    (hd : F.depthOf (F.ancestorAtDepth u d) = F.depthOf a) :
    accumulated (foldFused F ref u d) = p := by
  have hstop := parentPath_endpoint_of_depth (live_foldTrace_spec ok hu d).2.1 hp hd
  have hp' : ParentPath ref F.depthOf u (F.ancestorAtDepth u d) p := by
    rw [hstop]
    exact hp
  rw [live_foldFused_eq_foldTrace ok hu d, ← (live_foldTrace_exact ok hu hp').2]
  cases foldTrace F ref u d <;> rfl

theorem live_foldStored_steps_le {bits : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {F : JumpForest} {ref : Store} {tags : TagsFit bits}
    {live : Nat → Prop}
    (dec : DecodedOccupied mem R F ref tags live)
    (ok : LiveStoreOK F ref live)
    {u n : Nat} (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R tags u d).steps ≤ 3 * ceilLog2 (n + 2) := by
  rw [dec.foldStored_exact_live hu d, live_foldFused_eq_foldTrace ok hu d]
  have hc := foldTrace_cost ref dec.valid (dec.live_lt_size u hu) hn d
  omega

theorem live_run_read_charge {bits : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {F : JumpForest} {ref : Store} {tags : TagsFit bits}
    {live : Nat → Prop}
    (dec : DecodedOccupied mem R F ref tags live)
    (ok : LiveStoreOK F ref live)
    {u n : Nat} (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3 := by
  obtain ⟨c, hc, hwords⟩ := foldStored_wordReads mem R tags u d
  have hsteps := live_foldStored_steps_le dec ok hu hn d
  exact ⟨c, hc, hwords, by omega⟩

theorem live_run_eq_query_of_route
    {H : LabelledQuotient} {m bits : Nat}
    {mem : Array (Word bits)} {R : Region bits mem.size} {F : JumpForest}
    {ref : Store} {tags : TagsFit bits} {live : Nat → Prop}
    {W : BuiltExit.Model H m} {P : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    {z : Fin H.vertexCount} {A B : CutPair H}
    (q : Query W P S B z) (rb : BaseReader P) (rm : MapReader S)
    (slot : CutPair H → Nat) (howner : W.owner z = some A)
    (edges : RouteSlotEdges W rm slot F ref)
    (dec : DecodedOccupied mem R F ref tags live) (ok : LiveStoreOK F ref live)
    (hu : live (slot A)) (d : Nat)
    (hdepth : F.depthOf (F.ancestorAtDepth (slot A) d) = d)
    (hend : F.depthOf (slot B) = d)
    (prior : Array (Option Values)) (v : Fin prior.size)
    (hbase : (prior[v.val]'(v.isLt)) = rb z q.readOK) :
    PriorBase.run mem R tags prior v (slot A) d = q.run rb rm := by
  rw [PriorBase.run, dec.foldStored_exact_live hu d,
    live_accumulated_foldFused_of_path ok hu (route_parentPath q.route edges howner)
      (hdepth.trans hend.symm),
    hbase, Query.run]

end LiveStoreBridge

/-! ### 2. Actual Sweep Bundle & Split-`F₀`/`F` Raw Exit Model -/

/-- Certified upstream sweep state and reflection package extracted from
`OrderedReaderResult`. -/
structure ActualSweepBundle (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) (r : PaperB.OrderedReaderResult p data size_data rank large) where
  F : JumpForest
  up : Fin F.size → Fin F.size
  distinctRanks : Function.Injective rank
  full : FullRows p rank (orderedRows p data size_data)
  g0 : Grounded (orderedConfig p large) JumpForest.init
    (initial (orderedConfig p large) (ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables
  ch : Chronology (orderedConfig p large) g0 r.out r.log
  G : Grounded (orderedConfig p large) F r.out.tables
  hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val
  E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True)
  hRoot : ∃ h0 : 0 < F.size, E.image ⟨0, h0⟩ = (buildProperLossForest H rank).rootNode
  hSurj : Function.Surjective E.image
  hSlot : ∀ (q : CutPair H) (n : Nat),
    physicalPairSlot? (orderedConfig p large) r.out.tables q = some n ↔
      ∃ a : Fin F.size, a.val = n ∧
        (buildProperLossForest H rank).nodeKey? (E.image a) = some q
  hLoss : ∀ (q : CutPair H) (y : Vertex H),
    (q.fst < q.snd ∧ H.ProperLoss q y) ↔
      ∃ n, physicalPairSlot? (orderedConfig p large) r.out.tables q = some n ∧
        ∃ k, climb F.parentOf k ((selectors (orderedConfig p large) r.out).label y) = n

noncomputable def buildActualSweepBundle
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    ActualSweepBundle H p data size_data rank large r := by
  have distinctRanks : Function.Injective rank := by
    intro a b hab
    obtain ⟨i, hi⟩ := covers a
    obtain ⟨j, hj⟩ := covers b
    have hij : i.val = j.val := by
      rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
      · have h := increasing i j hlt
        rw [hi, hj] at h
        omega
      · exact heq
      · have h := increasing j i hgt
        rw [hj, hi] at h
        omega
    exact hi.symm.trans ((congrArg (orderedVertexAt data size_data) (Fin.ext hij)).trans hj)
  have full : FullRows p rank (orderedRows p data size_data) :=
    orderedRows_full p data size_data rank increasing covers
  have layout0 : JumpWordLayout (orderedConfig p large).region JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1 :=
    ConcreteInit.init_layout H.vertexCount
  have g0 : Grounded (orderedConfig p large) JumpForest.init
      (initial (orderedConfig p large)
        (ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables :=
    initial_grounded (orderedConfig p large) layout0 rfl H.vertexCount
  have ch : Chronology (orderedConfig p large) g0 r.out r.log :=
    OrderedFreshHeads.chronology r g0
      (preparedInstalls (orderedConfig p large) rank distinctRanks)
      (appendParents (orderedConfig p large))
      (fun row hr => by rw [full.tests_eq row hr]; exact p.spec row.head)
  let hRefl := OutputOK.physicalReflection r.index.ok rankArc distinctRanks flat
  let F := Classical.choose hRefl
  let hRefl1 := Classical.choose_spec hRefl
  let up := Classical.choose hRefl1
  let hRefl2 := Classical.choose_spec hRefl1
  let E := Classical.choose hRefl2.2.2
  let hRefl3 := Classical.choose_spec hRefl2.2.2
  exact ⟨F, up, distinctRanks, full, g0, ch,
    hRefl2.1, hRefl2.2.1, E, hRefl3.1, hRefl3.2.1, hRefl3.2.2.1, hRefl3.2.2.2⟩

section WithBundle

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
variable {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
variable {large : 3 ≤ H.vertexCount}
variable {r : PaperB.OrderedReaderResult p data size_data rank large}
variable (B : ActualSweepBundle H p data size_data rank large r)
include B

theorem bundle_next_pos : 0 < r.out.tables.next := by
  have hle := SlotRun.next_le B.ch.slots
  change 1 ≤ r.out.tables.next at hle
  omega

omit B in
theorem bundle_next_le : r.out.tables.next ≤ H.vertexCount + 1 :=
  r.index.ok.2.1

theorem bundle_numInserted_le : B.F.numInserted ≤ H.vertexCount := by
  have h1 : B.F.size = r.out.tables.next := B.G.size_eq
  have h2 := bundle_next_le (r := r)
  change B.F.size - 1 ≤ H.vertexCount
  omega

theorem bundle_depthOf_lt {u : Nat} (hu : u < B.F.size) :
    B.F.depthOf u < B.F.size := by
  have hle := B.G.layout.valid.exists_forestInvariant.choose_spec.depthOf_le_self hu
  omega

private theorem bundle_realNode_has_image
    {k : CanonNode H rank} {_q : CutPair H}
    (_hk : (buildProperLossForest H rank).nodeKey? k = some _q) :
    ∃ a : Fin B.F.size, B.E.image a = k :=
  B.hSurj k

private theorem bundle_pos_of_real_image
    (a : Fin B.F.size) {q : CutPair H}
    (hq : (buildProperLossForest H rank).nodeKey? (B.E.image a) = some q) :
    0 < a.val := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hsize : 0 < B.F.size := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have ha : a = (⟨0, hsize⟩ : Fin B.F.size) := Fin.ext hz
  have hn : (none : Option (CutPair H)) = some q := by
    simpa only [ha, B.E.root_eq hsize, buildProperLossForest_nodeKey?_root] using hq
  cases hn

theorem bundle_order_covers :
    ∀ y : Vertex H, ∃ j : Fin H.vertexCount, (actualP r).orderAt j = y := by
  intro y
  obtain ⟨row, hr, he⟩ := B.full.covers y
  let make (j : Fin H.vertexCount) : Row H :=
    ⟨orderedVertexAt data size_data j, p.row (orderedVertexAt data size_data j)⟩
  change row ∈ List.ofFn make at hr
  obtain ⟨j, hj, hh⟩ := List.mem_iff_getElem.mp hr
  let k : Fin H.vertexCount := ⟨j, by simpa only [List.length_ofFn] using hj⟩
  have hk : make k = row := by simpa only [List.getElem_ofFn] using hh
  exact ⟨k, (congrArg Row.head hk).trans he⟩

/-- Split-`F₀`/`F` driver provenance avoiding the upstream shared-`F` collision. -/
theorem bundle_drivers_provenance {d : ExitTransferDriver H}
    (hd : d ∈ exitTransferDrivers r) :
    ∃ (y : Vertex H) (i : Fin r.out.tables.next) (a : Fin B.F.size),
      actualSlot r y = some i ∧
      (actualP r).firstAt y i ∧
      i.val = d.address ∧
      a.val = d.address ∧
      actualPhysicalParent r d.address ≠ 0 ∧
      (B.up a).val = actualPhysicalParent r d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.child =
        some d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.parent =
        some (actualPhysicalParent r d.address) ∧
      (buildProperLossForest H rank).nodeKey? (B.E.image a) = some d.child ∧
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (B.E.image a)) = some d.parent := by
  obtain ⟨j, i, hit, hi, keys⟩ := (mem_exitTransferDrivers_iff_order r d).mp hd
  let y := (actualP r).orderAt j
  have firstAt : (actualP r).firstAt y i :=
    (actualSlot_exact r B.full B.ch y i).mp hit
  obtain ⟨a, child, parent, ha, hp0, hup, _hcb, _hpb, hcs, hps, hck, hpk, hkeys⟩ :=
    actualSlot_exitHeadKeys r B.G B.hUp B.E hit firstAt
  have hk : (child, parent) = (d.child, d.parent) :=
    Option.some.inj (hkeys.symm.trans keys)
  have hc : child = d.child := congrArg Prod.fst hk
  have hp : parent = d.parent := congrArg Prod.snd hk
  subst child
  subst parent
  refine ⟨y, i, a, hit, firstAt, hi, ha.trans hi, ?_⟩
  rw [← hi]
  exact ⟨hp0, hup, hcs, hps, hck, hpk⟩

theorem bundle_drivers_covers_realEdge
    {k : CanonNode H rank} {child parent : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some child)
    (hp : (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent k) = some parent) :
    ∃ (d : ExitTransferDriver H) (a : Fin B.F.size),
      d ∈ exitTransferDrivers r ∧
        d.child = child ∧ d.parent = parent ∧
        d.address = a.val ∧ B.E.image a = k := by
  obtain ⟨a, ha⟩ := bundle_realNode_has_image B hk
  have hcKey : (buildProperLossForest H rank).nodeKey? (B.E.image a) = some child := by
    simpa only [ha] using hk
  have hpKey : (buildProperLossForest H rank).nodeKey? (B.E.image (B.up a)) = some parent := by
    simpa only [B.E.parent_eq a, ha] using hp
  have hcBack : r.out.tables.back[a.val]? = some (some child) :=
    (B.E.back_eq a).trans (congrArg some hcKey)
  have hpBack : r.out.tables.back[(B.up a).val]? = some (some parent) :=
    (B.E.back_eq (B.up a)).trans (congrArg some hpKey)
  have haPos := bundle_pos_of_real_image B a hcKey
  have hpPos := bundle_pos_of_real_image B (B.up a) hpKey
  have haLt : a.val < r.out.tables.next := by
    simpa only [B.G.size_eq] using a.isLt
  have hpLt : (B.up a).val < r.out.tables.next := by
    simpa only [B.G.size_eq] using (B.up a).isLt
  have hphys : actualPhysicalParent r a.val = (B.up a).val := by
    unfold actualPhysicalParent
    rw [(readRecordWords_spec B.G.layout a.isLt).1, B.hUp a] <;> rfl
  have hphysNe : actualPhysicalParent r a.val ≠ 0 := by
    rw [hphys]
    exact Nat.ne_of_gt hpPos
  obtain ⟨e, he, heLookup⟩ :=
    (slot_exact_physical r B.full B.ch (k := a.val)).mpr ⟨haPos, haLt, hphysNe⟩
  let i : Fin r.out.tables.next := ⟨a.val, haLt⟩
  have hslot : actualSlot r e.head = some i := by
    change
      (match headLookup r e.head with
       | none => none
       | some ev =>
         if h : ev.node < r.out.tables.next then some ⟨ev.node, h⟩ else none) = some i
    simp only [heLookup, he, dite_eq_left haLt, i]
  have hkeys : exitHeadKeys? r e.head = some (child, parent) := by
    simp [exitHeadKeys?, hslot, i, hphys, exitBackKey?,
      hcBack, hpBack, Nat.ne_of_gt haPos, Nat.ne_of_gt hpPos]
  let d : ExitTransferDriver H := ⟨a.val, child, parent⟩
  have hd : d ∈ exitTransferDrivers r :=
    (mem_exitTransferDrivers_iff r (bundle_order_covers B) d).mpr
      ⟨e.head, i, hslot, rfl, hkeys⟩
  exact ⟨d, a, hd, rfl, rfl, rfl, ha⟩

private def compactDriver (j : Fin (exitTransferDrivers r).size) : ExitTransferDriver H :=
  (exitTransferDrivers r)[j.val]'j.isLt

private theorem compactDriver_address_lt (j : Fin (exitTransferDrivers r).size) :
    (compactDriver j).address < B.F.size := by
  rw [B.G.size_eq]
  exact exitTransferDrivers_address_lt r j

noncomputable def bundleForestInputs :
    GenericRawExitModel.ForestInputs H (buildProperLossForest H rank)
      (exitTransferDrivers r).size where
  owner := exitDenseOwnerKey? r
  slots := Array.ofFn fun j : Fin (exitTransferDrivers r).size =>
    B.E.image ⟨(compactDriver j).address, compactDriver_address_lt B j⟩
  size_eq := by simp
  child := fun j => (compactDriver j).child
  parent := fun j => (compactDriver j).parent

private theorem bundleForestInputs_edgeNode_eq
    (j : Fin (exitTransferDrivers r).size) (a : Fin B.F.size)
    (ha : a.val = (compactDriver j).address) :
    (bundleForestInputs B).edgeNode j = B.E.image a := by
  simp only [GenericRawExitModel.ForestInputs.edgeNode, bundleForestInputs, Array.getElem_ofFn]
  exact congrArg B.E.image (Fin.ext ha.symm)

theorem bundleForestInputs_keyAgreement :
    GenericRawExitModel.KeyAgreement (bundleForestInputs B) := by
  constructor
  · intro y
    exact exitDenseOwnerKey?_eq_canonical r B.E y
  · intro j
    have hd : compactDriver j ∈ exitTransferDrivers r :=
      Array.mem_iff_getElem.mpr ⟨j.val, j.isLt, rfl⟩
    obtain ⟨_, _, a, _, _, _, ha, _, _, _, _, hc, _⟩ :=
      bundle_drivers_provenance B hd
    rw [bundleForestInputs_edgeNode_eq B j a ha]
    exact hc
  · intro j
    have hd : compactDriver j ∈ exitTransferDrivers r :=
      Array.mem_iff_getElem.mpr ⟨j.val, j.isLt, rfl⟩
    obtain ⟨_, _, a, _, _, _, ha, _, _, _, _, _, hp⟩ :=
      bundle_drivers_provenance B hd
    rw [bundleForestInputs_edgeNode_eq B j a ha]
    exact hp

def actualRuntime (H : LabelledQuotient) (entryRank : Fin H.origVertexCount → Nat) :
    GenericRawExitModel.Runtime H where
  raw := ForestIncomingRaw.prepare H
  entryRank := entryRank

noncomputable def actualModel
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    BuiltExit.Model H (exitTransferDrivers r).size :=
  GenericRawExitModel.model (actualRuntime H entryRank) rfl
    rank rankArc B.distinctRanks flat
    (bundleForestInputs B) (bundleForestInputs_keyAgreement B)

theorem actualModel_driverCoverage
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {k : CanonNode H rank} {child parent : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some child)
    (hp : (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent k) = some parent) :
    ∃ j : Fin (exitTransferDrivers r).size,
      (actualModel B entryRank rankArc flat).edgeNode j = k := by
  obtain ⟨d, a, hd, _, _, haddr, himage⟩ :=
    bundle_drivers_covers_realEdge B hk hp
  obtain ⟨i, hi, hread⟩ := Array.mem_iff_getElem.mp hd
  let j : Fin (exitTransferDrivers r).size := ⟨i, hi⟩
  have hj : compactDriver j = d := hread
  have ha : a.val = (compactDriver j).address := by rw [hj]; exact haddr.symm
  exact ⟨j, (bundleForestInputs_edgeNode_eq B j a ha).trans himage⟩

/-! ### 3. Proof-only `Kernel`, `BankLayout`, Initial Seeded Bank, and `DirectDepthContract` -/

private def trueDeps (n m : Nat) : Deps n m where
  installBase := fun _ _ => True
  installMap := fun _ _ => True
  vertexBase := fun _ _ => True
  vertexMap := fun _ _ => True

noncomputable def actualKernel
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    BuiltExit.Kernel (actualModel B entryRank rankArc flat)
      (trueDeps H.vertexCount (exitTransferDrivers r).size) := by
  let W := actualModel B entryRank rankArc flat
  have facts : RouteForestFacts W.forest :=
    RouteForestFacts.of_build rankArc B.distinctRanks flat
  have hOwner : ∀ z, W.owner z = W.forest.nodeKey? (W.forest.label z) :=
    exitDenseOwnerKey?_eq_canonical r B.E
  have mkRoute : ∀ (Bcut : CutPair H) (z : Vertex H),
      (∃ u, W.forest.nodeKey? u = some Bcut) →
      H.ProperLoss Bcut z →
      Route W (fun _ => True) z Bcut := by
    intro Bcut z hNode hLoss
    let a := Classical.choose hNode
    have ha : W.forest.nodeKey? a = some Bcut := Classical.choose_spec hNode
    have hAnc : IsForestAncestor W.forest.parent a (W.forest.label z) :=
      (buildProperLossForest_properLoss_iff_of_node rankArc B.distinctRanks flat ha z).mp hLoss
    have hLive : RoutePathEdgeLive W (fun _ => True) a z :=
      RoutePathEdgeLive.of_driverCoverage
        (fun k {_ _} hk hp => actualModel_driverCoverage B entryRank rankArc flat hk hp)
        (fun _ _ _ => True.intro)
    exact Classical.choice (Route.nonempty_of_forestAncestor facts (hOwner z) ha hAnc hLive)
  refine ⟨?_, ?_⟩
  · intro i k hSlotNone
    let z := W.endpoint (W.child i) k
    have hNotMem : ¬ (W.parent i).Mem z := (W.slot_none _ _).mp hSlotNone
    have hLost : H.Lost (W.parent i) z :=
      buildProperLossForest_edge_endpoints_lost rankArc flat
        (W.childKey i) (W.parentKey i) z (W.endpoint_mem (W.child i) k)
    have hProper : H.ProperLoss (W.parent i) z := ⟨hLost, hNotMem⟩
    have hNode : ∃ u, W.forest.nodeKey? u = some (W.parent i) :=
      ⟨W.forest.parent (W.edgeNode i), W.parentKey i⟩
    exact ⟨True.intro, mkRoute (W.parent i) z hNode hProper⟩
  · intro y Bcut hOwn
    have hNode : ∃ u, W.forest.nodeKey? u = some Bcut :=
      ⟨W.forest.label y, (hOwner y).symm.trans hOwn⟩
    refine ⟨(W.incoming y).map (fun e => ⟨e, ?_⟩), ?_⟩
    · classical
      exact if hMem : Bcut.Mem (W.source e) then .direct hMem
        else if hLoss : H.ProperLoss Bcut (W.source e) then
          .lift hLoss ⟨True.intro, mkRoute Bcut (W.source e) hNode hLoss⟩
        else .skip hMem hLoss
    · simp only [List.map_map]
      exact List.map_id _

def actualLookup (j : Fin (exitTransferDrivers r).size) :
    Fin r.out.tables.next × Fin r.out.tables.next :=
  let child : Fin r.out.tables.next := actualDriverAddress r j
  let parentNat := B.F.parentOf child.val
  have hParent : parentNat < r.out.tables.next := by
    rw [← B.G.size_eq]
    exact B.G.layout.valid.parentOf_lt_size (by rw [B.G.size_eq]; exact child.isLt)
  (child, ⟨parentNat, hParent⟩)

def actualKnownLoss (cut : Fin r.out.tables.next) (z : Vertex H) : Bool :=
  decide (0 < cut.val) &&
    B.F.decideAncestor cut.val ((selectors (orderedConfig p large) r.out).label z)

private def rebindRegion {bits a b : Nat} (h : a = b) (R : Region bits a) : Region bits b :=
  h ▸ R

def actualOwners : StaticHeadSweep.Slots H.vertexCount (Option (Fin r.out.tables.next)) where
  data := (exitDenseOwnerSlots r B.E).data.map (Option.map (Fin.cast B.G.size_eq))
  len := by simp [(exitDenseOwnerSlots r B.E).len]

private theorem actualOwners_read (y : Vertex H) :
    (actualOwners B).read y =
      ((exitDenseOwnerSlots r B.E).read y).map (Fin.cast B.G.size_eq) := by
  simp [actualOwners, StaticHeadSweep.Slots.read]

def actualInput {bits : Nat} (tags : TagsFit bits)
    (bank : WriteResult bits (r.out.tables.next + 18 * r.out.tables.next))
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    (entryRank : Fin H.origVertexCount → Nat) :
    PackedRuntime.Input H r.out.tables.next bits :=
  let bl : BankLayout (BankLayout.zeroStart bits)
      (r.out.tables.next + 18 * r.out.tables.next) r.out.tables.next :=
    BankLayout.direct hLayout (Nat.le_refl _)
  { rows := ForestIncomingRaw.prepare H
    owners := actualOwners B
    orientation := ⟨physicalSlotEnds r r.out.tables.next H.root, physicalSlotEnds_size _ _ _⟩
    depth := ⟨Array.ofFn fun u : Fin r.out.tables.next => B.F.depthOf u.val, by simp⟩
    knownLoss := actualKnownLoss B
    entryRank := ⟨Array.ofFn entryRank, by simp⟩
    physicalTail := fun a => a.origTail
    arena := ⟨bank.mem, rebindRegion bank.size_eq.symm bl.region, tags⟩ }

def actualPacking :
    Packing H.vertexCount (exitTransferDrivers r).size r.out.tables.next Map where
  addr := actualDriverAddress r
  view _ st := st.parentMap
  job _ i edge :=
    let u := (actualDriverAddress r i).val
    { slot := u, parent := B.F.parentOf u, jump := B.F.jumpOf u, edge := edge }

private def actualSeedProbe (u : Nat) : Prop :=
  u < r.out.tables.next ∧ (u = 0 ∨ B.F.parentOf u = 0)

def actualOcc
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v) : Nat → Nat → Prop :=
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  PrefixOcc.occ S (fun i => (actualDriverAddress r i).val) (actualSeedProbe B)

noncomputable def actualOld
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) : Nat → Store
  | 0 => fun _ => seedRecord
  | k + 1 =>
    let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
    let W := actualModel B entryRank rankArc flat
    if hk : k < H.vertexCount then
      let y := S.vertex ⟨k, hk⟩
      match S.mapSlot.read y with
      | none => actualOld increasing covers entryRank rankArc flat k
      | some i =>
        ((actualPacking B).jobAt y i (W.wantMap i)).overlay
          (actualOld increasing covers entryRank rankArc flat k)
    else actualOld increasing covers entryRank rankArc flat k

private def actualSeedCert (u : Fin r.out.tables.next)
    (hu : decide (u.val = 0 ∨ B.F.parentOf u.val = 0) = true) :
    Seed B.F (fun _ => seedRecord) r.out.tables.next :=
  ⟨u.val,
    { bound := u.isLt
      designated := by
        have h := of_decide_eq_true hu
        by_cases hz : u.val = 0
        · exact Or.inl hz
        · exact Or.inr ⟨Nat.pos_of_ne_zero hz,
            by rw [B.G.size_eq]; exact u.isLt, h.resolve_left hz⟩
      read_eq := rfl }⟩

private def actualSeedsAux : List (Fin r.out.tables.next) →
    List (Seed B.F (fun _ => seedRecord) r.out.tables.next)
  | [] => []
  | u :: us =>
    if hu : decide (u.val = 0 ∨ B.F.parentOf u.val = 0) = true then
      actualSeedCert B u hu :: actualSeedsAux us
    else actualSeedsAux us

def actualSeeds : List (Seed B.F (fun _ => seedRecord) r.out.tables.next) :=
  actualSeedsAux B (List.finRange r.out.tables.next)

private theorem actualSeedsAux_map_val (xs : List (Fin r.out.tables.next)) :
    (actualSeedsAux B xs).map Subtype.val =
      (xs.filter (fun u => decide (u.val = 0 ∨ B.F.parentOf u.val = 0))).map Fin.val := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    by_cases hu : decide (u.val = 0 ∨ B.F.parentOf u.val = 0) = true
    · simp only [actualSeedsAux, hu, ↓reduceDIte, List.map_cons, List.filter_cons]
      exact congrArg (u.val :: ·) ih
    · simp only [actualSeedsAux, hu, ↓reduceDIte, List.filter_cons, Bool.false_eq_true]
      exact ih

theorem actualSeeds_nodup : ((actualSeeds B).map Subtype.val).Nodup := by
  unfold actualSeeds
  rw [actualSeedsAux_map_val]
  have hnodup : (List.finRange r.out.tables.next).Nodup := List.nodup_finRange _
  have hfilt : ((List.finRange r.out.tables.next).filter
      (fun u => decide (u.val = 0 ∨ B.F.parentOf u.val = 0))).Nodup :=
    hnodup.filter _
  exact hfilt.map Fin.val (fun _ _ hne heq => hne (Fin.ext heq))

theorem actualSeeds_length_le : (actualSeeds B).length ≤ r.out.tables.next := by
  have hmap : (actualSeeds B).length = ((actualSeeds B).map Subtype.val).length :=
    (List.length_map _).symm
  rw [hmap, actualSeeds, actualSeedsAux_map_val, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem actualSeeds_mem_iff (u : Nat) :
    u ∈ (actualSeeds B).map Subtype.val ↔ actualSeedProbe B u := by
  unfold actualSeeds
  rw [actualSeedsAux_map_val, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hx
    exact ⟨x.isLt, hx⟩
  · rintro ⟨hu, hp⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact hp

/-! ### 4. `MapBound` closure and step invariants -/

end WithBundle

section RankHelpers

private theorem seedPass_preserves_depthAgrees
    {bits words slots : Nat} (tags : TagsFit bits) (base : Word bits)
    (layout : ExitPhysicalOneSlot.Layout base words slots)
    {depthBase : Word bits} {R : Region bits words}
    (C : Column R depthBase) (hrBase : R.base = base) (hrSlots : R.slots = slots)
    (hBefore : depthBase.val + R.slots ≤ R.base.val)
    (fit : (storedCodec tags).valid seedRecord)
    {F : JumpForest} {ref : Store}
    (seeds : List (Seed F ref slots)) {depth : Fin R.slots → Nat} :
    ∀ (bank : WriteResult bits words) (distinct : (seeds.map Subtype.val).Nodup),
      DepthAgrees bank R depth →
      DepthAgrees (ExitPhysicalSeedPass.run tags base layout fit seeds bank distinct) R depth := by
  subst hrBase hrSlots
  induction seeds with
  | nil =>
    intro bank distinct agree
    simpa [ExitPhysicalSeedPass.run] using agree
  | cons s ss ih =>
    intro bank distinct agree
    simp only [ExitPhysicalSeedPass.run, List.foldl_cons]
    refine ih _ (List.nodup_cons.mp distinct).2 ?_
    exact seedWrite_preserves_depthAgrees C tags layout hBefore bank s.val
      s.property.bound s.property.designated fit agree

private theorem rankBound_summary {limit : Nat} (xs : List Nat)
    (h : ∀ k ∈ xs, k < limit) : RankBound limit (ExitSummary.summary xs) := by
  induction xs with
  | nil => simp [ExitSummary.summary, RankBound]
  | cons k ks ih =>
    have h0 : k < limit := h k (by simp)
    have h1 : RankBound limit (ExitSummary.summary ks) :=
      ih (fun x hx => h x (by simp [hx]))
    have hs : RankBound limit (ExitSummary.singleton k) := ⟨h0, h0⟩
    simpa [ExitSummary.summary] using rankBound_join hs h1

private theorem rankBound_coord_compose {limit : Nat} {a : Map} {c : Coord}
    (ha : MapBound limit a) (hc : RankBound limit c.base) :
    RankBound limit (Coord.compose a c).base := by
  cases hs : c.slot with
  | none =>
    simp [Coord.compose, hs]
    exact hc
  | some j =>
    have hget : RankBound limit (Two.get a j).base := by
      rcases fin2_cases j with rfl | rfl
      · exact ha.1
      · exact ha.2
    simpa [Coord.compose, hs] using rankBound_join hc hget

private theorem mapBound_compose {limit : Nat} {a b : Map}
    (ha : MapBound limit a) (hb : MapBound limit b) :
    MapBound limit (Map.compose a b) :=
  ⟨rankBound_coord_compose ha hb.1, rankBound_coord_compose ha hb.2⟩

private theorem mapBound_ref {H : LabelledQuotient} {m endpoints : Nat} (W : BuiltExit.Model H m)
    (hRank : ∀ x : Fin H.origVertexCount, W.rank x < endpoints)
    (Bcut : CutPair H) (y : Vertex H) (j : Fin 2) :
    RankBound endpoints (Two.get (W.ref Bcut y) j) := by
  rw [Model.ref, BuiltExit.get_tab]
  refine rankBound_summary _ ?_
  intro k hk
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hk
  exact hRank x

private theorem mapBound_wantMap {H : LabelledQuotient} {m endpoints : Nat} (W : BuiltExit.Model H m)
    (hRank : ∀ x : Fin H.origVertexCount, W.rank x < endpoints) (i : Fin m) :
    MapBound endpoints (W.wantMap i) := by
  have hFresh (k j : Fin 2) : RankBound endpoints (Two.get (W.refFresh i k) j) := by
    unfold Model.refFresh
    split
    · exact mapBound_ref W hRank _ _ j
    · simp [BuiltExit.zero, BuiltExit.get_tab, RankBound]
  have hJoin (j : Fin 2) :
      RankBound endpoints (Two.get (vjoin (W.refFresh i 0) (W.refFresh i 1)) j) := by
    rw [BuiltExit.get_vjoin]
    exact rankBound_join (hFresh 0 j) (hFresh 1 j)
  constructor <;> simp [Model.wantMap, Model.pack]
  · exact hJoin 0
  · exact hJoin 1

end RankHelpers

section WithBundle

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
variable {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
variable {large : 3 ≤ H.vertexCount}
variable {r : PaperB.OrderedReaderResult p data size_data rank large}
variable (B : ActualSweepBundle H p data size_data rank large r)
include B

private theorem root_parent_zero (hF : ValidJumpForest B.F) : B.F.parentOf 0 = 0 :=
  hF.exists_forestInvariant.choose_spec.root_parent

private theorem root_jump_zero (hF : ValidJumpForest B.F) : B.F.jumpOf 0 = 0 :=
  hF.exists_forestInvariant.choose_spec.root_jump

private theorem parent_zero_jump_zero {u : Nat} (hu : u < B.F.size)
    (hp : B.F.parentOf u = 0) : B.F.jumpOf u = 0 := by
  by_cases hz : u = 0
  · subst u; exact root_jump_zero B B.G.layout.valid
  · obtain ⟨exps, inv⟩ := B.G.layout.valid.exists_forestInvariant
    have hPos : 0 < u := Nat.pos_of_ne_zero hz
    cases (inv.nodes u hu).pos_jump_cases hPos with
    | inl h => exact h.trans hp
    | inr h =>
      rw [h, hp, inv.root_jump]
      exact inv.root_jump

private theorem pos_jump_cases {u : Nat} (hu : u < B.F.size) (hPos : 0 < u) :
    B.F.jumpOf u = B.F.parentOf u ∨
      B.F.jumpOf u = B.F.jumpOf (B.F.jumpOf (B.F.parentOf u)) :=
  (B.G.layout.valid.exists_forestInvariant.choose_spec.nodes u hu).pos_jump_cases hPos

private theorem depth_pos_of_pos {u : Nat} (hu : u < B.F.size) (hPos : 0 < u) :
    0 < B.F.depthOf u := by
  have inv := B.G.layout.valid.exists_forestInvariant.choose_spec
  have hstep := (inv.nodes u hu).pos_depth hPos
  omega

private theorem pos_parent_lt {u : Nat} (hu : u < B.F.size) (hPos : 0 < u) :
    B.F.parentOf u < u :=
  (B.G.layout.valid.exists_forestInvariant.choose_spec.nodes u hu).pos_parent_lt hPos

private theorem jump_le_self {u : Nat} (hu : u < B.F.size) :
    B.F.jumpOf u ≤ u :=
  B.G.layout.valid.exists_forestInvariant.choose_spec.jump_le_self hu

private theorem parent_down_all {u : Nat} (hu : u < B.F.size) (hd : 0 < B.F.depthOf u) :
    B.F.depthOf (B.F.parentOf u) < B.F.depthOf u := by
  have inv := B.G.layout.valid.exists_forestInvariant.choose_spec
  have hPos : 0 < u := by
    by_cases hz : u = 0
    · rw [hz, inv.root_depth] at hd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hstep := (inv.nodes u hu).pos_depth hPos
  omega

private theorem storedParent_eq_parentOf {u : Nat} (hu : u < B.F.size) :
    storedParent B.G u = B.F.parentOf u := by
  rw [storedParent, dite_eq_left hu]
  exact B.G.layout.valid.parentOf_lt_size hu |> fun _ => rfl

variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)

private theorem slot_has_driver_of_pos_parent {v : Nat}
    (hvPos : 0 < v) (hvLt : v < r.out.tables.next)
    (hpNe : B.F.parentOf v ≠ 0) :
    ∃ (cr : Event H) (i : Fin (exitTransferDrivers r).size),
      cr ∈ r.log ∧ cr.fresh = true ∧ cr.node = v ∧
      headLookup r cr.head = some cr ∧
      actualSlot r cr.head = some ⟨v, hvLt⟩ ∧
      (actualDriverAddress r i).val = v ∧
      (actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).mapSlot.read cr.head = some i := by
  have hvF : v < B.F.size := by rw [B.G.size_eq]; exact hvLt
  have hphys : actualPhysicalParent r v = B.F.parentOf v := by
    unfold actualPhysicalParent
    rw [(readRecordWords_spec B.G.layout hvF).1] <;> rfl
  have hphysNe : actualPhysicalParent r v ≠ 0 := by rw [hphys]; exact hpNe
  obtain ⟨cr, hcrNode, hcrHit⟩ :=
    (slot_exact_physical r B.full B.ch (k := v)).mpr ⟨hvPos, hvLt, hphysNe⟩
  obtain ⟨hcrMem, hcrFresh, _, _⟩ := (headLookup_eq_some_iff r B.full cr.head cr).mp hcrHit
  let iv : Fin r.out.tables.next := ⟨v, hvLt⟩
  have hslot : actualSlot r cr.head = some iv := by
    change
      (match headLookup r cr.head with
       | none => none
       | some ev =>
         if h : ev.node < r.out.tables.next then some ⟨ev.node, h⟩ else none) = some iv
    simp only [hcrHit, hcrNode, dite_eq_left hvLt, iv]
  have hFirst : (actualP r).firstAt cr.head iv :=
    (actualSlot_exact r B.full B.ch cr.head iv).mp hslot
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hkeys⟩ :=
    actualSlot_exitHeadKeys r B.G B.hUp B.E hslot hFirst
  obtain ⟨chKey, paKey, hKeysSome⟩ : ∃ chKey paKey, exitHeadKeys? r cr.head = some (chKey, paKey) := by
    cases hx : exitHeadKeys? r cr.head with
    | none => rw [hx] at hkeys; cases hkeys
    | some _ => exact ⟨_, _, rfl⟩
  let d : ExitTransferDriver H := ⟨v, chKey, paKey⟩
  have hd : d ∈ exitTransferDrivers r :=
    (mem_exitTransferDrivers_iff r (bundle_order_covers B) d).mpr
      ⟨cr.head, iv, hslot, rfl, hKeysSome⟩
  obtain ⟨idx, hidx, hget⟩ := Array.mem_iff_getElem.mp hd
  let i : Fin (exitTransferDrivers r).size := ⟨idx, hidx⟩
  have haddr : (actualDriverAddress r i).val = v := congrArg ExitTransferDriver.address hget
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  have hEqIv : iv = actualDriverAddress r i := Fin.ext haddr.symm
  have hS : S.mapSlot.read cr.head = some i :=
    (S.slot_exact cr.head i).mpr
      ((driverPlan_firstAt_iff r increasing covers cr.head (actualDriverAddress r i)).mpr
        ((actualSlot_exact r B.full B.ch cr.head (actualDriverAddress r i)).mp
          (by rw [← hEqIv]; exact hslot)))
  exact ⟨cr, i, hcrMem, hcrFresh, hcrNode, hcrHit, hslot, haddr, hS⟩

private theorem unique_fresh_in_log {v : Nat} (hvPos : 0 < v) (hvLt : v < r.out.tables.next)
    {e1 e2 : Event H}
    (h1m : e1 ∈ r.log) (h1f : e1.fresh = true) (h1n : e1.node = v)
    (h2m : e2 ∈ r.log) (h2f : e2.fresh = true) (h2n : e2.node = v) :
    e1 = e2 := by
  obtain ⟨pre, x, post, hsplit, hxn, _, hpre, hpost⟩ := rootFirst B.ch.slots hvPos hvLt
  have eq_x (e : Event H) (hm : e ∈ r.log) (hf : e.fresh = true) (hn : e.node = v) :
      e = x := by
    rw [hsplit] at hm
    rcases List.mem_append.mp hm with hpre' | htail
    · exact absurd hn (hpre e hpre')
    · rcases List.mem_cons.mp htail with rfl | hpost'
      · rfl
      · have := hpost e hpost' hn
        simp [hf] at this
  exact (eq_x e1 h1m h1f h1n).trans (eq_x e2 h2m h2f h2n).symm

private theorem occ_of_earlier_slot
    {a : Fin H.vertexCount} {row : Event H}
    {pre post : Log H}
    (hsplit : r.log = pre ++ row :: post)
    (hRowHead : row.head =
      (actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a)
    {v : Nat} (hvLt : v < r.out.tables.next)
    (hPrem : v = 0 ∨ B.F.parentOf v = 0 ∨
      (∃ cr ∈ pre, cr.fresh = true ∧ cr.node = v)) :
    actualOcc B increasing covers a.val v := by
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  rcases hPrem with rfl | hp0 | ⟨cr', hcrPre, hcrFresh, hcrNode⟩
  · exact Or.inl ⟨hvLt, Or.inl rfl⟩
  · exact Or.inl ⟨hvLt, Or.inr hp0⟩
  · by_cases hp0 : B.F.parentOf v = 0
    · exact Or.inl ⟨hvLt, Or.inr hp0⟩
    · have hlogMem : cr' ∈ r.log := by rw [hsplit]; exact List.mem_append.mpr (Or.inl hcrPre)
      have hvPos : 0 < v := by
        have := B.ch.slots.fresh_ge cr' hlogMem hcrFresh
        change 1 ≤ cr'.node at this
        omega
      obtain ⟨cr, i, hcrMem, hcrFresh', hcrNode', _, _, haddr, hS⟩ :=
        slot_has_driver_of_pos_parent B increasing covers hvPos hvLt hp0
      have heq : cr = cr' :=
        unique_fresh_in_log B hvPos hvLt hcrMem hcrFresh' hcrNode' hlogMem hcrFresh hcrNode
      subst cr'
      have hRankLt : rank cr.head < rank row.head :=
        rank_lt_of_mem_log_prefix r B.full hsplit hcrPre
      rw [hRowHead] at hRankLt
      obtain ⟨b, hb⟩ := S.covers cr.head
      change S.vertex b = cr.head at hb
      have hbLt : b.val < a.val := by
        apply (S.rank_lt_rank_iff b a).mp
        change rank (S.vertex b) < rank (S.vertex a)
        rw [hb]
        exact hRankLt
      exact Or.inr ⟨b, hbLt, i, by rw [hb]; exact hS, haddr.symm⟩

private theorem occ_of_rank_lt_vertex
    {a : Fin H.vertexCount} {s : Vertex H}
    (hs : rank s < rank ((actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a))
    {v : Nat} (hvLt : v < r.out.tables.next)
    (hLab : (selectors (orderedConfig p large) r.out).label s = v) :
    actualOcc B increasing covers a.val v := by
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  by_cases hp0 : v = 0 ∨ B.F.parentOf v = 0
  · exact Or.inl ⟨hvLt, hp0⟩
  · have hvPos : 0 < v := Nat.pos_of_ne_zero (fun h => hp0 (Or.inl h))
    have hpNe : B.F.parentOf v ≠ 0 := fun h => hp0 (Or.inr h)
    obtain ⟨cr, i, hcrMem, hcrFresh, hcrNode, _, _, haddr, hS⟩ :=
      slot_has_driver_of_pos_parent B increasing covers hvPos hvLt hpNe
    obtain ⟨e, heMem, heHead⟩ := logHeadCovers r B.full s
    have heNode : e.node = v := (r.logLabels e heMem).symm.trans (by rw [heHead, hLab])
    obtain ⟨pre, x, post, hsplit, hxn, hxf, hpre, hpost⟩ := rootFirst B.ch.slots hvPos hvLt
    have hcrEq : cr = x := unique_fresh_in_log B hvPos hvLt hcrMem hcrFresh hcrNode
      (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp))) hxf hxn
    subst cr
    have hrankLe : rank x.head ≤ rank s := by
      rw [← heHead]
      have hm := heMem
      rw [hsplit] at hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact absurd heNode (hpre e h1)
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Nat.le_refl _
        · have hpw := logRankPairwise r B.full
          rw [hsplit] at hpw
          have hpw2 := (List.pairwise_append.mp hpw).2.1
          exact Nat.le_of_lt ((List.pairwise_cons.mp hpw2).1 e h3)
    have hRankLt : rank x.head < rank (S.vertex a) := Nat.lt_of_le_of_lt hrankLe hs
    obtain ⟨b, hb⟩ := S.covers x.head
    change S.vertex b = x.head at hb
    have hbLt : b.val < a.val := by
      apply (S.rank_lt_rank_iff b a).mp
      change rank (S.vertex b) < rank (S.vertex a)
      rw [hb]
      exact hRankLt
    exact Or.inr ⟨b, hbLt, i, by rw [hb]; exact hS, haddr.symm⟩

private theorem actualOcc_all_final {v : Nat} (hv : v < B.F.size) :
    actualOcc B increasing covers H.vertexCount v := by
  have hvLt : v < r.out.tables.next := by rw [← B.G.size_eq]; exact hv
  by_cases hp0 : v = 0 ∨ B.F.parentOf v = 0
  · exact Or.inl ⟨hvLt, hp0⟩
  · have hvPos : 0 < v := Nat.pos_of_ne_zero (fun h => hp0 (Or.inl h))
    have hpNe : B.F.parentOf v ≠ 0 := fun h => hp0 (Or.inr h)
    obtain ⟨cr, i, _, _, _, _, _, haddr, hS⟩ :=
      slot_has_driver_of_pos_parent B increasing covers hvPos hvLt hpNe
    let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
    obtain ⟨b, hb⟩ := S.covers cr.head
    change S.vertex b = cr.head at hb
    exact Or.inr ⟨b, b.isLt, i, by rw [hb]; exact hS, haddr.symm⟩

private theorem actualOld_step_none
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (a : Fin H.vertexCount)
    (ho : (actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).mapSlot.read
      ((actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a) = none) :
    actualOld B increasing covers entryRank rankArc flat (a.val + 1) =
      actualOld B increasing covers entryRank rankArc flat a.val := by
  change (if hlt : a.val < H.vertexCount then _ else _) = _
  rw [dite_eq_left a.isLt]
  dsimp only
  rw [ho]

private theorem actualOld_step_some
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (a : Fin H.vertexCount) (i : Fin (exitTransferDrivers r).size)
    (ho : (actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).mapSlot.read
      ((actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a) = some i) :
    actualOld B increasing covers entryRank rankArc flat (a.val + 1) =
      ((actualPacking B).jobAt
        ((actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a)
        i ((actualModel B entryRank rankArc flat).wantMap i)).overlay
        (actualOld B increasing covers entryRank rankArc flat a.val) := by
  change (if hlt : a.val < H.vertexCount then _ else _) = _
  rw [dite_eq_left a.isLt]
  dsimp only
  rw [ho]

/-- Inductive invariant on `(actualOcc, actualOld)` across `0 ≤ k ≤ H.vertexCount`. -/
private structure ActualStepInv
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (endpoints : Nat) (k : Nat) : Prop where
  live_lt : ∀ u, actualOcc B increasing covers k u → u < B.F.size
  parent_eq : ∀ u, actualOcc B increasing covers k u →
    (actualOld B increasing covers entryRank rankArc flat k u).parent = B.F.parentOf u
  jump_eq : ∀ u, actualOcc B increasing covers k u →
    (actualOld B increasing covers entryRank rankArc flat k u).jump = B.F.jumpOf u
  parent_live : ∀ u, actualOcc B increasing covers k u →
    actualOcc B increasing covers k (B.F.parentOf u)
  jump_live : ∀ u, actualOcc B increasing covers k u →
    actualOcc B increasing covers k (B.F.jumpOf u)
  maps_bound : ∀ u, actualOcc B increasing covers k u →
    MapBound endpoints (actualOld B increasing covers entryRank rankArc flat k u).parentMap ∧
    MapBound endpoints (actualOld B increasing covers entryRank rankArc flat k u).jumpMap
  hops : ExactLiveHops (actualOld B increasing covers entryRank rankArc flat k)
    B.F.depthOf (actualOcc B increasing covers k)

private theorem actualStepInv_zero
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (endpoints : Nat) :
    ActualStepInv B increasing covers entryRank rankArc flat endpoints 0 := by
  have hOcc0 (u : Nat) : actualOcc B increasing covers 0 u ↔ actualSeedProbe B u :=
    PrefixOcc.zero _ _ _ u
  have hInvF := B.G.layout.valid.exists_forestInvariant.choose_spec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [B.G.size_eq]
    exact ((hOcc0 u).mp hu).1
  · intro u hu
    rcases ((hOcc0 u).mp hu).2 with rfl | hp0
    · exact (root_parent_zero B B.G.layout.valid).symm
    · exact hp0.symm
  · intro u hu
    obtain ⟨huLt, hp0⟩ := (hOcc0 u).mp hu
    have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
    rcases hp0 with rfl | hp0
    · exact (root_jump_zero B B.G.layout.valid).symm
    · exact (parent_zero_jump_zero B huF hp0).symm
  · intro u hu
    obtain ⟨huLt, hp0⟩ := (hOcc0 u).mp hu
    apply (hOcc0 _).mpr
    have h0Lt : 0 < r.out.tables.next := bundle_next_pos B
    rcases hp0 with rfl | hp0
    · rw [root_parent_zero B B.G.layout.valid]; exact ⟨h0Lt, Or.inl rfl⟩
    · rw [hp0]; exact ⟨h0Lt, Or.inl rfl⟩
  · intro u hu
    obtain ⟨huLt, hp0⟩ := (hOcc0 u).mp hu
    have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
    apply (hOcc0 _).mpr
    have h0Lt : 0 < r.out.tables.next := bundle_next_pos B
    rcases hp0 with rfl | hp0
    · rw [root_jump_zero B B.G.layout.valid]; exact ⟨h0Lt, Or.inl rfl⟩
    · rw [parent_zero_jump_zero B huF hp0]; exact ⟨h0Lt, Or.inl rfl⟩
  · intro u _
    have hsm : (actualOld B increasing covers entryRank rankArc flat 0 u) = seedRecord := rfl
    rw [hsm]
    refine ⟨⟨by simp [seedRecord, Stored.parentOnly, Map.identity, RankBound],
        by simp [seedRecord, Stored.parentOnly, Map.identity, RankBound]⟩,
      ⟨by simp [seedRecord, Stored.parentOnly, Map.identity, RankBound],
        by simp [seedRecord, Stored.parentOnly, Map.identity, RankBound]⟩⟩
  · refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨huLt, hp0⟩ := (hOcc0 u).mp hu
      by_cases hz : u = 0
      · subst u
        change ParentPath (fun _ => seedRecord) B.F.depthOf 0 (seedRecord).parent (seedRecord).parentMap
        exact ParentPath.nil 0
      · have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
        have hdp : 0 < B.F.depthOf u := depth_pos_of_pos B huF (Nat.pos_of_ne_zero hz)
        have down : B.F.depthOf (seedRecord).parent < B.F.depthOf u := by
          simpa [seedRecord, Stored.parentOnly, hInvF.root_depth] using hdp
        have hsm : (seedRecord).parentMap = Map.identity := rfl
        have hp := ParentPath.cons (read := fun _ => seedRecord) (rank := B.F.depthOf) u down
          (ParentPath.nil 0)
        simp only [hsm, compose_identity] at hp
        exact hp
    · intro u hu
      obtain ⟨huLt, _⟩ := (hOcc0 u).mp hu
      by_cases hz : u = 0
      · subst u
        exact (rootSeed_ok (read := fun _ => seedRecord) (depth := B.F.depthOf)
          hInvF.root_depth rfl).2.2.2.2
      · have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
        exact topSeed_jumpOK (read := fun _ => seedRecord) (depth := B.F.depthOf)
          hInvF.root_depth (depth_pos_of_pos B huF (Nat.pos_of_ne_zero hz)) rfl

private theorem parent_of_driver_occ_earlier
    {a : Fin H.vertexCount} {i : Fin (exitTransferDrivers r).size}
    (hi : (actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).mapSlot.read
      ((actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch).vertex a) = some i) :
    let u := (actualDriverAddress r i).val
    0 < u ∧ u < r.out.tables.next ∧ B.F.parentOf u ≠ 0 ∧
    actualOcc B increasing covers a.val (B.F.parentOf u) ∧
    actualOcc B increasing covers a.val (B.F.jumpOf (B.F.parentOf u)) := by
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  let y := S.vertex a
  let u := (actualDriverAddress r i).val
  have hySlot : actualSlot r y = some (actualDriverAddress r i) := by
    have hr := (S.slot_exact y i).mp hi
    have hf : (actualP r).firstAt y (actualDriverAddress r i) :=
      (driverPlan_firstAt_iff r increasing covers y (actualDriverAddress r i)).mp hr
    exact (actualSlot_exact r B.full B.ch y (actualDriverAddress r i)).mpr hf
  have huLt : u < r.out.tables.next := (actualDriverAddress r i).isLt
  have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
  have hphys : actualPhysicalParent r u = B.F.parentOf u := by
    unfold actualPhysicalParent
    rw [(readRecordWords_spec B.G.layout huF).1] <;> rfl
  have hd : compactDriver i ∈ exitTransferDrivers r :=
    Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
  obtain ⟨_, _, aF, _, _, _, haF, hpNe, _, _, _, hck, _⟩ :=
    bundle_drivers_provenance B hd
  have haddrEq : (compactDriver i).address = u := rfl
  rw [haddrEq] at hpNe
  have hpNeF : B.F.parentOf u ≠ 0 := by rw [← hphys]; exact hpNe
  have huPos : 0 < u := by
    change 0 < (compactDriver i).address
    rw [← haF]
    exact bundle_pos_of_real_image B aF hck
  obtain ⟨eY, heYHit, heYNode⟩ : ∃ eY, headLookup r y = some eY ∧ eY.node = u := by
    cases hl : headLookup r y with
    | none => simp [actualSlot, actualCreationEvent, hl] at hySlot
    | some eY =>
      simp only [actualSlot, actualCreationEvent, hl] at hySlot
      split at hySlot
      · exact ⟨eY, rfl, congrArg Fin.val (Option.some.inj hySlot)⟩
      · cases hySlot
  obtain ⟨heYMem, heYFresh, _, heYHead⟩ := (headLookup_eq_some_iff r B.full y eY).mp heYHit
  obtain ⟨pre, x, post, hsplit, hxn, hxf, _, _⟩ := rootFirst B.ch.slots huPos huLt
  have heYEq : eY = x := unique_fresh_in_log B huPos huLt heYMem heYFresh heYNode
    (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp))) hxf hxn
  subst eY
  change x.head = S.vertex a at heYHead
  have w_earlier {w : Nat} (hwLt : w < u) :
      actualOcc B increasing covers a.val w := by
    have hwF : w < B.F.size := Nat.lt_trans hwLt huF
    have hwN : w < r.out.tables.next := by rw [← B.G.size_eq]; exact hwF
    by_cases hw0 : w = 0 ∨ B.F.parentOf w = 0
    · exact occ_of_earlier_slot B increasing covers hsplit heYHead hwN
        (hw0.elim Or.inl (fun h => Or.inr (Or.inl h)))
    · have hwPos : 0 < w := Nat.pos_of_ne_zero (fun h => hw0 (Or.inl h))
      obtain ⟨_, crW, _, hsplitW, hwnW, hwfW, _, _⟩ := rootFirst B.ch.slots hwPos hwN
      have hcrWMem : crW ∈ r.log := by rw [hsplitW]; exact List.mem_append.mpr (Or.inr (by simp))
      have hLogSplit : r.log = pre ++ (x :: post) := hsplit
      have hSlots : SlotRun (initial (orderedConfig p large)
          (ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables (pre ++ (x :: post)) r.out.tables :=
        hLogSplit ▸ B.ch.slots
      obtain ⟨mid, _, hpostRun⟩ := SlotRun.splitAtPrefix hSlots
      have hxNext : x.node = mid.next := by
        cases hpostRun with
        | reuse hr => simp [hr] at hxf
        | alloc _ hx => exact hx
      have hInPre : crW ∈ pre := by
        rw [hLogSplit] at hcrWMem
        rcases List.mem_append.mp hcrWMem with h1 | h2
        · exact h1
        · have hge := hpostRun.fresh_ge crW h2 hwfW
          omega
      exact occ_of_earlier_slot B increasing covers hsplit heYHead hwN
        (Or.inr (Or.inr ⟨crW, hInPre, hwfW, hwnW⟩))
  have hpLt : B.F.parentOf u < u := pos_parent_lt B huF huPos
  have hpF : B.F.parentOf u < B.F.size := Nat.lt_trans hpLt huF
  have hjLt : B.F.jumpOf (B.F.parentOf u) < u :=
    Nat.lt_of_le_of_lt (jump_le_self B hpF) hpLt
  exact ⟨huPos, huLt, hpNeF, w_earlier hpLt, w_earlier hjLt⟩

private theorem actualStepInv_succ
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (endpoints : Nat)
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (a : Fin H.vertexCount)
    (ih : ActualStepInv B increasing covers entryRank rankArc flat endpoints a.val) :
    ActualStepInv B increasing covers entryRank rankArc flat endpoints (a.val + 1) := by
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  let W := actualModel B entryRank rankArc flat
  let occ := actualOcc B increasing covers
  let old := actualOld B increasing covers entryRank rankArc flat
  have haLt : a.val < H.vertexCount := a.isLt
  have hStepOld : old (a.val + 1) =
      match S.mapSlot.read (S.vertex a) with
      | none => old a.val
      | some i => ((actualPacking B).jobAt (S.vertex a) i (W.wantMap i)).overlay (old a.val) := by
    change (if hk : a.val < H.vertexCount then _ else _) = _
    rw [dite_eq_left haLt]
  cases ho : S.mapSlot.read (S.vertex a) with
  | none =>
    have hOccEq : occ (a.val + 1) = occ a.val := PrefixOcc.keep S _ _ ho
    have hOldEq : old (a.val + 1) = old a.val := by rw [hStepOld, ho]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu; change occ (a.val + 1) u at hu; rw [hOccEq] at hu; exact ih.live_lt u hu
    · intro u hu; change occ (a.val + 1) u at hu; change (old (a.val + 1) u).parent = B.F.parentOf u; rw [hOccEq] at hu; rw [hOldEq]; exact ih.parent_eq u hu
    · intro u hu; change occ (a.val + 1) u at hu; change (old (a.val + 1) u).jump = B.F.jumpOf u; rw [hOccEq] at hu; rw [hOldEq]; exact ih.jump_eq u hu
    · intro u hu; change occ (a.val + 1) u at hu; change occ (a.val + 1) (B.F.parentOf u); rw [hOccEq] at hu ⊢; exact ih.parent_live u hu
    · intro u hu; change occ (a.val + 1) u at hu; change occ (a.val + 1) (B.F.jumpOf u); rw [hOccEq] at hu ⊢; exact ih.jump_live u hu
    · intro u hu; change occ (a.val + 1) u at hu; change MapBound endpoints (old (a.val + 1) u).parentMap ∧ MapBound endpoints (old (a.val + 1) u).jumpMap; rw [hOccEq] at hu; rw [hOldEq]; exact ih.maps_bound u hu
    · change ExactLiveHops (old (a.val + 1)) B.F.depthOf (occ (a.val + 1)); rw [hOccEq, hOldEq]; exact ih.hops
  | some i =>
    let uNew := (actualDriverAddress r i).val
    let j := (actualPacking B).jobAt (S.vertex a) i (W.wantMap i)
    have hinj : ∀ {i₁ i₂ : Fin (exitTransferDrivers r).size},
        (actualDriverAddress r i₁).val = (actualDriverAddress r i₂).val → i₁ = i₂ :=
      fun h => exitTransferDrivers_address_injective r increasing covers B.full B.ch h
    obtain ⟨huPos, huLt, hpNe, hpOcc, hjpOcc⟩ := parent_of_driver_occ_earlier B increasing covers ho
    have hNotSeed : ¬ actualSeedProbe B uNew := by
      rintro ⟨_, hz | hp0⟩
      · omega
      · exact hpNe hp0
    obtain ⟨hFresh, hOccEq⟩ := PrefixOcc.put S (fun k => (actualDriverAddress r k).val)
      (actualSeedProbe B) ho hinj hNotSeed
    have hOldEq : old (a.val + 1) = j.overlay (old a.val) := by rw [hStepOld, ho]
    have huF : uNew < B.F.size := by rw [B.G.size_eq]; exact huLt
    have hSlotEq : j.slot = uNew := rfl
    have hParEq : j.parent = B.F.parentOf uNew := rfl
    have hBuildEq : j.overlay (old a.val) uNew =
        buildOneSlot (old a.val) (B.F.parentOf uNew) (B.F.jumpOf uNew) (W.wantMap i) := by
      simp [Job.overlay, hSlotEq, hParEq]
      rfl
    have hjOcc : occ a.val (B.F.jumpOf uNew) := by
      cases pos_jump_cases B huF huPos with
      | inl h => rw [h]; exact hpOcc
      | inr h =>
        rw [h]
        exact ih.jump_live _ hjpOcc
    have hSameOld : ∀ u, occ a.val u → j.overlay (old a.val) u = old a.val u := by
      intro u hu
      have hne : u ≠ j.slot := fun he =>
        hFresh (by change PrefixOcc.occ S _ _ a.val j.slot; rw [← he]; exact hu)
      simp [Job.overlay, ite_eq_right hne]
    have hInvF := B.G.layout.valid.exists_forestInvariant.choose_spec
    have hSpecU := hInvF.nodes uNew huF
    have hdown : B.F.depthOf (B.F.parentOf uNew) < B.F.depthOf uNew := by
      have hd := hSpecU.pos_depth huPos
      omega
    have hNewPar : (j.overlay (old a.val) uNew).parent = B.F.parentOf uNew := by
      rw [hBuildEq]
      unfold buildOneSlot
      split <;> rfl
    have hNewJump : (j.overlay (old a.val) uNew).jump = B.F.jumpOf uNew := by
      rw [hBuildEq]
      unfold buildOneSlot
      split
      next heq => simp [Stored.parentOnly, heq]
      next hne =>
        have hc : B.F.jumpOf uNew = B.F.jumpOf (B.F.jumpOf (B.F.parentOf uNew)) :=
          (pos_jump_cases B huF huPos).resolve_left hne
        simp only [Stored.skew]
        rw [ih.jump_eq _ hpOcc, ih.jump_eq _ hjpOcc, ← hc]
    have hWBound : MapBound endpoints (W.wantMap i) :=
      mapBound_wantMap W (fun x => hRank x) i
    have hNewBounds :
        MapBound endpoints (j.overlay (old a.val) uNew).parentMap ∧
        MapBound endpoints (j.overlay (old a.val) uNew).jumpMap := by
      rw [hBuildEq]
      unfold buildOneSlot
      split
      · exact ⟨hWBound, hWBound⟩
      · have hPB := ih.maps_bound _ hpOcc
        have hQB : MapBound endpoints (old a.val (old a.val (B.F.parentOf uNew)).jump).jumpMap := by
          rw [ih.jump_eq _ hpOcc]
          exact (ih.maps_bound _ hjpOcc).2
        exact ⟨hWBound, mapBound_compose hWBound (mapBound_compose hPB.2 hQB)⟩
    have hHopsNew : ExactLiveHops (j.overlay (old a.val)) B.F.depthOf (j.occupy (occ a.val)) := by
      have closedOld : ∀ u, occ a.val u → occ a.val ((old a.val u).parent) := fun u hu => by
        rw [ih.parent_eq u hu]; exact ih.parent_live u hu
      have framed : ExactLiveHops (j.overlay (old a.val)) B.F.depthOf (occ a.val) :=
        ih.hops.frame_on_live closedOld hSameOld (fun _ _ => rfl)
      have hJumpNewOK : JumpOK (j.overlay (old a.val)) B.F.depthOf uNew := by
        by_cases hbr : B.F.jumpOf uNew = B.F.parentOf uNew
        · have hPOnly : j.overlay (old a.val) uNew = Stored.parentOnly (B.F.parentOf uNew) (W.wantMap i) := by
            rw [hBuildEq, buildOneSlot, ite_eq_left hbr]
          exact jumpOK_parentOnly hPOnly hdown
        · have hSkew : j.overlay (old a.val) uNew =
              Stored.skew (B.F.parentOf uNew) (W.wantMap i)
                (old a.val (B.F.parentOf uNew))
                (old a.val (old a.val (B.F.parentOf uNew)).jump) := by
            rw [hBuildEq, buildOneSlot, ite_eq_right hbr]
          have hpEq : j.overlay (old a.val) (B.F.parentOf uNew) = old a.val (B.F.parentOf uNew) :=
            hSameOld _ hpOcc
          have hjpEq : j.overlay (old a.val) (j.overlay (old a.val) (B.F.parentOf uNew)).jump =
              old a.val (old a.val (B.F.parentOf uNew)).jump := by
            rw [hpEq, ih.jump_eq _ hpOcc]
            exact hSameOld _ hjpOcc
          have hSkew' : j.overlay (old a.val) uNew =
              Stored.skew (B.F.parentOf uNew) (W.wantMap i)
                (j.overlay (old a.val) (B.F.parentOf uNew))
                (j.overlay (old a.val) (j.overlay (old a.val) (B.F.parentOf uNew)).jump) := by
            have hjpEq' : j.overlay (old a.val) (old a.val (B.F.parentOf uNew)).jump =
                old a.val (old a.val (B.F.parentOf uNew)).jump := by
              rw [ih.jump_eq _ hpOcc]
              exact hSameOld _ hjpOcc
            rw [hSkew, hpEq, hjpEq']
          exact jumpOK_skew hSkew' hdown
            (framed.jump_path _ hpOcc)
            (by rw [hpEq, ih.jump_eq _ hpOcc]; exact framed.jump_path _ hjpOcc)
      have hParNewPath : ParentPath (j.overlay (old a.val)) B.F.depthOf uNew
          (j.overlay (old a.val) uNew).parent (j.overlay (old a.val) uNew).parentMap := by
        have hdown' : B.F.depthOf (j.overlay (old a.val) uNew).parent < B.F.depthOf uNew := by
          rw [hNewPar]; exact hdown
        have hp1 := ParentPath.cons (read := j.overlay (old a.val)) (rank := B.F.depthOf) uNew
          hdown' (ParentPath.nil _)
        simpa only [compose_identity] using hp1
      refine ⟨?_, ?_⟩
      · intro u hu
        rcases hu with huOld | rfl
        · exact framed.parent_path u huOld
        · exact hParNewPath
      · intro u hu
        rcases hu with huOld | rfl
        · exact framed.jump_path u huOld
        · exact hJumpNewOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      rw [hOccEq] at hu
      rcases hu with rfl | huOld
      · exact huF
      · exact ih.live_lt u huOld
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      change (old (a.val + 1) u).parent = B.F.parentOf u
      rw [hOccEq] at hu; rw [hOldEq]
      rcases hu with rfl | huOld
      · exact hNewPar
      · rw [hSameOld u huOld]; exact ih.parent_eq u huOld
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      change (old (a.val + 1) u).jump = B.F.jumpOf u
      rw [hOccEq] at hu; rw [hOldEq]
      rcases hu with rfl | huOld
      · exact hNewJump
      · rw [hSameOld u huOld]; exact ih.jump_eq u huOld
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) (B.F.parentOf u)
      rw [hOccEq] at hu ⊢
      rcases hu with rfl | huOld
      · exact Or.inr hpOcc
      · exact Or.inr (ih.parent_live u huOld)
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) (B.F.jumpOf u)
      rw [hOccEq] at hu ⊢
      rcases hu with rfl | huOld
      · exact Or.inr hjOcc
      · exact Or.inr (ih.jump_live u huOld)
    · intro u hu
      change PrefixOcc.occ S (fun k => (actualDriverAddress r k).val) (actualSeedProbe B) (a.val + 1) u at hu
      change MapBound endpoints (old (a.val + 1) u).parentMap ∧ MapBound endpoints (old (a.val + 1) u).jumpMap
      rw [hOccEq] at hu; rw [hOldEq]
      rcases hu with rfl | huOld
      · exact hNewBounds
      · rw [hSameOld u huOld]; exact ih.maps_bound u huOld
    · change ExactLiveHops (old (a.val + 1)) B.F.depthOf (occ (a.val + 1))
      have hOccJ : occ (a.val + 1) = j.occupy (occ a.val) := by
        funext x; apply propext; change PrefixOcc.occ S _ _ (a.val + 1) x ↔ _; rw [hOccEq, Job.occupy]; exact or_comm
      rw [hOccJ, hOldEq]
      exact hHopsNew

private theorem actualStepInv_all
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (endpoints : Nat)
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (k : Nat) (hk : k ≤ H.vertexCount) :
    ActualStepInv B increasing covers entryRank rankArc flat endpoints k := by
  induction k with
  | zero => exact actualStepInv_zero B increasing covers entryRank rankArc flat endpoints
  | succ k ih =>
    have hk' : k < H.vertexCount := by omega
    exact actualStepInv_succ B increasing covers entryRank rankArc flat endpoints hRank
      ⟨k, hk'⟩ (ih (by omega))

private theorem actualOcc_eq_min (k : Nat) :
    actualOcc B increasing covers k =
      actualOcc B increasing covers (min k H.vertexCount) := by
  by_cases h : k ≤ H.vertexCount
  · simp [Nat.min_eq_left h]
  · simp only [Nat.min_eq_right (Nat.le_of_not_le h)]
    funext x
    apply propext
    unfold actualOcc PrefixOcc.occ
    constructor
    · rintro (hp | ⟨b, _, hc⟩)
      · exact Or.inl hp
      · exact Or.inr ⟨b, b.isLt, hc⟩
    · rintro (hp | ⟨b, _, hc⟩)
      · exact Or.inl hp
      · exact Or.inr ⟨b, by have := b.isLt; omega, hc⟩

private theorem actualOld_eq_min
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (k : Nat) :
    actualOld B increasing covers entryRank rankArc flat k =
      actualOld B increasing covers entryRank rankArc flat (min k H.vertexCount) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < H.vertexCount
    · have hle : k + 1 ≤ H.vertexCount := h
      rw [Nat.min_eq_left hle]
    · have hge : H.vertexCount ≤ k := Nat.le_of_not_lt h
      have hge1 : H.vertexCount ≤ k + 1 := by omega
      rw [Nat.min_eq_right hge1]
      change (if hk : k < H.vertexCount then _ else _) = _
      rw [dite_eq_right h, ih, Nat.min_eq_right hge]

theorem actual_liveStoreOK_final
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (endpoints : Nat)
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints) :
    LiveStoreOK B.F
      (actualOld B increasing covers entryRank rankArc flat H.vertexCount)
      (actualOcc B increasing covers H.vertexCount) :=
  let inv := actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank
    H.vertexCount (Nat.le_refl _)
  { live_lt := inv.live_lt
    parent_eq := inv.parent_eq
    jump_eq := inv.jump_eq
    parent_live := inv.parent_live
    jump_live := inv.jump_live
    parent_down := fun u hu hd => parent_down_all B (inv.live_lt u hu) hd
    hops := inv.hops }

/-! ### 5. End-to-End `DirectIntegration.directDepthContract` and Built Bank Package -/

end WithBundle

def actualBankRegion
    (slots : Nat) {bits : Nat}
    (hLayout : slots + 18 * slots ≤ 2 ^ bits)
    (bank : WriteResult bits (slots + 18 * slots)) :
    Region bits bank.mem.size :=
  let bl : BankLayout (BankLayout.zeroStart bits) (slots + 18 * slots) slots :=
    BankLayout.direct hLayout (Nat.le_refl _)
  { slots := bl.region.slots
    depthAddr := bl.region.depthAddr
    depthMem := fun v => Nat.lt_of_lt_of_le (bl.region.depthMem v) (Nat.le_of_eq bank.size_eq.symm)
    base := bl.region.base
    recordAddr := bl.region.recordAddr
    recordMem := fun v => Nat.le_trans (bl.region.recordMem v) (Nat.le_of_eq bank.size_eq.symm) }

/-- Complete result of running the EX4.2/EX4.3 packed forest sweep on `H`. -/
structure ActualBuiltBank
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (bits endpoints : Nat) where
  bundle : ActualSweepBundle H p data size_data rank large r
  wFit : Width bits (max r.out.tables.next endpoints)
  hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits
  model : BuiltExit.Model H (exitTransferDrivers r).size
  model_eq : model = actualModel bundle entryRank rankArc flat
  bank : WriteResult bits (r.out.tables.next + 18 * r.out.tables.next)
  bases : Slots Values H.vertexCount
  seedWrites : Nat
  sweepWrites : Nat
  seedWrites_le : seedWrites ≤ 19 * (H.vertexCount + 1)
  sweepWrites_le : sweepWrites ≤ 18 * H.vertexCount
  totalWrites_eq : bank.writes = seedWrites + sweepWrites
  live : Nat → Prop
  ref : Store
  all_live : ∀ u, u < bundle.F.size → live u
  decoded : DecodedOccupied bank.mem (actualBankRegion r.out.tables.next hLayout bank)
    bundle.F ref wFit.tags live
  liveOK : LiveStoreOK bundle.F ref live
  bases_exact : ∀ y : Vertex H, bases.read y = some (model.wantBase y)
  owner_eq : ∀ y : Vertex H, model.owner y = model.forest.nodeKey? (model.forest.label y)
  slotOf : CutPair H → Nat
  slot_key_lt : ∀ (Bcut : CutPair H) {a : Fin (model.forest.realNodeCount + 1)},
    model.forest.nodeKey? a = some Bcut → slotOf Bcut < bundle.F.size
  slot_key_at : ∀ (y : Vertex H) (Acut : CutPair H),
    model.owner y = some Acut →
      ∃ u : Fin bundle.F.size,
        (exitDenseOwnerSlots r bundle.E).read y = some u ∧ u.val = slotOf Acut
  edges : @RouteSlotEdges H (exitTransferDrivers r).size model (fun _ => True)
    (fun i _ => some (model.wantMap i)) slotOf bundle.F ref
  slot_depth_eq : ∀ {Bcut : CutPair H} {a : Fin (model.forest.realNodeCount + 1)},
    model.forest.nodeKey? a = some Bcut →
      bundle.F.depthOf (slotOf Bcut) = model.forest.depth a

private theorem foldTo_writes_le
    {n m bits words slots : Nat} {M : Type} {B : Type} {P : Plan n m}
    (tags : TagsFit bits) (base : Word bits)
    (L : Layout base words slots) (K : Packing n m slots M) (S : Schedule P)
    (Q : DirectCallbacks n m bits words M B)
    (DepthOK : WriteResult bits words → Prop)
    {occ : Nat → Nat → Prop} {old : Nat → Store} {wm : Fin m → M} {wb : Fin n → B}
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) :
    ∀ (fuel start : Nat) (hk : start + fuel = dst)
      (s : PhysicalState n bits words B)
      (h : DirectDepthInv tags base L S DepthOK occ old wb start s),
      (directDepthFoldTo tags base L K S Q DepthOK H dst hd fuel start hk s h).val.bank.writes ≤
        s.bank.writes + 18 * fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro start hk s h
    rw [directDepthFoldTo_zero_val]
    omega
  | succ fuel ih =>
    intro start hk s h
    rw [directDepthFoldTo_succ_val]
    let a : Fin n := ⟨start, by omega⟩
    let t := directDepthEvent tags base L K S Q DepthOK H a s h
    have hTail := ih (start + 1) (by omega) t.val ⟨t.property.core.inv, t.property.depth⟩
    have hStep : t.val.bank.writes ≤ s.bank.writes + 18 := by
      have he := t.property.core.stage_effect
      cases ho : S.mapSlot.read (S.vertex a) with
      | none =>
        have hb : t.val.bank = s.bank := he.1 ho
        rw [hb]
        omega
      | some i =>
        obtain ⟨rj, hbank⟩ := he.2 i ho
        rw [hbank, step_writes]
        omega
    exact Nat.le_trans hTail (by omega)

private theorem foldTo_writes_ge
    {n m bits words slots : Nat} {M : Type} {B : Type} {P : Plan n m}
    (tags : TagsFit bits) (base : Word bits)
    (L : Layout base words slots) (K : Packing n m slots M) (S : Schedule P)
    (Q : DirectCallbacks n m bits words M B)
    (DepthOK : WriteResult bits words → Prop)
    {occ : Nat → Nat → Prop} {old : Nat → Store} {wm : Fin m → M} {wb : Fin n → B}
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) :
    ∀ (fuel start : Nat) (hk : start + fuel = dst)
      (s : PhysicalState n bits words B)
      (h : DirectDepthInv tags base L S DepthOK occ old wb start s),
      s.bank.writes ≤
        (directDepthFoldTo tags base L K S Q DepthOK H dst hd fuel start hk s h).val.bank.writes := by
  intro fuel
  induction fuel with
  | zero =>
    intro start hk s h
    rw [directDepthFoldTo_zero_val]
    exact Nat.le_refl _
  | succ fuel ih =>
    intro start hk s h
    rw [directDepthFoldTo_succ_val]
    let a : Fin n := ⟨start, by omega⟩
    let t := directDepthEvent tags base L K S Q DepthOK H a s h
    have hTail := ih (start + 1) (by omega) t.val ⟨t.property.core.inv, t.property.depth⟩
    have hStep : s.bank.writes ≤ t.val.bank.writes := by
      have he := t.property.core.stage_effect
      cases ho : S.mapSlot.read (S.vertex a) with
      | none =>
        have hb : t.val.bank = s.bank := he.1 ho
        rw [hb]
        exact Nat.le_refl _
      | some i =>
        obtain ⟨rj, hbank⟩ := he.2 i ho
        rw [hbank, step_writes]
        omega
    exact Nat.le_trans hStep hTail

noncomputable def buildActualDirectBank
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
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
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits) :
    ActualBuiltBank H p data size_data rank large r entryRank rankArc flat bits endpoints := by
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  let N := r.out.tables.next
  let words := N + 18 * N
  let bl : BankLayout (BankLayout.zeroStart bits) words N :=
    BankLayout.direct hLayout (Nat.le_refl _)
  let W := actualModel B entryRank rankArc flat
  let S := actualCompactArraySchedule r increasing covers (g := B.g0) B.full B.ch
  let occ := actualOcc B increasing covers
  let old := actualOld B increasing covers entryRank rankArc flat
  let seeds := actualSeeds B
  have hSeedNodup := actualSeeds_nodup B
  let blankBank : WriteResult bits words :=
    ⟨Array.replicate words ⟨0, Nat.two_pow_pos bits⟩, by simp, 0⟩
  have hDepthFit : ∀ v : Fin bl.region.slots, B.F.depthOf v.val < 2 ^ bits := by
    intro v
    have hvF : v.val < B.F.size := by rw [B.G.size_eq]; exact v.isLt
    have hlt := bundle_depthOf_lt B hvF
    rw [B.G.size_eq] at hlt
    exact Nat.lt_of_lt_of_le hlt (Nat.le_trans (Nat.le_max_left N endpoints) wFit.ranks)
  let depthBank := writeDepthColumn bl.column blankBank (fun v => B.F.depthOf v.val) hDepthFit
  have hSeedsFit : (storedCodec wFit.tags).valid seedRecord := by
    have hNpos : 0 < N := bundle_next_pos B
    have hMax : 0 < max N endpoints := Nat.lt_of_lt_of_le hNpos (Nat.le_max_left _ _)
    refine seedRecord_fits (ids := max N endpoints) (endpoints := max N endpoints)
      ⟨by simpa only [Nat.max_self] using wFit.ranks, wFit.tags⟩ hMax ?_
    exact ⟨by simp [Map.identity, RankBound], by simp [Map.identity, RankBound]⟩
  let seedBank := ExitPhysicalSeedPass.run wFit.tags bl.region.base bl.layout hSeedsFit
    seeds depthBank hSeedNodup
  have hOccDepth : OccupiedExact wFit.tags bl.region.base bl.layout depthBank (fun _ => False) (old 0) :=
    fun _ h => h.elim
  have hOcc0 : OccupiedExact wFit.tags bl.region.base bl.layout seedBank (occ 0) (old 0) := by
    have hex := ExitPhysicalSeedPass.run_exact wFit.tags bl.region.base bl.layout hSeedsFit
      seeds depthBank hSeedNodup (fun _ => False) (old := old 0) hOccDepth (fun _ h => h.elim)
    intro u hu
    apply hex u
    have huP : actualSeedProbe B u := (PrefixOcc.zero _ _ _ u).mp hu
    exact Or.inr ((actualSeeds_mem_iff B u).mpr huP)
  have hDepth0 : DepthAgrees seedBank bl.region (fun v => B.F.depthOf v.val) :=
    seedPass_preserves_depthAgrees wFit.tags bl.region.base bl.layout bl.column rfl rfl
      bl.depthBeforeRecords hSeedsFit seeds depthBank hSeedNodup
      (writeDepthColumn_depthAgrees bl.column blankBank _ hDepthFit)
  let blRegion : Region bits seedBank.mem.size :=
    { slots := bl.region.slots
      depthAddr := bl.region.depthAddr
      depthMem := fun v => Nat.lt_of_lt_of_le (bl.region.depthMem v) (Nat.le_of_eq seedBank.size_eq.symm)
      base := bl.region.base
      recordAddr := bl.region.recordAddr
      recordMem := fun v => Nat.le_trans (bl.region.recordMem v) (Nat.le_of_eq seedBank.size_eq.symm) }
  let blLayout : ExitPhysicalOneSlot.Layout blRegion.base seedBank.mem.size blRegion.slots :=
    ⟨bl.layout.address, Nat.le_trans bl.layout.capacity (Nat.le_of_eq seedBank.size_eq.symm)⟩
  let blColumn : Column blRegion (BankLayout.zeroStart bits) := ⟨bl.column.addr_eq⟩
  let seedBank' : WriteResult bits seedBank.mem.size :=
    ⟨seedBank.mem, rfl, seedBank.writes⟩
  let inp : PackedRuntime.Input H N bits :=
    { actualInput B wFit.tags seedBank hLayout entryRank with
      arena := ⟨seedBank.mem, blRegion, wFit.tags⟩ }
  have hRegEq : layoutRegion inp (rfl : inp.arena.mem.size = seedBank.mem.size) = blRegion := rfl
  let K := actualKernel B entryRank rankArc flat
  let lookup := actualLookup B
  have hGeom : Geometry inp W lookup := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      have hd : compactDriver i ∈ exitTransferDrivers r :=
        Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
      obtain ⟨_, _, aF, _, _, _, haF, _, _, _, _, hck, _⟩ :=
        bundle_drivers_provenance B hd
      have hcb : exitBackKey? r (lookup i).1.val = some (W.child i) := by
        have hpos : 0 < (lookup i).1.val := by
          change 0 < (compactDriver i).address
          rw [← haF]
          exact bundle_pos_of_real_image B aF hck
        have hne : (lookup i).1.val ≠ 0 := Nat.ne_of_gt hpos
        have hb : r.out.tables.back[(lookup i).1.val]? = some (some (W.child i)) := by
          change r.out.tables.back[(compactDriver i).address]? = some (some (compactDriver i).child)
          rw [← haF, B.E.back_eq aF, hck]
        simp [exitBackKey?, ite_eq_right hne, hb]
      have hend := physicalSlotEnds_endpoints r N H.root (lookup i).1 hcb
      rcases fin2_cases j with rfl | rfl
      · exact hend.1
      · exact hend.2
    · intro i j
      have hd : compactDriver i ∈ exitTransferDrivers r :=
        Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
      obtain ⟨_, _, aF, _, _, _, haF, hpNe, hup, _, _, _, hpk⟩ :=
        bundle_drivers_provenance B hd
      have hParEq : (lookup i).2.val = (B.up aF).val := by
        change B.F.parentOf (compactDriver i).address = (B.up aF).val
        rw [← haF, B.hUp aF]
      have hpos : 0 < (lookup i).2.val := by
        rw [hParEq, hup]
        exact Nat.pos_of_ne_zero hpNe
      have hne : (lookup i).2.val ≠ 0 := Nat.ne_of_gt hpos
      have hpk' : (buildProperLossForest H rank).nodeKey? (B.E.image (B.up aF)) =
          some (W.parent i) := by
        rw [B.E.parent_eq aF]
        exact hpk
      have hb : r.out.tables.back[(lookup i).2.val]? = some (some (W.parent i)) := by
        rw [hParEq, B.E.back_eq (B.up aF), hpk']
      have hpb : exitBackKey? r (lookup i).2.val = some (W.parent i) := by
        simp [exitBackKey?, ite_eq_right hne, hb]
      have hend := physicalSlotEnds_endpoints r N H.root (lookup i).2 hpb
      rcases fin2_cases j with rfl | rfl
      · exact hend.1
      · exact hend.2
    · intro y hy
      change (actualOwners B).read y = none at hy
      rw [actualOwners_read, Option.map_eq_none_iff] at hy
      rw [exitDenseOwnerSlots_read_none_iff r B.E y] at hy
      change exitDenseOwnerKey? r y = none
      simp [exitDenseOwnerKey?, exitBackKey?, hy]
    · intro y cut hcut
      change (actualOwners B).read y = some cut at hcut
      rw [actualOwners_read] at hcut
      obtain ⟨cutF, hcutF, hcutCast⟩ := Option.map_eq_some_iff.mp hcut
      have hcutVal : cutF.val = cut.val := congrArg Fin.val hcutCast
      rw [exitDenseOwnerSlots_read r B.E y] at hcutF
      dsimp only [exitDenseOwnerCell] at hcutF
      split at hcutF
      · cases hcutF
      next hnz =>
        have hcutEq : cut.val = (selectors (orderedConfig p large) r.out).label y :=
          hcutVal.symm.trans (congrArg Fin.val (Option.some.inj hcutF).symm)
        have hb : ∃ Bcut : CutPair H,
            (buildProperLossForest H rank).nodeKey? (B.E.image cutF) = some Bcut := by
          cases hk : (buildProperLossForest H rank).nodeKey? (B.E.image cutF) with
          | some Bcut => exact ⟨Bcut, rfl⟩
          | none =>
            have h0 : 0 < B.F.size := by rw [B.G.size_eq]; exact bundle_next_pos B
            let z : Fin B.F.size := ⟨0, h0⟩
            have hz : (buildProperLossForest H rank).nodeKey? (B.E.image z) = none := by
              rw [B.E.root_eq h0, buildProperLossForest_nodeKey?_root]
            have hcz := B.E.injective (buildProperLossForest_nodeKey?_inj H rank (hk.trans hz.symm))
            have h0v : cut.val = 0 := hcutVal.symm.trans (congrArg Fin.val hcz)
            exact (hnz (hcutEq.symm.trans h0v)).elim
        obtain ⟨Bcut, hBcut⟩ := hb
        have hback : r.out.tables.back[cut.val]? = some (some Bcut) := by
          rw [← hcutVal]
          exact (B.E.back_eq cutF).trans (congrArg some hBcut)
        have hOwner : W.owner y = some Bcut := by
          change exitDenseOwnerKey? r y = some Bcut
          have hcutNe : cut.val ≠ 0 := by rw [hcutEq]; exact hnz
          rw [exitDenseOwnerKey?, ← hcutEq]
          simp [exitBackKey?, hcutNe, hback]
        have hcb : exitBackKey? r cut.val = some Bcut := by
          have hne' : cut.val ≠ 0 := by rw [hcutEq]; exact hnz
          simp [exitBackKey?, ite_eq_right hne', hback]
        refine ⟨Bcut, hOwner, fun j => ?_⟩
        have hend := physicalSlotEnds_endpoints r N H.root cut hcb
        rcases fin2_cases j with rfl | rfl
        · exact hend.1
        · exact hend.2
  have hInvAll (k : Nat) :=
    actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank
      (min k H.vertexCount) (Nat.min_le_right _ _)
  have hStages : ForestStages blRegion B.F occ old := by
    refine ⟨by rw [B.G.size_eq]; exact Nat.le_refl _, B.G.layout.valid, ?_, ?_, ?_, ?_, ?_⟩
    · intro k u hu
      change actualOcc B increasing covers k u at hu
      rw [actualOcc_eq_min B increasing covers k] at hu
      exact (hInvAll k).live_lt u hu
    · intro k u hu
      change actualOcc B increasing covers k u at hu
      change (actualOld B increasing covers entryRank rankArc flat k u).parent = B.F.parentOf u
      rw [actualOcc_eq_min B increasing covers k] at hu
      rw [actualOld_eq_min B increasing covers entryRank rankArc flat k]
      exact (hInvAll k).parent_eq u hu
    · intro k u hu
      change actualOcc B increasing covers k u at hu
      change (actualOld B increasing covers entryRank rankArc flat k u).jump = B.F.jumpOf u
      rw [actualOcc_eq_min B increasing covers k] at hu
      rw [actualOld_eq_min B increasing covers entryRank rankArc flat k]
      exact (hInvAll k).jump_eq u hu
    · intro k u hu
      change actualOcc B increasing covers k u at hu
      change actualOcc B increasing covers k (B.F.parentOf u)
      rw [actualOcc_eq_min B increasing covers k] at hu ⊢
      exact (hInvAll k).parent_live u hu
    · intro k u hu
      change actualOcc B increasing covers k u at hu
      change actualOcc B increasing covers k (B.F.jumpOf u)
      rw [actualOcc_eq_min B increasing covers k] at hu ⊢
      exact (hInvAll k).jump_live u hu
  have hOwnerLoss : ∀ (y : Vertex H) (cut : Fin N) (Bcut : CutPair H),
      inp.owners.read y = some cut → W.owner y = some Bcut →
      (∀ z, inp.knownLoss cut z = true ↔ H.ProperLoss Bcut z) := by
    intro y cut Bcut hcut hown z
    change (actualOwners B).read y = some cut at hcut
    rw [actualOwners_read] at hcut
    obtain ⟨cutF, hcutF, hcutCast⟩ := Option.map_eq_some_iff.mp hcut
    have hcutVal : cutF.val = cut.val := congrArg Fin.val hcutCast
    rw [exitDenseOwnerSlots_read r B.E y] at hcutF
    dsimp only [exitDenseOwnerCell] at hcutF
    split at hcutF
    · cases hcutF
    next hnz =>
      have hcutEq : cut.val = (selectors (orderedConfig p large) r.out).label y :=
        hcutVal.symm.trans (congrArg Fin.val (Option.some.inj hcutF).symm)
      have hBcutNode : (buildProperLossForest H rank).nodeKey? (B.E.image cutF) = some Bcut := by
        have h0 : W.owner y = (buildProperLossForest H rank).nodeKey?
            ((buildProperLossForest H rank).label y) :=
          exitDenseOwnerKey?_eq_canonical r B.E y
        have hFin : (⟨(selectors (orderedConfig p large) r.out).label y,
            B.E.label_lt y True.intro⟩ : Fin B.F.size) = cutF :=
          Fin.ext (hcutEq.symm.trans hcutVal.symm)
        have hLab : B.E.image cutF = (buildProperLossForest H rank).label y := by
          rw [← hFin]; exact B.E.label_eq y True.intro
        rw [hLab, ← h0]
        exact hown
      have hCan : Bcut.fst < Bcut.snd :=
        buildProperLossForest_realKeys_canonical H rank Bcut (nodeKeyOfList?_mem hBcutNode)
      have hSlotEq : physicalPairSlot? (orderedConfig p large) r.out.tables Bcut = some cut.val :=
        (B.hSlot Bcut cut.val).mpr ⟨cutF, hcutVal, hBcutNode⟩
      have hLabLt : (selectors (orderedConfig p large) r.out).label z < B.F.size :=
        B.E.label_lt z True.intro
      have hCutLt : cut.val < B.F.size := by rw [B.G.size_eq]; exact cut.isLt
      have hPos : 0 < cut.val := Nat.pos_of_ne_zero (by rw [hcutEq]; exact hnz)
      have iterParent_eq_climb : ∀ (k u : Nat), B.F.iterParent k u = climb B.F.parentOf k u := by
        intro k
        induction k with
        | zero => intro u; rfl
        | succ k ih =>
          intro u
          have hcl : climb B.F.parentOf (k + 1) u = climb B.F.parentOf k (B.F.parentOf u) := by
            clear ih
            induction k generalizing u with
            | zero => rfl
            | succ m ihm => exact congrArg B.F.parentOf (ihm u)
          rw [hcl]
          exact ih (B.F.parentOf u)
      have hAncIff : B.F.decideAncestor cut.val ((selectors (orderedConfig p large) r.out).label z) = true ↔
          ∃ k, climb B.F.parentOf k ((selectors (orderedConfig p large) r.out).label z) = cut.val := by
        rw [B.G.layout.valid.decideAncestor_eq_true_iff hCutLt hLabLt]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k, (iterParent_eq_climb k _).symm.trans hk⟩
        · rintro ⟨k, hk⟩; exact ⟨k, (iterParent_eq_climb k _).trans hk⟩
      change (decide (0 < cut.val) &&
        B.F.decideAncestor cut.val ((selectors (orderedConfig p large) r.out).label z)) = true ↔
        H.ProperLoss Bcut z
      rw [Bool.and_eq_true, decide_eq_true_eq, hAncIff]
      constructor
      · rintro ⟨_, hk⟩
        exact ((B.hLoss Bcut z).mpr ⟨cut.val, hSlotEq, hk⟩).2
      · intro hloss
        refine ⟨hPos, ?_⟩
        obtain ⟨n', hn', hk⟩ := (B.hLoss Bcut z).mp ⟨hCan, hloss⟩
        have hEq : n' = cut.val := Option.some.inj (hn'.symm.trans hSlotEq)
        rwa [← hEq]
  let slotOf (Bcut : CutPair H) : Nat :=
    (physicalPairSlot? (orderedConfig p large) r.out.tables Bcut).getD 0
  have hSlotOf_nodeKey : ∀ {Bcut : CutPair H} {v : Fin B.F.size},
      (buildProperLossForest H rank).nodeKey? (B.E.image v) = some Bcut →
      slotOf Bcut = v.val := by
    intro Bcut v hk
    have hp : physicalPairSlot? (orderedConfig p large) r.out.tables Bcut = some v.val :=
      (B.hSlot Bcut v.val).mpr ⟨v, rfl, hk⟩
    simp [slotOf, hp]
  have hSlotOf_edge_child (i : Fin (exitTransferDrivers r).size) :
      slotOf (W.child i) = (lookup i).1.val := by
    have hd : compactDriver i ∈ exitTransferDrivers r :=
      Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
    obtain ⟨_, _, aF, _, _, _, haF, _, _, _, _, hck, _⟩ := bundle_drivers_provenance B hd
    have hs := hSlotOf_nodeKey hck
    exact hs.trans haF
  have hSlotOf_edge_parent (i : Fin (exitTransferDrivers r).size) :
      slotOf (W.parent i) = (lookup i).2.val := by
    have hd : compactDriver i ∈ exitTransferDrivers r :=
      Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
    obtain ⟨_, _, aF, _, _, _, haF, _, hup, _, _, _, hpk⟩ := bundle_drivers_provenance B hd
    have hpk' : (buildProperLossForest H rank).nodeKey? (B.E.image (B.up aF)) =
        some (W.parent i) := by
      change (buildProperLossForest H rank).nodeKey? (B.E.image (B.up aF)) =
        some (compactDriver i).parent
      rw [B.E.parent_eq aF]
      exact hpk
    have hs := hSlotOf_nodeKey hpk'
    have hpar : (lookup i).2.val = (B.up aF).val := by
      change B.F.parentOf (compactDriver i).address = (B.up aF).val
      rw [← haF, B.hUp aF]
    exact hs.trans hpar.symm
  have hActualOld_parentMap_eq :
      ∀ (k : Nat), k ≤ H.vertexCount →
      ∀ (i : Fin (exitTransferDrivers r).size),
        occ k (actualDriverAddress r i).val →
        (old k (actualDriverAddress r i).val).parentMap = W.wantMap i := by
    intro k hk
    induction k with
    | zero =>
      intro i hiOcc
      have h0 : occ 0 (actualDriverAddress r i).val ↔
          actualSeedProbe B (actualDriverAddress r i).val :=
        PrefixOcc.zero _ _ _ _
      have hp0 := ((h0.mp hiOcc).2)
      have hd : compactDriver i ∈ exitTransferDrivers r :=
        Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
      obtain ⟨_, _, aF, _, _, _, haF, hpNe, _, _, _, hck, _⟩ :=
        bundle_drivers_provenance B hd
      have hpos : 0 < (actualDriverAddress r i).val := by
        change 0 < (compactDriver i).address
        rw [← haF]; exact bundle_pos_of_real_image B aF hck
      have hphys : actualPhysicalParent r (actualDriverAddress r i).val =
          B.F.parentOf (actualDriverAddress r i).val := by
        unfold actualPhysicalParent
        have hlt : (actualDriverAddress r i).val < B.F.size := by
          rw [B.G.size_eq]; exact (actualDriverAddress r i).isLt
        rw [(readRecordWords_spec B.G.layout hlt).1] <;> rfl
      rcases hp0 with hz | hpz
      · omega
      · exact absurd hpz (by rw [← hphys]; exact hpNe)
    | succ k ih =>
      intro i hiOcc
      let a : Fin H.vertexCount := ⟨k, hk⟩
      have hStepOld : old (k + 1) =
          match S.mapSlot.read (S.vertex a) with
          | none => old k
          | some j => ((actualPacking B).jobAt (S.vertex a) j (W.wantMap j)).overlay (old k) := by
        change (if hlt : k < H.vertexCount then _ else _) = _
        rw [dite_eq_left a.isLt]
      cases ho : S.mapSlot.read (S.vertex a) with
      | none =>
        have hOccEq := PrefixOcc.keep S (fun q => (actualDriverAddress r q).val)
          (actualSeedProbe B) ho
        change ((old (k + 1)) (actualDriverAddress r i).val).parentMap = W.wantMap i
        rw [hStepOld, ho]
        dsimp only
        have hOccK : PrefixOcc.occ S (fun q => (actualDriverAddress r q).val)
            (actualSeedProbe B) (a.val + 1) (actualDriverAddress r i).val := hiOcc
        rw [hOccEq] at hOccK
        exact ih (Nat.le_of_lt hk) i hOccK
      | some j =>
        have hinj : ∀ {i₁ i₂ : Fin (exitTransferDrivers r).size},
            (actualDriverAddress r i₁).val = (actualDriverAddress r i₂).val → i₁ = i₂ :=
          fun h => exitTransferDrivers_address_injective r increasing covers B.full B.ch h
        have hNotSeed : ¬ actualSeedProbe B (actualDriverAddress r j).val := by
          obtain ⟨huPos, _, hpNe, _, _⟩ := parent_of_driver_occ_earlier B increasing covers ho
          rintro ⟨_, hz | hp0⟩
          · omega
          · exact hpNe hp0
        obtain ⟨_, hOccEq⟩ := PrefixOcc.put S (fun q => (actualDriverAddress r q).val)
          (actualSeedProbe B) ho hinj hNotSeed
        have hiPut : (actualDriverAddress r i).val = (actualDriverAddress r j).val ∨
            occ k (actualDriverAddress r i).val := by
          have hmem : PrefixOcc.occ S (fun q => (actualDriverAddress r q).val)
              (actualSeedProbe B) (a.val + 1) (actualDriverAddress r i).val := hiOcc
          rw [hOccEq] at hmem
          exact hmem
        by_cases heq : (actualDriverAddress r i).val = (actualDriverAddress r j).val
        · have hij : i = j := hinj heq
          subst hij
          change ((old (k + 1)) (actualDriverAddress r i).val).parentMap = W.wantMap i
          rw [hStepOld, ho]
          dsimp only
          change ((actualPacking B).jobAt (S.vertex a) i (W.wantMap i) |>.overlay (old k)
            ((actualPacking B).jobAt (S.vertex a) i (W.wantMap i)).slot).parentMap = W.wantMap i
          simp only [Job.overlay, ↓reduceIte, buildOneSlot]
          split <;> rfl
        · have hiOld : occ k (actualDriverAddress r i).val := hiPut.resolve_left heq
          have hSame : ((actualPacking B).jobAt (S.vertex a) j (W.wantMap j)).overlay
              (old k) (actualDriverAddress r i).val = old k (actualDriverAddress r i).val := by
            simp [Job.overlay, actualPacking, Packing.jobAt, heq]
          change ((old (k + 1)) (actualDriverAddress r i).val).parentMap = W.wantMap i
          rw [hStepOld, ho]
          dsimp only
          rw [hSame]
          exact ih (Nat.le_of_lt hk) i hiOld
  have mkEdges : ∀ (k : Nat), k ≤ H.vertexCount →
      RouteSlotEdges W (fun i _ => some (W.wantMap i)) slotOf B.F (old k)
        (S := fun i => occ k (slotOf (W.child i))) := by
    intro k hk
    have hInvK := actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank k hk
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [hSlotOf_edge_child i] at hi ⊢
      rw [hSlotOf_edge_parent i]
      exact hInvK.parent_eq _ hi
    · intro i hi
      rw [hSlotOf_edge_child i] at hi ⊢
      exact hActualOld_parentMap_eq k hk i hi
    · intro i hi
      rw [hSlotOf_edge_child i] at hi ⊢
      rw [hSlotOf_edge_parent i]
      have hd : compactDriver i ∈ exitTransferDrivers r :=
        Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
      obtain ⟨_, _, aF, _, _, _, haF, hpNe, _, _, _, hck, _⟩ := bundle_drivers_provenance B hd
      have hpos : 0 < (lookup i).1.val := by
        change 0 < (compactDriver i).address
        rw [← haF]; exact bundle_pos_of_real_image B aF hck
      have hltF : (lookup i).1.val < B.F.size := hInvK.live_lt _ hi
      have hdp := depth_pos_of_pos B hltF hpos
      exact parent_down_all B hltF hdp
  have anc_of_root : ∀ {x y : CanonNode H rank},
      IsForestAncestor W.forest.parent x y →
      y = W.forest.rootNode → x = W.forest.rootNode := by
    intro x y h
    induction h with
    | refl => exact id
    | step w _ ih =>
      intro hw
      subst hw
      exact ih (buildProperLossForest_parent_root H rank)
  have mkSourcePath : ∀ (k : Nat), k ≤ H.vertexCount →
      ∀ (a : Fin H.vertexCount), a.val ≤ k →
      ∀ (cut : Fin N) (Bcut : CutPair H) (s : Vertex H),
      (buildProperLossForest H rank).nodeKey? (B.E.image (Fin.cast B.G.size_eq.symm cut)) = some Bcut →
      rank s < rank (S.vertex a) →
      H.ProperLoss Bcut s →
      SourceAt inp W S B.F (occ k) (old k) a cut Bcut s := by
    intro k hk a haLe cut Bcut s hCutKey hsRank hsProper
    let cutF : Fin B.F.size := Fin.cast B.G.size_eq.symm cut
    change (buildProperLossForest H rank).nodeKey? (B.E.image cutF) = some Bcut at hCutKey
    obtain ⟨b, hb⟩ := S.covers s
    change S.vertex b = s at hb
    have hbLt : b.val < a.val := by
      apply (S.rank_lt_rank_iff b a).mp
      change rank (S.vertex b) < rank (S.vertex a)
      rw [hb]; exact hsRank
    have h0 : 0 < B.F.size := by rw [B.G.size_eq]; exact bundle_next_pos B
    have hLabNZ : (selectors (orderedConfig p large) r.out).label s ≠ 0 := by
      intro hz
      let z0 : Fin B.F.size := ⟨0, h0⟩
      have hFin0 : (⟨(selectors (orderedConfig p large) r.out).label s,
          B.E.label_lt s True.intro⟩ : Fin B.F.size) = z0 := Fin.ext hz
      have hLab0 : B.E.image z0 = W.forest.label s := by
        rw [← hFin0]; exact B.E.label_eq s True.intro
      have hRootEq : W.forest.label s = W.forest.rootNode := by
        rw [← hLab0]; exact B.E.root_eq h0
      have hAnc : IsForestAncestor W.forest.parent (B.E.image cutF) (W.forest.label s) :=
        (buildProperLossForest_properLoss_iff_of_node rankArc B.distinctRanks flat hCutKey s).mp hsProper
      have hCutRoot : B.E.image cutF = (buildProperLossForest H rank).rootNode :=
        anc_of_root hAnc hRootEq
      rw [hCutRoot, buildProperLossForest_nodeKey?_root] at hCutKey
      cases hCutKey
    let u : Fin N := ⟨(selectors (orderedConfig p large) r.out).label s, by
      dsimp only [N]; rw [← B.G.size_eq]; exact B.E.label_lt s True.intro⟩
    let uF : Fin B.F.size := ⟨u.val, by rw [B.G.size_eq]; exact u.isLt⟩
    have huOwn : inp.owners.read s = some u := by
      change (actualOwners B).read s = some u
      rw [actualOwners_read, exitDenseOwnerSlots_read]
      simp [exitDenseOwnerCell, hLabNZ, u, Fin.cast]
    have huOccA : occ a.val u.val :=
      occ_of_rank_lt_vertex B increasing covers hsRank u.isLt rfl
    have occ_mono : ∀ {k₁ k₂ x : Nat}, k₁ ≤ k₂ → occ k₁ x → occ k₂ x := by
      intro k₁ k₂ x hkLe
      rintro (h | ⟨c, hc, hcr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, Nat.lt_of_lt_of_le hc hkLe, hcr⟩
    have huOcc : occ k u.val := occ_mono haLe huOccA
    have hSOwn : ∃ As, W.owner s = some As ∧
        (buildProperLossForest H rank).nodeKey? (B.E.image uF) = some As := by
      cases hk : (buildProperLossForest H rank).nodeKey? (B.E.image uF) with
      | some As =>
        refine ⟨As, ?_, rfl⟩
        have h0' := exitDenseOwnerKey?_eq_canonical r B.E s
        have hLab : B.E.image uF = (buildProperLossForest H rank).label s :=
          B.E.label_eq s True.intro
        rw [hLab] at hk
        exact h0'.trans hk
      | none =>
        have hz := B.E.injective (buildProperLossForest_nodeKey?_inj H rank
          (hk.trans ((congrArg (buildProperLossForest H rank).nodeKey? (B.E.root_eq h0)).trans
            (buildProperLossForest_nodeKey?_root H rank)).symm))
        exact absurd (congrArg Fin.val hz) hLabNZ
    obtain ⟨As, hAsOwn, hAsKey⟩ := hSOwn
    have hAnc : IsForestAncestor W.forest.parent (B.E.image cutF) (W.forest.label s) :=
      (buildProperLossForest_properLoss_iff_of_node rankArc B.distinctRanks flat hCutKey s).mp hsProper
    have hAncF : IsForestAncestor W.forest.parent (B.E.image cutF) (B.E.image uF) := by
      change IsForestAncestor (buildProperLossForest H rank).parent
        (B.E.image cutF) (B.E.image uF)
      rw [B.E.label_eq s True.intro]
      exact hAnc
    have hInvF := B.G.layout.valid.exists_forestInvariant.choose_spec
    have hUpLe : ∀ v : Fin B.F.size, (B.up v).val ≤ v.val := by
      intro v
      rw [B.hUp v]
      exact (FinalEmbeddingAncestry.valid_parent_slot_order B.G.layout.valid).1 v.val v.isLt
    have facts := RouteForestFacts.of_build rankArc B.distinctRanks flat
    let S_k : Fin (exitTransferDrivers r).size → Prop := fun i => occ k (slotOf (W.child i))
    have hRouteLive : RoutePathEdgeLive W S_k (B.E.image cutF) s := by
      refine RoutePathEdgeLive.of_driverCoverage
        (fun node {_ _} hk hp => actualModel_driverCoverage B entryRank rankArc flat hk hp)
        (fun i _ hBelow => ?_)
      change occ k (slotOf (W.child i))
      have hd : compactDriver i ∈ exitTransferDrivers r :=
        Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
      obtain ⟨_, _, aF, _, _, _, haF, hpNe, _, _, _, hck, _⟩ := bundle_drivers_provenance B hd
      have hNodeEq : W.edgeNode i = B.E.image aF := by
        apply buildProperLossForest_nodeKey?_inj H rank
        exact (W.childKey i).trans hck.symm
      have hAncEdge : IsForestAncestor W.forest.parent (B.E.image aF) (B.E.image uF) := by
        have hBelow' := hBelow
        change IsForestAncestor (buildProperLossForest H rank).parent
          (W.edgeNode i) ((buildProperLossForest H rank).label s) at hBelow'
        rw [hNodeEq, ← B.E.label_eq s True.intro] at hBelow'
        exact hBelow'
      have haLeU : aF.val ≤ u.val :=
        FinalEmbeddingAncestry.physical_le_of_image B.E hAncEdge hUpLe
      have hSlotChild : slotOf (W.child i) = aF.val := hSlotOf_nodeKey hck
      rw [hSlotChild]
      have haPos : 0 < aF.val := bundle_pos_of_real_image B aF hck
      have huPos : 0 < u.val := Nat.lt_of_lt_of_le haPos haLeU
      have haLtN : aF.val < N := by dsimp only [N]; rw [← B.G.size_eq]; exact aF.isLt
      have hphysA : actualPhysicalParent r aF.val = B.F.parentOf aF.val := by
        unfold actualPhysicalParent
        rw [(readRecordWords_spec B.G.layout aF.isLt).1] <;> rfl
      have hpNeFA : B.F.parentOf aF.val ≠ 0 := by
        rw [← hphysA]
        have hpNe' : actualPhysicalParent r aF.val ≠ 0 := haF.symm ▸ hpNe
        exact hpNe'
      by_cases hEqAU : aF.val = u.val
      · rw [hEqAU]; exact huOcc
      · have haLtU : aF.val < u.val := Nat.lt_of_le_of_ne haLeU hEqAU
        have hpNeFU : B.F.parentOf u.val ≠ 0 := by
          intro hpu0
          have hPhysAU := FinalEmbeddingAncestry.physical_ancestor_of_image B.E hAncEdge
          have auxRoot : ∀ {x y : Nat},
              PaperB.ExitPublishedSlotChronology.PhysicalAncestor
                (FinalEmbeddingAncestry.slotEdge B.up) x y →
              B.F.parentOf x = 0 → y = x ∨ y = 0 := by
            intro x y hp
            induction hp with
            | here x => intro _; exact Or.inl rfl
            | @up x m y hedge _ ih =>
              intro hpx
              obtain ⟨v, hvx, hvm⟩ := hedge
              subst hvx
              have hm0 : m = 0 := by rw [← hvm, B.hUp v, hpx]
              subst hm0
              rcases ih (root_parent_zero B B.G.layout.valid) with rfl | rfl
              · exact Or.inr rfl
              · exact Or.inr rfl
          rcases auxRoot hPhysAU hpu0 with heq | hz
          · exact hEqAU heq
          · exact absurd hz (Nat.ne_of_gt haPos)
        obtain ⟨preU, xU, postU, hsplitU, hxnU, hxfU, hpreU, _⟩ := rootFirst B.ch.slots huPos u.isLt
        obtain ⟨preA, xA, postA, hsplitA, hxnA, hxfA, _, _⟩ := rootFirst B.ch.slots haPos haLtN
        have hxAMem : xA ∈ r.log := by rw [hsplitA]; exact List.mem_append.mpr (Or.inr (by simp))
        have hInPreU : xA ∈ preU := by
          have hxU := hxAMem
          rw [hsplitU] at hxU
          rcases List.mem_append.mp hxU with h1 | h2
          · exact h1
          · have hLogU : SlotRun (initial (orderedConfig p large)
                (ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables
                (preU ++ xU :: postU) r.out.tables := hsplitU ▸ B.ch.slots
            obtain ⟨midU, _, hpostRun⟩ := SlotRun.splitAtPrefix hLogU
            have hxUNext : xU.node = midU.next := by
              cases hpostRun with
              | reuse hr => simp [hr] at hxfU
              | alloc _ hx => exact hx
            have hge := hpostRun.fresh_ge xA h2 hxfA
            omega
        have hRankXA : rank xA.head < rank xU.head :=
          rank_lt_of_mem_log_prefix r B.full hsplitU hInPreU
        obtain ⟨eS, heSMem, heSHead⟩ := logHeadCovers r B.full s
        have heSNode : eS.node = u.val :=
          (r.logLabels eS heSMem).symm.trans (by rw [heSHead])
        have hRankXU : rank xU.head ≤ rank s := by
          rw [← heSHead]
          have hm := heSMem
          rw [hsplitU] at hm
          rcases List.mem_append.mp hm with h1 | h2
          · exact absurd heSNode (hpreU eS h1)
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exact Nat.le_refl _
            · have hpw := logRankPairwise r B.full
              rw [hsplitU] at hpw
              have hpw2 := (List.pairwise_append.mp hpw).2.1
              exact Nat.le_of_lt ((List.pairwise_cons.mp hpw2).1 eS h3)
        have hRankLtA : rank xA.head < rank (S.vertex a) :=
          Nat.lt_trans (Nat.lt_of_lt_of_le hRankXA hRankXU) hsRank
        obtain ⟨crA, jA, hcrAMem, hcrAFresh, hcrANode, _, _, haddrA, hSA⟩ :=
          slot_has_driver_of_pos_parent B increasing covers haPos haLtN hpNeFA
        have hcrEq : crA = xA :=
          unique_fresh_in_log B haPos haLtN hcrAMem hcrAFresh hcrANode hxAMem hxfA hxnA
        subst crA
        obtain ⟨bA, hbA⟩ := S.covers xA.head
        change S.vertex bA = xA.head at hbA
        have hbALt : bA.val < a.val := by
          apply (S.rank_lt_rank_iff bA a).mp
          change rank (S.vertex bA) < rank (S.vertex a)
          rw [hbA]; exact hRankLtA
        exact occ_mono haLe
          (Or.inr ⟨bA, hbALt, jA, by rw [hbA]; exact hSA, haddrA.symm⟩)
    obtain ⟨rt⟩ := Route.nonempty_of_forestAncestor facts
      (exitDenseOwnerKey?_eq_canonical r B.E s) hCutKey hAnc hRouteLive
    have hInvK := actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank k hk
    have hOK : LiveStoreOK B.F (old k) (occ k) :=
      { live_lt := hInvK.live_lt
        parent_eq := hInvK.parent_eq
        jump_eq := hInvK.jump_eq
        parent_live := hInvK.parent_live
        jump_live := hInvK.jump_live
        parent_down := fun v hv hd => parent_down_all B (hInvK.live_lt v hv) hd
        hops := hInvK.hops }
    have hpPath := route_parentPath rt (mkEdges k hk) hAsOwn
    have hCutDepth : inp.depth.read cut = B.F.depthOf cut.val := by
      simp [inp, actualInput, StaticHeadSweep.Slots.read]
    have hAncPhys : PaperB.ExitPublishedSlotChronology.PhysicalAncestor
        (FinalEmbeddingAncestry.slotEdge B.up) uF.val cut.val :=
      FinalEmbeddingAncestry.physical_ancestor_of_image B.E hAncF
    have hDepthLe : B.F.depthOf cut.val ≤ B.F.depthOf u.val := by
      have aux : ∀ {x y : Nat},
          PaperB.ExitPublishedSlotChronology.PhysicalAncestor
            (FinalEmbeddingAncestry.slotEdge B.up) x y →
          x < B.F.size → B.F.depthOf y ≤ B.F.depthOf x := by
        intro x y hp
        induction hp with
        | here _ => intro _; exact Nat.le_refl _
        | @up x m y hedge _ ih =>
          intro hxF
          obtain ⟨v, hvx, hvm⟩ := hedge
          subst hvx
          have hparLt : (B.up v).val < B.F.size := (B.up v).isLt
          have hmLe := ih (by rw [← hvm]; exact hparLt)
          rw [← hvm, B.hUp v] at hmLe
          by_cases hv0 : v.val = 0
          · have hp0 : B.F.parentOf v.val = 0 := by rw [hv0]; exact hInvF.root_parent
            rw [hv0]; rw [hp0] at hmLe; exact hmLe
          · have hvPos : 0 < v.val := Nat.pos_of_ne_zero hv0
            have hdStep : B.F.depthOf (B.F.parentOf v.val) ≤ B.F.depthOf v.val := by
              have hdn := depth_pos_of_pos B v.isLt hvPos
              exact Nat.le_of_lt (parent_down_all B v.isLt hdn)
            exact Nat.le_trans hmLe hdStep
      exact aux hAncPhys uF.isLt
    have hAncDepth := (B.G.layout.valid.ancestorAtDepth_spec uF.isLt hDepthLe).2.2
    have hEval : Map.eval (PriorBase.accumulated (foldFused B.F (old k) u.val (inp.depth.read cut)))
        (W.wantBase s) = W.ref Bcut s := by
      have hSlotU : slotOf As = u.val := hSlotOf_nodeKey hAsKey
      have hSlotCut : slotOf Bcut = cut.val := hSlotOf_nodeKey hCutKey
      rw [hSlotU, hSlotCut] at hpPath
      rw [hCutDepth]
      rw [live_accumulated_foldFused_of_path hOK huOcc hpPath hAncDepth]
      exact rt.actual_exact (fun i _ => some (W.wantMap i)) (fun _ _ => rfl)
    exact ⟨⟨b, hbLt, hb⟩, u, huOwn, huOcc, hEval⟩
  have hInstallSource : ∀ (a : Fin H.vertexCount) (i : Fin (exitTransferDrivers r).size),
      S.mapSlot.read (S.vertex a) = some i → ∀ j : Fin 2,
      W.slot (W.parent i) (W.endpoint (W.child i) j) = none →
      SourceAt inp W S B.F (occ a.val) (old a.val) a (lookup i).2
        (W.parent i) (W.endpoint (W.child i) j) := by
    intro a i hi j hj
    let z := W.endpoint (W.child i) j
    have hd : compactDriver i ∈ exitTransferDrivers r :=
      Array.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩
    obtain ⟨_, _, aF, _, _, _, haF, _, hup, _, _, hck, hpk⟩ :=
      bundle_drivers_provenance B hd
    have hParEq : (lookup i).2.val = (B.up aF).val := by
      change B.F.parentOf (compactDriver i).address = (B.up aF).val
      rw [← haF, B.hUp aF]
    have hCutKey : (buildProperLossForest H rank).nodeKey?
        (B.E.image (Fin.cast B.G.size_eq.symm (lookup i).2)) =
        some (W.parent i) := by
      have hImgEq : B.E.image (Fin.cast B.G.size_eq.symm (lookup i).2) = B.E.image (B.up aF) :=
        congrArg B.E.image (Fin.ext hParEq)
      rw [hImgEq, B.E.parent_eq aF]
      exact hpk
    have hNotMem : ¬ (W.parent i).Mem z := (W.slot_none _ _).mp hj
    have hLost : H.Lost (W.parent i) z :=
      buildProperLossForest_edge_endpoints_lost rankArc flat
        (W.childKey i) (W.parentKey i) z (W.endpoint_mem (W.child i) j)
    have hProper : H.ProperLoss (W.parent i) z := ⟨hLost, hNotMem⟩
    -- Prove `rank z < rank (S.vertex a)` via `W.owner (S.vertex a) = some (W.child i)`.
    have hySlot : actualSlot r (S.vertex a) = some (actualDriverAddress r i) := by
      have hr := (S.slot_exact (S.vertex a) i).mp hi
      have hf : (actualP r).firstAt (S.vertex a) (actualDriverAddress r i) :=
        (driverPlan_firstAt_iff r increasing covers (S.vertex a) (actualDriverAddress r i)).mp hr
      exact (actualSlot_exact r B.full B.ch (S.vertex a) (actualDriverAddress r i)).mpr hf
    obtain ⟨eY, heYHit, heYNode⟩ : ∃ eY, headLookup r (S.vertex a) = some eY ∧
        eY.node = (actualDriverAddress r i).val := by
      cases hl : headLookup r (S.vertex a) with
      | none => simp [actualSlot, actualCreationEvent, hl] at hySlot
      | some eY =>
        simp only [actualSlot, actualCreationEvent, hl] at hySlot
        split at hySlot
        · exact ⟨eY, rfl, congrArg Fin.val (Option.some.inj hySlot)⟩
        · cases hySlot
    obtain ⟨heYMem, _, _, heYHead⟩ := (headLookup_eq_some_iff r B.full (S.vertex a) eY).mp heYHit
    have hLabY : (selectors (orderedConfig p large) r.out).label (S.vertex a) = aF.val := by
      have h1 : (selectors (orderedConfig p large) r.out).label (S.vertex a) = eY.node := by
        rw [← heYHead]
        exact r.logLabels eY heYMem
      exact h1.trans (heYNode.trans haF.symm)
    have hOwnY : W.owner (S.vertex a) = some (W.child i) := by
      have h0' : W.owner (S.vertex a) = W.forest.nodeKey? (W.forest.label (S.vertex a)) :=
        exitDenseOwnerKey?_eq_canonical r B.E (S.vertex a)
      have hLabImg : W.forest.label (S.vertex a) = B.E.image aF := by
        have hFinY : (⟨(selectors (orderedConfig p large) r.out).label (S.vertex a),
            B.E.label_lt (S.vertex a) True.intro⟩ : Fin B.F.size) = aF := Fin.ext hLabY
        change (buildProperLossForest H rank).label (S.vertex a) = B.E.image aF
        rw [← hFinY]
        exact (B.E.label_eq (S.vertex a) True.intro).symm
      rw [h0', hLabImg]
      exact hck
    have hProperChild := W.ownerProper (S.vertex a) (W.child i) hOwnY
    have hzRank : rank z < rank (S.vertex a) :=
      properLoss_follows_endpoints rankArc flat hProperChild
        (W.endpoint_mem (W.child i) j)
    exact mkSourcePath a.val (Nat.le_of_lt a.isLt) a (Nat.le_refl _) (lookup i).2
      (W.parent i) z hCutKey hzRank hProper
  have hBaseSource : ∀ (a : Fin H.vertexCount) (cut : Fin N) (Bcut : CutPair H),
      inp.owners.read (S.vertex a) = some cut → W.owner (S.vertex a) = some Bcut →
      ∀ s, RowSource inp cut (S.vertex a) s (W.endpoint Bcut) →
        SourceAt inp W S B.F (occ (a.val + 1)) (old (a.val + 1)) a cut Bcut s := by
    intro a cut Bcut hcut hBcut s hs
    have hCutKey : (buildProperLossForest H rank).nodeKey?
        (B.E.image (Fin.cast B.G.size_eq.symm cut)) = some Bcut := by
      change (actualOwners B).read (S.vertex a) = some cut at hcut
      rw [actualOwners_read] at hcut
      obtain ⟨cutF, hcutF, hcutCast⟩ := Option.map_eq_some_iff.mp hcut
      have hcutVal : cutF.val = cut.val := congrArg Fin.val hcutCast
      rw [exitDenseOwnerSlots_read r B.E (S.vertex a)] at hcutF
      dsimp only [exitDenseOwnerCell] at hcutF
      split at hcutF
      · cases hcutF
      next hnz =>
        have hcutEq : cut.val = (selectors (orderedConfig p large) r.out).label (S.vertex a) :=
          hcutVal.symm.trans (congrArg Fin.val (Option.some.inj hcutF).symm)
        have hFin : (⟨(selectors (orderedConfig p large) r.out).label (S.vertex a),
            B.E.label_lt (S.vertex a) True.intro⟩ : Fin B.F.size) =
            Fin.cast B.G.size_eq.symm cut := Fin.ext hcutEq.symm
        have hLab : B.E.image (Fin.cast B.G.size_eq.symm cut) =
            (buildProperLossForest H rank).label (S.vertex a) := by
          rw [← hFin]; exact B.E.label_eq (S.vertex a) True.intro
        rw [hLab, ← exitDenseOwnerKey?_eq_canonical r B.E (S.vertex a)]
        exact hBcut
    rcases hs with ⟨⟨e, heMem, heSrc⟩, _, _, hLoss⟩
    have heRow : e ∈ ForestIncomingRaw.row H (ForestIncomingRaw.prepare H) (S.vertex a) := heMem
    have hMemRow := (ForestIncomingRaw.mem_row H e.1 (S.vertex a) e.2).mp heRow
    have hArc : H.HasQuotientArc s (S.vertex a) := by
      have hsEq : e.1 = s := heSrc
      subst hsEq
      exact ⟨e.2, hMemRow.1, hMemRow.2⟩
    have hsRank : rank s < rank (S.vertex a) := rankArc s (S.vertex a) hArc
    have hsProper : H.ProperLoss Bcut s := (hOwnerLoss (S.vertex a) cut Bcut hcut hBcut s).mp hLoss
    exact mkSourcePath (a.val + 1) a.isLt a (Nat.le_succ _) cut Bcut s hCutKey hsRank hsProper
  have hIncoming : ∀ y cut Bcut, inp.owners.read y = some cut → W.owner y = some Bcut →
      IncomingLaw inp W cut Bcut y := by
    intro y cut Bcut hcut hBcut
    have hOwnLoss : ∀ z, ¬ Bcut.Mem z →
        (inp.knownLoss cut z = true ↔ H.ProperLoss Bcut z) :=
      fun z _ => hOwnerLoss y cut Bcut hcut hBcut z
    have hHy : H.ProperLoss Bcut y := W.ownerProper y Bcut hBcut
    refine incomingLaw_of_occurrence (K.site y Bcut hBcut) id (List.map_id _)
      (fun _ _ => rfl)
      (fun _ _ => by
        dsimp only [inp, actualInput, W, actualModel, actualRuntime, GenericRawExitModel.model]
        simp [StaticHeadSweep.Slots.read])
      hOwnLoss hHy
      (fun v _ => some (W.wantBase v)) (fun i _ => some (W.wantMap i))
      (fun _ _ => rfl) (fun _ _ => rfl) ?_
    intro z _ q
    exact (q.run_exact (fun v _ => some (W.wantBase v)) (fun i _ => some (W.wantMap i))
      (fun _ _ => rfl) (fun _ _ => rfl)).symm
  have hKeep : ∀ a : Fin H.vertexCount, S.mapSlot.read (S.vertex a) = none →
      occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val := by
    intro a ho
    exact ⟨PrefixOcc.keep S _ _ ho, actualOld_step_none B increasing covers entryRank rankArc flat a ho⟩
  have hPut : ∀ (a : Fin H.vertexCount) (i : Fin (exitTransferDrivers r).size),
      S.mapSlot.read (S.vertex a) = some i →
      let j := (actualPacking B).jobAt (S.vertex a) i (W.wantMap i)
      PaperB.ExitPhysicalPass.Ready wFit.tags (layoutRegion inp (rfl : inp.arena.mem.size = seedBank.mem.size)).slots
        j (occ a.val) (old a.val) ∧
      occ (a.val + 1) = j.occupy (occ a.val) ∧
      old (a.val + 1) = j.overlay (old a.val) := by
    intro a i ho
    let j := (actualPacking B).jobAt (S.vertex a) i (W.wantMap i)
    let uNew := (actualDriverAddress r i).val
    have hinj : ∀ {i₁ i₂ : Fin (exitTransferDrivers r).size},
        (actualDriverAddress r i₁).val = (actualDriverAddress r i₂).val → i₁ = i₂ :=
      fun h => exitTransferDrivers_address_injective r increasing covers B.full B.ch h
    obtain ⟨huPos, huLt, hpNe, hpOcc, hjpOcc⟩ := parent_of_driver_occ_earlier B increasing covers ho
    have hNotSeed : ¬ actualSeedProbe B uNew := by
      rintro ⟨_, hz | hp0⟩
      · omega
      · exact hpNe hp0
    obtain ⟨hFresh, hOccEq⟩ := PrefixOcc.put S (fun q => (actualDriverAddress r q).val)
      (actualSeedProbe B) ho hinj hNotSeed
    have hInvA := actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank
      a.val (Nat.le_of_lt a.isLt)
    have hBound : j.slot < (layoutRegion inp rfl).slots := huLt
    have hDeps : j.Dependencies (occ a.val) (old a.val) := by
      intro _
      refine ⟨hpOcc, ?_⟩
      change occ a.val ((old a.val (B.F.parentOf uNew)).jump)
      rw [hInvA.jump_eq _ hpOcc]
      exact hjpOcc
    have hFit : (storedCodec wFit.tags).valid
        (buildOneSlot (old a.val) j.parent j.jump j.edge) := by
      have huF : uNew < B.F.size := by rw [B.G.size_eq]; exact huLt
      have hParF : B.F.parentOf uNew < N := by
        dsimp only [N]; rw [← B.G.size_eq]; exact B.G.layout.valid.parentOf_lt_size huF
      have hJumpF : B.F.jumpOf uNew < N := by
        dsimp only [N]; rw [← B.G.size_eq]; exact B.G.layout.valid.jumpOf_lt_size huF
      have hWBound : MapBound endpoints (W.wantMap i) :=
        mapBound_wantMap W (fun x => hRank x) i
      have hjOcc : occ a.val (B.F.jumpOf uNew) := by
        cases pos_jump_cases B huF huPos with
        | inl h => rw [h]; exact hpOcc
        | inr h => rw [h]; exact hInvA.jump_live _ hjpOcc
      have hBounds : MapBound endpoints (buildOneSlot (old a.val) j.parent j.jump j.edge).parentMap ∧
          MapBound endpoints (buildOneSlot (old a.val) j.parent j.jump j.edge).jumpMap := by
        change MapBound endpoints (buildOneSlot (old a.val) (B.F.parentOf uNew)
            (B.F.jumpOf uNew) (W.wantMap i)).parentMap ∧
          MapBound endpoints (buildOneSlot (old a.val) (B.F.parentOf uNew)
            (B.F.jumpOf uNew) (W.wantMap i)).jumpMap
        unfold buildOneSlot
        split
        · exact ⟨hWBound, hWBound⟩
        · have hPB := hInvA.maps_bound _ hpOcc
          have hQB : MapBound endpoints (old a.val (old a.val (B.F.parentOf uNew)).jump).jumpMap := by
            rw [hInvA.jump_eq _ hpOcc]
            exact (hInvA.maps_bound _ hjpOcc).2
          exact ⟨hWBound, mapBound_compose hWBound (mapBound_compose hPB.2 hQB)⟩
      have hParEq : (buildOneSlot (old a.val) j.parent j.jump j.edge).parent = B.F.parentOf uNew := by
        change (buildOneSlot (old a.val) (B.F.parentOf uNew) (B.F.jumpOf uNew) (W.wantMap i)).parent = _
        unfold buildOneSlot; split <;> rfl
      have hJumpEq : (buildOneSlot (old a.val) j.parent j.jump j.edge).jump = B.F.jumpOf uNew := by
        change (buildOneSlot (old a.val) (B.F.parentOf uNew) (B.F.jumpOf uNew) (W.wantMap i)).jump = _
        unfold buildOneSlot
        split
        next heq => simp [Stored.parentOnly, heq]
        next hne =>
          have hc : B.F.jumpOf uNew = B.F.jumpOf (B.F.jumpOf (B.F.parentOf uNew)) :=
            (pos_jump_cases B huF huPos).resolve_left hne
          simp only [Stored.skew]
          rw [hInvA.jump_eq _ hpOcc, hInvA.jump_eq _ hjpOcc, ← hc]
      exact stored_fits (ids := N) (endpoints := endpoints) wFit _
        (by rw [hParEq]; exact hParF) (by rw [hJumpEq]; exact hJumpF) hBounds.1 hBounds.2
    have hOccJ : occ (a.val + 1) = j.occupy (occ a.val) := by
      funext x; apply propext
      change PrefixOcc.occ S _ _ (a.val + 1) x ↔ _
      rw [hOccEq, Job.occupy]; exact or_comm
    have hOldJ : old (a.val + 1) = j.overlay (old a.val) :=
      actualOld_step_some B increasing covers entryRank rankArc flat a i ho
    exact ⟨⟨hBound, hFresh, hDeps, hFit⟩, hOccJ, hOldJ⟩
  have hContract : DirectDepthContract wFit.tags blRegion.base blLayout (actualPacking B) S
      (callbacks inp (rfl : inp.arena.mem.size = seedBank.mem.size) lookup)
      (fun bank => DepthAgrees bank blRegion (fun v => B.F.depthOf v.val))
      occ old W.wantMap W.wantBase :=
    directDepthContract inp (rfl : inp.arena.mem.size = seedBank.mem.size)
      lookup K hGeom S hStages blLayout (actualPacking B) blColumn bl.depthBeforeRecords
      hInstallSource hBaseSource hIncoming hKeep hPut
  have hOcc0' : OccupiedExact wFit.tags blRegion.base blLayout seedBank' (occ 0) (old 0) := by
    intro u hu
    obtain ⟨huLt, hEq⟩ := hOcc0 u hu
    refine ⟨huLt, ?_⟩
    simpa only [readSlot] using hEq
  have hDepth0' : DepthAgrees seedBank' blRegion (fun v => B.F.depthOf v.val) := by
    intro v
    exact hDepth0 ⟨v.val, v.isLt⟩
  let initState : PhysicalState H.vertexCount bits seedBank.mem.size Values :=
    ⟨seedBank', Slots.empty Values H.vertexCount⟩
  let hInitInv : DirectDepthInv wFit.tags blRegion.base blLayout S
      (fun bank => DepthAgrees bank blRegion (fun v => B.F.depthOf v.val))
      occ old W.wantBase 0 initState :=
    ⟨⟨hOcc0', fun a => ⟨fun ha => (Nat.not_lt_zero a.val ha).elim,
      fun _ => by simp [initState, Slots.empty, Slots.read]⟩⟩, hDepth0'⟩
  let finalRes := directDepthRunPrefix wFit.tags blRegion.base blLayout (actualPacking B) S
    (callbacks inp (rfl : inp.arena.mem.size = seedBank.mem.size) lookup)
    (fun bank => DepthAgrees bank blRegion (fun v => B.F.depthOf v.val))
    hContract H.vertexCount (Nat.le_refl _) seedBank' hOcc0' hDepth0'
  have hSeedWritesLe : seedBank.writes ≤ 19 * (H.vertexCount + 1) := by
    have hs1 : seedBank.writes = depthBank.writes + 18 * seeds.length :=
      ExitPhysicalSeedPass.run_writes wFit.tags bl.region.base bl.layout hSeedsFit
        seeds depthBank hSeedNodup
    have hs2 : depthBank.writes = blankBank.writes + bl.region.slots :=
      writeDepthColumn_writes bl.column blankBank _ hDepthFit
    have hs3 : blankBank.writes = 0 := rfl
    have hs4 : seeds.length ≤ N := actualSeeds_length_le B
    have hs5 : bl.region.slots = N := rfl
    have hs6 : N ≤ H.vertexCount + 1 := bundle_next_le (r := r)
    omega
  have hWritesBound : finalRes.val.bank.writes ≤ seedBank.writes + 18 * H.vertexCount :=
    foldTo_writes_le wFit.tags blRegion.base blLayout (actualPacking B) S
      (callbacks inp (rfl : inp.arena.mem.size = seedBank.mem.size) lookup)
      (fun bank => DepthAgrees bank blRegion (fun v => B.F.depthOf v.val))
      hContract H.vertexCount (Nat.le_refl _) H.vertexCount 0 (Nat.zero_add H.vertexCount)
      initState hInitInv
  have hSeedLeFinal : seedBank.writes ≤ finalRes.val.bank.writes :=
    foldTo_writes_ge wFit.tags blRegion.base blLayout (actualPacking B) S
      (callbacks inp (rfl : inp.arena.mem.size = seedBank.mem.size) lookup)
      (fun bank => DepthAgrees bank blRegion (fun v => B.F.depthOf v.val))
      hContract H.vertexCount (Nat.le_refl _) H.vertexCount 0 (Nat.zero_add H.vertexCount)
      initState hInitInv
  let finalBank : WriteResult bits words :=
    ⟨finalRes.val.bank.mem, finalRes.val.bank.size_eq.trans seedBank.size_eq,
      finalRes.val.bank.writes⟩
  have hDecoded : DecodedOccupied finalBank.mem (actualBankRegion N hLayout finalBank) B.F
      (old H.vertexCount) wFit.tags (occ H.vertexCount) := by
    let finalLayout : ExitPhysicalOneSlot.Layout
        (actualBankRegion N hLayout finalBank).base words
        (actualBankRegion N hLayout finalBank).slots :=
      ⟨bl.layout.address, bl.layout.capacity⟩
    have hOccFin : OccupiedExact wFit.tags (actualBankRegion N hLayout finalBank).base
        finalLayout finalBank (occ H.vertexCount) (old H.vertexCount) := by
      intro u hu
      obtain ⟨huLt, hEq⟩ := finalRes.property.inv.maps u hu
      exact ⟨huLt, by simpa only [readSlot, actualBankRegion, blRegion, finalBank] using hEq⟩
    have hDepFin : DepthAgrees finalRes.val.bank blRegion (fun v => B.F.depthOf v.val) :=
      finalRes.property.depth
    refine DecodedOccupied.ofOccupiedExact hOccFin hStages.size_le
      hStages.valid (hStages.live_lt H.vertexCount) ?_
      (hStages.parent_eq H.vertexCount) (hStages.jump_eq H.vertexCount)
      (hStages.parent_live H.vertexCount) (hStages.jump_live H.vertexCount)
    intro v _
    have hslot' : v.val < bl.region.slots := v.isLt
    have hv := hDepFin ⟨v.val, hslot'⟩
    dsimp only [depthAt, regionIn, blRegion, actualBankRegion, finalBank] at hv ⊢
    split at hv
    · exact hv
    · exact absurd hslot' ‹_›
  have hBasesExact : ∀ y : Vertex H, finalRes.val.bases.read y = some (W.wantBase y) := by
    intro y
    obtain ⟨b, hb⟩ := S.covers y
    change S.vertex b = y at hb
    have hcell := finalRes.property.inv.bases b
    rw [hb] at hcell
    simpa [Cell, b.isLt] using hcell
  have hSlotKeyAt : ∀ (y : Vertex H) (Acut : CutPair H),
      W.owner y = some Acut →
      ∃ u : Fin B.F.size, (exitDenseOwnerSlots r B.E).read y = some u ∧ u.val = slotOf Acut := by
    intro y Acut hOwn
    rw [exitDenseOwnerSlots_read]
    dsimp only [exitDenseOwnerCell]
    have h0' := exitDenseOwnerKey?_eq_canonical r B.E y
    have hLabKey : (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y) =
        some Acut :=
      h0'.symm.trans hOwn
    have h0 : 0 < B.F.size := by rw [B.G.size_eq]; exact bundle_next_pos B
    have hLabNZ : (selectors (orderedConfig p large) r.out).label y ≠ 0 := by
      intro hz
      let z0 : Fin B.F.size := ⟨0, h0⟩
      have hFin0 : (⟨(selectors (orderedConfig p large) r.out).label y,
          B.E.label_lt y True.intro⟩ : Fin B.F.size) = z0 := Fin.ext hz
      have hLab0 : B.E.image z0 = (buildProperLossForest H rank).label y := by
        rw [← hFin0]; exact B.E.label_eq y True.intro
      rw [← hLab0, B.E.root_eq h0, buildProperLossForest_nodeKey?_root] at hLabKey
      cases hLabKey
    refine ⟨⟨(selectors (orderedConfig p large) r.out).label y,
        B.E.label_lt y True.intro⟩, ?_, ?_⟩
    · simp [hLabNZ]
    · let uF : Fin B.F.size := ⟨(selectors (orderedConfig p large) r.out).label y,
        B.E.label_lt y True.intro⟩
      have hKeyU : (buildProperLossForest H rank).nodeKey? (B.E.image uF) = some Acut := by
        rw [B.E.label_eq y True.intro]; exact hLabKey
      exact (hSlotOf_nodeKey hKeyU).symm
  have hSlotDepthEq : ∀ {Bcut : CutPair H} {a : Fin (W.forest.realNodeCount + 1)},
      W.forest.nodeKey? a = some Bcut →
      B.F.depthOf (slotOf Bcut) = W.forest.depth a := by
    intro Bcut a ha
    change (buildProperLossForest H rank).nodeKey? a = some Bcut at ha
    change B.F.depthOf (slotOf Bcut) = (buildProperLossForest H rank).depth a
    obtain ⟨v, hv⟩ := B.hSurj a
    have hkv : (buildProperLossForest H rank).nodeKey? (B.E.image v) = some Bcut := by
      simpa only [hv] using ha
    rw [hSlotOf_nodeKey hkv, ← hv, ← B.E.depth_eq v]
    have hRec := (readRecordWords_spec B.G.layout v.isLt).1
    exact (congrArg JumpRecord.depth hRec).symm
  have hfw : finalBank.writes = finalRes.val.bank.writes := rfl
  exact
    { bundle := B
      wFit := wFit
      hLayout := hLayout
      model := W
      model_eq := rfl
      bank := finalBank
      bases := finalRes.val.bases
      seedWrites := seedBank.writes
      sweepWrites := finalRes.val.bank.writes - seedBank.writes
      seedWrites_le := hSeedWritesLe
      sweepWrites_le := by omega
      totalWrites_eq := by rw [hfw]; omega
      live := occ H.vertexCount
      ref := old H.vertexCount
      all_live := fun u hu => actualOcc_all_final B increasing covers hu
      decoded := hDecoded
      liveOK := actual_liveStoreOK_final B increasing covers entryRank rankArc flat endpoints hRank
      bases_exact := hBasesExact
      owner_eq := exitDenseOwnerKey?_eq_canonical r B.E
      slotOf := slotOf
      slot_key_lt := fun Bcut {a} ha => by
        change (buildProperLossForest H rank).nodeKey? a = some Bcut at ha
        obtain ⟨v, hv⟩ := B.hSurj a
        have hkv : (buildProperLossForest H rank).nodeKey? (B.E.image v) = some Bcut := by
          simpa only [hv] using ha
        rw [hSlotOf_nodeKey hkv]
        exact v.isLt
      slot_key_at := hSlotKeyAt
      edges := by
        have hed := mkEdges H.vertexCount (Nat.le_refl _)
        exact
          { parent := fun i _ => hed.parent i (by
              rw [hSlotOf_edge_child i]
              exact actualOcc_all_final B increasing covers
                (by rw [B.G.size_eq]; exact (actualDriverAddress r i).isLt))
            parentMap := fun i _ => hed.parentMap i (by
              rw [hSlotOf_edge_child i]
              exact actualOcc_all_final B increasing covers
                (by rw [B.G.size_eq]; exact (actualDriverAddress r i).isLt))
            down := fun i _ => hed.down i (by
              rw [hSlotOf_edge_child i]
              exact actualOcc_all_final B increasing covers
                (by rw [B.G.size_eq]; exact (actualDriverAddress r i).isLt)) }
      slot_depth_eq := hSlotDepthEq }

theorem buildActualDirectBank_mapBounds
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
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
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits) :
    let built := buildActualDirectBank H flat increasing covers rankArc r entryRank hRank wFit hLayout
    ∀ u, u < built.bundle.F.size →
      MapBound endpoints (built.ref u).parentMap ∧ MapBound endpoints (built.ref u).jumpMap := by
  intro built u hu
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  have hInv := actualStepInv_all B increasing covers entryRank rankArc flat endpoints hRank
    H.vertexCount (Nat.le_refl _)
  change u < B.F.size at hu
  exact hInv.maps_bound u (actualOcc_all_final B increasing covers hu)

end PaperB.ExitActualContract


