module

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

/-! Match stored-forest ancestry with the packed DFS interval. -/

open PaperB.Jumps
open PaperB.EX24.FinalDFS
open _root_.EX24.PreStep

theorem ancestor_iff_entry_stop {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    {u v : Nat} (hu : u < r.out.tables.next) (hv : v < r.out.tables.next) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
      (nodeCount_eq_next r.index.ok).symm
    B.F.decideAncestor u v = true ↔
      r.index.reader.entry (Fin.cast hN ⟨u, hu⟩) ≤
        r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) ∧
      r.index.reader.entry (Fin.cast hN ⟨v, hv⟩) <
        r.index.reader.stop (Fin.cast hN ⟨u, hu⟩) := by
  intro B hN
  let x := PaperB.EX24.FinalDFS.packedInput r.index.ok
  have hPar := reader_matches_bundle_forest flat increasing covers rankArc r
  have huF : u < B.F.size := by rw [B.G.size_eq]; exact hu
  have hvF : v < B.F.size := by rw [B.G.size_eq]; exact hv
  have hParent (w : Fin (nodeCount (orderedConfig p large) r.out)) :
      (x.parent.read w).val = B.F.parentOf w.val := by
    let z := Fin.cast hN.symm w
    have hz : Fin.cast hN z = w := Fin.ext rfl
    have hp := (hPar z).1
    rw [hz] at hp
    exact hp
  have hIter (k : Nat) :
      ∀ z, (iterParentFin x.parent.read k z).val = B.F.iterParent k z.val := by
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      simp only [iterParentFin, JumpForest.iterParent, ih, hParent]
  have hDec := B.G.layout.valid.decideAncestor_eq_true_iff huF hvF
  have hRd := isForestAncestor_iff_dfsIntervalContains r.index.reader.input_ok
    (Fin.cast hN ⟨u, hu⟩) (Fin.cast hN ⟨v, hv⟩)
  unfold dfsIntervalContains at hRd
  rw [← r.index.reader.stop_exact (Fin.cast hN ⟨u, hu⟩),
      ← r.index.reader.entry_exact (Fin.cast hN ⟨u, hu⟩),
      ← r.index.reader.entry_exact (Fin.cast hN ⟨v, hv⟩)] at hRd
  change IsForestAncestor x.parent.read (Fin.cast hN ⟨u, hu⟩) (Fin.cast hN ⟨v, hv⟩) ↔ _ at hRd
  rw [hDec, ← hRd, isForestAncestor_iff_iterParentFin]
  change (∃ k, B.F.iterParent k v = u) ↔
    ∃ k, iterParentFin x.parent.read k (Fin.cast hN ⟨v, hv⟩) = Fin.cast hN ⟨u, hu⟩
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Fin.ext (by rw [hIter k (Fin.cast hN ⟨v, hv⟩)]; exact hk)⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hi : (iterParentFin x.parent.read k (Fin.cast hN ⟨v, hv⟩)).val =
        B.F.iterParent k v := hIter k (Fin.cast hN ⟨v, hv⟩)
    exact hi.symm.trans (congrArg Fin.val hk)

theorem owner_eq_none_of_label_zero {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    (y : Vertex H)
    (hy0 : (selectors (orderedConfig p large) r.out).label y = 0) :
    (actualModel (buildActualSweepBundle H flat increasing covers rankArc r)
      entryRank rankArc flat).owner y = none := by
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  change exitDenseOwnerKey? r y = none
  rw [exitDenseOwnerKey?_eq_canonical r B.E y]
  have h0 : 0 < B.F.size := by rw [B.G.size_eq]; exact (B_next_pos flat increasing covers rankArc r).1
  have hLabLt : (selectors (orderedConfig p large) r.out).label y < B.F.size := B.E.label_lt y True.intro
  have hCast0 : (⟨(selectors (orderedConfig p large) r.out).label y, hLabLt⟩ : Fin B.F.size) = ⟨0, h0⟩ :=
    Fin.ext hy0
  have hLabEq : (buildProperLossForest H rank).label y = (buildProperLossForest H rank).rootNode := by
    rw [← B.E.label_eq y True.intro, hCast0, B.E.root_eq h0]
  rw [hLabEq, buildProperLossForest_nodeKey?_root]

theorem owner_eq_some_of_label_pos {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    (y : Vertex H)
    (hyPos : 0 < (selectors (orderedConfig p large) r.out).label y) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let s := (selectors (orderedConfig p large) r.out).label y
    ∃ Bcut : CutPair H,
      (actualModel B entryRank rankArc flat).owner y = some Bcut ∧
      r.out.tables.back[s]? = some (some Bcut) ∧
      Bcut.fst < Bcut.snd ∧
      (buildProperLossForest H rank).nodeKey? (B.E.image ⟨s, B.E.label_lt y True.intro⟩) = some Bcut := by
  intro B s
  have hLabLt : s < B.F.size := B.E.label_lt y True.intro
  let uF : Fin B.F.size := ⟨s, hLabLt⟩
  have hb : ∃ Bcut : CutPair H,
      (buildProperLossForest H rank).nodeKey? (B.E.image uF) = some Bcut := by
    cases hk : (buildProperLossForest H rank).nodeKey? (B.E.image uF) with
    | some Bcut => exact ⟨Bcut, rfl⟩
    | none =>
      exfalso
      have h0 : 0 < B.F.size := by rw [B.G.size_eq]; exact (B_next_pos flat increasing covers rankArc r).1
      have hRoot := buildProperLossForest_nodeKey?_inj H rank
        (hk.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      rw [← B.E.root_eq h0] at hRoot
      have h0s := congrArg Fin.val (B.E.injective hRoot)
      change s = 0 at h0s
      exact (Nat.ne_of_gt hyPos) h0s
  obtain ⟨Bcut, hBcut⟩ := hb
  have hBack : r.out.tables.back[s]? = some (some Bcut) :=
    (B.E.back_eq uF).trans (congrArg some hBcut)
  have hOwn : (actualModel B entryRank rankArc flat).owner y = some Bcut := by
    change exitDenseOwnerKey? r y = some Bcut
    rw [exitDenseOwnerKey?_eq_canonical r B.E y, ← B.E.label_eq y True.intro]
    exact hBcut
  have hCan : Bcut.fst < Bcut.snd :=
    buildProperLossForest_realKeys_canonical H rank Bcut (nodeKeyOfList?_mem hBcut)
  exact ⟨Bcut, hOwn, hBack, hCan, hBcut⟩

theorem properLoss_iff_ramTest {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    {ownerSlot : Nat} (hOwnPos : 0 < ownerSlot) (hOwnLt : ownerSlot < r.out.tables.next)
    {Bcut : CutPair H}
    (hNode : (buildProperLossForest H rank).nodeKey?
      ((buildActualSweepBundle H flat increasing covers rankArc r).E.image
        ⟨ownerSlot, (buildActualSweepBundle H flat increasing covers rankArc r).G.size_eq.symm ▸ hOwnLt⟩) =
      some Bcut)
    (u : Vertex H) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let v := (selectors (orderedConfig p large) r.out).label u
    let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
      (nodeCount_eq_next r.index.ok).symm
    have hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
    H.ProperLoss Bcut u ↔
      (0 < v ∧
       r.index.reader.entry (Fin.cast hN ⟨ownerSlot, hOwnLt⟩) ≤
         r.index.reader.entry (Fin.cast hN ⟨v, hvLt⟩) ∧
       r.index.reader.entry (Fin.cast hN ⟨v, hvLt⟩) <
         r.index.reader.stop (Fin.cast hN ⟨ownerSlot, hOwnLt⟩)) := by
  intro B v hN hvLt
  have hCan : Bcut.fst < Bcut.snd :=
    buildProperLossForest_realKeys_canonical H rank Bcut (nodeKeyOfList?_mem hNode)
  have hSlotEq : physicalPairSlot? (orderedConfig p large) r.out.tables Bcut = some ownerSlot :=
    (B.hSlot Bcut ownerSlot).mpr ⟨⟨ownerSlot, B.G.size_eq.symm ▸ hOwnLt⟩, rfl, hNode⟩
  have hOwnF : ownerSlot < B.F.size := B.G.size_eq.symm ▸ hOwnLt
  have hVF : v < B.F.size := B.E.label_lt u True.intro
  have hDec : B.F.decideAncestor ownerSlot v = true ↔ H.ProperLoss Bcut u := by
    rw [B.G.layout.valid.decideAncestor_eq_true_iff hOwnF hVF]
    have hIterClimb : ∀ k z, B.F.iterParent k z = climb B.F.parentOf k z := by
      intro k
      induction k with
      | zero => intro z; rfl
      | succ k ih =>
        intro z
        change B.F.iterParent k (B.F.parentOf z) = B.F.parentOf (climb B.F.parentOf k z)
        rw [ih (B.F.parentOf z)]
        clear ih
        induction k with
        | zero => rfl
        | succ k ih =>
          exact congrArg B.F.parentOf ih
    constructor
    · rintro ⟨k, hk⟩
      rw [hIterClimb] at hk
      exact ((B.hLoss Bcut u).mpr ⟨ownerSlot, hSlotEq, k, hk⟩).2
    · intro hProp
      obtain ⟨n', hn', k, hk⟩ := (B.hLoss Bcut u).mp ⟨hCan, hProp⟩
      have hEq : n' = ownerSlot := Option.some.inj (hn'.symm.trans hSlotEq)
      exact ⟨k, by rw [hIterClimb, ← hEq]; exact hk⟩
  have hVPosOfDec : B.F.decideAncestor ownerSlot v = true → 0 < v := by
    intro hT
    apply Nat.pos_of_ne_zero
    intro hv0
    obtain ⟨k, hk⟩ := (B.G.layout.valid.decideAncestor_eq_true_iff hOwnF hVF).mp hT
    have hzIter : ∀ m, B.F.iterParent m 0 = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        change B.F.iterParent m (B.F.parentOf 0) = 0
        rw [(validJumpForest_root_zero B.G.layout.valid).1, ih]
    rw [hv0, hzIter k] at hk
    omega
  have hInterval := ancestor_iff_entry_stop flat increasing covers rankArc r hOwnLt hvLt
  constructor
  · intro hProp
    have hTrue := hDec.mpr hProp
    exact ⟨hVPosOfDec hTrue, hInterval.mp hTrue⟩
  · rintro ⟨_, h1, h2⟩
    exact hDec.mp (hInterval.mpr ⟨h1, h2⟩)

end PaperB.RamProgram.ExitSummaryBuild
