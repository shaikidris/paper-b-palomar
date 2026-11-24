module

public import PaperB.ExitActualContract
public import PaperB.RamForestPhaseLink
public import PaperB.RamForestIncomingArcs
public import PaperB.ForestPreparedBuild
public import PaperB.OracleContract

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary builder setup (`PaperB/RamExitSummarySetup.lean`).

Contains:
1. Input/output memory layout (`exitWorkCap n m ≤ 48 * (n + m + 1)`, metadata slots,
   `ExitBuildInput`).
2. Mathematical specification bridges:
   - DFS `(fEntry, fStop)` stack reconstruction matching `B.F.parentOf`,
     `B.F.depthOf`, and `B.F.jumpOf`;
   - Topological trigger ordering (`triggerRank parent < triggerRank child` and
     `triggerRank owner < topoRank y`);
   - `Occupied` / `DecodedOccupied` / `LiveStoreOK` / `RouteSlotEdges` bridges.
3. 15-register Word-RAM execution helpers, `PhasesExec`, `linkNonEmpty`,
   `initMetaPhase`, Stage 1 (`forestReconPhase`), Stage 2 (`csrKahnPhase`),
   Stage 3 (`seedAndTriggerPhase`), and reusable Stage 4 slices (`intervalJoin`,
   `mapEval`, `eval15`, `mapCompose`, `buildOneSlot`).
-/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
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

/-! ### 1. Work-memory layout & `ExitBuildInput` contract -/

section LayoutAndInput

/-- Exact linear work-memory budget `33 * n + 2 * m + 80 ≤ 48 * (n + m + 1)`
for all `3 ≤ n`. -/
def exitWorkCap (n m : Nat) : Nat := 33 * n + 2 * m + 80

theorem exitWorkCap_le (n m : Nat) (hn : 3 ≤ n) :
    exitWorkCap n m ≤ 48 * (n + m + 1) := by
  unfold exitWorkCap
  omega

/-- Total output words `19 * N + 6 * n ≤ 25 * n + 19` when `N ≤ n + 1`. -/
def exitOutputWords (N n : Nat) : Nat := 19 * N + 6 * n

theorem exitOutputWords_le {N n : Nat} (hN : N ≤ n + 1) :
    exitOutputWords N n ≤ 25 * n + 19 := by
  unfold exitOutputWords
  omega

def depthBase : Nat := 0
def storedBase (N : Nat) : Nat := N
def priorBase (N : Nat) : Nat := 19 * N
def orderArrBase (n N : Nat) : Nat := 19 * N + 6 * n
def topoRankArrBase (n N : Nat) : Nat := orderArrBase n N + n
def trigHeadArrBase (n N : Nat) : Nat := topoRankArrBase n N + n
def trigNextArrBase (n N : Nat) : Nat := trigHeadArrBase n N + n
def inStartArrBase (n N : Nat) : Nat := trigNextArrBase n N + N
def inArcIdArrBase (n N : Nat) : Nat := inStartArrBase n N + (n + 1)
def metaArrBase (n m N : Nat) : Nat := inArcIdArrBase n N + m
def tempArrBase (n m N : Nat) : Nat := metaArrBase n m N + 48

theorem metaArrBase_eq (n m N : Nat) :
    metaArrBase n m N = 20 * N + 10 * n + m + 1 := by
  unfold metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase
    trigHeadArrBase topoRankArrBase orderArrBase
  omega

theorem tempArrBase_stage1_le {n m N : Nat} (hN : N ≤ n + 1) :
    tempArrBase n m N + 3 * N ≤ exitWorkCap n m := by
  unfold tempArrBase exitWorkCap
  rw [metaArrBase_eq]
  omega

theorem tempArrBase_stage2_le {n m N : Nat} (hN : N ≤ n + 1) :
    tempArrBase n m N + (3 * n + 1 + m) ≤ exitWorkCap n m := by
  unfold tempArrBase exitWorkCap
  rw [metaArrBase_eq]
  omega

theorem tempArrBase_stage4_le {n m N : Nat} (hn : 3 ≤ n) (hN : N ≤ n + 1) :
    tempArrBase n m N + 16 ≤ exitWorkCap n m := by
  unfold tempArrBase exitWorkCap
  rw [metaArrBase_eq]
  omega

/-- Metadata indices relative to `rMeta = reg 14 = metaArrBase n m N`. -/
abbrev mIdxN : Nat := 0
abbrev mIdxM : Nat := 1
abbrev mIdxNH : Nat := 2
abbrev mIdxNGlobal : Nat := 3
abbrev mIdxStoredBase : Nat := 4
abbrev mIdxPriorBase : Nat := 5
abbrev mIdxOrderBase : Nat := 6
abbrev mIdxTopoRankBase : Nat := 7
abbrev mIdxTrigHeadBase : Nat := 8
abbrev mIdxTrigNextBase : Nat := 9
abbrev mIdxInStartBase : Nat := 10
abbrev mIdxInArcIdBase : Nat := 11
abbrev mIdxMetaBase : Nat := 12
abbrev mIdxTempBase : Nat := 13
abbrev mIdxQSrcInBase : Nat := 14
abbrev mIdxQHeadInBase : Nat := 15
abbrev mIdxQTailRankInBase : Nat := 16
abbrev mIdxFEntryInBase : Nat := 17
abbrev mIdxFStopInBase : Nat := 18
abbrev mIdxLabelsInBase : Nat := 19
abbrev mIdxBackFstInBase : Nat := 20
abbrev mIdxBackSndInBase : Nat := 21
abbrev mIdxKCursor : Nat := 22
abbrev mIdxCurY : Nat := 23
abbrev mIdxCurOwner : Nat := 24
abbrev mIdxArcPtr : Nat := 25
abbrev mIdxArcEnd : Nat := 26
abbrev mIdxCCursor : Nat := 27
abbrev mIdxEvalU : Nat := 28
abbrev mIdxEvalD : Nat := 29
abbrev mIdxAcc0 : Nat := 30
abbrev mIdxEval0 : Nat := 36
abbrev mIdxTmp0 : Nat := 42

/-- Reserved meta register holding `metaArrBase n m N`. -/
abbrev rMeta : Fin 15 := ⟨14, by decide⟩

/-- Read-only input contract matching `ExitBuildInput` in `#53`. -/
structure ExitBuildInput {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout bits inputCap workCap hi hw))
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (nGlobal : Nat) : Prop where
  cap_ge : 4 + H.vertexCount + 4 * r.out.tables.next + 3 * H.arcCount ≤ inputCap
  hdr_n : (input.words[0]?).map Fin.val = some H.vertexCount
  hdr_m : (input.words[1]?).map Fin.val = some H.arcCount
  hdr_NH : (input.words[2]?).map Fin.val = some r.out.tables.next
  hdr_nGlobal : (input.words[3]?).map Fin.val = some nGlobal
  hRank_lt : ∀ x : Fin H.origVertexCount, entryRank x < nGlobal
  hVertex_le_nGlobal : H.vertexCount ≤ nGlobal
  labels_at : ∀ y : Fin H.vertexCount,
    (input.words[4 + y.val]?).map Fin.val =
      some ((selectors (orderedConfig p large) r.out).label y)
  back_at : ∀ u : Fin r.out.tables.next,
    ∃ o : Option (CutPair H),
      r.out.tables.back[u.val]? = some o ∧
      (input.words[4 + H.vertexCount + u.val]?).map Fin.val = some (encodeBackPair o).1 ∧
      (input.words[4 + H.vertexCount + r.out.tables.next + u.val]?).map Fin.val =
        some (encodeBackPair o).2
  fEntry_at : ∀ u : Fin r.out.tables.next,
    (input.words[4 + H.vertexCount + 2 * r.out.tables.next + u.val]?).map Fin.val =
      some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm u))
  fStop_at : ∀ u : Fin r.out.tables.next,
    (input.words[4 + H.vertexCount + 3 * r.out.tables.next + u.val]?).map Fin.val =
      some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm u))
  qSrc_at : ∀ e : Fin H.arcCount,
    (input.words[4 + H.vertexCount + 4 * r.out.tables.next + e.val]?).map Fin.val =
      some (rawOccurrence H e).1.val
  qHead_at : ∀ e : Fin H.arcCount,
    (input.words[4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + e.val]?).map Fin.val =
      some (rawHead H e).val
  qTailRank_at : ∀ e : Fin H.arcCount,
    (input.words[4 + H.vertexCount + 4 * r.out.tables.next + 2 * H.arcCount + e.val]?).map Fin.val =
      some (entryRank (rawOccurrence H e).2.origTail)

theorem exitBuildInput_size_le {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    4 + H.vertexCount + 4 * r.out.tables.next + 3 * H.arcCount ≤
      6 + 6 * H.vertexCount + 3 * H.arcCount := by
  have hLe := (nodeCount_eq_next r.index.ok).symm ▸ nodeCount_le r.index.ok
  have h3 := large
  omega

end LayoutAndInput

/-! ### 2. Mathematical specification bridges -/

section MathBridges

open PaperB.StaticTreeReader
open PaperB.PackedStaticLayout

theorem B_next_pos {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    0 < r.out.tables.next ∧ r.out.tables.next ≤ H.vertexCount + 1 := by
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  have hF := B.G.size_eq
  have h0 : 0 < B.F.size := by
    obtain ⟨_, inv⟩ := B.G.layout.valid.exists_forestInvariant
    exact inv.size_pos
  have hLe : r.out.tables.next ≤ H.vertexCount + 1 :=
    (nodeCount_eq_next r.index.ok).symm ▸ nodeCount_le r.index.ok
  exact ⟨hF ▸ h0, hLe⟩

/-- `ValidJumpForest` DFS-interval parent/depth/jump characterization:
the stack algorithm on `(fEntry, fStop)` produces `(B.F.parentOf, B.F.depthOf, B.F.jumpOf)`. -/
theorem dfs_preorder_bijection {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    let N := r.out.tables.next
    let rd := r.index.reader
    have hN : N = nodeCount (orderedConfig p large) r.out := (nodeCount_eq_next r.index.ok).symm
    (∀ u : Fin N, rd.entry (Fin.cast hN u) < N) ∧
    (∀ u₁ u₂ : Fin N, rd.entry (Fin.cast hN u₁) = rd.entry (Fin.cast hN u₂) → u₁ = u₂) ∧
    (∀ u : Fin N, rd.entry (Fin.cast hN u) < rd.stop (Fin.cast hN u) ∧
      rd.stop (Fin.cast hN u) ≤ N) := by
  intro N rd hN
  let x := PaperB.EX24.FinalDFS.packedInput r.index.ok
  have hx : ValidDepthTree x.root x.parent.read x.depth.read := rd.input_ok
  have hCol : ∀ v : Fin (nodeCount (orderedConfig p large) r.out),
      rd.entry v = (StaticLinearHead.entryColumn x).read v := fun v => by
    unfold Reader.entry
    rw [rd.layout_exact]
  refine ⟨fun u => ?_, fun u₁ u₂ hEq => ?_, fun u => ?_⟩
  · have hLt := StaticLinearHead.entry_lt x hx (Fin.cast hN u)
    rw [hCol (Fin.cast hN u)]
    exact Nat.lt_of_lt_of_le hLt (Nat.le_of_eq hN.symm)
  · have hE' : (StaticLinearHead.entryColumn x).read (Fin.cast hN u₁) =
        (StaticLinearHead.entryColumn x).read (Fin.cast hN u₂) := by
      rw [← hCol (Fin.cast hN u₁), ← hCol (Fin.cast hN u₂), hEq]
    have hL1 : (StaticLinearHead.entryColumn x).read (Fin.cast hN u₁) <
        (StaticLinearHead.preorderSpec x).length := by
      rw [StaticLinearHead.preorder_length x hx]
      exact StaticLinearHead.entry_lt x hx (Fin.cast hN u₁)
    have hL2 : (StaticLinearHead.entryColumn x).read (Fin.cast hN u₂) <
        (StaticLinearHead.preorderSpec x).length := by
      rw [StaticLinearHead.preorder_length x hx]
      exact StaticLinearHead.entry_lt x hx (Fin.cast hN u₂)
    have g1 : (StaticLinearHead.preorderSpec x)[(StaticLinearHead.entryColumn x).read (Fin.cast hN u₁)]? =
        some (Fin.cast hN u₁) := by
      rw [List.getElem?_eq_getElem hL1, StaticLinearHead.preorder_get_entry x hx (Fin.cast hN u₁)]
    have g2 : (StaticLinearHead.preorderSpec x)[(StaticLinearHead.entryColumn x).read (Fin.cast hN u₂)]? =
        some (Fin.cast hN u₂) := by
      rw [List.getElem?_eq_getElem hL2, StaticLinearHead.preorder_get_entry x hx (Fin.cast hN u₂)]
    rw [hE'] at g1
    have hCast : Fin.cast hN u₁ = Fin.cast hN u₂ := Option.some.inj (g1.symm.trans g2)
    exact Fin.ext (congrArg (fun z : Fin (nodeCount (orderedConfig p large) r.out) => z.val) hCast)
  · rw [rd.entry_exact, rd.stop_exact]
    obtain ⟨pre, post, hsplit⟩ := exists_split_dfsPreorder hx (Fin.cast hN u)
    have hlen := congrArg List.length hsplit
    rw [length_dfsPreorder hx, List.length_append, List.length_append] at hlen
    have hEnd := entry_eq_length_of_dfsPreorder_split hx hsplit
    have hU := dfsSubtree_unfold hx (Fin.cast hN u)
    have hPos : 0 < (dfsSubtree x.root x.parent.read x.depth.read (Fin.cast hN u)).length := by
      rw [hU]; exact Nat.succ_pos _
    dsimp only [x] at hlen hEnd hPos
    omega

/-- Notice `r.index.reader.input` has `parentOf` and `depthOf` equal to `B.F.parentOf` and `B.F.depthOf`
since `r.index.ok` fixes the same `JumpWordLayout` (deterministic function of `r.out.tables.mem`). -/
theorem reader_matches_bundle_forest {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out := (nodeCount_eq_next r.index.ok).symm
    ∀ u : Fin r.out.tables.next,
      ((PaperB.EX24.FinalDFS.packedInput r.index.ok).parent.read (Fin.cast hN u)).val =
        B.F.parentOf u.val ∧
      (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN u) =
        B.F.depthOf u.val := by
  intro B hN u
  have hp := PaperB.EX24.FinalDFS.packedInput_parent r.index.ok B.G (Fin.cast hN u)
  have hd := PaperB.EX24.FinalDFS.packedInput_depth r.index.ok B.G (Fin.cast hN u)
  exact ⟨hp, hd⟩

/-- Skew-binary jump rule computed on slot `u > 0` matches `B.F.jumpOf u` when
`parent[u] = B.F.parentOf u`, `depth[w] = B.F.depthOf w`, and `jump[w] = B.F.jumpOf w` for ancestors `w`. -/
theorem validJumpForest_skew_rule {F : JumpForest} (hV : ValidJumpForest F) :
    ∀ u : Nat, 0 < u → u < F.size →
      let p := F.parentOf u
      let a := F.jumpOf p
      let b := F.jumpOf a
      let len1 := F.depthOf p - F.depthOf a
      let len2 := F.depthOf a - F.depthOf b
      F.jumpOf u = if 0 < len1 ∧ len1 = len2 then b else p := by
  induction hV with
  | init =>
    intro u hu hlt
    change u < 1 at hlt
    omega
  | @appendLeaf F p hF hp ih =>
    intro u hu hlt
    rw [JumpForest.size_appendLeaf] at hlt
    by_cases hOld : u < F.size
    · have hpF : F.parentOf u < F.size := hF.parentOf_lt_size hOld
      have haF : F.jumpOf (F.parentOf u) < F.size := hF.jumpOf_lt_size hpF
      have hbF : F.jumpOf (F.jumpOf (F.parentOf u)) < F.size := hF.jumpOf_lt_size haF
      dsimp only
      rw [jumpOf_appendLeaf_old F p hOld, parentOf_appendLeaf_old F p hOld,
          jumpOf_appendLeaf_old F p hpF, jumpOf_appendLeaf_old F p haF,
          depthOf_appendLeaf_old F p hpF, depthOf_appendLeaf_old F p haF,
          depthOf_appendLeaf_old F p hbF]
      exact ih u hu hOld
    · have huEq : u = F.size := by omega
      subst u
      have hPar : (F.appendLeaf p).parentOf F.size = p := by
        unfold JumpForest.parentOf
        rw [recordAt_appendLeaf_new]
        rfl
      have hJmp : (F.appendLeaf p).jumpOf F.size =
          let a := F.jumpOf p
          let b := F.jumpOf a
          let len1 := F.depthOf p - F.depthOf a
          let len2 := F.depthOf a - F.depthOf b
          if 0 < len1 ∧ len1 = len2 then b else p := by
        unfold JumpForest.jumpOf
        rw [recordAt_appendLeaf_new]
        rfl
      have haF : F.jumpOf p < F.size := hF.jumpOf_lt_size hp
      have hbF : F.jumpOf (F.jumpOf p) < F.size := hF.jumpOf_lt_size haF
      dsimp only
      rw [hPar, hJmp, jumpOf_appendLeaf_old F p hp, jumpOf_appendLeaf_old F p haF,
          depthOf_appendLeaf_old F p hp, depthOf_appendLeaf_old F p haF,
          depthOf_appendLeaf_old F p hbF]

/-- For any topological rank `rankKahn` of `H`, if `u` has `CutPair` key `P_u = (a_u, b_u)`,
and `H.ProperLoss P_u y`, then `max (rankKahn a_u) (rankKahn b_u) < rankKahn y`. -/
theorem trigger_lt_properLoss {H : LabelledQuotient} (flat : H.IsFlat)
    (rankKahn : Vertex H → Nat)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    {B : CutPair H} {y : Vertex H} (hProp : H.ProperLoss B y) :
    max (rankKahn B.fst) (rankKahn B.snd) < rankKahn y := by
  have h1 := properLoss_follows_endpoints rankArcKahn flat hProp (Or.inl rfl)
  have h2 := properLoss_follows_endpoints rankArcKahn flat hProp (Or.inr rfl)
  exact Nat.max_lt.mpr ⟨h1, h2⟩

/-- For any topological rank `rankKahn` of `H`, if `p = B.F.parentOf c ≠ 0`,
then `max (rankKahn a_p) (rankKahn b_p) < max (rankKahn a_c) (rankKahn b_c)`. -/
theorem trigger_parent_lt_child {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pRows : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult pRows data size_data rank large)
    (rankKahn : Vertex H → Nat)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    {c : Nat} (hcPos : 0 < c) (hcLt : c < r.out.tables.next) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let p := B.F.parentOf c
    0 < p →
    ∃ Pc Pp : CutPair H,
      r.out.tables.back[c]? = some (some Pc) ∧
      r.out.tables.back[p]? = some (some Pp) ∧
      max (rankKahn Pp.fst) (rankKahn Pp.snd) < max (rankKahn Pc.fst) (rankKahn Pc.snd) := by
  intro B p hpPos
  have hcF : c < B.F.size := by rw [B.G.size_eq]; exact hcLt
  have hpLt : p < B.F.size := B.G.layout.valid.parentOf_lt_size hcF
  let cF : Fin B.F.size := ⟨c, hcF⟩
  let pF : Fin B.F.size := ⟨p, hpLt⟩
  have hcReal : ∃ Pc : CutPair H, (buildProperLossForest H rank).nodeKey? (B.E.image cF) = some Pc := by
    cases hK : (buildProperLossForest H rank).nodeKey? (B.E.image cF) with
    | some Pc => exact ⟨Pc, rfl⟩
    | none =>
      have h0 : 0 < B.F.size := B.G.size_eq ▸ (B_next_pos flat increasing covers rankArc r).1
      have hEq := buildProperLossForest_nodeKey?_inj H rank
        (hK.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      rw [← B.E.root_eq h0] at hEq
      have hc0 := B.E.injective hEq
      have : c = 0 := congrArg Fin.val hc0
      omega
  have hpReal : ∃ Pp : CutPair H, (buildProperLossForest H rank).nodeKey? (B.E.image pF) = some Pp := by
    cases hK : (buildProperLossForest H rank).nodeKey? (B.E.image pF) with
    | some Pp => exact ⟨Pp, rfl⟩
    | none =>
      have h0 : 0 < B.F.size := B.G.size_eq ▸ (B_next_pos flat increasing covers rankArc r).1
      have hEq := buildProperLossForest_nodeKey?_inj H rank
        (hK.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      rw [← B.E.root_eq h0] at hEq
      have hp0 := B.E.injective hEq
      have : p = 0 := congrArg Fin.val hp0
      omega
  obtain ⟨Pc, hPcKey⟩ := hcReal
  obtain ⟨Pp, hPpKey⟩ := hpReal
  have hpUp : B.E.image pF = (buildProperLossForest H rank).parent (B.E.image cF) := by
    have hEqF : B.up cF = pF := Fin.ext (B.hUp cF)
    rw [← hEqF, B.E.parent_eq cF]
  have hPpParent : (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).parent (B.E.image cF)) = some Pp := by
    rw [← hpUp]; exact hPpKey
  have hDistinct := buildProperLossForest_edge_distinct_cuts rankArc flat hPcKey hPpParent
  have hFresh : ∃ z : Vertex H, Pc.Mem z ∧ ¬ Pp.Mem z := by
    by_cases h1 : Pp.Mem Pc.fst
    · by_cases h2 : Pp.Mem Pc.snd
      · exfalso
        apply hDistinct
        intro z
        constructor
        · intro hz
          rcases hz with rfl | rfl
          · by_cases he1 : Pp.fst = Pc.fst
            · exact Or.inl he1
            · by_cases he2 : Pp.fst = Pc.snd
              · exact Or.inr he2
              · exfalso
                rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
                · exact he1 h1a.symm
                · exact he1 h1a.symm
                · exact he2 h2a.symm
                · exact Pc.ne (h1b.trans h2b.symm)
          · by_cases he1 : Pp.snd = Pc.fst
            · exact Or.inl he1
            · by_cases he2 : Pp.snd = Pc.snd
              · exact Or.inr he2
              · exfalso
                rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
                · exact Pc.ne (h1a.trans h2a.symm)
                · exact he2 h2b.symm
                · exact he1 h1b.symm
                · exact Pc.ne (h1b.trans h2b.symm)
        · intro hz
          rcases hz with rfl | rfl
          · exact h1
          · exact h2
      · exact ⟨Pc.snd, Or.inr rfl, h2⟩
    · exact ⟨Pc.fst, Or.inl rfl, h1⟩
  obtain ⟨z, hzPc, hzNotPp⟩ := hFresh
  have hzLost : H.Lost Pp z := buildProperLossForest_edge_endpoints_lost rankArc flat hPcKey hPpParent z hzPc
  have hTrigZ : max (rankKahn Pp.fst) (rankKahn Pp.snd) < rankKahn z :=
    trigger_lt_properLoss flat rankKahn rankArcKahn ⟨hzLost, hzNotPp⟩
  have hzLeMax : rankKahn z ≤ max (rankKahn Pc.fst) (rankKahn Pc.snd) := by
    rcases hzPc with rfl | rfl
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  exact ⟨Pc, Pp, (B.E.back_eq cF).trans (congrArg some hPcKey),
    (B.E.back_eq pF).trans (congrArg some hPpKey), Nat.lt_of_lt_of_le hTrigZ hzLeMax⟩

end MathBridges

/-! ### 3. Shared 15-register RAM stepping & `PhasesExec` helpers -/

section RamHelpers

variable {bits : Nat} {L : Layout bits}

private def putReg (s : State L) (d : Fin L.registerCount) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_putReg (s : State L) (d r : Fin L.registerCount) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r; simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp only [he, ite_false]
    exact Array.getElem_set_ne hd hr hv.symm

theorem step_imm_at {code : Program L} {input : Input L} {s : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {d a : Fin L.registerCount}
    (hf : code[s.pc]? = some (.mov d a)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s a ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d (reg s a), ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d (reg s a))) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem sub_no_wrap {bits : Nat} (a b : Word bits) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  rw [sub_val, show 2 ^ bits + a.val - b.val = (a.val - b.val) + 2 ^ bits by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem step_add_at {code : Program L} {input : Input L} {s : State L}
    {d a b : Fin L.registerCount}
    (hf : code[s.pc]? = some (.add d a b)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = add (reg s a) (reg s b) ∧
      (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d (add (reg s a) (reg s b)), ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d (add (reg s a) (reg s b)))) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_sub_at {code : Program L} {input : Input L} {s : State L}
    {d a b : Fin L.registerCount}
    (hf : code[s.pc]? = some (.sub d a b)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = sub (reg s a) (reg s b) ∧
      (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d (sub (reg s a) (reg s b)), ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d (sub (reg s a) (reg s b)))) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_loadInput_at {code : Program L} {input : Input L} {s : State L}
    {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw : input.words[(reg s a).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (input.words[(reg s a).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_loadData_at {code : Program L} {input : Input L} {s : State L}
    {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData d a)) (hn : s.pc + 1 < code.size)
    (hw : s.data[(reg s a).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step; rw [hf]
    change (s.data[(reg s a).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr; simp [reg_putReg, hr]

theorem step_storeData_at {code : Program L} {input : Input L} {s : State L}
    {a v : Fin L.registerCount} (hf : code[s.pc]? = some (.storeData a v))
    (ha : (reg s a).val < s.data.size) (hn : s.pc + 1 < code.size) :
    let t : State L :=
      { s with
        data := s.data.set (reg s a).val (reg s v) ha
        pc := s.pc + 1
        data_size := by simp only [Array.size_set, s.data_size] }
    step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧ t.regs = s.regs := by
  intro t
  have hs : step code input s = some (.next t) := by
    unfold step; rw [hf]
    change (if h : (reg s a).val < s.data.size then
      if s.pc + 1 < code.size then some (Transition.next t) else none else none) = _
    rw [dite_eq_left ha, ite_eq_left hn]
  exact ⟨hs, rfl, rfl⟩

theorem step_storeData_opaque {code : Program L} {input : Input L} {s : State L}
    {a v : Fin L.registerCount} (hf : code[s.pc]? = some (.storeData a v))
    (ha : (reg s a).val < s.data.size) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.regs = s.regs ∧ t.data = s.data.set (reg s a).val (reg s v) ha :=
  ⟨_, (step_storeData_at hf ha hn).1, rfl, rfl, rfl⟩

theorem step_branchLt_at {code : Program L} {input : Input L} {s : State L}
    {a b : Fin L.registerCount} {tT tF : Nat}
    (hf : code[s.pc]? = some (.branchLt a b tT tF))
    (hFit : (if (reg s a).val < (reg s b).val then tT else tF) < code.size) :
    let nextPc := if (reg s a).val < (reg s b).val then tT else tF
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = nextPc ∧
      t.regs = s.regs ∧ t.data = s.data := by
  intro nextPc
  refine ⟨{ s with pc := nextPc }, ?_, rfl, rfl, rfl⟩
  unfold step; rw [hf]
  change (if (if ltb (reg s a) (reg s b) then tT else tF) < code.size then
    some (Transition.next { s with pc := if ltb (reg s a) (reg s b) then tT else tF }) else none) = _
  have hEq : ltb (reg s a) (reg s b) = decide ((reg s a).val < (reg s b).val) := by
    cases h : ltb (reg s a) (reg s b) with
    | true => simp [(ltb_eq_true (reg s a) (reg s b)).mp h]
    | false =>
      have hn : ¬ (reg s a).val < (reg s b).val := fun hlt => by
        rw [(ltb_eq_true _ _).mpr hlt] at h; cases h
      simp [hn]
  simp only [hEq, decide_eq_true_eq]
  rw [ite_eq_left hFit]

/-- Unconditional jump encoded as `branchLt r0 r0 tgt tgt`. -/
def jmpInstr {bits k : Nat} (hk : 0 < k) (tgt : Nat) : Instr bits k :=
  .branchLt ⟨0, hk⟩ ⟨0, hk⟩ tgt tgt

theorem step_jmp_at {code : Program L} {input : Input L} {s : State L} {tgt : Nat}
    (hReg : 0 < L.registerCount)
    (hf : code[s.pc]? = some (.branchLt ⟨0, hReg⟩ ⟨0, hReg⟩ tgt tgt)) (hFit : tgt < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = tgt ∧
      t.regs = s.regs ∧ t.data = s.data := by
  have h := step_branchLt_at (input := input) hf (by split <;> exact hFit)
  simpa only [ite_self] using h

theorem sub_exact {x y : Word bits} (hle : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hx := x.isLt
  have hlt : x.val - y.val < 2 ^ bits := by omega
  rw [sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

/-! ### `PhasesExec` & `linkNonEmpty` -/

inductive PhasesExec (input : Input L) :
    List (Phase L) → State L → State L → Nat → Prop where
  | nil (s : State L) : PhasesExec input [] s s 0
  | cons {p : Phase L} {ps : List (Phase L)} {s t u : State L} {a b : Nat} :
      run p.code input a (Phase.initial s) = some ⟨t, a⟩ →
      PhasesExec input ps t u b →
      PhasesExec input (p :: ps) s u (a + b)

theorem PhasesExec.single {input : Input L} (p : Phase L) {s t : State L} {w : Nat}
    (h : run p.code input w (Phase.initial s) = some ⟨t, w⟩) :
    PhasesExec input [p] s t w := by
  simpa only [Nat.add_zero] using PhasesExec.cons h (PhasesExec.nil t)

theorem PhasesExec.append {input : Input L} {ps qs : List (Phase L)}
    {s t u : State L} {a b : Nat}
    (hp : PhasesExec input ps s t a) (hq : PhasesExec input qs t u b) :
    PhasesExec input (ps ++ qs) s u (a + b) := by
  induction hp with
  | nil => simpa only [Nat.zero_add, List.nil_append] using hq
  | cons hstep _ ih =>
    simpa only [List.cons_append, Nat.add_assoc] using PhasesExec.cons hstep (ih hq)

def linkNonEmpty (p : Phase L) : List (Phase L) → Phase L
  | [] => p
  | q :: qs => p.link (linkNonEmpty q qs)

theorem run_linkNonEmpty {input : Input L} :
    ∀ (ps : List (Phase L)) (p : Phase L) {s t : State L} {w : Nat},
      PhasesExec input (p :: ps) s t w →
      ∃ u states,
        u.regs = t.regs ∧
        u.data = t.data ∧
        run (linkNonEmpty p ps).code input w (Phase.initial s) = some ⟨u, w⟩ ∧
        SuccessfulTrace (linkNonEmpty p ps).code input (Phase.initial s) states ⟨u, w⟩ ∧
        tracePeakWords input states = footprint L
  | [], p, s, t, w, h => by
    cases h with
    | cons hr hNil =>
      cases hNil with
      | nil =>
        rw [Nat.add_zero]
        obtain ⟨states, hTrace⟩ := run_has_successfulTrace hr
        exact ⟨t, states, rfl, rfl, hr, hTrace, hTrace.peak_eq⟩
  | q :: qs, p, s, t, w, h => by
    cases h with
    | cons hr hTail =>
      obtain ⟨mid, _, hMidRegs, hMidData, hMidRun, _, _⟩ := run_linkNonEmpty qs q hTail
      have hMidRun' : run (linkNonEmpty q qs).code input _ (Phase.initial _) = some ⟨mid, _⟩ := hMidRun
      have hSize : 0 < (linkNonEmpty q qs).code.size :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (linkNonEmpty q qs).haltFits
      obtain ⟨v, states, hvRegs, hvData, hvRun, hvTrace, hvPeak⟩ :=
        run_linked_pair p (linkNonEmpty q qs).code hSize hr hMidRun'
      exact ⟨v, states, hvRegs.trans hMidRegs, hvData.trans hMidData, hvRun, hvTrace, hvPeak⟩

theorem steps_add_mul6 {code : Program L} {input : Input L} {basePc : Nat}
    {dst s : Fin L.registerCount} (hne : dst ≠ s)
    (hPl : Placed code basePc
      [ .add dst s s
      , .add dst dst s
      , .add dst dst dst
      ])
    (hSz : basePc + 3 < code.size)
    (st : State L) (hpc : st.pc = basePc)
    (hFit : 6 * (reg st s).val < 2 ^ bits) :
    ∃ t : State L, Steps code input 3 st t ∧ t.pc = basePc + 3 ∧
      t.data = st.data ∧ (reg t dst).val = 6 * (reg st s).val ∧
      (∀ r, r ≠ dst → reg t r = reg st r) := by
  let x := (reg st s).val
  have h1 : code[st.pc]? = some (.add dst s s) := by
    rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hrd1, hro1, hd1⟩ := step_add_at (input := input) h1 (by rw [hpc]; omega)
  have hNo1 : (reg st s).val + (reg st s).val < 2 ^ bits := by omega
  have hr1d : (reg s1 dst).val = 2 * x := by rw [hrd1, add_no_wrap _ _ hNo1]; omega
  have hr1s : (reg s1 s).val = x := by rw [hro1 s hne.symm]
  have h2 : code[s1.pc]? = some (.add dst dst s) := by
    rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hrd2, hro2, hd2⟩ := step_add_at (input := input) h2 (by rw [hpc1, hpc]; omega)
  have hNo2 : (reg s1 dst).val + (reg s1 s).val < 2 ^ bits := by rw [hr1d, hr1s]; omega
  have hr2d : (reg s2 dst).val = 3 * x := by rw [hrd2, add_no_wrap _ _ hNo2, hr1d, hr1s]; omega
  have h3 : code[s2.pc]? = some (.add dst dst dst) := by
    rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hrd3, hro3, hd3⟩ := step_add_at (input := input) h3 (by rw [hpc2, hpc1, hpc]; omega)
  have hNo3 : (reg s2 dst).val + (reg s2 dst).val < 2 ^ bits := by rw [hr2d]; omega
  have hr3d : (reg s3 dst).val = 6 * x := by rw [hrd3, add_no_wrap _ _ hNo3, hr2d]; omega
  refine ⟨s3, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.zero s3))),
    by omega, by rw [hd3, hd2, hd1], hr3d, fun r hr => ?_⟩
  rw [hro3 r hr, hro2 r hr, hro1 r hr]

theorem steps_add_mul18 {code : Program L} {input : Input L} {basePc : Nat}
    {dst tmp s : Fin L.registerCount}
    (_hne1 : tmp ≠ s) (hne2 : dst ≠ tmp) (_hne3 : dst ≠ s)
    (hPl : Placed code basePc
      [ .add tmp s s
      , .add dst tmp tmp
      , .add dst dst dst
      , .add dst dst dst
      , .add dst dst tmp
      ])
    (hSz : basePc + 5 < code.size)
    (st : State L) (hpc : st.pc = basePc)
    (hFit : 18 * (reg st s).val < 2 ^ bits) :
    ∃ t : State L, Steps code input 5 st t ∧ t.pc = basePc + 5 ∧
      t.data = st.data ∧ (reg t dst).val = 18 * (reg st s).val ∧
      (∀ r, r ≠ dst → r ≠ tmp → reg t r = reg st r) := by
  let x := (reg st s).val
  have h1 : code[st.pc]? = some (.add tmp s s) := by rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hrd1, hro1, hd1⟩ := step_add_at (input := input) h1 (by rw [hpc]; omega)
  have hr1t : (reg s1 tmp).val = 2 * x := by
    rw [hrd1, add_no_wrap _ _ (by omega)]; omega
  have h2 : code[s1.pc]? = some (.add dst tmp tmp) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hrd2, hro2, hd2⟩ := step_add_at (input := input) h2 (by rw [hpc1, hpc]; omega)
  have hr2d : (reg s2 dst).val = 4 * x := by
    rw [hrd2, add_no_wrap _ _ (by rw [hr1t]; omega), hr1t]; omega
  have hr2t : (reg s2 tmp).val = 2 * x := by rw [hro2 tmp hne2.symm, hr1t]
  have h3 : code[s2.pc]? = some (.add dst dst dst) := by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hrd3, hro3, hd3⟩ := step_add_at (input := input) h3 (by rw [hpc2, hpc1, hpc]; omega)
  have hr3d : (reg s3 dst).val = 8 * x := by
    rw [hrd3, add_no_wrap _ _ (by rw [hr2d]; omega), hr2d]; omega
  have hr3t : (reg s3 tmp).val = 2 * x := by rw [hro3 tmp hne2.symm, hr2t]
  have h4 : code[s3.pc]? = some (.add dst dst dst) := by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl
  obtain ⟨s4, hs4, hpc4, hrd4, hro4, hd4⟩ := step_add_at (input := input) h4 (by rw [hpc3, hpc2, hpc1, hpc]; omega)
  have hr4d : (reg s4 dst).val = 16 * x := by
    rw [hrd4, add_no_wrap _ _ (by rw [hr3d]; omega), hr3d]; omega
  have hr4t : (reg s4 tmp).val = 2 * x := by rw [hro4 tmp hne2.symm, hr3t]
  have h5 : code[s4.pc]? = some (.add dst dst tmp) := by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl
  obtain ⟨s5, hs5, hpc5, hrd5, hro5, hd5⟩ := step_add_at (input := input) h5 (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; omega)
  have hr5d : (reg s5 dst).val = 18 * x := by
    rw [hrd5, add_no_wrap _ _ (by rw [hr4d, hr4t]; omega), hr4d, hr4t]; omega
  refine ⟨s5, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.zero s5))))),
    by omega, by rw [hd5, hd4, hd3, hd2, hd1], hr5d, fun r hr1 hr2 => ?_⟩
  rw [hro5 r hr1, hro4 r hr1, hro3 r hr1, hro2 r hr1, hro1 r hr2]

def storeSeqInstrs {bits k : Nat} (ptr one : Fin k) : List (Fin k) → List (Instr bits k)
  | [] => []
  | [v] => [.storeData ptr v]
  | v :: w :: vs => .storeData ptr v :: .add ptr ptr one :: storeSeqInstrs ptr one (w :: vs)

@[simp] theorem storeSeqInstrs_length {bits k : Nat} (ptr one : Fin k) (vs : List (Fin k)) :
    (storeSeqInstrs (bits := bits) ptr one vs).length =
      match vs with | [] => 0 | _ => 2 * vs.length - 1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      simp only [storeSeqInstrs, List.length_cons] at ih ⊢
      omega

theorem nonHalt_storeSeqInstrs {bits : Nat} (ptr one : Fin 15) (vs : List (Fin 15))
    {inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (storeSeqInstrs (bits := bits) ptr one vs).all (nonHalt (L := layout bits inputCap workCap hi hw)) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      simp only [storeSeqInstrs, List.all_cons]
      exact ih

theorem run_storeSeq {code : Program L} {input : Input L}
    (ptr one : Fin L.registerCount) (hne : ptr ≠ one)
    (vs : List (Fin L.registerCount)) :
    ∀ (basePc base : Nat) (st : State L),
      (∀ v ∈ vs, v ≠ ptr) →
      Placed code basePc (storeSeqInstrs ptr one vs) →
      basePc + (storeSeqInstrs (bits := bits) ptr one vs).length < code.size →
      st.pc = basePc →
      (reg st ptr).val = base →
      (reg st one).val = 1 →
      base + vs.length ≤ st.data.size →
      base + vs.length < 2 ^ bits →
      ∃ t : State L,
        Steps code input (storeSeqInstrs (bits := bits) ptr one vs).length st t ∧
        t.pc = basePc + (storeSeqInstrs (bits := bits) ptr one vs).length ∧
        (0 < vs.length → (reg t ptr).val = base + (vs.length - 1)) ∧
        (∀ r, r ≠ ptr → reg t r = reg st r) ∧
        (∀ j, (j < base ∨ base + vs.length ≤ j) → t.data[j]? = st.data[j]?) ∧
        (∀ i (hi : i < vs.length), t.data[base + i]? = some (reg st (vs[i]'hi))) := by
  induction vs with
  | nil =>
    intro basePc base st _ _ _ hpc _ _ _ _
    exact ⟨st, Steps.zero st, by simp [hpc], fun h => False.elim (Nat.not_lt_zero _ h),
      fun _ _ => rfl, fun _ _ => rfl, fun i hi => by cases hi⟩
  | cons v vs ih =>
    cases vs with
    | nil =>
      intro basePc base st _ hPl hSz hpc hPtr _ hFit _
      have hAt : code[st.pc]? = some (.storeData ptr v) := by rw [hpc]; exact hPl 0 _ rfl
      have hStLt : (reg st ptr).val < st.data.size := by rw [hPtr]; simp at hFit; omega
      obtain ⟨hs, hpc1, _⟩ := step_storeData_at (input := input) hAt hStLt (by
        rw [hpc]; simp only [storeSeqInstrs, List.length_singleton] at hSz; exact hSz)
      refine ⟨_, Steps.cons hs (Steps.zero _), by rw [hpc1, hpc]; rfl,
        fun _ => by change (reg st ptr).val = base + (1 - 1); omega,
        fun _ _ => rfl, fun j hj => ?_, fun i hi => ?_⟩
      · simp only [List.length_singleton] at hj
        have hjne : base ≠ j := by omega
        change (st.data.set (reg st ptr).val (reg st v) hStLt)[j]? = st.data[j]?
        exact Array.getElem?_set_ne hStLt (by rw [hPtr]; exact hjne)
      · have hi0 : i = 0 := by simp at hi; omega
        subst i
        simp only [Nat.add_zero, List.getElem_cons_zero]
        change (st.data.set (reg st ptr).val (reg st v) hStLt)[base]? = _
        rw [← hPtr]
        simp [hStLt]
    | cons w ws =>
      intro basePc base st hneV hPl hSz hpc hPtr hOne hFit hFitB
      have hAt0 : code[st.pc]? = some (.storeData ptr v) := by rw [hpc]; exact hPl 0 _ rfl
      have hStLt : (reg st ptr).val < st.data.size := by rw [hPtr]; simp at hFit; omega
      obtain ⟨hs0, hpc1, _⟩ := step_storeData_at (input := input) hAt0 hStLt (by
        rw [hpc]; simp only [storeSeqInstrs, List.length_cons] at hSz; omega)
      let s1 : State L :=
        { st with
          data := st.data.set (reg st ptr).val (reg st v) hStLt
          pc := st.pc + 1
          data_size := by simp only [Array.size_set, st.data_size] }
      have hAt1 : code[s1.pc]? = some (.add ptr ptr one) := by
        change code[st.pc + 1]? = _
        rw [hpc]; exact hPl 1 _ rfl
      obtain ⟨s2, hs1, hpc2, hrd2, hro2, hd2⟩ := step_add_at (input := input) hAt1 (by
        change st.pc + 1 + 1 < code.size
        rw [hpc]; simp only [storeSeqInstrs, List.length_cons] at hSz; omega)
      have hPtr2 : (reg s2 ptr).val = base + 1 := by
        have hrp1 : reg s1 ptr = reg st ptr := rfl
        have hro1 : reg s1 one = reg st one := rfl
        rw [hrd2, hrp1, hro1, add_no_wrap _ _ (by rw [hPtr, hOne]; simp at hFitB; omega), hPtr, hOne]
      have hOne2 : (reg s2 one).val = 1 := by
        rw [hro2 one hne.symm]; exact hOne
      have hPlRest : Placed code (basePc + 2) (storeSeqInstrs ptr one (w :: ws)) := by
        intro i op hi
        rw [Nat.add_assoc]
        exact hPl (2 + i) op (by
          rw [show 2 + i = i.succ.succ by omega]
          exact hi)
      have hSzRest : (basePc + 2) + (storeSeqInstrs (bits := bits) ptr one (w :: ws)).length < code.size := by
        simp only [storeSeqInstrs, List.length_cons] at hSz ⊢; omega
      obtain ⟨t, htSteps, htpc, htPtr, htRegs, htFrame, htWrite⟩ :=
        ih (basePc + 2) (base + 1) s2
          (fun x hx => hneV x (List.mem_cons_of_mem v hx)) hPlRest hSzRest
          (by rw [hpc2]; change st.pc + 1 + 1 = _; rw [hpc])
          hPtr2 hOne2 (by rw [s2.data_size]; simp only [← st.data_size] at hFit ⊢; simp at hFit ⊢; omega)
          (by simp at hFitB ⊢; omega)
      have hReg2 : ∀ r, r ≠ ptr → reg s2 r = reg st r := fun r hr => by
        rw [hro2 r hr]; rfl
      refine ⟨t, Steps.cons hs0 (Steps.cons hs1 htSteps), ?_, ?_,
        fun r hr => (htRegs r hr).trans (hReg2 r hr),
        fun j hj => ?_, fun i hi => ?_⟩
      · simp only [storeSeqInstrs, List.length_cons] at htpc ⊢; omega
      · intro _
        rw [htPtr (by simp)]
        simp only [List.length_cons]
        omega
      · rw [htFrame j (by simp at hj ⊢; omega), hd2]
        change (st.data.set (reg st ptr).val (reg st v) hStLt)[j]? = st.data[j]?
        exact Array.getElem?_set_ne hStLt (by rw [hPtr]; simp at hj; omega)
      · cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [htFrame base (Or.inl (Nat.lt_succ_self base)), hd2]
          change (st.data.set (reg st ptr).val (reg st v) hStLt)[base]? = some (reg st v)
          rw [← hPtr]
          simp [hStLt]
        | succ k =>
          have hk : k < (w :: ws).length := by simp at hi ⊢; omega
          rw [show base + (k + 1) = (base + 1) + k by omega, htWrite k hk]
          have hwNe : (w :: ws)[k]'hk ≠ ptr := hneV _ (List.mem_cons_of_mem v (List.getElem_mem hk))
          rw [hReg2 _ hwNe]
          rfl

theorem step_goto_at {code : Program L} {input : Input L} {s : State L} {tgt : Nat}
    (hf : code[s.pc]? = some (.goto tgt)) (hFit : tgt < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = tgt ∧
      t.regs = s.regs ∧ t.data = s.data := by
  refine ⟨{ s with pc := tgt }, ?_, rfl, rfl, rfl⟩
  unfold step; rw [hf]
  change (if tgt < code.size then some (Transition.next { s with pc := tgt }) else none) = _
  rw [ite_eq_left hFit]

theorem step_halt_at {code : Program L} {input : Input L} {s : State L}
    (hf : code[s.pc]? = some .halt) :
    step code input s = some (.halted s) := by
  unfold step; rw [hf]; rfl

theorem Placed_append_left {code : Program L} {base : Nat}
    {a b : List (Instr bits L.registerCount)}
    (h : Placed code base (a ++ b)) : Placed code base a := by
  intro i op hi
  exact h i op (by rw [List.getElem?_append_left (by
    cases hc : a[i]? with
    | none => rw [hc] at hi; cases hi
    | some _ => exact List.getElem?_eq_some_iff.mp hc |>.1)]; exact hi)

theorem Placed_append_right {code : Program L} {base : Nat}
    {a b : List (Instr bits L.registerCount)}
    (h : Placed code base (a ++ b)) : Placed code (base + a.length) b := by
  intro i op hi
  rw [Nat.add_assoc]
  exact h (a.length + i) op (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hi)

theorem Placed_toArray_halt {xs : List (Instr bits L.registerCount)} :
    Placed ((xs ++ [Instr.halt]).toArray) 0 xs := by
  intro i op hi
  simp only [Nat.zero_add]
  have hlt : i < xs.length := by
    cases hc : xs[i]? with
    | none => rw [hc] at hi; cases hi
    | some _ => exact (List.getElem?_eq_some_iff.mp hc).1
  have hL : i < (xs ++ [Instr.halt]).length := Nat.lt_of_lt_of_le hlt (by simp)
  change (xs ++ [Instr.halt]).toArray[i]? = some op
  rw [Array.getElem?_eq_getElem (by simpa using hL)]
  simp [List.getElem_append_left hlt, List.getElem?_eq_getElem hlt] at hi ⊢
  exact hi

theorem steps_1_of_step {code : Program L} {input : Input L} {s t : State L}
    (hs : step code input s = some (.next t)) : Steps code input 1 s t :=
  Steps.cons hs (Steps.zero t)

end RamHelpers

/-! ### 3B. Codec Word Characterization Helpers -/

section CodecWords

theorem mapValid_of_mapBound {bits : Nat} (hTag : TagsFit bits) {m : Map}
    (hm : MapBound (2 ^ bits) m) : (mapCodec hTag).valid m :=
  ⟨⟨hm.1, trivial⟩, ⟨hm.2, trivial⟩⟩

theorem storedValid_of_bounds {bits : Nat} (hTag : TagsFit bits) {r : CheckedFold.Stored}
    (hp : r.parent < 2 ^ bits) (hj : r.jump < 2 ^ bits)
    (hpm : MapBound (2 ^ bits) r.parentMap) (hjm : MapBound (2 ^ bits) r.jumpMap) :
    (storedCodec hTag).valid r :=
  ⟨⟨hp, hj⟩, ⟨mapValid_of_mapBound hTag hpm, mapValid_of_mapBound hTag hjm⟩⟩

theorem intervalCodec_encode_0 {bits : Nat} (hTag : TagsFit bits)
    (x : Interval) (hx : RankBound (2 ^ bits) x) :
    ((intervalCodec hTag).encode x hx 0).val =
      match x with | .empty => 0 | .span _ _ => 1 := by
  cases x <;> rfl

theorem intervalCodec_encode_1 {bits : Nat} (hTag : TagsFit bits)
    (x : Interval) (hx : RankBound (2 ^ bits) x) :
    ((intervalCodec hTag).encode x hx 1).val =
      match x with | .empty => 0 | .span lo _ => lo := by
  cases x <;> rfl

theorem intervalCodec_encode_2 {bits : Nat} (hTag : TagsFit bits)
    (x : Interval) (hx : RankBound (2 ^ bits) x) :
    ((intervalCodec hTag).encode x hx 2).val =
      match x with | .empty => 0 | .span _ hi => hi := by
  cases x <;> rfl

theorem slotCodec_encode_0 {bits : Nat} (hTag : TagsFit bits)
    (s : Option (Fin 2)) (hs : (slotCodec hTag).valid s) :
    ((slotCodec hTag).encode s hs 0).val =
      match s with | none => 0 | some 0 => 1 | some 1 => 2 := by
  rcases s with _ | j
  · rfl
  · rcases fin2_cases j with rfl | rfl <;> rfl

theorem coordCodec_encode_at {bits : Nat} (hTag : TagsFit bits)
    (c : Coord) (hc : (coordCodec hTag).valid c) (i : Fin 4) :
    ((coordCodec hTag).encode c hc i).val =
      if i.val = 0 then (match c.base with | .empty => 0 | .span _ _ => 1)
      else if i.val = 1 then (match c.base with | .empty => 0 | .span lo _ => lo)
      else if i.val = 2 then (match c.base with | .empty => 0 | .span _ hi => hi)
      else (match c.slot with | none => 0 | some 0 => 1 | some 1 => 2) := by
  rcases i with ⟨iv, hiv⟩
  rcases c with ⟨b, sl⟩
  match iv with
  | 0 => cases b <;> rfl
  | 1 => cases b <;> rfl
  | 2 => cases b <;> rfl
  | 3 =>
    rcases sl with _ | j
    · rfl
    · rcases fin2_cases j with rfl | rfl <;> rfl
  | n + 4 => omega

theorem mapCodec_encode_at {bits : Nat} (hTag : TagsFit bits)
    (m : Map) (hm : MapBound (2 ^ bits) m) (i : Fin 8) :
    (mapCodec hTag).encode m (mapValid_of_mapBound hTag hm) i =
      if h : i.val < 4 then (coordCodec hTag).encode m.x0 ⟨hm.1, trivial⟩ ⟨i.val, h⟩
      else (coordCodec hTag).encode m.x1 ⟨hm.2, trivial⟩ ⟨i.val - 4, by omega⟩ := by
  rcases i with ⟨iv, hiv⟩
  match iv with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | n + 8 => omega

theorem mapCodec_encode_identity {bits : Nat} (hTag : TagsFit bits)
    (hm : (mapCodec hTag).valid Map.identity) (i : Fin 8) :
    ((mapCodec hTag).encode Map.identity hm i).val =
      if i.val = 3 then 1 else if i.val = 7 then 2 else 0 := by
  rcases i with ⟨iv, hiv⟩
  match iv with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | n + 8 => omega

theorem storedCodec_encode_at {bits : Nat} (hTag : TagsFit bits)
    (r : CheckedFold.Stored)
    (hp : r.parent < 2 ^ bits) (hj : r.jump < 2 ^ bits)
    (hpm : MapBound (2 ^ bits) r.parentMap) (hjm : MapBound (2 ^ bits) r.jumpMap)
    (i : Fin 18) :
    ((storedCodec hTag).encode r (storedValid_of_bounds hTag hp hj hpm hjm) i) =
      if _ : i.val = 0 then ⟨r.parent, hp⟩
      else if _ : i.val = 1 then ⟨r.jump, hj⟩
      else if h2 : i.val < 10 then
        (mapCodec hTag).encode r.parentMap (mapValid_of_mapBound hTag hpm) ⟨i.val - 2, by omega⟩
      else
        (mapCodec hTag).encode r.jumpMap (mapValid_of_mapBound hTag hjm) ⟨i.val - 10, by omega⟩ := by
  rcases i with ⟨iv, hiv⟩
  match iv with
  | 0 => rfl | 1 => rfl
  | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl
  | n + 18 => omega

end CodecWords

/-! ### 4. Metadata & Phase 0 (`initMetaPhase`) -/

section MetaAndPhase0

variable {bits : Nat}

abbrev reg0 : Fin 15 := ⟨0, by decide⟩
abbrev reg1 : Fin 15 := ⟨1, by decide⟩
abbrev reg2 : Fin 15 := ⟨2, by decide⟩
abbrev reg3 : Fin 15 := ⟨3, by decide⟩
abbrev reg4 : Fin 15 := ⟨4, by decide⟩
abbrev reg5 : Fin 15 := ⟨5, by decide⟩
abbrev reg6 : Fin 15 := ⟨6, by decide⟩
abbrev reg7 : Fin 15 := ⟨7, by decide⟩
abbrev reg8 : Fin 15 := ⟨8, by decide⟩
abbrev reg9 : Fin 15 := ⟨9, by decide⟩
abbrev reg10 : Fin 15 := ⟨10, by decide⟩
abbrev reg11 : Fin 15 := ⟨11, by decide⟩
abbrev reg12 : Fin 15 := ⟨12, by decide⟩
abbrev reg13 : Fin 15 := ⟨13, by decide⟩

def mul6Instrs (dst src : Fin 15) : List (Instr bits 15) :=
  [ .add dst src src
  , .add dst dst src
  , .add dst dst dst
  ]

/-- `dst := 18 * src` (`dst ≠ src`). Note `2*s -> 4*s -> 8*s -> 16*s -> ...`;
simpler: `3*s -> 6*s -> 9*s -> 18*s` with `tmp`! Or in 5 instructions with `dst` alone?
`dst := 2*s`, `dst := 4*s`, `dst := 8*s`, `dst := 16*s`: needs `2*s` in `src` or `tmp`.
With `(dst tmp : Fin 15)`: `tmp := s + s` (`2s`), `dst := tmp + tmp` (`4s`),
`dst := dst + dst` (`8s`), `dst := dst + dst` (`16s`), `dst := dst + tmp` (`18s`) (`5` instrs!). -/
def mul18Instrs (dst tmp src : Fin 15) : List (Instr bits 15) :=
  [ .add tmp src src
  , .add dst tmp tmp
  , .add dst dst dst
  , .add dst dst dst
  , .add dst dst tmp
  ]

def metaLoadInstrs (dst tmp : Fin 15) (off : Nat) (hOff : off < 2 ^ bits) :
    List (Instr bits 15) :=
  [ .imm tmp ⟨off, hOff⟩
  , .add tmp rMeta tmp
  , .loadData dst tmp
  ]

def metaStoreInstrs (src tmp : Fin 15) (off : Nat) (hOff : off < 2 ^ bits) :
    List (Instr bits 15) :=
  [ .imm tmp ⟨off, hOff⟩
  , .add tmp rMeta tmp
  , .storeData tmp src
  ]

def initMetaPartA (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg0 ⟨0, by omega⟩
  , .imm reg1 ⟨1, by omega⟩
  , .imm reg2 ⟨2, by omega⟩
  , .imm reg3 ⟨3, by omega⟩
  , .loadInput reg4 reg0   -- reg4 = n_H
  , .loadInput reg5 reg1   -- reg5 = m_H
  , .loadInput reg6 reg2   -- reg6 = N_H
  , .loadInput reg7 reg3   -- reg7 = nGlobal
  ]

def initMetaPartB : List (Instr bits 15) :=
  [ .add reg10 reg9 reg10
  , .add reg11 reg10 reg4   -- reg11 := topoRankBase = orderBase + n_H
  , .add reg12 reg11 reg4   -- reg12 := trigHeadBase = topoRankBase + n_H
  , .add reg13 reg12 reg4   -- reg13 := trigNextBase = trigHeadBase + n_H
  , .add reg8 reg13 reg6    -- reg8  := inStartBase = trigNextBase + N_H
  , .add reg2 reg8 reg4
  , .add reg2 reg2 reg1     -- reg2  := inArcIdBase = inStartBase + n_H + 1
  , .add rMeta reg2 reg5    -- rMeta := metaBase = inArcIdBase + m_H
  , .mov reg3 rMeta
  ]

def initMetaSeq1Vars : List (Fin 15) :=
  [reg4, reg5, reg6, reg7, reg6, reg9, reg10, reg11, reg12, reg13, reg8, reg2, rMeta]

def initMetaPartC (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .add reg3 reg3 reg1
  , .imm reg8 ⟨48, by omega⟩
  , .add reg8 rMeta reg8
  , .storeData reg3 reg8
  , .add reg3 reg3 reg1    -- reg3 at metaBase + 14
  , .imm reg7 ⟨4, by omega⟩
  , .add reg8 reg7 reg4     -- reg8  := backFstIn = 4 + n_H
  , .add reg9 reg8 reg6     -- reg9  := backSndIn = backFstIn + N_H
  , .add reg10 reg9 reg6    -- reg10 := fEntryIn = backSndIn + N_H
  , .add reg11 reg10 reg6   -- reg11 := fStopIn = fEntryIn + N_H
  , .add reg12 reg11 reg6   -- reg12 := qSrcIn = fStopIn + N_H
  , .add reg13 reg12 reg5   -- reg13 := qHeadIn = qSrcIn + m_H
  , .add reg2 reg13 reg5    -- reg2  := qTailRankIn = qHeadIn + m_H
  ]

def initMetaSeq2Vars : List (Fin 15) :=
  [reg12, reg13, reg2, reg10, reg11, reg7, reg8, reg9]

/-- Phase 0 (`initMeta`): reads `[n_H, m_H, N_H, nGlobal]` from `input.words[0..3]`,
computes all 22 fixed bank pointers into `data[metaBase + 0 .. 21]`, and leaves
`rMeta = metaBase`, `reg0 = 0`, `reg1 = 1`. -/
def initMetaInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  initMetaPartA h100 ++
  (mul18Instrs reg9 reg8 reg6 ++
  ([ .add reg9 reg9 reg6 ] ++
  (mul6Instrs reg10 reg4 ++
  (initMetaPartB ++
  (storeSeqInstrs reg3 reg1 initMetaSeq1Vars ++
  (initMetaPartC h100 ++
  storeSeqInstrs reg3 reg1 initMetaSeq2Vars))))))

end MetaAndPhase0

section Phase0Proofs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_metaLoad_slice {code : Program DomL} {input : Input DomL}
    {basePc off : Nat} {dst tmp : Fin 15} {hOff : off < 2 ^ bits}
    {st : State DomL} {metaBase val : Nat}
    (_hdm : dst ≠ rMeta) (htm : tmp ≠ rMeta)
    (hPl : Placed code basePc (metaLoadInstrs dst tmp off hOff))
    (hSz : basePc + 3 < code.size)
    (hpc : st.pc = basePc)
    (hMeta : (reg st rMeta).val = metaBase)
    (hFit : metaBase + off < 2 ^ bits)
    (hMem : (st.data[metaBase + off]?).map Fin.val = some val) :
    ∃ t : State DomL, Steps code input 3 st t ∧ t.pc = basePc + 3 ∧
      t.data = st.data ∧ (reg t dst).val = val ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ tmp → reg t r = reg st r) := by
  have h1 : code[st.pc]? = some (.imm tmp ⟨off, hOff⟩) := by rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hrt1, hro1, hd1⟩ := step_imm_at (input := input) h1 (by rw [hpc]; omega)
  have hrm1 : (reg s1 rMeta).val = metaBase := by rw [hro1 rMeta htm.symm, hMeta]
  have h2 : code[s1.pc]? = some (.add tmp rMeta tmp) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hrt2, hro2, hd2⟩ := step_add_at (input := input) h2 (by rw [hpc1, hpc]; omega)
  have hAddr2 : (reg s2 tmp).val = metaBase + off := by
    have htr1 : (reg s1 tmp).val = off := by rw [hrt1]
    rw [hrt2, add_no_wrap _ _ (by rw [hrm1, htr1]; exact hFit), hrm1, htr1]
  obtain ⟨w, hw, hwv⟩ := Option.map_eq_some_iff.mp hMem
  have hMem2 : s2.data[(reg s2 tmp).val]? = some w := by
    rw [hAddr2, hd2, hd1]; exact hw
  have h3 : code[s2.pc]? = some (.loadData dst tmp) := by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hrd3, hro3, hd3⟩ := step_loadData_at (input := input) h3 (by rw [hpc2, hpc1, hpc]; omega) hMem2
  refine ⟨s3, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.zero s3))),
    by omega, by rw [hd3, hd2, hd1], by rw [hrd3, hwv], fun r hrd hrt => ?_⟩
  have hr2 := hro3 r hrd
  by_cases hr1 : r = tmp
  · exact absurd hr1 hrt
  · rw [hr2, hro2 r hr1, hro1 r hr1]

theorem run_metaStore_slice {code : Program DomL} {input : Input DomL}
    {basePc off : Nat} {src tmp : Fin 15} {hOff : off < 2 ^ bits}
    {st : State DomL} {metaBase : Nat}
    (htm : tmp ≠ rMeta) (hst : tmp ≠ src)
    (hPl : Placed code basePc (metaStoreInstrs src tmp off hOff))
    (hSz : basePc + 3 < code.size)
    (hpc : st.pc = basePc)
    (hMeta : (reg st rMeta).val = metaBase)
    (hFit : metaBase + off < 2 ^ bits)
    (hLt : metaBase + off < st.data.size) :
    ∃ t : State DomL, Steps code input 3 st t ∧ t.pc = basePc + 3 ∧
      t.data[metaBase + off]? = some (reg st src) ∧
      (∀ j, j ≠ metaBase + off → t.data[j]? = st.data[j]?) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg st r) := by
  have h1 : code[st.pc]? = some (.imm tmp ⟨off, hOff⟩) := by rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, hrt1, hro1, hd1⟩ := step_imm_at (input := input) h1 (by rw [hpc]; omega)
  have hrm1 : (reg s1 rMeta).val = metaBase := by rw [hro1 rMeta htm.symm, hMeta]
  have h2 : code[s1.pc]? = some (.add tmp rMeta tmp) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hrt2, hro2, hd2⟩ := step_add_at (input := input) h2 (by rw [hpc1, hpc]; omega)
  have hAddr2 : (reg s2 tmp).val = metaBase + off := by
    have htr1 : (reg s1 tmp).val = off := by rw [hrt1]
    rw [hrt2, add_no_wrap _ _ (by rw [hrm1, htr1]; exact hFit), hrm1, htr1]
  have hLt2 : (reg s2 tmp).val < s2.data.size := by rw [hAddr2, hd2, hd1]; exact hLt
  have h3 : code[s2.pc]? = some (.storeData tmp src) := by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨hs3, hpc3, hreg3⟩ := step_storeData_at (input := input) h3 hLt2 (by rw [hpc2, hpc1, hpc]; omega)
  have hrs2 : reg s2 src = reg st src := by
    rw [hro2 src hst.symm, hro1 src hst.symm]
  refine ⟨_, Steps.cons hs1 (Steps.cons hs2 (steps_1_of_step hs3)), by omega, ?_, ?_, ?_⟩
  · change (s2.data.set (reg s2 tmp).val (reg s2 src) hLt2)[metaBase + off]? = some (reg st src)
    rw [← hAddr2, ← hrs2]; simp [hLt2]
  · intro j hj
    change (s2.data.set (reg s2 tmp).val (reg s2 src) hLt2)[j]? = st.data[j]?
    rw [Array.getElem?_set_ne hLt2 (by rw [hAddr2]; exact hj.symm), hd2, hd1]
  · intro r hrt
    change reg s2 r = reg st r
    rw [hro2 r hrt, hro1 r hrt]

def metaExpected (n m N nGlobal : Nat) : List Nat :=
  [ n                                        -- 0: n_H
  , m                                        -- 1: m_H
  , N                                        -- 2: N_H
  , nGlobal                                  -- 3: nGlobal
  , N                                        -- 4: storedBase
  , 19 * N                                   -- 5: priorBase
  , orderArrBase n N                         -- 6: orderBase
  , topoRankArrBase n N                      -- 7: topoRankBase
  , trigHeadArrBase n N                      -- 8: trigHeadBase
  , trigNextArrBase n N                      -- 9: trigNextBase
  , inStartArrBase n N                       -- 10: inStartBase
  , inArcIdArrBase n N                       -- 11: inArcIdBase
  , metaArrBase n m N                        -- 12: metaBase
  , tempArrBase n m N                        -- 13: tempBase
  , 4 + n + 4 * N                            -- 14: qSrcInBase
  , 4 + n + 4 * N + m                        -- 15: qHeadInBase
  , 4 + n + 4 * N + 2 * m                    -- 16: qTailRankInBase
  , 4 + n + 2 * N                            -- 17: fEntryInBase
  , 4 + n + 3 * N                            -- 18: fStopInBase
  , 4                                        -- 19: labelsInBase
  , 4 + n                                    -- 20: backFstInBase
  , 4 + n + N                                -- 21: backSndInBase
  ]

structure MetaReady {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (s : State (layout bits inputCap workCap hi hw)) (n m N nGlobal : Nat) : Prop where
  rMeta_eq : (reg s rMeta).val = metaArrBase n m N
  r0_zero : (reg s reg0).val = 0
  r1_one : (reg s reg1).val = 1
  meta_n : (s.data[metaArrBase n m N + mIdxN]?).map Fin.val = some n
  meta_m : (s.data[metaArrBase n m N + mIdxM]?).map Fin.val = some m
  meta_NH : (s.data[metaArrBase n m N + mIdxNH]?).map Fin.val = some N
  meta_nGlobal : (s.data[metaArrBase n m N + mIdxNGlobal]?).map Fin.val = some nGlobal
  meta_storedBase : (s.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some N
  meta_priorBase : (s.data[metaArrBase n m N + mIdxPriorBase]?).map Fin.val = some (19 * N)
  meta_orderBase : (s.data[metaArrBase n m N + mIdxOrderBase]?).map Fin.val = some (orderArrBase n N)
  meta_topoRankBase : (s.data[metaArrBase n m N + mIdxTopoRankBase]?).map Fin.val = some (topoRankArrBase n N)
  meta_trigHeadBase : (s.data[metaArrBase n m N + mIdxTrigHeadBase]?).map Fin.val = some (trigHeadArrBase n N)
  meta_trigNextBase : (s.data[metaArrBase n m N + mIdxTrigNextBase]?).map Fin.val = some (trigNextArrBase n N)
  meta_inStartBase : (s.data[metaArrBase n m N + mIdxInStartBase]?).map Fin.val = some (inStartArrBase n N)
  meta_inArcIdBase : (s.data[metaArrBase n m N + mIdxInArcIdBase]?).map Fin.val = some (inArcIdArrBase n N)
  meta_metaBase : (s.data[metaArrBase n m N + mIdxMetaBase]?).map Fin.val = some (metaArrBase n m N)
  meta_tempBase : (s.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N)
  meta_qSrcIn : 0 < m → (s.data[metaArrBase n m N + mIdxQSrcInBase]?).map Fin.val = some (4 + n + 4 * N)
  meta_qHeadIn : 0 < m → (s.data[metaArrBase n m N + mIdxQHeadInBase]?).map Fin.val = some (4 + n + 4 * N + m)
  meta_qTailRankIn : 0 < m → (s.data[metaArrBase n m N + mIdxQTailRankInBase]?).map Fin.val = some (4 + n + 4 * N + 2 * m)
  meta_fEntryIn : (s.data[metaArrBase n m N + mIdxFEntryInBase]?).map Fin.val = some (4 + n + 2 * N)
  meta_fStopIn : (s.data[metaArrBase n m N + mIdxFStopInBase]?).map Fin.val = some (4 + n + 3 * N)
  meta_labelsIn : (s.data[metaArrBase n m N + mIdxLabelsInBase]?).map Fin.val = some 4
  meta_backFstIn : (s.data[metaArrBase n m N + mIdxBackFstInBase]?).map Fin.val = some (4 + n)
  meta_backSndIn : (s.data[metaArrBase n m N + mIdxBackSndInBase]?).map Fin.val = some (4 + n + N)

theorem MetaReady.preserve {s t : State DomL} {n m N nGlobal : Nat}
    (hs : MetaReady s n m N nGlobal)
    (hMeta : (reg t rMeta).val = metaArrBase n m N)
    (h0 : (reg t reg0).val = 0) (h1 : (reg t reg1).val = 1)
    (hData : ∀ i, i < 22 → t.data[metaArrBase n m N + i]? = s.data[metaArrBase n m N + i]?) :
    MetaReady t n m N nGlobal :=
  ⟨hMeta, h0, h1,
    by rw [hData mIdxN (by decide)]; exact hs.meta_n,
    by rw [hData mIdxM (by decide)]; exact hs.meta_m,
    by rw [hData mIdxNH (by decide)]; exact hs.meta_NH,
    by rw [hData mIdxNGlobal (by decide)]; exact hs.meta_nGlobal,
    by rw [hData mIdxStoredBase (by decide)]; exact hs.meta_storedBase,
    by rw [hData mIdxPriorBase (by decide)]; exact hs.meta_priorBase,
    by rw [hData mIdxOrderBase (by decide)]; exact hs.meta_orderBase,
    by rw [hData mIdxTopoRankBase (by decide)]; exact hs.meta_topoRankBase,
    by rw [hData mIdxTrigHeadBase (by decide)]; exact hs.meta_trigHeadBase,
    by rw [hData mIdxTrigNextBase (by decide)]; exact hs.meta_trigNextBase,
    by rw [hData mIdxInStartBase (by decide)]; exact hs.meta_inStartBase,
    by rw [hData mIdxInArcIdBase (by decide)]; exact hs.meta_inArcIdBase,
    by rw [hData mIdxMetaBase (by decide)]; exact hs.meta_metaBase,
    by rw [hData mIdxTempBase (by decide)]; exact hs.meta_tempBase,
    fun hm => by rw [hData mIdxQSrcInBase (by decide)]; exact hs.meta_qSrcIn hm,
    fun hm => by rw [hData mIdxQHeadInBase (by decide)]; exact hs.meta_qHeadIn hm,
    fun hm => by rw [hData mIdxQTailRankInBase (by decide)]; exact hs.meta_qTailRankIn hm,
    by rw [hData mIdxFEntryInBase (by decide)]; exact hs.meta_fEntryIn,
    by rw [hData mIdxFStopInBase (by decide)]; exact hs.meta_fStopIn,
    by rw [hData mIdxLabelsInBase (by decide)]; exact hs.meta_labelsIn,
    by rw [hData mIdxBackFstInBase (by decide)]; exact hs.meta_backFstIn,
    by rw [hData mIdxBackSndInBase (by decide)]; exact hs.meta_backSndIn⟩

def initMetaPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : Phase (layout bits inputCap workCap hi hw) :=
  let code : Program (layout bits inputCap workCap hi hw) :=
    (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray
  Phase.ofLast code (initMetaInstrs (bits := bits) h100).length
    (by
      dsimp only [code]
      simp)
    (by
      change (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray[(initMetaInstrs (bits := bits) h100).length]? = some .halt
      have hLt : (initMetaInstrs (bits := bits) h100).length <
          (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray.size := by
        simp
      rw [Array.getElem?_eq_getElem hLt]
      simp)
    (by
      rw [List.take_left]
      simp [initMetaInstrs, initMetaPartA, mul18Instrs, mul6Instrs, initMetaPartB,
        initMetaPartC, nonHalt_storeSeqInstrs, nonHalt])

private theorem initMetaPartA_spec {code : Program DomL} {input : Input DomL}
    {basePc : Nat} (h100 : 100 ≤ 2 ^ bits)
    {n m N nGlobal : Nat}
    (hPl : Placed code basePc (initMetaPartA (bits := bits) h100))
    (hSz : basePc + (initMetaPartA (bits := bits) h100).length < code.size)
    (st : State DomL) (hpc : st.pc = basePc)
    (h0 : (input.words[0]?).map Fin.val = some n)
    (h1 : (input.words[1]?).map Fin.val = some m)
    (h2 : (input.words[2]?).map Fin.val = some N)
    (h3 : (input.words[3]?).map Fin.val = some nGlobal) :
    ∃ t : State DomL, Steps code input 8 st t ∧ t.pc = basePc + 8 ∧ t.data = st.data ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t reg4).val = n ∧ (reg t reg5).val = m ∧
      (reg t reg6).val = N ∧ (reg t reg7).val = nGlobal := by
  have hlen : (initMetaPartA (bits := bits) h100).length = 8 := rfl
  obtain ⟨s1, hs1, hpc1, hr1d, hr1o, hd1⟩ := step_imm_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by rw [hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s2, hs2, hpc2, hr2d, hr2o, hd2⟩ := step_imm_at (input := input)
    (by rw [hpc1, hpc]; exact hPl 1 _ rfl) (by rw [hpc1, hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s3, hs3, hpc3, hr3d, hr3o, hd3⟩ := step_imm_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by rw [hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s4, hs4, hpc4, hr4d, hr4o, hd4⟩ := step_imm_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) (by rw [hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h4_0 : (reg s4 reg0).val = 0 := by
    rw [hr4o reg0 (by intro h; cases h), hr3o reg0 (by intro h; cases h), hr2o reg0 (by intro h; cases h), hr1d]
  have h4_1 : (reg s4 reg1).val = 1 := by
    rw [hr4o reg1 (by intro h; cases h), hr3o reg1 (by intro h; cases h), hr2d]
  have h4_2 : (reg s4 reg2).val = 2 := by rw [hr4o reg2 (by intro h; cases h), hr3d]
  have h4_3 : (reg s4 reg3).val = 3 := by rw [hr4d]
  obtain ⟨w0, hw0, hw0v⟩ := Option.map_eq_some_iff.mp h0
  obtain ⟨w1, hw1, hw1v⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨w2, hw2, hw2v⟩ := Option.map_eq_some_iff.mp h2
  obtain ⟨w3, hw3, hw3v⟩ := Option.map_eq_some_iff.mp h3
  obtain ⟨s5, hs5, hpc5, hr5d, hr5o, hd5⟩ := step_loadInput_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega) (by rw [h4_0]; exact hw0)
  obtain ⟨s6, hs6, hpc6, hr6d, hr6o, hd6⟩ := step_loadInput_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
    (by rw [hr5o reg1 (by intro h; cases h), h4_1]; exact hw1)
  obtain ⟨s7, hs7, hpc7, hr7d, hr7o, hd7⟩ := step_loadInput_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
    (by rw [hr6o reg2 (by intro h; cases h), hr5o reg2 (by intro h; cases h), h4_2]; exact hw2)
  obtain ⟨s8, hs8, hpc8, hr8d, hr8o, hd8⟩ := step_loadInput_at (input := input)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
    (by rw [hr7o reg3 (by intro h; cases h), hr6o reg3 (by intro h; cases h), hr5o reg3 (by intro h; cases h), h4_3]; exact hw3)
  refine ⟨s8, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
    (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (steps_1_of_step hs8))))))),
    by omega, by rw [hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr8o reg0 (by intro h; cases h), hr7o reg0 (by intro h; cases h), hr6o reg0 (by intro h; cases h), hr5o reg0 (by intro h; cases h), h4_0]
  · rw [hr8o reg1 (by intro h; cases h), hr7o reg1 (by intro h; cases h), hr6o reg1 (by intro h; cases h), hr5o reg1 (by intro h; cases h), h4_1]
  · rw [hr8o reg4 (by intro h; cases h), hr7o reg4 (by intro h; cases h), hr6o reg4 (by intro h; cases h), hr5d, hw0v]
  · rw [hr8o reg5 (by intro h; cases h), hr7o reg5 (by intro h; cases h), hr6d, hw1v]
  · rw [hr8o reg6 (by intro h; cases h), hr7d, hw2v]
  · rw [hr8d, hw3v]

private theorem initMetaPartB_spec {code : Program DomL} {input : Input DomL}
    {basePc : Nat} {n m N : Nat}
    (hPl : Placed code basePc (initMetaPartB (bits := bits)))
    (hSz : basePc + (initMetaPartB (bits := bits)).length < code.size)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr1 : (reg st reg1).val = 1) (hr4 : (reg st reg4).val = n)
    (hr5 : (reg st reg5).val = m) (hr6 : (reg st reg6).val = N)
    (hr9 : (reg st reg9).val = 19 * N) (hr10 : (reg st reg10).val = 6 * n)
    (hFit : metaArrBase n m N < 2 ^ bits) :
    ∃ t : State DomL, Steps code input 9 st t ∧ t.pc = basePc + 9 ∧ t.data = st.data ∧
      (reg t reg10).val = orderArrBase n N ∧
      (reg t reg11).val = topoRankArrBase n N ∧
      (reg t reg12).val = trigHeadArrBase n N ∧
      (reg t reg13).val = trigNextArrBase n N ∧
      (reg t reg8).val = inStartArrBase n N ∧
      (reg t reg2).val = inArcIdArrBase n N ∧
      (reg t rMeta).val = metaArrBase n m N ∧
      (reg t reg3).val = metaArrBase n m N ∧
      (∀ r : Fin 15, r ∈ [reg0, reg1, reg4, reg5, reg6, reg7, reg9] → reg t r = reg st r) := by
  have hlen : (initMetaPartB (bits := bits)).length = 9 := rfl
  have hm_eq := metaArrBase_eq n m N
  have ho_eq : orderArrBase n N = 19 * N + 6 * n := rfl
  have htr_eq : topoRankArrBase n N = orderArrBase n N + n := rfl
  have hth_eq : trigHeadArrBase n N = topoRankArrBase n N + n := rfl
  have htn_eq : trigNextArrBase n N = trigHeadArrBase n N + n := rfl
  have his_eq : inStartArrBase n N = trigNextArrBase n N + N := rfl
  have hia_eq : inArcIdArrBase n N = inStartArrBase n N + (n + 1) := rfl
  obtain ⟨s1, hs1, hpc1, hr1d, hr1o, hd1⟩ := step_add_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by rw [hpc]; rw [hlen] at hSz; omega)
  have h1_10 : (reg s1 reg10).val = orderArrBase n N := by
    rw [hr1d, add_no_wrap _ _ (by rw [hr9, hr10]; omega), hr9, hr10, ho_eq]
  obtain ⟨s2, hs2, hpc2, hr2d, hr2o, hd2⟩ := step_add_at (input := input)
    (by rw [hpc1, hpc]; exact hPl 1 _ rfl) (by rw [hpc1, hpc]; rw [hlen] at hSz; omega)
  have h2_11 : (reg s2 reg11).val = topoRankArrBase n N := by
    rw [hr2d, hr1o reg4 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h1_10, hr4]; omega), h1_10, hr4, htr_eq]
  obtain ⟨s3, hs3, hpc3, hr3d, hr3o, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by rw [hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h3_12 : (reg s3 reg12).val = trigHeadArrBase n N := by
    rw [hr3d, hr2o reg4 (by intro h; cases h), hr1o reg4 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h2_11, hr4]; omega), h2_11, hr4, hth_eq]
  obtain ⟨s4, hs4, hpc4, hr4d, hr4o, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) (by rw [hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h4_13 : (reg s4 reg13).val = trigNextArrBase n N := by
    rw [hr4d, hr3o reg4 (by intro h; cases h), hr2o reg4 (by intro h; cases h), hr1o reg4 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h3_12, hr4]; omega), h3_12, hr4, htn_eq]
  obtain ⟨s5, hs5, hpc5, hr5d, hr5o, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl) (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h5_8 : (reg s5 reg8).val = inStartArrBase n N := by
    rw [hr5d, hr4o reg6 (by intro h; cases h), hr3o reg6 (by intro h; cases h),
      hr2o reg6 (by intro h; cases h), hr1o reg6 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h4_13, hr6]; omega), h4_13, hr6, his_eq]
  obtain ⟨s6, hs6, hpc6, hr6d, hr6o, hd6⟩ := step_add_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl) (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h6_2 : (reg s6 reg2).val = inStartArrBase n N + n := by
    rw [hr6d, hr5o reg4 (by intro h; cases h), hr4o reg4 (by intro h; cases h),
      hr3o reg4 (by intro h; cases h), hr2o reg4 (by intro h; cases h), hr1o reg4 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h5_8, hr4]; omega), h5_8, hr4]
  obtain ⟨s7, hs7, hpc7, hr7d, hr7o, hd7⟩ := step_add_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl) (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h7_2 : (reg s7 reg2).val = inArcIdArrBase n N := by
    rw [hr7d, hr6o reg1 (by intro h; cases h), hr5o reg1 (by intro h; cases h), hr4o reg1 (by intro h; cases h),
      hr3o reg1 (by intro h; cases h), hr2o reg1 (by intro h; cases h), hr1o reg1 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h6_2, hr1]; omega), h6_2, hr1]
    rw [hia_eq]; omega
  obtain ⟨s8, hs8, hpc8, hr8d, hr8o, hd8⟩ := step_add_at (input := input)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl) (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h8_m : (reg s8 rMeta).val = metaArrBase n m N := by
    rw [hr8d, hr7o reg5 (by intro h; cases h), hr6o reg5 (by intro h; cases h),
      hr5o reg5 (by intro h; cases h), hr4o reg5 (by intro h; cases h), hr3o reg5 (by intro h; cases h), hr2o reg5 (by intro h; cases h),
      hr1o reg5 (by intro h; cases h), add_no_wrap _ _ (by rw [h7_2, hr5]; unfold inArcIdArrBase at hia_eq ⊢; omega),
      h7_2, hr5]
    rw [hia_eq]; unfold metaArrBase; omega
  obtain ⟨s9, hs9, hpc9, hr9d, hr9o, hd9⟩ := step_mov_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 8 _ rfl)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  refine ⟨s9, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
    (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (steps_1_of_step hs9)))))))),
    by omega, by rw [hd9, hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr9o reg10 (by intro h; cases h), hr8o reg10 (by intro h; cases h), hr7o reg10 (by intro h; cases h), hr6o reg10 (by intro h; cases h),
      hr5o reg10 (by intro h; cases h), hr4o reg10 (by intro h; cases h), hr3o reg10 (by intro h; cases h), hr2o reg10 (by intro h; cases h), h1_10]
  · rw [hr9o reg11 (by intro h; cases h), hr8o reg11 (by intro h; cases h), hr7o reg11 (by intro h; cases h), hr6o reg11 (by intro h; cases h),
      hr5o reg11 (by intro h; cases h), hr4o reg11 (by intro h; cases h), hr3o reg11 (by intro h; cases h), h2_11]
  · rw [hr9o reg12 (by intro h; cases h), hr8o reg12 (by intro h; cases h), hr7o reg12 (by intro h; cases h), hr6o reg12 (by intro h; cases h),
      hr5o reg12 (by intro h; cases h), hr4o reg12 (by intro h; cases h), h3_12]
  · rw [hr9o reg13 (by intro h; cases h), hr8o reg13 (by intro h; cases h), hr7o reg13 (by intro h; cases h), hr6o reg13 (by intro h; cases h),
      hr5o reg13 (by intro h; cases h), h4_13]
  · rw [hr9o reg8 (by intro h; cases h), hr8o reg8 (by intro h; cases h), hr7o reg8 (by intro h; cases h), hr6o reg8 (by intro h; cases h), h5_8]
  · rw [hr9o reg2 (by intro h; cases h), hr8o reg2 (by intro h; cases h), h7_2]
  · rw [hr9o rMeta (by intro h; cases h), h8_m]
  · rw [hr9d, h8_m]
  · intro r hrMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrMem
    rcases hrMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [hr9o _ (by intro h; cases h), hr8o _ (by intro h; cases h), hr7o _ (by intro h; cases h), hr6o _ (by intro h; cases h),
        hr5o _ (by intro h; cases h), hr4o _ (by intro h; cases h), hr3o _ (by intro h; cases h), hr2o _ (by intro h; cases h), hr1o _ (by intro h; cases h)]

private theorem initMetaPartC_spec {code : Program DomL} {input : Input DomL}
    {basePc : Nat} (h100 : 100 ≤ 2 ^ bits) {n m N : Nat}
    (hPl : Placed code basePc (initMetaPartC (bits := bits) h100))
    (hSz : basePc + (initMetaPartC (bits := bits) h100).length < code.size)
    (st : State DomL) (hpc : st.pc = basePc)
    (hReg3 : (reg st reg3).val = metaArrBase n m N + 12)
    (hMeta : (reg st rMeta).val = metaArrBase n m N)
    (hr1 : (reg st reg1).val = 1) (hr4 : (reg st reg4).val = n)
    (hr5 : (reg st reg5).val = m) (hr6 : (reg st reg6).val = N)
    (hLt13 : metaArrBase n m N + 13 < st.data.size)
    (hTempFit : tempArrBase n m N < 2 ^ bits)
    (hInFit : 4 + n + 4 * N ≤ 2 ^ bits)
    (hNPos : 0 < N)
    (hMFit : 0 < m → 4 + n + 4 * N + 2 * m < 2 ^ bits) :
    ∃ t : State DomL, Steps code input 13 st t ∧ t.pc = basePc + 13 ∧
      t.data[metaArrBase n m N + 13]? = some ⟨tempArrBase n m N, hTempFit⟩ ∧
      (∀ j, j ≠ metaArrBase n m N + 13 → t.data[j]? = st.data[j]?) ∧
      (reg t rMeta).val = metaArrBase n m N ∧
      (reg t reg0).val = (reg st reg0).val ∧
      (reg t reg1).val = 1 ∧
      (reg t reg3).val = metaArrBase n m N + 14 ∧
      (reg t reg7).val = 4 ∧
      (reg t reg8).val = 4 + n ∧
      (reg t reg9).val = 4 + n + N ∧
      (reg t reg10).val = 4 + n + 2 * N ∧
      (reg t reg11).val = 4 + n + 3 * N ∧
      (0 < m → (reg t reg12).val = 4 + n + 4 * N ∧
        (reg t reg13).val = 4 + n + 4 * N + m ∧
        (reg t reg2).val = 4 + n + 4 * N + 2 * m) := by
  have hlen : (initMetaPartC (bits := bits) h100).length = 13 := rfl
  have htb : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  obtain ⟨s1, hs1, hpc1, hr1d, hr1o, hd1⟩ := step_add_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by rw [hpc]; rw [hlen] at hSz; omega)
  have h1_3 : (reg s1 reg3).val = metaArrBase n m N + 13 := by
    rw [hr1d, add_no_wrap _ _ (by rw [hReg3, hr1]; omega), hReg3, hr1]
  obtain ⟨s2, hs2, hpc2, hr2d, hr2o, hd2⟩ := step_imm_at (input := input)
    (by rw [hpc1, hpc]; exact hPl 1 _ rfl) (by rw [hpc1, hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s3, hs3, hpc3, hr3d, hr3o, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by rw [hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h3_8 : (reg s3 reg8).val = tempArrBase n m N := by
    have hrm2 : (reg s2 rMeta).val = metaArrBase n m N := by
      rw [hr2o rMeta (by intro h; cases h), hr1o rMeta (by intro h; cases h), hMeta]
    have hr8_2 : (reg s2 reg8).val = 48 := by rw [hr2d]
    rw [hr3d, add_no_wrap _ _ (by rw [hrm2, hr8_2, ← htb]; exact hTempFit), hrm2, hr8_2, htb]
  have h3_3 : (reg s3 reg3).val = metaArrBase n m N + 13 := by
    rw [hr3o reg3 (by intro h; cases h), hr2o reg3 (by intro h; cases h), h1_3]
  have hs3Lt : (reg s3 reg3).val < s3.data.size := by rw [h3_3, hd3, hd2, hd1]; exact hLt13
  obtain ⟨hs4, hpc4, hreg4⟩ := step_storeData_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) hs3Lt
    (by rw [hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  let s4 : State DomL :=
    { s3 with
      data := s3.data.set (reg s3 reg3).val (reg s3 reg8) hs3Lt
      pc := s3.pc + 1
      data_size := by simp only [Array.size_set, s3.data_size] }
  have hs4_data13 : s4.data[metaArrBase n m N + 13]? = some ⟨tempArrBase n m N, hTempFit⟩ := by
    change (s3.data.set (reg s3 reg3).val (reg s3 reg8) hs3Lt)[metaArrBase n m N + 13]? = _
    rw [← h3_3]; simp [hs3Lt]; exact Fin.ext h3_8
  have hs4_frame : ∀ j, j ≠ metaArrBase n m N + 13 → s4.data[j]? = st.data[j]? := fun j hj => by
    change (s3.data.set (reg s3 reg3).val (reg s3 reg8) hs3Lt)[j]? = st.data[j]?
    rw [Array.getElem?_set_ne hs3Lt (by rw [h3_3]; exact hj.symm), hd3, hd2, hd1]
  have h4_reg : ∀ r, reg s4 r = reg s3 r := fun _ => rfl
  obtain ⟨s5, hs5, hpc5, hr5d, hr5o, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h5_3 : (reg s5 reg3).val = metaArrBase n m N + 14 := by
    have h1_4 : (reg s4 reg1).val = 1 := by
      rw [h4_reg, hr3o reg1 (by intro h; cases h), hr2o reg1 (by intro h; cases h), hr1o reg1 (by intro h; cases h), hr1]
    have h3_4 : (reg s4 reg3).val = metaArrBase n m N + 13 := by
      rw [h4_reg]; exact h3_3
    rw [hr5d]
    change (add (reg s4 reg3) (reg s4 reg1)).val = _
    rw [add_no_wrap _ _ (by rw [h3_4, h1_4]; omega), h3_4, h1_4]
  obtain ⟨s6, hs6, hpc6, hr6d, hr6o, hd6⟩ := step_imm_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h6_7 : (reg s6 reg7).val = 4 := by rw [hr6d]
  have h6_4 : (reg s6 reg4).val = n := by
    rw [hr6o reg4 (by intro h; cases h), hr5o reg4 (by intro h; cases h), h4_reg,
      hr3o reg4 (by intro h; cases h), hr2o reg4 (by intro h; cases h), hr1o reg4 (by intro h; cases h), hr4]
  have h6_5 : (reg s6 reg5).val = m := by
    rw [hr6o reg5 (by intro h; cases h), hr5o reg5 (by intro h; cases h), h4_reg,
      hr3o reg5 (by intro h; cases h), hr2o reg5 (by intro h; cases h), hr1o reg5 (by intro h; cases h), hr5]
  have h6_6 : (reg s6 reg6).val = N := by
    rw [hr6o reg6 (by intro h; cases h), hr5o reg6 (by intro h; cases h), h4_reg,
      hr3o reg6 (by intro h; cases h), hr2o reg6 (by intro h; cases h), hr1o reg6 (by intro h; cases h), hr6]
  obtain ⟨s7, hs7, hpc7, hr7d, hr7o, hd7⟩ := step_add_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h7_8 : (reg s7 reg8).val = 4 + n := by
    rw [hr7d, add_no_wrap _ _ (by rw [h6_7, h6_4]; omega), h6_7, h6_4]
  obtain ⟨s8, hs8, hpc8, hr8d, hr8o, hd8⟩ := step_add_at (input := input)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h8_9 : (reg s8 reg9).val = 4 + n + N := by
    rw [hr8d, hr7o reg6 (by intro h; cases h), add_no_wrap _ _ (by rw [h7_8, h6_6]; omega), h7_8, h6_6]
  obtain ⟨s9, hs9, hpc9, hr9d, hr9o, hd9⟩ := step_add_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 8 _ rfl)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h9_10 : (reg s9 reg10).val = 4 + n + 2 * N := by
    rw [hr9d, hr8o reg6 (by intro h; cases h), hr7o reg6 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h8_9, h6_6]; omega), h8_9, h6_6]; omega
  obtain ⟨s10, hs10, hpc10, hr10d, hr10o, hd10⟩ := step_add_at (input := input)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 9 _ rfl)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  have h10_11 : (reg s10 reg11).val = 4 + n + 3 * N := by
    rw [hr10d, hr9o reg6 (by intro h; cases h), hr8o reg6 (by intro h; cases h), hr7o reg6 (by intro h; cases h),
      add_no_wrap _ _ (by rw [h9_10, h6_6]; omega), h9_10, h6_6]; omega
  obtain ⟨s11, hs11, hpc11, hr11d, hr11o, hd11⟩ := step_add_at (input := input)
    (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 10 _ rfl)
    (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s12, hs12, hpc12, hr12d, hr12o, hd12⟩ := step_add_at (input := input)
    (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 11 _ rfl)
    (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  obtain ⟨s13, hs13, hpc13, hr13d, hr13o, hd13⟩ := step_add_at (input := input)
    (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 12 _ rfl)
    (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; rw [hlen] at hSz; omega)
  refine ⟨s13, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
    (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
      (Steps.cons hs11 (Steps.cons hs12 (steps_1_of_step hs13)))))))))))),
    by omega, by rw [hd13, hd12, hd11, hd10, hd9, hd8, hd7, hd6, hd5]; exact hs4_data13,
    fun j hj => by rw [hd13, hd12, hd11, hd10, hd9, hd8, hd7, hd6, hd5]; exact hs4_frame j hj,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr13o rMeta (by intro h; cases h), hr12o rMeta (by intro h; cases h), hr11o rMeta (by intro h; cases h), hr10o rMeta (by intro h; cases h),
      hr9o rMeta (by intro h; cases h), hr8o rMeta (by intro h; cases h), hr7o rMeta (by intro h; cases h), hr6o rMeta (by intro h; cases h),
      hr5o rMeta (by intro h; cases h), h4_reg, hr3o rMeta (by intro h; cases h), hr2o rMeta (by intro h; cases h), hr1o rMeta (by intro h; cases h), hMeta]
  · rw [hr13o reg0 (by intro h; cases h), hr12o reg0 (by intro h; cases h), hr11o reg0 (by intro h; cases h), hr10o reg0 (by intro h; cases h),
      hr9o reg0 (by intro h; cases h), hr8o reg0 (by intro h; cases h), hr7o reg0 (by intro h; cases h), hr6o reg0 (by intro h; cases h),
      hr5o reg0 (by intro h; cases h), h4_reg, hr3o reg0 (by intro h; cases h), hr2o reg0 (by intro h; cases h), hr1o reg0 (by intro h; cases h)]
  · rw [hr13o reg1 (by intro h; cases h), hr12o reg1 (by intro h; cases h), hr11o reg1 (by intro h; cases h), hr10o reg1 (by intro h; cases h),
      hr9o reg1 (by intro h; cases h), hr8o reg1 (by intro h; cases h), hr7o reg1 (by intro h; cases h), hr6o reg1 (by intro h; cases h),
      hr5o reg1 (by intro h; cases h), h4_reg, hr3o reg1 (by intro h; cases h), hr2o reg1 (by intro h; cases h), hr1o reg1 (by intro h; cases h), hr1]
  · rw [hr13o reg3 (by intro h; cases h), hr12o reg3 (by intro h; cases h), hr11o reg3 (by intro h; cases h), hr10o reg3 (by intro h; cases h),
      hr9o reg3 (by intro h; cases h), hr8o reg3 (by intro h; cases h), hr7o reg3 (by intro h; cases h), hr6o reg3 (by intro h; cases h), h5_3]
  · rw [hr13o reg7 (by intro h; cases h), hr12o reg7 (by intro h; cases h), hr11o reg7 (by intro h; cases h), hr10o reg7 (by intro h; cases h),
      hr9o reg7 (by intro h; cases h), hr8o reg7 (by intro h; cases h), hr7o reg7 (by intro h; cases h), h6_7]
  · rw [hr13o reg8 (by intro h; cases h), hr12o reg8 (by intro h; cases h), hr11o reg8 (by intro h; cases h), hr10o reg8 (by intro h; cases h),
      hr9o reg8 (by intro h; cases h), hr8o reg8 (by intro h; cases h), h7_8]
  · rw [hr13o reg9 (by intro h; cases h), hr12o reg9 (by intro h; cases h), hr11o reg9 (by intro h; cases h), hr10o reg9 (by intro h; cases h),
      hr9o reg9 (by intro h; cases h), h8_9]
  · rw [hr13o reg10 (by intro h; cases h), hr12o reg10 (by intro h; cases h), hr11o reg10 (by intro h; cases h), hr10o reg10 (by intro h; cases h), h9_10]
  · rw [hr13o reg11 (by intro h; cases h), hr12o reg11 (by intro h; cases h), hr11o reg11 (by intro h; cases h), h10_11]
  · intro hm
    have hM := hMFit hm
    have h11_12 : (reg s11 reg12).val = 4 + n + 4 * N := by
      rw [hr11d, hr10o reg6 (by intro h; cases h), hr9o reg6 (by intro h; cases h),
        hr8o reg6 (by intro h; cases h), hr7o reg6 (by intro h; cases h),
        add_no_wrap _ _ (by rw [h10_11, h6_6]; omega), h10_11, h6_6]; omega
    have h11_5 : (reg s11 reg5).val = m := by
      rw [hr11o reg5 (by intro h; cases h), hr10o reg5 (by intro h; cases h), hr9o reg5 (by intro h; cases h),
        hr8o reg5 (by intro h; cases h), hr7o reg5 (by intro h; cases h), h6_5]
    have h12_13 : (reg s12 reg13).val = 4 + n + 4 * N + m := by
      rw [hr12d, add_no_wrap _ _ (by rw [h11_12, h11_5]; omega), h11_12, h11_5]
    have h12_5 : (reg s12 reg5).val = m := by rw [hr12o reg5 (by intro h; cases h), h11_5]
    have h13_2 : (reg s13 reg2).val = 4 + n + 4 * N + 2 * m := by
      rw [hr13d, add_no_wrap _ _ (by rw [h12_13, h12_5]; omega), h12_13, h12_5]; omega
    exact ⟨by rw [hr13o reg12 (by intro h; cases h), hr12o reg12 (by intro h; cases h), h11_12],
      by rw [hr13o reg13 (by intro h; cases h), h12_13], h13_2⟩

theorem run_initMeta {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL) :
    ∃ t : State DomL,
      run (initMetaPhase hi hw h100).code input
        ((initMetaInstrs (bits := bits) h100).length + 1) (Phase.initial s0) =
          some ⟨t, (initMetaInstrs (bits := bits) h100).length + 1⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ j, j < metaArrBase H.vertexCount H.arcCount r.out.tables.next ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 22 ≤ j →
        t.data[j]? = s0.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  have hn3 : 3 ≤ n := large
  have hNLe : N ≤ n + 1 := by
    change r.out.tables.next ≤ n + 1
    exact (nodeCount_eq_next r.index.ok).symm ▸ nodeCount_le r.index.ok
  have htb : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hStage2 : tempArrBase n m N + (3 * n + 1 + m) ≤ workCap :=
    Nat.le_trans (tempArrBase_stage2_le hNLe) hWork
  have hTempBits : tempArrBase n m N < 2 ^ bits := by omega
  have hMetaBits : metaArrBase n m N + 22 < 2 ^ bits := by omega
  have hInCap := hIn.cap_ge
  change 4 + n + 4 * N + 3 * m ≤ inputCap at hInCap
  have hInFit : 4 + n + 4 * N ≤ 2 ^ bits := by omega
  have hMFit : 0 < m → 4 + n + 4 * N + 2 * m < 2 ^ bits := fun hm => by omega
  have hPhasePl : Placed (initMetaPhase hi hw h100).code 0 (initMetaInstrs (bits := bits) h100) :=
    Placed_toArray_halt
  have hCodeSz : (initMetaPhase hi hw h100).code.size = (initMetaInstrs (bits := bits) h100).length + 1 := by
    change (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray.size = _
    simp
  have hLA : (initMetaPartA (bits := bits) h100).length = 8 := rfl
  have hLM18 : (mul18Instrs (bits := bits) reg9 reg8 reg6).length = 5 := rfl
  have hLM6 : (mul6Instrs (bits := bits) reg10 reg4).length = 3 := rfl
  have hLB : (initMetaPartB (bits := bits)).length = 9 := rfl
  have hLS1 : (storeSeqInstrs (bits := bits) reg3 reg1 initMetaSeq1Vars).length = 25 := rfl
  have hLC : (initMetaPartC (bits := bits) h100).length = 13 := rfl
  have hLS2 : (storeSeqInstrs (bits := bits) reg3 reg1 initMetaSeq2Vars).length = 15 := rfl
  have hLenTot : (initMetaInstrs (bits := bits) h100).length = 79 := by
    unfold initMetaInstrs
    simp only [List.length_append, hLA, hLM18, List.length_singleton, hLM6, hLB, hLS1, hLC, hLS2]
  have hPl1 : Placed (initMetaPhase hi hw h100).code 0 (initMetaPartA (bits := bits) h100) := by
    unfold initMetaInstrs at hPhasePl
    exact Placed_append_left hPhasePl
  have hPlRest1 := Placed_append_right (by unfold initMetaInstrs at hPhasePl; exact hPhasePl)
  rw [hLA] at hPlRest1
  have hPl2 : Placed (initMetaPhase hi hw h100).code (0 + 8) (mul18Instrs reg9 reg8 reg6) :=
    Placed_append_left hPlRest1
  have hPlRest2 := Placed_append_right hPlRest1
  rw [hLM18] at hPlRest2
  have hPl3 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5) [.add reg9 reg9 reg6] :=
    Placed_append_left hPlRest2
  have hPlRest3 := Placed_append_right hPlRest2
  have hPl4 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5 + 1) (mul6Instrs reg10 reg4) :=
    Placed_append_left hPlRest3
  have hPlRest4 := Placed_append_right hPlRest3
  rw [hLM6] at hPlRest4
  have hPl5 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5 + 1 + 3) (initMetaPartB (bits := bits)) :=
    Placed_append_left hPlRest4
  have hPlRest5 := Placed_append_right hPlRest4
  rw [hLB] at hPlRest5
  have hPl6 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5 + 1 + 3 + 9)
      (storeSeqInstrs reg3 reg1 initMetaSeq1Vars) :=
    Placed_append_left hPlRest5
  have hPlRest6 := Placed_append_right hPlRest5
  rw [hLS1] at hPlRest6
  have hPl7 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5 + 1 + 3 + 9 + 25)
      (initMetaPartC (bits := bits) h100) :=
    Placed_append_left hPlRest6
  have hPl8 : Placed (initMetaPhase hi hw h100).code (0 + 8 + 5 + 1 + 3 + 9 + 25 + 13)
      (storeSeqInstrs reg3 reg1 initMetaSeq2Vars) := by
    have hR := Placed_append_right hPlRest6
    rw [hLC] at hR
    exact hR
  obtain ⟨sA, hStA, hpcA, hdA, hr0A, hr1A, hr4A, hr5A, hr6A, hr7A⟩ :=
    initMetaPartA_spec h100 hPl1 (by rw [hCodeSz, hLenTot]; omega) (Phase.initial s0) rfl
      hIn.hdr_n hIn.hdr_m hIn.hdr_NH hIn.hdr_nGlobal
  obtain ⟨sM18, hStM18, hpcM18, hdM18, hr9M18, hroM18⟩ :=
    steps_add_mul18 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) hPl2 (by rw [hCodeSz, hLenTot]; omega)
      sA hpcA (by rw [hr6A]; have := metaArrBase_eq n m N; omega)
  have hr6M18 : (reg sM18 reg6).val = N := by rw [hroM18 reg6 (by intro h; cases h) (by intro h; cases h), hr6A]
  obtain ⟨s19, hs19, hpc19, hr19d, hr19o, hd19⟩ := step_add_at (input := input)
    (by rw [hpcM18]; exact hPl3 0 _ rfl) (by rw [hpcM18, hCodeSz, hLenTot]; omega)
  have hr9_19 : (reg s19 reg9).val = 19 * N := by
    rw [hr19d, add_no_wrap _ _ (by rw [hr9M18, hr6M18, hr6A]; have := metaArrBase_eq n m N; omega),
      hr9M18, hr6M18, hr6A]; omega
  have hr4_19 : (reg s19 reg4).val = n := by
    rw [hr19o reg4 (by intro h; cases h), hroM18 reg4 (by intro h; cases h) (by intro h; cases h), hr4A]
  obtain ⟨sM6, hStM6, hpcM6, hdM6, hr10M6, hroM6⟩ :=
    steps_add_mul6 (by intro h; cases h) hPl4 (by rw [hCodeSz, hLenTot]; omega)
      s19 (by rw [hpc19, hpcM18]) (by rw [hr4_19]; have := metaArrBase_eq n m N; omega)
  have h19to6 : ∀ r : Fin 15, r ∈ [reg0, reg1, reg4, reg5, reg6, reg7] →
      reg sM6 r = reg sA r := fun r hrMem => by
    have hrNe : r ≠ reg9 ∧ r ≠ reg8 ∧ r ≠ reg10 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrMem
      rcases hrMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨(by intro h; cases h), (by intro h; cases h), (by intro h; cases h)⟩
    rw [hroM6 r hrNe.2.2, hr19o r hrNe.1, hroM18 r hrNe.1 hrNe.2.1]
  obtain ⟨sB, hStB, hpcB, hdB, hr10B, hr11B, hr12B, hr13B, hr8B, hr2B, hrmB, hr3B, hroB⟩ :=
    initMetaPartB_spec hPl5 (by rw [hCodeSz, hLenTot]; omega) sM6 hpcM6
      (by rw [h19to6 reg1 (by decide), hr1A])
      (by rw [hroM6 reg4 (by intro h; cases h), hr4_19])
      (by rw [h19to6 reg5 (by decide), hr5A])
      (by rw [h19to6 reg6 (by decide), hr6A])
      (by rw [hroM6 reg9 (by intro h; cases h), hr9_19])
      (by rw [hr10M6, hr4_19])
      (by change metaArrBase n m N < 2 ^ bits; omega)
  have hBReg : ∀ r : Fin 15, r ∈ [reg0, reg1, reg4, reg5, reg6, reg7] →
      reg sB r = reg sA r := fun r hr => by
    have hr' : r ∈ [reg0, reg1, reg4, reg5, reg6, reg7, reg9] := by
      simp only [List.mem_cons] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | hrFalse
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · cases hrFalse
    rw [hroB r hr', h19to6 r hr]
  have hd_eq_s0 : sB.data = s0.data := by
    rw [hdB, hdM6, hd19, hdM18, hdA]; rfl
  obtain ⟨sS1, hStS1, hpcS1, hr3S1, hroS1, hFrS1, hWrS1⟩ :=
    run_storeSeq reg3 reg1 (by intro h; cases h) initMetaSeq1Vars _ (metaArrBase n m N) sB
      (fun v hv => by simp only [initMetaSeq1Vars, List.mem_cons, List.not_mem_nil,
        or_false] at hv; rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (intro h; cases h))
      hPl6 (by rw [hCodeSz, hLenTot]; omega) hpcB hr3B
      (by rw [hBReg reg1 (by decide), hr1A])
      (by rw [sB.data_size]; simp only [initMetaSeq1Vars, List.length_cons, List.length_nil]; omega)
      (by simp only [initMetaSeq1Vars, List.length_cons, List.length_nil]; omega)
  obtain ⟨sC, hStC, hpcC, hC13, hCFr, hCm, hCr0, hCr1, hCr3, hCr7, hCr8, hCr9, hCr10, hCr11, hCM⟩ :=
    initMetaPartC_spec h100 hPl7 (by rw [hCodeSz, hLenTot]; omega) sS1 hpcS1
      (by rw [hr3S1 (by simp [initMetaSeq1Vars])]; simp only [initMetaSeq1Vars, List.length_cons, List.length_nil])
      (by rw [hroS1 rMeta (by intro h; cases h), hrmB])
      (by rw [hroS1 reg1 (by intro h; cases h), hBReg reg1 (by decide), hr1A])
      (by rw [hroS1 reg4 (by intro h; cases h), hBReg reg4 (by decide), hr4A])
      (by rw [hroS1 reg5 (by intro h; cases h), hBReg reg5 (by decide), hr5A])
      (by rw [hroS1 reg6 (by intro h; cases h), hBReg reg6 (by decide), hr6A])
      (by rw [sS1.data_size]; change metaArrBase n m N + 13 < workCap; omega)
      hTempBits hInFit
      (by
        have hP := Nat.zero_lt_of_lt ((PaperB.EX24.FinalDFS.packedInput r.index.ok).root.isLt)
        have hEq := (nodeCount_eq_next r.index.ok).symm
        change 0 < nodeCount (orderedConfig p large) r.out at hP
        omega)
      hMFit
  obtain ⟨sS2, hStS2, hpcS2, _, hroS2, hFrS2, hWrS2⟩ :=
    run_storeSeq reg3 reg1 (by intro h; cases h) initMetaSeq2Vars _ (metaArrBase n m N + 14) sC
      (fun v hv => by simp only [initMetaSeq2Vars, List.mem_cons, List.not_mem_nil,
        or_false] at hv; rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (intro h; cases h))
      hPl8 (by rw [hCodeSz, hLenTot]; omega) hpcC hCr3 hCr1
      (by rw [sC.data_size]; change metaArrBase n m N + 14 + _ ≤ workCap
          simp only [initMetaSeq2Vars, List.length_cons, List.length_nil]; omega)
      (by simp only [initMetaSeq2Vars, List.length_cons, List.length_nil]; omega)
  have hAllSteps : Steps (initMetaPhase hi hw h100).code input
      (initMetaInstrs (bits := bits) h100).length (Phase.initial s0) sS2 := by
    rw [hLenTot]
    exact hStA.append (hStM18.append ((steps_1_of_step hs19).append
      (hStM6.append (hStB.append (hStS1.append (hStC.append hStS2))))))
  have hHalt : step (initMetaPhase hi hw h100).code input sS2 = some (.halted sS2) :=
    step_halt_at (by
      have hp : sS2.pc = (initMetaInstrs (bits := bits) h100).length := by
        rw [hpcS2, hLenTot]; simp [initMetaSeq2Vars]
      rw [hp]
      change (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray[(initMetaInstrs (bits := bits) h100).length]? = some .halt
      have hLt : (initMetaInstrs (bits := bits) h100).length <
          (initMetaInstrs (bits := bits) h100 ++ [Instr.halt]).toArray.size := by simp
      rw [Array.getElem?_eq_getElem hLt]
      simp)
  have hReadSeq1 : ∀ (i : Nat) (hi13 : i < 13),
      sS2.data[metaArrBase n m N + i]? =
        some (reg sB (initMetaSeq1Vars[i]'(by
          simp only [initMetaSeq1Vars, List.length_cons, List.length_nil] at hi13 ⊢; omega))) := by
    intro i hi13
    rw [hFrS2 _ (Or.inl (by omega)), hCFr _ (by omega)]
    exact hWrS1 i (by simpa only [initMetaSeq1Vars, List.length_cons, List.length_nil] using hi13)
  have hReadSeq2 : ∀ (i : Nat) (hi8 : i < 8),
      sS2.data[metaArrBase n m N + 14 + i]? =
        some (reg sC (initMetaSeq2Vars[i]'(by
          simp only [initMetaSeq2Vars, List.length_cons, List.length_nil] at hi8 ⊢; omega))) :=
    fun i hi8 => hWrS2 i (by simpa only [initMetaSeq2Vars, List.length_cons, List.length_nil] using hi8)
  refine ⟨sS2, hAllSteps.halts hHalt, ?_, ?_⟩
  · refine ⟨by rw [hroS2 rMeta (by intro h; cases h), hCm],
      by rw [hroS2 reg0 (by intro h; cases h), hCr0, hroS1 reg0 (by intro h; cases h), hBReg reg0 (by decide), hr0A],
      by rw [hroS2 reg1 (by intro h; cases h), hCr1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 0]? = _
      rw [hReadSeq1 0 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_zero, Option.map_some]
      rw [hBReg reg4 (by decide), hr4A]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 1]? = _
      rw [hReadSeq1 1 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hBReg reg5 (by decide), hr5A]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 2]? = _
      rw [hReadSeq1 2 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hBReg reg6 (by decide), hr6A]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 3]? = _
      rw [hReadSeq1 3 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hBReg reg7 (by decide), hr7A]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 4]? = _
      rw [hReadSeq1 4 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hBReg reg6 (by decide), hr6A]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 5]? = _
      rw [hReadSeq1 5 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hroB reg9 (by decide), hroM6 reg9 (by intro h; cases h), hr9_19]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 6]? = _
      rw [hReadSeq1 6 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr10B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 7]? = _
      rw [hReadSeq1 7 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr11B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 8]? = _
      rw [hReadSeq1 8 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr12B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 9]? = _
      rw [hReadSeq1 9 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr13B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 10]? = _
      rw [hReadSeq1 10 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr8B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 11]? = _
      rw [hReadSeq1 11 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hr2B]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 12]? = _
      rw [hReadSeq1 12 (by decide)]; simp only [initMetaSeq1Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hrmB]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 13]? = _
      rw [hFrS2 _ (Or.inl (by omega)), hC13]; rfl
    · intro hm
      change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 0]? = _
      rw [hReadSeq2 0 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_zero, Option.map_some]
      rw [(hCM hm).1]
    · intro hm
      change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 1]? = _
      rw [hReadSeq2 1 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [(hCM hm).2.1]
    · intro hm
      change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 2]? = _
      rw [hReadSeq2 2 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [(hCM hm).2.2]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 3]? = _
      rw [hReadSeq2 3 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hCr10]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 4]? = _
      rw [hReadSeq2 4 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hCr11]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 5]? = _
      rw [hReadSeq2 5 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hCr7]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 6]? = _
      rw [hReadSeq2 6 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hCr8]
    · change Option.map Fin.val sS2.data[metaArrBase n m N + 14 + 7]? = _
      rw [hReadSeq2 7 (by decide)]; simp only [initMetaSeq2Vars, List.getElem_cons_succ, List.getElem_cons_zero, Option.map_some]
      rw [hCr9]
  · intro j hj
    change j < metaArrBase n m N ∨ metaArrBase n m N + 22 ≤ j at hj
    have hj2 : j < metaArrBase n m N + 14 ∨ metaArrBase n m N + 14 + initMetaSeq2Vars.length ≤ j := by
      simp only [initMetaSeq2Vars, List.length_cons, List.length_nil]
      omega
    have hj1 : j < metaArrBase n m N ∨ metaArrBase n m N + initMetaSeq1Vars.length ≤ j := by
      simp only [initMetaSeq1Vars, List.length_cons, List.length_nil]
      omega
    rw [hFrS2 j hj2, hCFr j (by omega), hFrS1 j hj1, hd_eq_s0]

end Phase0Proofs

/-! ### 5. Stage 1: DFS Interval Inversion & Forest Parent/Depth/Jump Reconstruction -/

section Stage1ForestRecon

open PaperB.StaticTreeReader

section DfsStackMath

theorem dfs_root_eq_zero {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large) :
    (PaperB.EX24.FinalDFS.packedInput r.index.ok).root.val = 0 := by
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  let x := PaperB.EX24.FinalDFS.packedInput r.index.ok
  let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
    (nodeCount_eq_next r.index.ok).symm
  have hF := B.G.layout.valid
  have hB0 := (reader_matches_bundle_forest flat increasing covers rankArc r
    (Fin.cast hN.symm x.root)).2
  have hEq : x.depth.read x.root = B.F.depthOf x.root.val := by
    have hCast : Fin.cast hN (Fin.cast hN.symm x.root) = x.root := by apply Fin.ext; rfl
    rw [← hCast]; exact hB0
  have hZ : x.depth.read x.root = 0 := r.index.reader.input_ok.depth_root
  rw [hZ] at hEq
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  exact (inv.depth_eq_zero_iff (Nat.lt_of_lt_of_eq x.root.isLt (by rw [← hN, B.G.size_eq]))).mp hEq.symm

private theorem isForestAncestor_trans {N : Nat} {parent : Fin N → Fin N} {a b c : Fin N}
    (hab : IsForestAncestor parent a b) (hbc : IsForestAncestor parent b c) :
    IsForestAncestor parent a c := by
  induction hbc with
  | refl => exact hab
  | step w _ ih => exact IsForestAncestor.step w ih

theorem isForestAncestor_iff_rd_interval {N : Nat} {x : PackedStaticLayout.Input N}
    (rd : StaticTreeReader.Reader x) (a v : Fin N) :
    IsForestAncestor x.parent.read a v ↔ rd.entry a ≤ rd.entry v ∧ rd.entry v < rd.stop a := by
  rw [rd.entry_exact a, rd.entry_exact v, rd.stop_exact a]
  exact isForestAncestor_iff_dfsIntervalContains rd.input_ok a v

theorem list_nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: xs, l₂, hNd, hSub => by
    have ha : a ∈ l₂ := hSub a List.mem_cons_self
    have hNdXs : xs.Nodup := (List.nodup_cons.mp hNd).2
    have haNot : a ∉ xs := (List.nodup_cons.mp hNd).1
    have hSubErase : ∀ y ∈ xs, y ∈ l₂.erase a := fun y hy =>
      (List.mem_erase_of_ne (fun he => haNot (by rw [← he]; exact hy))).mpr
        (hSub y (List.mem_cons_of_mem a hy))
    have ih := list_nodup_length_le_of_subset xs (l₂.erase a) hNdXs hSubErase
    have hLenErase : (l₂.erase a).length + 1 = l₂.length := by
      have := List.length_erase_of_mem ha
      have hPos : 0 < l₂.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

theorem fin_entry_surjective {N : Nat} (entry : Fin N → Nat)
    (hLt : ∀ u : Fin N, entry u < N) (hInj : ∀ u v : Fin N, entry u = entry v → u = v) :
    ∀ t : Nat, t < N → ∃ u : Fin N, entry u = t := by
  intro t ht
  by_cases hEx : ∃ u : Fin N, entry u = t
  · exact hEx
  · exfalso
    let ys := (List.finRange N).map entry
    have hNdYs : ys.Nodup :=
      List.Pairwise.map entry (fun {a b} hne heq => hne (hInj a b heq)) (List.nodup_finRange N)
    have hTNot : t ∉ ys := by
      intro hm
      rcases List.mem_map.mp hm with ⟨u, _, hu⟩
      exact hEx ⟨u, hu⟩
    have hNd : (t :: ys).Nodup := List.nodup_cons.mpr ⟨hTNot, hNdYs⟩
    have hSub : ∀ x ∈ t :: ys, x ∈ List.range N := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hm
      · exact List.mem_range.mpr ht
      · rcases List.mem_map.mp hm with ⟨u, _, rfl⟩
        exact List.mem_range.mpr (hLt u)
    have hLe := list_nodup_length_le_of_subset (t :: ys) (List.range N) hNd hSub
    simp only [List.length_cons, ys, List.length_map, List.length_finRange, List.length_range] at hLe
    omega

private theorem dfs_stop_le_of_entry_lt {N : Nat} {x : PackedStaticLayout.Input N}
    (rd : StaticTreeReader.Reader x)
    (hLt : ∀ u : Fin N, rd.entry u < N)
    (hInj : ∀ u v : Fin N, rd.entry u = rd.entry v → u = v)
    (hSpan : ∀ u : Fin N, rd.entry u < rd.stop u ∧ rd.stop u ≤ N)
    {a b : Fin N} (hab : rd.entry a ≤ rd.entry b) (hba : rd.entry b < rd.stop a) :
    IsForestAncestor x.parent.read a b ∧ rd.stop b ≤ rd.stop a := by
  have hAncAB : IsForestAncestor x.parent.read a b :=
    (isForestAncestor_iff_rd_interval rd a b).mpr ⟨hab, hba⟩
  refine ⟨hAncAB, ?_⟩
  have hSub := (hSpan b).1
  have hStopLe := (hSpan b).2
  obtain ⟨v, hv⟩ := fin_entry_surjective rd.entry hLt hInj (rd.stop b - 1) (by omega)
  have hAncBV : IsForestAncestor x.parent.read b v :=
    (isForestAncestor_iff_rd_interval rd b v).mpr ⟨by omega, by omega⟩
  have hAncAV := isForestAncestor_trans hAncAB hAncBV
  have hV := ((isForestAncestor_iff_rd_interval rd a v).mp hAncAV).2
  omega

theorem dfs_stack_decreasing_stop {N : Nat} {x : PackedStaticLayout.Input N}
    (rd : StaticTreeReader.Reader x)
    (hLt : ∀ u : Fin N, rd.entry u < N)
    (hInj : ∀ u v : Fin N, rd.entry u = rd.entry v → u = v)
    (hSpan : ∀ u : Fin N, rd.entry u < rd.stop u ∧ rd.stop u ≤ N)
    {t : Nat} {stk : List (Fin N)}
    (hInc : ∀ i j (hi : i < stk.length) (hj : j < stk.length), i < j →
      rd.entry (stk[i]'hi) < rd.entry (stk[j]'hj))
    (hMem : ∀ w : Fin N, w ∈ stk ↔ rd.entry w < t ∧ t ≤ rd.stop w) :
    ∀ i j (hi : i < stk.length) (hj : j < stk.length), i ≤ j →
      rd.stop (stk[j]'hj) ≤ rd.stop (stk[i]'hi) := by
  intro i j hi hj hij
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · have hiMem := (hMem (stk[i]'hi)).mp (List.getElem_mem hi)
    have hjMem := (hMem (stk[j]'hj)).mp (List.getElem_mem hj)
    have he := hInc i j hi hj hlt
    exact (dfs_stop_le_of_entry_lt rd hLt hInj hSpan (Nat.le_of_lt he) (by omega)).2

theorem dfs_stack_top_parent {N : Nat} {x : PackedStaticLayout.Input N}
    (rd : StaticTreeReader.Reader x)
    (hInj : ∀ u v : Fin N, rd.entry u = rd.entry v → u = v)
    (_hSpan : ∀ u : Fin N, rd.entry u < rd.stop u ∧ rd.stop u ≤ N)
    (u : Fin N) {stk : List (Fin N)}
    (hInc : ∀ i j (hi : i < stk.length) (hj : j < stk.length), i < j →
      rd.entry (stk[i]'hi) < rd.entry (stk[j]'hj))
    (hMem : ∀ w : Fin N, w ∈ stk ↔ rd.entry w < rd.entry u ∧ rd.entry u < rd.stop w) :
    (stk.length = 0 → u = x.root) ∧
    (∀ hPos : 0 < stk.length, u ≠ x.root ∧ stk[stk.length - 1] = x.parent.read u) := by
  have hProperAnc : ∀ w : Fin N, w ∈ stk ↔ IsForestAncestor x.parent.read w u ∧ w ≠ u := by
    intro w
    rw [hMem w, isForestAncestor_iff_rd_interval rd w u]
    constructor
    · rintro ⟨hlt, hstop⟩
      exact ⟨⟨Nat.le_of_lt hlt, hstop⟩, fun he => by subst he; omega⟩
    · rintro ⟨⟨hle, hstop⟩, hne⟩
      exact ⟨Nat.lt_of_le_of_ne hle (fun he => hne (hInj w u he)), hstop⟩
  have hAncProp : ∀ w : Fin N, w ∈ stk → IsForestAncestor x.parent.read w (x.parent.read u) := by
    intro w hw
    obtain ⟨hAnc, hne⟩ := (hProperAnc w).mp hw
    cases hAnc with
    | refl => exact False.elim (hne rfl)
    | step _ hPrev => exact hPrev
  by_cases hRoot : u = x.root
  · subst hRoot
    have hEmpty : stk.length = 0 := by
      cases hs : stk.length with
      | zero => rfl
      | succ k =>
        exfalso
        have h0 : 0 < stk.length := by omega
        obtain ⟨hAnc, hne⟩ := (hProperAnc (stk[0]'h0)).mp (List.getElem_mem h0)
        have hle := rd.input_ok.depth_le_of_isForestAncestor hAnc
        rw [rd.input_ok.depth_root] at hle
        exact hne (rd.input_ok.eq_root_of_depth_zero (Nat.eq_zero_of_le_zero hle))
    exact ⟨fun _ => rfl, fun hPos => False.elim (by omega)⟩
  · have hpNe : x.parent.read u ≠ u := by
      intro heq
      have hstep := rd.input_ok.depth_step u hRoot
      rw [heq] at hstep
      omega
    have hpMem : x.parent.read u ∈ stk := by
      rw [hProperAnc]
      exact ⟨IsForestAncestor.step u IsForestAncestor.refl, hpNe⟩
    obtain ⟨k, hk, hEqP⟩ := List.mem_iff_getElem.mp hpMem
    have hPos : 0 < stk.length := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    refine ⟨fun hz => False.elim (by omega), fun _ => ⟨hRoot, ?_⟩⟩
    by_cases hTopEq : stk[stk.length - 1] = x.parent.read u
    · exact hTopEq
    · exfalso
      have hkLt : k < stk.length - 1 := by
        rcases Nat.lt_trichotomy k (stk.length - 1) with hlt | heq | hgt
        · exact hlt
        · subst heq; exact False.elim (hTopEq hEqP)
        · omega
      have hTopMem := List.getElem_mem (Nat.sub_lt hPos Nat.one_pos)
      have hTopAnc : IsForestAncestor x.parent.read (stk[stk.length - 1]) (x.parent.read u) :=
        hAncProp _ hTopMem
      have hTopEntry : rd.entry (stk[stk.length - 1]) ≤ rd.entry (x.parent.read u) :=
        ((isForestAncestor_iff_rd_interval rd _ _).mp hTopAnc).1
      have hIncTop := hInc k (stk.length - 1) hk (Nat.sub_lt hPos Nat.one_pos) hkLt
      rw [hEqP] at hIncTop
      omega

end DfsStackMath

section Stage1Instrs

variable {bits : Nat}

def invEntryInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg6 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg3 reg6 mIdxFEntryInBase (by change 17 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg4 reg6 mIdxNH (by change 2 < 2 ^ bits; omega) ++
  [ .mov reg5 reg0
  , .branchLt reg5 reg4 11 17
  , .add reg6 reg3 reg5
  , .loadInput reg7 reg6
  , .add reg6 reg2 reg7
  , .storeData reg6 reg5
  , .add reg5 reg5 reg1
  , .goto 10
  ]))

end Stage1Instrs

section Stage1Phases

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def mkHaltPhase (instrs : List (Instr bits 15))
    (hNonHalt : instrs.all (nonHalt (L := DomL)) = true) : Phase DomL :=
  let code : Program DomL := (instrs ++ [Instr.halt]).toArray
  Phase.ofLast code instrs.length
    (by simp [code])
    (by
      have hLt : instrs.length < (instrs ++ [Instr.halt]).length := by simp
      change code[instrs.length]? = some .halt
      dsimp only [code]
      rw [Array.getElem?_eq_getElem (by simp)]
      simp)
    (by
      dsimp only [code]
      have hT : (instrs ++ [Instr.halt]).toArray.toList.take instrs.length = instrs := by
        simp
      rw [hT]; exact hNonHalt)

def invEntryPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (invEntryInstrs (bits := bits) h100)
    (by simp [invEntryInstrs, metaLoadInstrs, nonHalt])

theorem run_invEntry {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ t : State DomL,
      run (invEntryPhase (hi := hi) (hw := hw) h100).code input (10 + 7 * r.out.tables.next + 2) (Phase.initial s0) =
        some ⟨t, 10 + 7 * r.out.tables.next + 2⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ u : Fin r.out.tables.next,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next +
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm u)]?).map Fin.val =
            some u.val) ∧
      (∀ j, j < tempArrBase H.vertexCount H.arcCount r.out.tables.next ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + r.out.tables.next ≤ j →
        t.data[j]? = s0.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let hN : N = nodeCount (orderedConfig p large) r.out := (nodeCount_eq_next r.index.ok).symm
  have hNLe : N ≤ n + 1 := hN ▸ nodeCount_le r.index.ok
  have hStage1 : tempArrBase n m N + 3 * N ≤ workCap :=
    Nat.le_trans (tempArrBase_stage1_le hNLe) hWork
  have hMetaBits : metaArrBase n m N + mIdxNH < 2 ^ bits := by
    have := show tempArrBase n m N = metaArrBase n m N + 48 by rfl
    change metaArrBase n m N + 2 < 2 ^ bits; omega
  have hMetaTempBits : metaArrBase n m N + mIdxTempBase < 2 ^ bits := by
    have := show tempArrBase n m N = metaArrBase n m N + 48 by rfl
    change metaArrBase n m N + 13 < 2 ^ bits; omega
  have hMetaFEntBits : metaArrBase n m N + mIdxFEntryInBase < 2 ^ bits := by
    have := show tempArrBase n m N = metaArrBase n m N + 48 by rfl
    change metaArrBase n m N + 17 < 2 ^ bits; omega
  have hPre := dfs_preorder_bijection r
  have hLtEntry := hPre.1
  have hInjEntry := hPre.2.1
  let ph := invEntryPhase (hi := hi) (hw := hw) h100
  have hCodeSz : ph.code.size = 18 := by
    change ((invEntryInstrs (bits := bits) h100 ++ [Instr.halt]).toArray : Program DomL).size = 18
    simp [invEntryInstrs, metaLoadInstrs]
  have hPhasePl : Placed ph.code 0 (invEntryInstrs (bits := bits) h100) := by
    change Placed ((invEntryInstrs (bits := bits) h100 ++ [Instr.halt]).toArray : Program DomL) 0 _
    exact Placed_toArray_halt
  have hPl1 : Placed ph.code 0
      (metaLoadInstrs reg2 reg6 mIdxTempBase (by change 13 < 2 ^ bits; omega)) := by
    unfold invEntryInstrs at hPhasePl; exact Placed_append_left hPhasePl
  have hR1 := Placed_append_right (by unfold invEntryInstrs at hPhasePl; exact hPhasePl)
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  rw [hLml] at hR1
  have hPl2 : Placed ph.code (0 + 3)
      (metaLoadInstrs reg3 reg6 mIdxFEntryInBase (by change 17 < 2 ^ bits; omega)) :=
    Placed_append_left hR1
  have hR2 := Placed_append_right hR1
  rw [hLml] at hR2
  have hPl3 : Placed ph.code (0 + 3 + 3)
      (metaLoadInstrs reg4 reg6 mIdxNH (by change 2 < 2 ^ bits; omega)) :=
    Placed_append_left hR2
  have hR3 := Placed_append_right hR2
  rw [hLml] at hR3
  obtain ⟨s1, hSt1, hpc1, hd1, hr2_1, hro1⟩ :=
    run_metaLoad_slice (st := Phase.initial s0) (by intro h; cases h) (by intro h; cases h) hPl1
      (by rw [hCodeSz]; omega) rfl hMeta.rMeta_eq hMetaTempBits hMeta.meta_tempBase
  obtain ⟨s2, hSt2, hpc2, hd2, hr3_2, hro2⟩ :=
    run_metaLoad_slice (by intro h; cases h) (by intro h; cases h) hPl2 (by rw [hCodeSz]; omega)
      hpc1 (by rw [hro1 rMeta (by intro h; cases h) (by intro h; cases h)]; change (reg s0 rMeta).val = _; exact hMeta.rMeta_eq)
      hMetaFEntBits (by rw [hd1]; exact hMeta.meta_fEntryIn)
  obtain ⟨s3, hSt3, hpc3, hd3, hr4_3, hro3⟩ :=
    run_metaLoad_slice (by intro h; cases h) (by intro h; cases h) hPl3 (by rw [hCodeSz]; omega)
      hpc2 (by rw [hro2 rMeta (by intro h; cases h) (by intro h; cases h),
        hro1 rMeta (by intro h; cases h) (by intro h; cases h)]; change (reg s0 rMeta).val = _; exact hMeta.rMeta_eq)
      hMetaBits (by rw [hd2, hd1]; exact hMeta.meta_NH)
  have hAtMov : ph.code[s3.pc]? = some (.mov reg5 reg0) := by
    rw [hpc3]; exact hR3 0 _ rfl
  obtain ⟨s4, hs4, hpc4, hr5_4, hro4, hd4⟩ := step_mov_at (input := input) hAtMov (by rw [hpc3, hCodeSz]; omega)
  have hr0_4 : (reg s4 reg0).val = 0 := by
    rw [hro4 reg0 (by intro h; cases h), hro3 reg0 (by intro h; cases h) (by intro h; cases h),
      hro2 reg0 (by intro h; cases h) (by intro h; cases h),
      hro1 reg0 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r0_zero
  have hr1_4 : (reg s4 reg1).val = 1 := by
    rw [hro4 reg1 (by intro h; cases h), hro3 reg1 (by intro h; cases h) (by intro h; cases h),
      hro2 reg1 (by intro h; cases h) (by intro h; cases h),
      hro1 reg1 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r1_one
  have hr2_4 : (reg s4 reg2).val = tempArrBase n m N := by
    rw [hro4 reg2 (by intro h; cases h), hro3 reg2 (by intro h; cases h) (by intro h; cases h),
      hro2 reg2 (by intro h; cases h) (by intro h; cases h), hr2_1]
  have hr3_4 : (reg s4 reg3).val = 4 + n + 2 * N := by
    rw [hro4 reg3 (by intro h; cases h), hro3 reg3 (by intro h; cases h) (by intro h; cases h), hr3_2]
  have hr4_4 : (reg s4 reg4).val = N := by rw [hro4 reg4 (by intro h; cases h), hr4_3]
  have hrm_4 : (reg s4 rMeta).val = metaArrBase n m N := by
    rw [hro4 rMeta (by intro h; cases h), hro3 rMeta (by intro h; cases h) (by intro h; cases h),
      hro2 rMeta (by intro h; cases h) (by intro h; cases h),
      hro1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  have hpc_4 : s4.pc = 10 := by rw [hpc4, hpc3]
  have hd_4 : s4.data = s0.data := by rw [hd4, hd3, hd2, hd1]; rfl
  -- Loop induction for remaining `N - k` iterations starting from `(k ≤ N, reg5 = k)`:
  have hLoop : ∀ (rem k : Nat) (st : State DomL),
      k + rem = N → st.pc = 10 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 → (reg st rMeta).val = metaArrBase n m N →
      (reg st reg2).val = tempArrBase n m N → (reg st reg3).val = 4 + n + 2 * N →
      (reg st reg4).val = N → (reg st reg5).val = k →
      (∀ u : Fin N, u.val < k →
        (st.data[tempArrBase n m N + r.index.reader.entry (Fin.cast hN u)]?).map Fin.val = some u.val) →
      (∀ j, j < tempArrBase n m N ∨ tempArrBase n m N + N ≤ j → st.data[j]? = s0.data[j]?) →
      ∃ t : State DomL, Steps ph.code input (7 * rem + 1) st t ∧
        t.pc = 17 ∧
        (reg t rMeta).val = metaArrBase n m N ∧ (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (∀ u : Fin N,
          (t.data[tempArrBase n m N + r.index.reader.entry (Fin.cast hN u)]?).map Fin.val = some u.val) ∧
        (∀ j, j < tempArrBase n m N ∨ tempArrBase n m N + N ≤ j → t.data[j]? = s0.data[j]?) := by
    intro rem
    induction rem with
    | zero =>
      intro k st hSum hpc h0 h1 hm h2 h3 h4 h5 hDone hFr
      have hkEq : k = N := by omega
      have hBrAt : ph.code[st.pc]? = some (.branchLt reg5 reg4 11 17) := by
        rw [hpc]; exact hR3 1 _ rfl
      obtain ⟨t, htStep, htpc, htr, htd⟩ := step_branchLt_at (input := input) hBrAt
        (by split <;> rw [hCodeSz] <;> omega)
      have hFalse : ¬ (reg st reg5).val < (reg st reg4).val := by rw [h5, h4]; omega
      rw [ite_eq_right hFalse] at htpc
      have htEqReg : ∀ r : Fin 15, reg t r = reg st r := fun r => by
        rcases t with ⟨tr, _, _, _, _⟩; rcases st with ⟨sr, _, _, _, _⟩
        dsimp only at htr; subst tr; rfl
      refine ⟨t, steps_1_of_step htStep, htpc, by rw [htEqReg]; exact hm, by rw [htEqReg]; exact h0,
        by rw [htEqReg]; exact h1, fun u => ?_, fun j hj => by rw [htd]; exact hFr j hj⟩
      rw [htd]; exact hDone u (by omega)
    | succ rem ih =>
      intro k st hSum hpc h0 h1 hm h2 h3 h4 h5 hDone hFr
      have hkLt : k < N := by omega
      have hBrAt : ph.code[st.pc]? = some (.branchLt reg5 reg4 11 17) := by
        rw [hpc]; exact hR3 1 _ rfl
      obtain ⟨sA, hsA, hpcA, hrA, hdA⟩ := step_branchLt_at (input := input) hBrAt
        (by split <;> rw [hCodeSz] <;> omega)
      have hTrue : (reg st reg5).val < (reg st reg4).val := by rw [h5, h4]; omega
      rw [ite_eq_left hTrue] at hpcA
      have hAEqReg : ∀ r : Fin 15, reg sA r = reg st r := fun r => by
        rcases sA with ⟨ar, _, _, _, _⟩; rcases st with ⟨sr, _, _, _, _⟩
        dsimp only at hrA; subst ar; rfl
      have hAddr1 : ph.code[sA.pc]? = some (.add reg6 reg3 reg5) := by
        rw [hpcA]; exact hR3 2 _ rfl
      obtain ⟨sB, hsB, hpcB, hrBd, hrBo, hdB⟩ := step_add_at (input := input) hAddr1
        (by rw [hpcA, hCodeSz]; omega)
      have hInCap := hIn.cap_ge
      change 4 + n + 4 * N + 3 * m ≤ inputCap at hInCap
      have hInIdx : (reg sB reg6).val = 4 + n + 2 * N + k := by
        have h3A : (reg sA reg3).val = 4 + n + 2 * N := by rw [hAEqReg]; exact h3
        have h5A : (reg sA reg5).val = k := by rw [hAEqReg]; exact h5
        rw [hrBd, add_no_wrap _ _ (by rw [h3A, h5A]; omega), h3A, h5A]
      let uk : Fin N := ⟨k, hkLt⟩
      have hFEnt := hIn.fEntry_at uk
      obtain ⟨we, hwe, hweV⟩ := Option.map_eq_some_iff.mp hFEnt
      have hLoadAt : ph.code[sB.pc]? = some (.loadInput reg7 reg6) := by
        rw [hpcB, hpcA]; exact hR3 3 _ rfl
      obtain ⟨sC, hsC, hpcC, hrCd, hrCo, hdC⟩ := step_loadInput_at (input := input) hLoadAt
        (by rw [hpcB, hpcA, hCodeSz]; omega) (by rw [hInIdx]; exact hwe)
      have hEntVal : (reg sC reg7).val = r.index.reader.entry (Fin.cast hN uk) := by
        rw [hrCd, hweV]
      have hEntLtN : (reg sC reg7).val < N := by rw [hEntVal]; exact hLtEntry uk
      have hAdd2At : ph.code[sC.pc]? = some (.add reg6 reg2 reg7) := by
        rw [hpcC, hpcB, hpcA]; exact hR3 4 _ rfl
      obtain ⟨sD, hsD, hpcD, hrDd, hrDo, hdD⟩ := step_add_at (input := input) hAdd2At
        (by rw [hpcC, hpcB, hpcA, hCodeSz]; omega)
      have hReg2C : (reg sC reg2).val = tempArrBase n m N := by
        rw [hrCo reg2 (by intro h; cases h), hrBo reg2 (by intro h; cases h), hAEqReg]; exact h2
      have hWrAddr : (reg sD reg6).val = tempArrBase n m N + r.index.reader.entry (Fin.cast hN uk) := by
        rw [hrDd, add_no_wrap _ _ (by rw [hReg2C, hEntVal]; have := hLtEntry uk; omega),
          hReg2C, hEntVal]
      have hStLt : (reg sD reg6).val < sD.data.size := by
        rw [hWrAddr, sD.data_size]
        change tempArrBase n m N + r.index.reader.entry (Fin.cast hN uk) < workCap
        have := hLtEntry uk; omega
      have hStoreAt : ph.code[sD.pc]? = some (.storeData reg6 reg5) := by
        rw [hpcD, hpcC, hpcB, hpcA]; exact hR3 5 _ rfl
      obtain ⟨hsE, hpcE, _⟩ := step_storeData_at (input := input) hStoreAt hStLt
        (by rw [hpcD, hpcC, hpcB, hpcA, hCodeSz]; omega)
      let sE : State DomL :=
        { sD with
          data := sD.data.set (reg sD reg6).val (reg sD reg5) hStLt
          pc := sD.pc + 1
          data_size := by simp only [Array.size_set, sD.data_size] }
      have hIncAt : ph.code[sE.pc]? = some (.add reg5 reg5 reg1) := by
        change ph.code[sD.pc + 1]? = _
        rw [hpcD, hpcC, hpcB, hpcA]; exact hR3 6 _ rfl
      obtain ⟨sF, hsF, hpcF, hrFd, hrFo, hdF⟩ := step_add_at (input := input) hIncAt
        (by change sD.pc + 1 + 1 < _; rw [hpcD, hpcC, hpcB, hpcA, hCodeSz]; omega)
      have hGotoAt : ph.code[sF.pc]? = some (.goto 10) := by
        rw [hpcF]; change ph.code[(sD.pc + 1) + 1]? = _
        rw [hpcD, hpcC, hpcB, hpcA]; exact hR3 7 _ rfl
      obtain ⟨sG, hsG, hpcG, hrG, hdG⟩ := step_goto_at (input := input) hGotoAt
        (by rw [hCodeSz]; omega)
      have hGEqReg : ∀ r : Fin 15, reg sG r = reg sF r := fun r => by
        rcases sG with ⟨gr, _, _, _, _⟩; rcases sF with ⟨fr, _, _, _, _⟩
        dsimp only at hrG; subst gr; rfl
      have hs5D : (reg sD reg5).val = k := by
        rw [hrDo reg5 (by intro h; cases h), hrCo reg5 (by intro h; cases h),
          hrBo reg5 (by intro h; cases h), hAEqReg]; exact h5
      have hs1E : (reg sE reg1).val = 1 := by
        change (reg sD reg1).val = 1
        rw [hrDo reg1 (by intro h; cases h), hrCo reg1 (by intro h; cases h),
          hrBo reg1 (by intro h; cases h), hAEqReg]; exact h1
      have hsEData : sE.data = sD.data.set (reg sD reg6).val (reg sD reg5) hStLt := rfl
      have hsDataPast : ∀ j, j ≠ tempArrBase n m N + r.index.reader.entry (Fin.cast hN uk) →
          sG.data[j]? = st.data[j]? := fun j hj => by
        rw [hdG, hdF, hsEData, Array.getElem?_set_ne hStLt (by rw [hWrAddr]; exact hj.symm),
          hdD, hdC, hdB, hdA]
      have hDoneNext : ∀ u : Fin N, u.val < k + 1 →
          (sG.data[tempArrBase n m N + r.index.reader.entry (Fin.cast hN u)]?).map Fin.val = some u.val := by
        intro u hu
        by_cases heq : u.val = k
        · have huEq : u = uk := Fin.ext heq
          subst huEq
          rw [hdG, hdF, hsEData, ← hWrAddr]
          simp [hStLt, Option.map_some, hs5D]
          exact heq.symm
        · have hneU : u ≠ uk := fun h => heq (congrArg Fin.val h)
          have hneE : r.index.reader.entry (Fin.cast hN u) ≠
              r.index.reader.entry (Fin.cast hN uk) := fun h => hneU (hInjEntry u uk h)
          rw [hsDataPast _ (by omega)]
          exact hDone u (by omega)
      have hFrNext : ∀ j, j < tempArrBase n m N ∨ tempArrBase n m N + N ≤ j →
          sG.data[j]? = s0.data[j]? := fun j hj => by
        have := hLtEntry uk
        rw [hsDataPast j (by omega)]
        exact hFr j hj
      have hPreserve : ∀ x : Fin 15, x ≠ reg5 → x ≠ reg6 → x ≠ reg7 → reg sG x = reg st x := by
        intro x h5x h6x h7x
        rw [hGEqReg, hrFo x h5x]
        change reg sD x = reg st x
        rw [hrDo x h6x, hrCo x h7x, hrBo x h6x, hAEqReg]
      obtain ⟨t, htSteps, htpc, htm, ht0, ht1, htDone, htFr⟩ :=
        ih (k + 1) sG (by omega) hpcG
          (by rw [hPreserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPreserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPreserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hm])
          (by rw [hPreserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2])
          (by rw [hPreserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3])
          (by rw [hPreserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by
            rw [hGEqReg, hrFd]
            change (add (reg sD reg5) (reg sE reg1)).val = k + 1
            rw [add_no_wrap _ _ (by rw [hs5D, hs1E]; omega), hs5D, hs1E])
          hDoneNext hFrNext
      refine ⟨t, Steps.cons hsA (Steps.cons hsB (Steps.cons hsC (Steps.cons hsD
        (Steps.cons hsE (Steps.cons hsF (Steps.cons hsG htSteps)))))),
        htpc, htm, ht0, ht1, htDone, htFr⟩
  obtain ⟨t, htSteps, htpc, htm, ht0, ht1, htDone, htFr⟩ :=
    hLoop N 0 s4 (Nat.zero_add N) hpc_4 hr0_4 hr1_4 hrm_4 hr2_4 hr3_4 hr4_4
      (by rw [hr5_4, hro3 reg0 (by intro h; cases h) (by intro h; cases h),
        hro2 reg0 (by intro h; cases h) (by intro h; cases h),
        hro1 reg0 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r0_zero)
      (fun u hu => False.elim (Nat.not_lt_zero _ hu))
      (fun j _ => by rw [hd_4])
  have hAllSteps : Steps ph.code input (10 + 7 * N + 1) (Phase.initial s0) t := by
    have h1 := hSt1.append (hSt2.append (hSt3.append (steps_1_of_step hs4)))
    rw [show 10 + 7 * N + 1 = 3 + (3 + (3 + 1)) + (7 * N + 1) by omega]
    exact h1.append htSteps
  have hHalt : step ph.code input t = some (.halted t) :=
    step_halt_at (by
      rw [htpc]
      change ((invEntryInstrs (bits := bits) h100 ++ [Instr.halt]).toArray : Program DomL)[17]? = some .halt
      have hL : (invEntryInstrs (bits := bits) h100).length = 17 := by
        simp [invEntryInstrs, metaLoadInstrs]
      rw [Array.getElem?_eq_getElem (by simp [hL])]
      simp [invEntryInstrs, metaLoadInstrs])
  refine ⟨t, hAllSteps.halts hHalt, hMeta.preserve htm ht0 ht1 (fun i hi22 => htFr _ (Or.inl (by
    change metaArrBase n m N + i < tempArrBase n m N
    have htb : tempArrBase n m N = metaArrBase n m N + 48 := rfl
    omega))), htDone, htFr⟩

/-! #### 5B. DFS stack reconstruction (`dfsStackPhase`) & `stage1Phases` -/

inductive JumpChain (F : JumpForest) (a : Nat) : Nat → Prop
  | refl : JumpChain F a a
  | step {b c : Nat} : 0 < c → c < F.size → b = F.parentOf c → JumpChain F a b → JumpChain F a c

theorem jumpChain_mono {F G : JumpForest}
    (h : ∀ a b, (0 < b ∧ b < F.size ∧ a = F.parentOf b) → (0 < b ∧ b < G.size ∧ a = G.parentOf b))
    {x y : Nat} (hc : JumpChain F x y) : JumpChain G x y := by
  induction hc with
  | refl => exact JumpChain.refl
  | step hb0 hbS ha _ ih =>
    have h' := h _ _ ⟨hb0, hbS, ha⟩
    exact JumpChain.step h'.1 h'.2.1 h'.2.2 ih

theorem jumpChain_trans {F : JumpForest} {a b : Nat}
    (h1 : JumpChain F a b) : ∀ {c : Nat}, JumpChain F b c → JumpChain F a c := by
  intro c h2
  induction h2 with
  | refl => exact h1
  | step hb0 hbS ha _ ih => exact JumpChain.step hb0 hbS ha ih

theorem validJumpForest_root_zero {F : JumpForest} (hV : ValidJumpForest F) :
    F.parentOf 0 = 0 ∧ F.jumpOf 0 = 0 ∧ F.depthOf 0 = 0 := by
  induction hV with
  | init => exact ⟨rfl, rfl, rfl⟩
  | @appendLeaf F p hF hp ih =>
    have hPos : 0 < F.size := Nat.zero_lt_of_lt hp
    rw [parentOf_appendLeaf_old F p hPos,
      jumpOf_appendLeaf_old F p hPos,
      depthOf_appendLeaf_old F p hPos]
    exact ih

theorem jumpForest_jump_ancestor {F : JumpForest} (hV : ValidJumpForest F) :
    ∀ u : Nat, u < F.size → JumpChain F (F.jumpOf u) u := by
  induction hV with
  | init =>
    intro u hu
    change u < 1 at hu
    have hu0 : u = 0 := by omega
    subst hu0
    rw [(validJumpForest_root_zero ValidJumpForest.init).2.1]
    exact JumpChain.refl
  | @appendLeaf F p hF hp ih =>
    intro u hu
    rw [JumpForest.size_appendLeaf] at hu
    have hStepMono : ∀ a b,
        (0 < b ∧ b < F.size ∧ a = F.parentOf b) →
        (0 < b ∧ b < (F.appendLeaf p).size ∧ a = (F.appendLeaf p).parentOf b) := by
      intro a b ⟨hb0, hbS, ha⟩
      refine ⟨hb0, by rw [JumpForest.size_appendLeaf]; omega, ?_⟩
      rw [ha, parentOf_appendLeaf_old F p hbS]
    by_cases hOld : u < F.size
    · rw [jumpOf_appendLeaf_old F p hOld]
      exact jumpChain_mono hStepMono (ih u hOld)
    · have huEq : u = F.size := by omega
      subst huEq
      have hPos : 0 < F.size := Nat.zero_lt_of_lt hp
      have hUpP : (F.appendLeaf p).parentOf F.size = p := by
        unfold JumpForest.parentOf
        rw [recordAt_appendLeaf_new]
        rfl
      have hRule := validJumpForest_skew_rule (ValidJumpForest.appendLeaf hF hp) F.size hPos
        (by rw [JumpForest.size_appendLeaf]; omega)
      dsimp only at hRule
      rw [hUpP, jumpOf_appendLeaf_old F p hp] at hRule
      have haLt : F.jumpOf p < F.size := hF.jumpOf_lt_size hp
      rw [jumpOf_appendLeaf_old F p haLt] at hRule
      rw [hRule]
      split
      · have hbToA := jumpChain_mono hStepMono (ih (F.jumpOf p) haLt)
        have haToP := jumpChain_mono hStepMono (ih p hp)
        exact JumpChain.step hPos (by rw [JumpForest.size_appendLeaf]; omega) hUpP.symm
          (jumpChain_trans hbToA haToP)
      · exact JumpChain.step hPos (by rw [JumpForest.size_appendLeaf]; omega) hUpP.symm
          JumpChain.refl

theorem isForestAncestor_of_jumpChain {H : LabelledQuotient} [DecidableEq (CutPair H)]
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
    {a b : Nat} :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    JumpChain B.F a b →
    ∀ (ha : a < r.out.tables.next) (hb : b < r.out.tables.next),
      let hN : r.out.tables.next = nodeCount (orderedConfig p large) r.out :=
        (nodeCount_eq_next r.index.ok).symm
      IsForestAncestor (PaperB.EX24.FinalDFS.packedInput r.index.ok).parent.read
        (Fin.cast hN ⟨a, ha⟩) (Fin.cast hN ⟨b, hb⟩) := by
  intro B hRel
  induction hRel with
  | refl =>
    intro ha hb hN
    have hEq : (⟨a, ha⟩ : Fin r.out.tables.next) = ⟨a, hb⟩ := rfl
    exact hEq ▸ IsForestAncestor.refl
  | @step c d hdPos hdSz hEqC _ ih =>
    intro ha hb hN
    subst hEqC
    have hcLt : B.F.parentOf d < r.out.tables.next := by
      have hSz : B.F.size = r.out.tables.next := B.G.size_eq
      have hPLt := B.G.layout.valid.parentOf_lt_size hdSz
      omega
    have ih' := ih ha hcLt
    have hp := (reader_matches_bundle_forest flat increasing covers rankArc r ⟨d, hb⟩).1
    have hPFin : (PaperB.EX24.FinalDFS.packedInput r.index.ok).parent.read (Fin.cast hN ⟨d, hb⟩) =
        Fin.cast hN ⟨B.F.parentOf d, hcLt⟩ := Fin.ext hp
    have hAnc : IsForestAncestor (PaperB.EX24.FinalDFS.packedInput r.index.ok).parent.read
        (Fin.cast hN ⟨B.F.parentOf d, hcLt⟩) (Fin.cast hN ⟨d, hb⟩) :=
      hPFin ▸ IsForestAncestor.step (Fin.cast hN ⟨d, hb⟩) IsForestAncestor.refl
    exact isForestAncestor_trans ih' hAnc

end Stage1Phases

end Stage1ForestRecon

section Stage2CsrKahn

section CsrMath

/-- Prefix count of outgoing arcs `[0..k)` whose quotient source is vertex `u`. -/
def outCountPrefix (H : LabelledQuotient) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, u =>
    outCountPrefix H k u +
      if h : k < H.arcCount then
        if (rawOccurrence H ⟨k, h⟩).1.val = u then 1 else 0
      else 0

/-- Prefix count of incoming arcs `[0..k)` whose quotient head is vertex `v`. -/
def inCountPrefix (H : LabelledQuotient) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, v =>
    inCountPrefix H k v +
      if h : k < H.arcCount then
        if (rawHead H ⟨k, h⟩).val = v then 1 else 0
      else 0

/-- Prefix list of outgoing arc indices in `[0..k)` whose source is `u`. -/
def outArcsPrefix (H : LabelledQuotient) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, u =>
    if h : k < H.arcCount then
      if (rawOccurrence H ⟨k, h⟩).1.val = u then outArcsPrefix H k u ++ [k]
      else outArcsPrefix H k u
    else outArcsPrefix H k u

/-- Prefix list of incoming arc indices in `[0..k)` whose head is `v`. -/
def inArcsPrefix (H : LabelledQuotient) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v =>
    if h : k < H.arcCount then
      if (rawHead H ⟨k, h⟩).val = v then inArcsPrefix H k v ++ [k]
      else inArcsPrefix H k v
    else inArcsPrefix H k v

def degOut (H : LabelledQuotient) (u : Nat) : Nat := outCountPrefix H H.arcCount u
def degIn (H : LabelledQuotient) (v : Nat) : Nat := inCountPrefix H H.arcCount v

def prefixOut (H : LabelledQuotient) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixOut H i + degOut H i

def prefixIn (H : LabelledQuotient) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixIn H i + degIn H i

theorem outArcsPrefix_length (H : LabelledQuotient) (k u : Nat) :
    (outArcsPrefix H k u).length = outCountPrefix H k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [outArcsPrefix, outCountPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk, dite_eq_left hk]
      by_cases hu : (rawOccurrence H ⟨k, hk⟩).1.val = u
      · rw [ite_eq_left hu, ite_eq_left hu]; simp [ih]
      · rw [ite_eq_right hu, ite_eq_right hu]; exact ih
    · rw [dite_eq_right hk, dite_eq_right hk]; simp [ih]

theorem inArcsPrefix_length (H : LabelledQuotient) (k v : Nat) :
    (inArcsPrefix H k v).length = inCountPrefix H k v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [inArcsPrefix, inCountPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk, dite_eq_left hk]
      by_cases hv : (rawHead H ⟨k, hk⟩).val = v
      · rw [ite_eq_left hv, ite_eq_left hv]; simp [ih]
      · rw [ite_eq_right hv, ite_eq_right hv]; exact ih
    · rw [dite_eq_right hk, dite_eq_right hk]; simp [ih]

theorem outArcsPrefix_lt (H : LabelledQuotient) (k u x : Nat)
    (hx : x ∈ outArcsPrefix H k u) : x < k := by
  induction k with
  | zero => simp [outArcsPrefix] at hx
  | succ k ih =>
    simp only [outArcsPrefix] at hx
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk] at hx
      by_cases hu : (rawOccurrence H ⟨k, hk⟩).1.val = u
      · rw [ite_eq_left hu] at hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with h1 | h2
        · exact Nat.lt_trans (ih h1) (Nat.lt_succ_self k)
        · subst h2; exact Nat.lt_succ_self x
      · rw [ite_eq_right hu] at hx
        exact Nat.lt_trans (ih hx) (Nat.lt_succ_self k)
    · rw [dite_eq_right hk] at hx
      exact Nat.lt_trans (ih hx) (Nat.lt_succ_self k)

theorem inArcsPrefix_lt (H : LabelledQuotient) (k v x : Nat)
    (hx : x ∈ inArcsPrefix H k v) : x < k := by
  induction k with
  | zero => simp [inArcsPrefix] at hx
  | succ k ih =>
    simp only [inArcsPrefix] at hx
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk] at hx
      by_cases hv : (rawHead H ⟨k, hk⟩).val = v
      · rw [ite_eq_left hv] at hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with h1 | h2
        · exact Nat.lt_trans (ih h1) (Nat.lt_succ_self k)
        · subst h2; exact Nat.lt_succ_self x
      · rw [ite_eq_right hv] at hx
        exact Nat.lt_trans (ih hx) (Nat.lt_succ_self k)
    · rw [dite_eq_right hk] at hx
      exact Nat.lt_trans (ih hx) (Nat.lt_succ_self k)

theorem outArcsPrefix_nodup (H : LabelledQuotient) (k u : Nat) :
    (outArcsPrefix H k u).Nodup := by
  induction k with
  | zero => simp [outArcsPrefix]
  | succ k ih =>
    simp only [outArcsPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hu : (rawOccurrence H ⟨k, hk⟩).1.val = u
      · rw [ite_eq_left hu, List.nodup_append]
        refine ⟨ih, by simp, fun a ha b hb hab => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb; subst hab
        exact absurd (outArcsPrefix_lt H _ u a ha) (Nat.lt_irrefl a)
      · rw [ite_eq_right hu]; exact ih
    · rw [dite_eq_right hk]; exact ih

theorem inArcsPrefix_nodup (H : LabelledQuotient) (k v : Nat) :
    (inArcsPrefix H k v).Nodup := by
  induction k with
  | zero => simp [inArcsPrefix]
  | succ k ih =>
    simp only [inArcsPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hv : (rawHead H ⟨k, hk⟩).val = v
      · rw [ite_eq_left hv, List.nodup_append]
        refine ⟨ih, by simp, fun a ha b hb hab => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb; subst hab
        exact absurd (inArcsPrefix_lt H _ v a ha) (Nat.lt_irrefl a)
      · rw [ite_eq_right hv]; exact ih
    · rw [dite_eq_right hk]; exact ih

theorem mem_outArcsPrefix_iff (H : LabelledQuotient) (k u x : Nat) :
    x ∈ outArcsPrefix H k u ↔
      ∃ hx : x < H.arcCount, x < k ∧ (rawOccurrence H ⟨x, hx⟩).1.val = u := by
  induction k with
  | zero => simp [outArcsPrefix]
  | succ k ih =>
    simp only [outArcsPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hSrc : (rawOccurrence H ⟨k, hk⟩).1.val = u
      · rw [ite_eq_left hSrc]
        simp only [List.mem_append, List.mem_singleton, ih]
        constructor
        · rintro (⟨hx, hxk, hEq⟩ | h2)
          · exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
          · subst h2; exact ⟨hk, Nat.lt_succ_self x, hSrc⟩
        · rintro ⟨hx, hxk1, hEq⟩
          by_cases hxk : x < k
          · exact Or.inl ⟨hx, hxk, hEq⟩
          · have : x = k := by omega
            exact Or.inr this
      · rw [ite_eq_right hSrc, ih]
        constructor
        · rintro ⟨hx, hxk, hEq⟩
          exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
        · rintro ⟨hx, hxk1, hEq⟩
          by_cases hxk : x < k
          · exact ⟨hx, hxk, hEq⟩
          · have hxEq : x = k := by omega
            subst hxEq
            exact absurd hEq hSrc
    · rw [dite_eq_right hk, ih]
      constructor
      · rintro ⟨hx, hxk, hEq⟩
        exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
      · rintro ⟨hx, hxk1, hEq⟩
        by_cases hxk : x < k
        · exact ⟨hx, hxk, hEq⟩
        · have hxEq : x = k := by omega
          subst hxEq
          exact absurd hx hk

theorem mem_inArcsPrefix_iff (H : LabelledQuotient) (k v x : Nat) :
    x ∈ inArcsPrefix H k v ↔
      ∃ hx : x < H.arcCount, x < k ∧ (rawHead H ⟨x, hx⟩).val = v := by
  induction k with
  | zero => simp [inArcsPrefix]
  | succ k ih =>
    simp only [inArcsPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hHead : (rawHead H ⟨k, hk⟩).val = v
      · rw [ite_eq_left hHead]
        simp only [List.mem_append, List.mem_singleton, ih]
        constructor
        · rintro (⟨hx, hxk, hEq⟩ | h2)
          · exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
          · subst h2; exact ⟨hk, Nat.lt_succ_self x, hHead⟩
        · rintro ⟨hx, hxk1, hEq⟩
          by_cases hxk : x < k
          · exact Or.inl ⟨hx, hxk, hEq⟩
          · have : x = k := by omega
            exact Or.inr this
      · rw [ite_eq_right hHead, ih]
        constructor
        · rintro ⟨hx, hxk, hEq⟩
          exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
        · rintro ⟨hx, hxk1, hEq⟩
          by_cases hxk : x < k
          · exact ⟨hx, hxk, hEq⟩
          · have hxEq : x = k := by omega
            subst hxEq
            exact absurd hEq hHead
    · rw [dite_eq_right hk, ih]
      constructor
      · rintro ⟨hx, hxk, hEq⟩
        exact ⟨hx, Nat.lt_trans hxk (Nat.lt_succ_self k), hEq⟩
      · rintro ⟨hx, hxk1, hEq⟩
        by_cases hxk : x < k
        · exact ⟨hx, hxk, hEq⟩
        · have hxEq : x = k := by omega
          subst hxEq
          exact absurd hx hk

theorem outCountPrefix_mono (H : LabelledQuotient) {a b : Nat} (hab : a ≤ b) (u : Nat) :
    outCountPrefix H a u ≤ outCountPrefix H b u := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    change outCountPrefix H a u ≤ outCountPrefix H m u + _
    omega

theorem inCountPrefix_mono (H : LabelledQuotient) {a b : Nat} (hab : a ≤ b) (v : Nat) :
    inCountPrefix H a v ≤ inCountPrefix H b v := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    change inCountPrefix H a v ≤ inCountPrefix H m v + _
    omega

theorem prefixOut_mono (H : LabelledQuotient) {i j : Nat} (hij : i ≤ j) :
    prefixOut H i ≤ prefixOut H j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    change prefixOut H i ≤ prefixOut H m + degOut H m
    omega

theorem prefixIn_mono (H : LabelledQuotient) {i j : Nat} (hij : i ≤ j) :
    prefixIn H i ≤ prefixIn H j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    change prefixIn H i ≤ prefixIn H m + degIn H m
    omega

private def sumNatUpTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => sumNatUpTo f i + f i

private theorem sumNatUpTo_add (f g : Nat → Nat) (n : Nat) :
    sumNatUpTo (fun i => f i + g i) n = sumNatUpTo f n + sumNatUpTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNatUpTo, ih]
    omega

private theorem sumNatUpTo_ite_eq {n v0 : Nat} (hv0 : v0 < n) :
    sumNatUpTo (fun i => if i = v0 then 1 else 0) n = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumNatUpTo]
    by_cases h : v0 = m
    · subst h
      have hZero : ∀ k ≤ v0, sumNatUpTo (fun i => if i = v0 then 1 else 0) k = 0 := by
        intro k hk
        induction k with
        | zero => rfl
        | succ k ihk =>
          simp only [sumNatUpTo, ihk (by omega)]
          have hne : k ≠ v0 := by omega
          simp [hne]
      rw [hZero v0 (Nat.le_refl _)]
      simp
    · have hvLt : v0 < m := by omega
      rw [ih hvLt]
      have hne : m ≠ v0 := fun heq => h heq.symm
      simp [hne]

theorem prefixOut_eq_sum (H : LabelledQuotient) (i : Nat) :
    prefixOut H i = sumNatUpTo (degOut H) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [prefixOut, sumNatUpTo, ih]

theorem prefixIn_eq_sum (H : LabelledQuotient) (i : Nat) :
    prefixIn H i = sumNatUpTo (degIn H) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [prefixIn, sumNatUpTo, ih]

theorem sum_outCountPrefix (H : LabelledQuotient) (k : Nat) (hk : k ≤ H.arcCount) :
    sumNatUpTo (outCountPrefix H k) H.vertexCount = k := by
  induction k with
  | zero =>
    change sumNatUpTo (fun _ => 0) H.vertexCount = 0
    induction H.vertexCount with
    | zero => rfl
    | succ m ih => simp [sumNatUpTo, ih]
  | succ k ih =>
    have hkLt : k < H.arcCount := hk
    have hkLe : k ≤ H.arcCount := Nat.le_of_lt hkLt
    have heq : (fun u => outCountPrefix H (k + 1) u) =
        fun u => outCountPrefix H k u +
          if u = (rawOccurrence H ⟨k, hkLt⟩).1.val then 1 else 0 := by
      funext u
      simp only [outCountPrefix, dite_eq_left hkLt]
      by_cases h : (rawOccurrence H ⟨k, hkLt⟩).1.val = u
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · have hne : u ≠ (rawOccurrence H ⟨k, hkLt⟩).1.val := fun he => h he.symm
        rw [ite_eq_right h, ite_eq_right hne]
    change sumNatUpTo (fun u => outCountPrefix H (k + 1) u) H.vertexCount = k + 1
    rw [heq, sumNatUpTo_add, ih hkLe, sumNatUpTo_ite_eq (rawOccurrence H ⟨k, hkLt⟩).1.isLt]

theorem sum_inCountPrefix (H : LabelledQuotient) (k : Nat) (hk : k ≤ H.arcCount) :
    sumNatUpTo (inCountPrefix H k) H.vertexCount = k := by
  induction k with
  | zero =>
    change sumNatUpTo (fun _ => 0) H.vertexCount = 0
    induction H.vertexCount with
    | zero => rfl
    | succ m ih => simp [sumNatUpTo, ih]
  | succ k ih =>
    have hkLt : k < H.arcCount := hk
    have hkLe : k ≤ H.arcCount := Nat.le_of_lt hkLt
    have heq : (fun v => inCountPrefix H (k + 1) v) =
        fun v => inCountPrefix H k v +
          if v = (rawHead H ⟨k, hkLt⟩).val then 1 else 0 := by
      funext v
      simp only [inCountPrefix, dite_eq_left hkLt]
      by_cases h : (rawHead H ⟨k, hkLt⟩).val = v
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · have hne : v ≠ (rawHead H ⟨k, hkLt⟩).val := fun he => h he.symm
        rw [ite_eq_right h, ite_eq_right hne]
    change sumNatUpTo (fun v => inCountPrefix H (k + 1) v) H.vertexCount = k + 1
    rw [heq, sumNatUpTo_add, ih hkLe, sumNatUpTo_ite_eq (rawHead H ⟨k, hkLt⟩).isLt]

theorem prefixOut_vertexCount (H : LabelledQuotient) :
    prefixOut H H.vertexCount = H.arcCount := by
  rw [prefixOut_eq_sum]
  exact sum_outCountPrefix H H.arcCount (Nat.le_refl _)

theorem prefixIn_vertexCount (H : LabelledQuotient) :
    prefixIn H H.vertexCount = H.arcCount := by
  rw [prefixIn_eq_sum]
  exact sum_inCountPrefix H H.arcCount (Nat.le_refl _)

end CsrMath

section MkHaltHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem Placed_mkHaltPhase (instrs : List (Instr bits 15))
    (hNonHalt : instrs.all (nonHalt (L := DomL)) = true) :
    Placed (mkHaltPhase (hi := hi) (hw := hw) instrs hNonHalt).code 0 instrs :=
  Placed_toArray_halt

theorem haltAt_mkHaltPhase {input : Input DomL} (instrs : List (Instr bits 15))
    (hNonHalt : instrs.all (nonHalt (L := DomL)) = true) {t : State DomL}
    (hpc : t.pc = instrs.length) :
    step (mkHaltPhase (hi := hi) (hw := hw) instrs hNonHalt).code input t = some (.halted t) := by
  apply step_halt_at
  rw [hpc]
  change ((instrs ++ [Instr.halt]).toArray : Program DomL)[instrs.length]? = some .halt
  rw [Array.getElem?_eq_getElem (by simp)]
  simp

theorem codeSize_mkHaltPhase (instrs : List (Instr bits 15))
    (hNonHalt : instrs.all (nonHalt (L := DomL)) = true) :
    (mkHaltPhase (hi := hi) (hw := hw) instrs hNonHalt).code.size = instrs.length + 1 := by
  change ((instrs ++ [Instr.halt]).toArray : Program DomL).size = instrs.length + 1
  simp

theorem reg_initial (s : State DomL) (r : Fin 15) :
    reg (Phase.initial s) r = reg s r := rfl

theorem data_initial (s : State DomL) :
    (Phase.initial s).data = s.data := rfl

theorem lt_data_size {s : State DomL} {n : Nat} (h : n < workCap) :
    n < s.data.size := by
  rw [s.data_size]; exact h

theorem reg_of_regs_eq {s t : State DomL} (h : t.regs = s.regs) (r : Fin 15) :
    reg t r = reg s r := by
  rcases t with ⟨tr, _, _, _, _⟩
  rcases s with ⟨sr, _, _, _, _⟩
  dsimp only at h
  subst tr
  rfl

theorem outCountPrefix_le (H : LabelledQuotient) (k u : Nat) :
    outCountPrefix H k u ≤ k := by
  induction k with
  | zero => simp [outCountPrefix]
  | succ k ih =>
    simp only [outCountPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hu : (rawOccurrence H ⟨k, hk⟩).1.val = u
      · rw [ite_eq_left hu]; omega
      · rw [ite_eq_right hu]; omega
    · rw [dite_eq_right hk]; omega

theorem inCountPrefix_le (H : LabelledQuotient) (k v : Nat) :
    inCountPrefix H k v ≤ k := by
  induction k with
  | zero => simp [inCountPrefix]
  | succ k ih =>
    simp only [inCountPrefix]
    by_cases hk : k < H.arcCount
    · rw [dite_eq_left hk]
      by_cases hv : (rawHead H ⟨k, hk⟩).val = v
      · rw [ite_eq_left hv]; omega
      · rw [ite_eq_right hv]; omega
    · rw [dite_eq_right hk]; omega

end MkHaltHelpers

section CsrZero

variable {bits : Nat}

def csrZeroLoop1Instrs : List (Instr bits 15) :=
  [ .branchLt reg5 reg4 9 13
  , .add reg6 reg3 reg5
  , .storeData reg6 reg0
  , .add reg5 reg5 reg1
  , .goto 8
  ]

def csrZeroLoop2Instrs : List (Instr bits 15) :=
  [ .branchLt reg5 reg4 19 23
  , .add reg6 reg3 reg5
  , .storeData reg6 reg0
  , .add reg5 reg5 reg1
  , .goto 18
  ]

def csrZeroInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg8 mIdxN (by change 0 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg3 reg8 mIdxInStartBase (by change 10 < 2 ^ bits; omega) ++
  ([.add reg4 reg2 reg1, .mov reg5 reg0] ++
  (csrZeroLoop1Instrs ++
  (metaLoadInstrs reg3 reg8 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  ([.add reg4 reg4 reg2, .mov reg5 reg0] ++
  csrZeroLoop2Instrs)))))

end CsrZero

section CsrZeroPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def csrZeroPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (csrZeroInstrs (bits := bits) h100)
    (by simp [csrZeroInstrs, csrZeroLoop1Instrs, csrZeroLoop2Instrs, metaLoadInstrs, nonHalt])

private theorem csrZeroLoop_spec {code : Program DomL} {input : Input DomL}
    {basePc exitPc : Nat} (hPl : Placed code basePc
      [ .branchLt reg5 reg4 (basePc + 1) exitPc
      , .add reg6 reg3 reg5
      , .storeData reg6 reg0
      , .add reg5 reg5 reg1
      , .goto basePc
      ])
    (hSz : basePc + 4 < code.size) (hExitSz : exitPc < code.size)
    {baseAddr total : Nat} (hEnd : baseAddr + total < workCap)
    (i : Nat) (hiLe : i ≤ total)
    (st : State DomL) (hpc : st.pc = basePc)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hBase : (reg st reg3).val = baseAddr)
    (hTotal : (reg st reg4).val = total)
    (hIdx : (reg st reg5).val = i) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 5 * (total - i) + 1 ∧
      Steps code input k st t ∧ t.pc = exitPc ∧
      (∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → reg t r = reg st r) ∧
      (∀ k', i ≤ k' → k' < total → (t.data[baseAddr + k']?).map Fin.val = some 0) ∧
      (∀ j, (j < baseAddr + i ∨ baseAddr + total ≤ j) → t.data[j]? = st.data[j]?) := by
  suffices hMain : ∀ rem i st, total - i = rem → i ≤ total → st.pc = basePc →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 → (reg st reg3).val = baseAddr →
      (reg st reg4).val = total → (reg st reg5).val = i →
      ∃ k : Nat, ∃ t : State DomL,
        k ≤ 5 * (total - i) + 1 ∧ Steps code input k st t ∧ t.pc = exitPc ∧
        (∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → reg t r = reg st r) ∧
        (∀ k', i ≤ k' → k' < total → (t.data[baseAddr + k']?).map Fin.val = some 0) ∧
        (∀ j, (j < baseAddr + i ∨ baseAddr + total ≤ j) → t.data[j]? = st.data[j]?) by
    exact hMain (total - i) i st rfl hiLe hpc h0 h1 hBase hTotal hIdx
  intro rem
  induction rem with
  | zero =>
    intro i st hrem hiLe hpc h0 h1 hBase hTotal hIdx
    have hiEq : i = total := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg5 reg4 (basePc + 1) exitPc) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hFalse : ¬ ((reg st reg5).val < (reg st reg4).val) := by
      rw [hIdx, hTotal, hiEq]; exact Nat.lt_irrefl _
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
      (by rw [ite_eq_right hFalse]; exact hExitSz)
    rw [ite_eq_right hFalse] at hpc1
    refine ⟨1, s1, by omega, steps_1_of_step hs1, hpc1,
      fun r _ _ => reg_of_regs_eq hreg1 r,
      fun k' hki hkt => by omega,
      fun j _ => by rw [hd1]⟩
  | succ rem ih =>
    intro i st hrem hiLe hpc h0 h1 hBase hTotal hIdx
    have hiLt : i < total := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg5 reg4 (basePc + 1) exitPc) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hTrue : (reg st reg5).val < (reg st reg4).val := by rw [hIdx, hTotal]; exact hiLt
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
      (by rw [ite_eq_left hTrue]; omega)
    rw [ite_eq_left hTrue] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    have hAdd : code[s1.pc]? = some (.add reg6 reg3 reg5) := by
      rw [hpc1]; exact hPl 1 _ rfl
    obtain ⟨s2, hs2, hpc2, h6_2, ho2, hd2⟩ := step_add_at (input := input) hAdd (by rw [hpc1]; omega)
    have hAddr : (reg s2 reg6).val = baseAddr + i := by
      rw [h6_2, add_no_wrap _ _ (by rw [hr1, hr1, hBase, hIdx]; exact Nat.lt_of_lt_of_le (by omega) hw),
        hr1, hr1, hBase, hIdx]
    have hLtMem : (reg s2 reg6).val < s2.data.size := lt_data_size (by rw [hAddr]; omega)
    have hStore : code[s2.pc]? = some (.storeData reg6 reg0) := by
      rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨hs3, hpc3, hreg3⟩ := step_storeData_at (input := input) hStore hLtMem (by rw [hpc2, hpc1]; omega)
    let s3 : State DomL :=
      { s2 with
        data := s2.data.set (reg s2 reg6).val (reg s2 reg0) hLtMem
        pc := s2.pc + 1
        data_size := by simp only [Array.size_set, s2.data_size] }
    have hpc3 : s3.pc = s2.pc + 1 := rfl
    have hZeroS2 : reg s2 reg0 = (0 : Word bits) := by
      ext; rw [ho2 reg0 (by intro h; cases h), hr1 reg0, h0]; rfl
    have hInc : code[s3.pc]? = some (.add reg5 reg5 reg1) := by
      change code[s2.pc + 1]? = some (.add reg5 reg5 reg1)
      rw [hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, hpc4, h5_4, ho4, hd4⟩ := step_add_at (input := input) hInc
      (by dsimp only [s3]; rw [hpc2, hpc1]; omega)
    have hi1 : (reg s4 reg5).val = i + 1 := by
      have hr5 : (reg s3 reg5).val = i := by
        change (reg s2 reg5).val = i
        rw [ho2 reg5 (by intro h; cases h), hr1 reg5, hIdx]
      have hr1_3 : (reg s3 reg1).val = 1 := by
        change (reg s2 reg1).val = 1
        rw [ho2 reg1 (by intro h; cases h), hr1 reg1, h1]
      rw [h5_4, add_no_wrap _ _ (by rw [hr5, hr1_3]; exact Nat.lt_of_lt_of_le (by omega) hw), hr5, hr1_3]
    have hJmp : code[s4.pc]? = some (.goto basePc) := by
      rw [hpc4]; change code[s2.pc + 1 + 1]? = some (.goto basePc)
      rw [hpc2, hpc1]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, hreg5, hd5⟩ := step_goto_at (input := input) hJmp (by omega)
    have hr5' : ∀ r : Fin 15, reg s5 r = reg s4 r := reg_of_regs_eq hreg5
    have h0_5 : (reg s5 reg0).val = 0 := by
      rw [hr5', ho4 reg0 (by intro h; cases h)]; exact congrArg Fin.val hZeroS2
    have h1_5 : (reg s5 reg1).val = 1 := by
      rw [hr5', ho4 reg1 (by intro h; cases h)]; change (reg s2 reg1).val = 1
      rw [ho2 reg1 (by intro h; cases h), hr1 reg1, h1]
    have hBase5 : (reg s5 reg3).val = baseAddr := by
      rw [hr5', ho4 reg3 (by intro h; cases h)]; change (reg s2 reg3).val = baseAddr
      rw [ho2 reg3 (by intro h; cases h), hr1 reg3, hBase]
    have hTot5 : (reg s5 reg4).val = total := by
      rw [hr5', ho4 reg4 (by intro h; cases h)]; change (reg s2 reg4).val = total
      rw [ho2 reg4 (by intro h; cases h), hr1 reg4, hTotal]
    have hIdx5 : (reg s5 reg5).val = i + 1 := by rw [hr5', hi1]
    obtain ⟨kRest, t, hkRest, hStepsRest, hpcT, hKeepT, hArrT, hFrT⟩ :=
      ih (i + 1) s5 (by omega) (by omega) hpc5 h0_5 h1_5 hBase5 hTot5 hIdx5
    have hStep5 : Steps code input 5 st s5 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
    refine ⟨5 + kRest, t, by omega, hStep5.append hStepsRest, hpcT, ?_, ?_, ?_⟩
    · intro r hr5 hr6
      rw [hKeepT r hr5 hr6, hr5', ho4 r hr5]
      change reg s2 r = reg st r
      rw [ho2 r hr6, hr1 r]
    · intro k' hki hkt
      by_cases hkEq : k' = i
      · subst hkEq
        rw [hFrT (baseAddr + k') (Or.inl (by omega))]
        rw [hd5, hd4]; dsimp only [s3]
        have hSet : (s2.data.set (reg s2 reg6).val (reg s2 reg0) hLtMem)[baseAddr + k']? =
            some (reg s2 reg0) := by
          rw [← hAddr]; simp [hLtMem]
        rw [hSet, hZeroS2]; rfl
      · exact hArrT k' (by omega) hkt
    · intro j hj
      rw [hFrT j (by
        rcases hj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h)]
      rw [hd5, hd4]
      change (s2.data.set (reg s2 reg6).val (reg s2 reg0) hLtMem)[j]? = st.data[j]?
      rw [Array.getElem?_set_ne hLtMem (by
        rw [hAddr]
        rcases hj with h | h
        · omega
        · omega), hd2, hd1]

theorem run_csrZero {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (_hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 18 * H.vertexCount + 25 ∧
      run (csrZeroPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ i ≤ H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some 0) ∧
      (∀ i < 2 * H.vertexCount + 1,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + i]?).map Fin.val = some 0) ∧
      (∀ j, j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤ j →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  have hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits := by omega
  have hInStartEnd : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) < workCap := by
    omega
  have hTempEnd : tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) < workCap := by
    omega
  let ph := csrZeroPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (csrZeroInstrs (bits := bits) h100).length = 23 := by
    simp [csrZeroInstrs, csrZeroLoop1Instrs, csrZeroLoop2Instrs, metaLoadInstrs]
  have hCodeSize : ph.code.size = 24 := by
    dsimp [ph, csrZeroPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (csrZeroInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlN := Placed_append_left (by unfold csrZeroInstrs at hPlFull; exact hPlFull)
  have hPlT1 := Placed_append_right (by unfold csrZeroInstrs at hPlFull; exact hPlFull)
  rw [hLml] at hPlT1
  have hPlInStart := Placed_append_left hPlT1
  have hPlT2 := Placed_append_right hPlT1
  rw [hLml] at hPlT2
  have hPlImm1 := Placed_append_left hPlT2
  have hPlT3 := Placed_append_right hPlT2
  rw [show ([Instr.add reg4 reg2 reg1, Instr.mov reg5 reg0] : List (Instr bits 15)).length = 2 by rfl] at hPlT3
  have hPlLoop1 := Placed_append_left hPlT3
  have hPlT4 := Placed_append_right hPlT3
  rw [show (csrZeroLoop1Instrs : List (Instr bits 15)).length = 5 by rfl] at hPlT4
  have hPlTemp := Placed_append_left hPlT4
  have hPlT5 := Placed_append_right hPlT4
  rw [hLml] at hPlT5
  have hPlImm2 := Placed_append_left hPlT5
  have hPlLoop2 := Placed_append_right hPlT5
  rw [show ([Instr.add reg4 reg4 reg2, Instr.mov reg5 reg0] : List (Instr bits 15)).length = 2 by rfl] at hPlLoop2
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlN (by omega)
    rfl hMeta.rMeta_eq (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) hMeta.meta_n
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlInStart (by omega)
    hpc1 hMeta1 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd1]; exact hMeta.meta_inStartBase)
  have h0_2 : (reg s2 reg0).val = 0 := by
    rw [ho2 reg0 (by intro h; cases h) (by intro h; cases h),
      ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have h2_2 : (reg s2 reg2).val = H.vertexCount := by
    rw [ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta1
  have hAdd4 : ph.code[s2.pc]? = some (.add reg4 reg2 reg1) := by
    rw [hpc2]; exact hPlImm1 0 _ rfl
  obtain ⟨s3, hs3, hpc3, h4_3, ho3, hd3⟩ := step_add_at (input := input) hAdd4 (by rw [hpc2]; omega)
  have h4Val : (reg s3 reg4).val = H.vertexCount + 1 := by
    rw [h4_3, add_no_wrap _ _ (by rw [h2_2, h1_2]; exact Nat.lt_of_lt_of_le (by omega) hw), h2_2, h1_2]
  have hMov5 : ph.code[s3.pc]? = some (.mov reg5 reg0) := by
    rw [hpc3, hpc2]; exact hPlImm1 1 _ rfl
  obtain ⟨s4, hs4, hpc4, h5_4, ho4, hd4⟩ := step_mov_at (input := input) hMov5 (by rw [hpc3, hpc2]; omega)
  have h5Val : (reg s4 reg5).val = 0 := by
    rw [h5_4, ho3 reg0 (by intro h; cases h), h0_2]
  have hPlLoop1' : Placed ph.code 8
      [ .branchLt reg5 reg4 (8 + 1) 13, .add reg6 reg3 reg5
      , .storeData reg6 reg0, .add reg5 reg5 reg1, .goto 8 ] := by
    intro i ins hiEq; simpa [csrZeroLoop1Instrs] using hPlLoop1 i ins hiEq
  obtain ⟨k1, s5, hk1, hSteps1, hpc5, hKeep5, hInStart5, hFr5⟩ :=
    csrZeroLoop_spec hPlLoop1' (by omega) (by omega) hInStartEnd 0 (Nat.zero_le _) s4
      (by omega)
      (by rw [ho4 reg0 (by intro h; cases h), ho3 reg0 (by intro h; cases h), h0_2])
      (by rw [ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), h1_2])
      (by rw [ho4 reg3 (by intro h; cases h), ho3 reg3 (by intro h; cases h), h3_2])
      (by rw [ho4 reg4 (by intro h; cases h), h4Val])
      h5Val
  have h0_5 : (reg s5 reg0).val = 0 := by
    rw [hKeep5 reg0 (by intro h; cases h) (by intro h; cases h),
      ho4 reg0 (by intro h; cases h), ho3 reg0 (by intro h; cases h), h0_2]
  have h1_5 : (reg s5 reg1).val = 1 := by
    rw [hKeep5 reg1 (by intro h; cases h) (by intro h; cases h),
      ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), h1_2]
  have h2_5 : (reg s5 reg2).val = H.vertexCount := by
    rw [hKeep5 reg2 (by intro h; cases h) (by intro h; cases h),
      ho4 reg2 (by intro h; cases h), ho3 reg2 (by intro h; cases h), h2_2]
  have h4_5 : (reg s5 reg4).val = H.vertexCount + 1 := by
    rw [hKeep5 reg4 (by intro h; cases h) (by intro h; cases h),
      ho4 reg4 (by intro h; cases h), h4Val]
  have hMeta5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [hKeep5 rMeta (by intro h; cases h) (by intro h; cases h),
      ho4 rMeta (by intro h; cases h), ho3 rMeta (by intro h; cases h), hMeta2]
  obtain ⟨s6, hs6, hpc6, hd6, h3_6, ho6⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega)
    hpc5 hMeta5 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by
      rw [hFr5 _ (Or.inr (by omega)), hd4, hd3, hd2, hd1]
      exact hMeta.meta_tempBase)
  have h0_6 : (reg s6 reg0).val = 0 := by
    rw [ho6 reg0 (by intro h; cases h) (by intro h; cases h), h0_5]
  have h1_6 : (reg s6 reg1).val = 1 := by
    rw [ho6 reg1 (by intro h; cases h) (by intro h; cases h), h1_5]
  have h2_6 : (reg s6 reg2).val = H.vertexCount := by
    rw [ho6 reg2 (by intro h; cases h) (by intro h; cases h), h2_5]
  have h4_6 : (reg s6 reg4).val = H.vertexCount + 1 := by
    rw [ho6 reg4 (by intro h; cases h) (by intro h; cases h), h4_5]
  have hMeta6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho6 rMeta (by intro h; cases h) (by intro h; cases h), hMeta5]
  have hAdd4_2 : ph.code[s6.pc]? = some (.add reg4 reg4 reg2) := by
    rw [hpc6]; exact hPlImm2 0 _ rfl
  obtain ⟨s7, hs7, hpc7, h4_7, ho7, hd7⟩ := step_add_at (input := input) hAdd4_2 (by rw [hpc6]; omega)
  have h4Val2 : (reg s7 reg4).val = 2 * H.vertexCount + 1 := by
    rw [h4_7, add_no_wrap _ _ (by rw [h4_6, h2_6]; exact Nat.lt_of_lt_of_le (by omega) hw), h4_6, h2_6]
    omega
  have hMov5_2 : ph.code[s7.pc]? = some (.mov reg5 reg0) := by
    rw [hpc7, hpc6]; exact hPlImm2 1 _ rfl
  obtain ⟨s8, hs8, hpc8, h5_8, ho8, hd8⟩ := step_mov_at (input := input) hMov5_2 (by rw [hpc7, hpc6]; omega)
  have h5Val2 : (reg s8 reg5).val = 0 := by
    rw [h5_8, ho7 reg0 (by intro h; cases h), h0_6]
  have hPlLoop2' : Placed ph.code 18
      [ .branchLt reg5 reg4 (18 + 1) 23, .add reg6 reg3 reg5
      , .storeData reg6 reg0, .add reg5 reg5 reg1, .goto 18 ] := by
    intro i ins hiEq; simpa [csrZeroLoop2Instrs] using hPlLoop2 i ins hiEq
  obtain ⟨k2, t, hk2, hSteps2, hpcT, hKeepT, hTempT, hFrT⟩ :=
    csrZeroLoop_spec hPlLoop2' (by omega) (by omega) hTempEnd 0 (Nat.zero_le _) s8
      (by omega)
      (by rw [ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h), h0_6])
      (by rw [ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h), h1_6])
      (by rw [ho8 reg3 (by intro h; cases h), ho7 reg3 (by intro h; cases h), h3_6])
      (by rw [ho8 reg4 (by intro h; cases h), h4Val2])
      h5Val2
  have hAllSteps : Steps ph.code input ((8 + k1) + (5 + k2)) (Phase.initial s0) t := by
    have hSetup1 : Steps ph.code input 8 (Phase.initial s0) s4 :=
      hs1.append (hs2.append (Steps.cons hs3 (steps_1_of_step hs4)))
    have hSetup2 : Steps ph.code input 5 s5 s8 :=
      hs6.append (Steps.cons hs7 (steps_1_of_step hs8))
    exact (hSetup1.append hSteps1).append (hSetup2.append hSteps2)
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrZeroInstrs (bits := bits) h100) _
      (by rw [hpcT, hCodeLen]) (input := input)
  refine ⟨(8 + k1) + (5 + k2) + 1, t, by have := large; omega, hAllSteps.halts hHalt, ?_, ?_,
    fun i hi => hTempT i (Nat.zero_le _) hi, ?_⟩
  · apply hMeta.preserve
    · rw [hKeepT rMeta (by intro h; cases h) (by intro h; cases h),
        ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h), hMeta6]
    · rw [hKeepT reg0 (by intro h; cases h) (by intro h; cases h),
        ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h), h0_6]
    · rw [hKeepT reg1 (by intro h; cases h) (by intro h; cases h),
        ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h), h1_6]
    · intro i hi22
      have hFrMeta1 : s5.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + i]? =
          s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + i]? := by
        rw [hFr5 _ (Or.inr (by omega)), hd4, hd3, hd2, hd1]; rfl
      have hFrMeta2 : t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + i]? =
          s5.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + i]? := by
        rw [hFrT _ (Or.inl (by omega)), hd8, hd7, hd6]
      rw [hFrMeta2, hFrMeta1]
  · intro i hiLe
    rw [hFrT _ (Or.inl (by omega)), hd8, hd7, hd6]
    exact hInStart5 i (by omega) (by omega)
  · intro j hj
    have hFr2 : t.data[j]? = s5.data[j]? := by
      rw [hFrT j (by
        rcases hj with h | ⟨_, h2⟩ | h
        · exact Or.inl (by omega)
        · exact Or.inl h2
        · exact Or.inr h), hd8, hd7, hd6]
    have hFr1 : s5.data[j]? = s0.data[j]? := by
      rw [hFr5 j (by
        rcases hj with h | ⟨h1, _⟩ | h
        · exact Or.inl h
        · exact Or.inr h1
        · exact Or.inr (by omega)),
        hd4, hd3, hd2, hd1]; rfl
    rw [hFr2, hFr1]

end CsrZeroPhase


end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
