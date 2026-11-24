module

public import PaperB.RamQuotientEmitter
public import PaperB.RamOracleQuery
public import PaperB.RamForestRawBuild
public import PaperB.ExitDenseLookupTransport
public import PaperB.KahnInverse
public import PaperB.DenseQuotientRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Bridge from the Word-RAM static tree representation (`StaticTreeSlice`) and
topological vertex order (`IsTopologicalList`) to the abstract online oracle
structures (`OriginalReader`, `DenseQuotientRows.Layout`,
`OriginalEntryInverse.Index`, `StaticHeaderSpec`, `StaticChildLookup.Valid`)
and transport of `IsFlat` / `IsAcyclic` / `SealedOwnerRecord` between
`S.ramQuotient d` and `ActualOnlineOracle.denseQuotient`.
-/

namespace PaperB.RamStaticReaderBridge

open PaperB
open PaperB.Machine (Word)
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestHead
open PaperB.EX16Assembly
open PaperB.PackedStaticLayout
open PaperB.StaticHeadSweep
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.EX44.ActualOnlineOracle
open PaperB.RamQuotientEmitter
open PaperB.OracleSealedIndexLayout
open PaperB.RamOracleQuery
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.ForestSlimIndex
open PaperB.RetainedProperLoss

/-! ### 1. Matching `StaticTreeSlice` against `PackedStaticLayout.build` -/

/-- Agreement between the materialized arrays of a `StaticTreeSlice` and the
deterministic static-tree layout computed from `S.packedInput`. -/
structure MatchesPackedLayout
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) : Prop where
  head_eq : ∀ v : Fin dense.length,
    S.head v = (StaticHeadSweep.tables (PackedStaticLayout.build S.packedInput).packed).head v
  heavy_eq : ∀ u : Fin dense.length,
    S.heavy u =
      match (PackedStaticLayout.build S.packedInput).packed.heavy.read u with
      | none => dense.length
      | some h => h.val
  entry_eq : ∀ v : Fin dense.length,
    S.entry v = (PackedStaticLayout.build S.packedInput).endpoints.entry.read v
  stop_eq : ∀ v : Fin dense.length,
    S.stop v = (PackedStaticLayout.build S.packedInput).endpoints.stop.read v
  childSlice_eq : ∀ d : Fin dense.length,
    S.childSlice d = (PackedStaticLayout.build S.packedInput).buckets.get d

/-! ### 2. Constructing `OriginalReader`, `DenseQuotientRows.Layout`, and `OriginalEntryInverse.Index` -/

section SliceBridge

private theorem idxOf_getElem_of_nodup {α : Type} [DecidableEq α]
    {xs : List α} (hnd : xs.Nodup) (i : Nat) (hi : i < xs.length) :
    xs.idxOf (xs[i]'hi) = i := by
  have hMem : xs[i]'hi ∈ xs := List.getElem_mem hi
  have hLt : xs.idxOf (xs[i]'hi) < xs.length := List.idxOf_lt_length_of_mem hMem
  have hEq : xs[xs.idxOf (xs[i]'hi)]'hLt = xs[i]'hi := List.getElem_idxOf hLt
  have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
  by_cases hne : xs.idxOf (xs[i]'hi) = i
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with h1 | h2
    · exact False.elim (hPw _ _ hLt hi h1 hEq)
    · exact False.elim (hPw _ _ hi hLt h2 hEq.symm)

private def denseFind {g : Digraph} (dense : List (Fin g.vertexCount))
    (v : Fin g.vertexCount) : Option (Fin dense.length) :=
  let i := dense.idxOf v
  if hi : i < dense.length then some ⟨i, hi⟩ else none

private def denseColumn {g : Digraph} (dense : List (Fin g.vertexCount)) :
    EX15.WholeScan.PackedInput.OriginalIds.Column g dense.length where
  data := dense.toArray
  size_eq := by simp

private theorem denseColumn_read {g : Digraph} (dense : List (Fin g.vertexCount))
    (k : Fin dense.length) :
    (denseColumn dense).read k = dense[k.val]'k.isLt := by
  simp [EX15.WholeScan.PackedInput.OriginalIds.Column.read, denseColumn]

private def idsOfSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    EX15.WholeScan.PackedInput.OriginalIds.Reader g r dense.length where
  find := denseFind dense
  originals := denseColumn dense
  miss_iff v := by
    unfold denseFind
    constructor
    · intro hNone hReach
      have hMem := S.mem_reach v hReach
      have hLt : dense.idxOf v < dense.length := List.idxOf_lt_length_of_mem hMem
      rw [dite_eq_left hLt] at hNone
      cases hNone
    · intro hNotReach
      have hNotMem : v ∉ dense := by
        intro hMem
        obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hMem
        exact hNotReach (hEq ▸ S.reach_mem i hi)
      have hGe : ¬ dense.idxOf v < dense.length := by
        intro hLt
        exact hNotMem (List.mem_of_getElem (List.getElem_idxOf hLt))
      exact dite_eq_right hGe
  original_of_slot v k hFind := by
    unfold denseFind at hFind
    by_cases hLt : dense.idxOf v < dense.length
    · rw [dite_eq_left hLt, Option.some.injEq] at hFind
      rw [denseColumn_read, ← hFind]
      exact List.getElem_idxOf hLt
    · rw [dite_eq_right hLt] at hFind
      cases hFind
  slot_of_original k := by
    rw [denseColumn_read]
    unfold denseFind
    have hIdx : dense.idxOf (dense[k.val]'k.isLt) = k.val :=
      idxOf_getElem_of_nodup S.nodup k.val k.isLt
    have hLt : dense.idxOf (dense[k.val]'k.isLt) < dense.length := by
      rw [hIdx]; exact k.isLt
    rw [dite_eq_left hLt]
    exact congrArg some (Fin.ext hIdx)

private theorem idsOfSlice_originals_read {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (k : Fin dense.length) :
    (idsOfSlice S).originals.read k = dense[k.val]'k.isLt :=
  denseColumn_read dense k

private theorem packedInput_parent_read {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (k : Fin dense.length) :
    S.packedInput.parent.read k = S.domParent k := by
  change (Array.ofFn S.domParent)[k.val]'(by simp) = S.domParent k
  simp [Array.getElem_ofFn]

private theorem packedInput_depth_read {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (k : Fin dense.length) :
    S.packedInput.depth.read k = S.domDepth k := by
  change (Array.ofFn S.domDepth)[k.val]'(by simp) = S.domDepth k
  simp [Array.getElem_ofFn]

private theorem parentSpecOfSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    g.ParentSpec r (fun v =>
      match (idsOfSlice S).find v with
      | none => v
      | some k => (idsOfSlice S).originals.read (S.packedInput.parent.read k)) := by
  refine ⟨?_, ?_⟩
  · have hr0 : (idsOfSlice S).find r = some ⟨0, S.qPos⟩ := by
      have hRead0 : (idsOfSlice S).originals.read ⟨0, S.qPos⟩ = r := by
        rw [idsOfSlice_originals_read]; exact S.head_eq
      simpa [hRead0] using (idsOfSlice S).slot_of_original ⟨0, S.qPos⟩
    rw [hr0]
    dsimp only
    rw [packedInput_parent_read, idsOfSlice_originals_read]
    have hRoot : (S.domParent ⟨0, S.qPos⟩).val = 0 := S.domParent_root
    simpa [hRoot] using S.head_eq
  · intro v hvNe
    by_cases hReach : g.InitiallyReachable r v
    · left
      refine ⟨hReach, ?_⟩
      let k : Fin dense.length :=
        ⟨dense.idxOf v, List.idxOf_lt_length_of_mem (S.mem_reach v hReach)⟩
      have hkFind : (idsOfSlice S).find v = some k := by
        change denseFind dense v = some k
        unfold denseFind
        exact dite_eq_left (List.idxOf_lt_length_of_mem (S.mem_reach v hReach))
      have hkOrig : dense[k.val]'k.isLt = v := by
        have hRead := (idsOfSlice S).original_of_slot v k hkFind
        rw [idsOfSlice_originals_read] at hRead
        exact hRead
      have hkPos : 0 < k.val := by
        apply Nat.pos_of_ne_zero
        intro hk0
        apply hvNe
        have hEq : dense[k.val]'k.isLt = dense[0]'S.qPos := by congr 1
        rw [hkOrig, S.head_eq] at hEq
        exact hEq
      rw [hkFind]
      dsimp only
      rw [packedInput_parent_read, idsOfSlice_originals_read]
      have hSpec := S.domParent_spec k hkPos
      rwa [hkOrig] at hSpec
    · right
      refine ⟨hReach, ?_⟩
      rw [((idsOfSlice S).miss_iff v).mpr hReach]

private def mkOriginalReaderWithIds {g : Digraph} {r : Fin g.vertexCount} {count : Nat}
    (x : PackedStaticLayout.Input count) (reader : StaticTreeReader.Reader x)
    (slot : (v : Fin g.vertexCount) → g.InitiallyReachable r v → Fin count)
    (ids : EX15.WholeScan.PackedInput.OriginalIds.Reader g r count)
    (find_slot : ∀ (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v), ids.find v = some (slot v hv))
    (parentSpec : g.ParentSpec r (fun v =>
      match ids.find v with | none => v | some k => ids.originals.read (x.parent.read k)))
    (dom_iff : ∀ (a v : Fin g.vertexCount) (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v),
      g.Dominates r a v ↔
        reader.entry (slot a ha) ≤ reader.entry (slot v hv) ∧
        reader.entry (slot v hv) < reader.stop (slot a ha)) :
    OriginalReader g r := by
  refine OriginalReader.mk count x reader slot ids find_slot ?_ dom_iff
  exact parentSpec

private theorem parentSpec_congr {g : Digraph} {r : Fin g.vertexCount}
    {p₁ p₂ : Fin g.vertexCount → Fin g.vertexCount}
    (h : ∀ v, p₁ v = p₂ v) (hp : g.ParentSpec r p₁) : g.ParentSpec r p₂ :=
  (funext h) ▸ hp

private def originalReaderOfSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hPack : MatchesPackedLayout S) :
    OriginalReader g r :=
  let slotFn : (v : Fin g.vertexCount) → g.InitiallyReachable r v → Fin dense.length :=
    fun v hv => ⟨dense.idxOf v, List.idxOf_lt_length_of_mem (S.mem_reach v hv)⟩
  let rdr := StaticTreeReader.build S.packedInput S.packedInput_ok
  mkOriginalReaderWithIds S.packedInput rdr slotFn (idsOfSlice S)
    (fun v hv => by
      change denseFind dense v = some (slotFn v hv)
      unfold denseFind
      exact dite_eq_left (List.idxOf_lt_length_of_mem (S.mem_reach v hv)))
    (parentSpec_congr (fun v => by cases (idsOfSlice S).find v <;> rfl) (parentSpecOfSlice S))
    (fun a v ha hv => by
      let sa := slotFn a ha
      let sv := slotFn v hv
      have haOrig : dense[sa.val]'sa.isLt = a := List.getElem_idxOf sa.isLt
      have hvOrig : dense[sv.val]'sv.isLt = v := List.getElem_idxOf sv.isLt
      have hEntA : rdr.entry sa = S.entry sa := by
        rw [StaticTreeReader.Reader.entry_exact, ← PackedStaticLayout.entry_exact _ S.packedInput_ok,
          ← hPack.entry_eq sa]
      have hEntV : rdr.entry sv = S.entry sv := by
        rw [StaticTreeReader.Reader.entry_exact, ← PackedStaticLayout.entry_exact _ S.packedInput_ok,
          ← hPack.entry_eq sv]
      have hStopA : rdr.stop sa = S.stop sa := by
        rw [StaticTreeReader.Reader.stop_exact, ← PackedStaticLayout.stop_exact _ S.packedInput_ok,
          ← hPack.stop_eq sa]
      rw [hEntA, hEntV, hStopA]
      simpa [haOrig, hvOrig] using S.dominates_iff_interval sa sv)

@[simp] private theorem originalReaderOfSlice_count {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hPack : MatchesPackedLayout S) :
    (originalReaderOfSlice S hPack).count = dense.length := rfl

private theorem originalReader_entry_eq {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hPack : MatchesPackedLayout S)
    (v : Fin dense.length) :
    (originalReaderOfSlice S hPack).reader.entry v = S.entry v := by
  change (StaticTreeReader.build S.packedInput S.packedInput_ok).entry v = S.entry v
  rw [StaticTreeReader.Reader.entry_exact, ← PackedStaticLayout.entry_exact _ S.packedInput_ok,
    ← hPack.entry_eq v]

private theorem originalReader_stop_eq {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hPack : MatchesPackedLayout S)
    (v : Fin dense.length) :
    (originalReaderOfSlice S hPack).reader.stop v = S.stop v := by
  change (StaticTreeReader.build S.packedInput S.packedInput_ok).stop v = S.stop v
  rw [StaticTreeReader.Reader.stop_exact, ← PackedStaticLayout.stop_exact _ S.packedInput_ok,
    ← hPack.stop_eq v]

private def bucketsOfSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    ForestLayout.ChildLists dense.length where
  rows := Array.ofFn S.childSlice
  rows_size := by simp

private theorem bucketsOfSlice_get {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (bucketsOfSlice S).get d = S.childSlice d := by
  simp [ForestLayout.ChildLists.get, bucketsOfSlice]

private def invOfSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hPack : MatchesPackedLayout S) :
    OriginalEntryInverse.Index (originalReaderOfSlice S hPack) where
  slots := ⟨Array.ofFn S.denseOfEntry, by change (Array.ofFn S.denseOfEntry).size = dense.length; simp⟩
  read_rank x := by
    have hxEnt : (originalReaderOfSlice S hPack).reader.entry x = S.entry x :=
      originalReader_entry_eq S hPack x
    have hxLt : S.entry x < dense.length := Nat.lt_of_lt_of_le (S.entry_lt_stop x).1 (S.entry_lt_stop x).2
    have hRkVal : (OriginalEntryInverse.entryRank (originalReaderOfSlice S hPack) x).val =
        S.entry x := by
      rw [OriginalEntryInverse.entryRank_val, hxEnt]
    change (Array.ofFn S.denseOfEntry)[(OriginalEntryInverse.entryRank (originalReaderOfSlice S hPack) x).val]'(by
      simp [hRkVal]; exact hxLt) = x
    rw [Array.getElem_ofFn]
    have hCast : (⟨(OriginalEntryInverse.entryRank (originalReaderOfSlice S hPack) x).val,
        by rw [hRkVal]; exact hxLt⟩ : Fin dense.length) = ⟨S.entry x, hxLt⟩ :=
      Fin.ext hRkVal
    rw [hCast]
    exact S.denseOfEntry_entry x hxLt

/-- Complete bridge bundle constructed directly from `(order, S)` for any
`S : StaticTreeSlice mem treeBase g r dense` matching `PackedStaticLayout.build S.packedInput`. -/
structure StaticReaderBridge {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    (g : Digraph) (r : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (hLen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order)
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice mem treeBase g r dense) where
  rank : Fin g.vertexCount → Nat
  progress : ∀ i j, g.HasArc i j → rank i < rank j
  injRank : ∀ ⦃i j⦄, rank i = rank j → i = j
  q : OriginalReader g r
  originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count))
  hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1
  buckets : ChildLists q.count
  rows : DenseQuotientRows.Layout buckets
  childOK : ∀ d c : Fin q.count, c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d
  inv : OriginalEntryInverse.Index q
  count_eq : q.count = dense.length
  root_eq : q.input.root.val = 0
  root_size_le : q.reader.tables.size q.reader.tables.root ≤ q.count
  buckets_eq : ∀ d : Fin dense.length,
    buckets.get (Fin.cast count_eq.symm d) = (S.childSlice d).map (Fin.cast count_eq.symm)
  matchesReader : S.MatchesReader q
  ranges_ids : ∀ d : Fin q.count,
    (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d
  ranges_valid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d)
  ranges_size_eq : ∀ d : Fin dense.length,
    (q.reader.ranges.read (Fin.cast count_eq.symm d)).size =
      S.childStart (d.val + 1) - S.childStart d.val
  ranges_at_eq : ∀ (d : Fin dense.length) (j : Nat)
    (hj : j < (q.reader.ranges.read (Fin.cast count_eq.symm d)).size),
    let pos := S.childStart d.val + j
    let ch := (q.reader.ranges.read (Fin.cast count_eq.symm d))[j]'hj
    ∃ hp : pos < dense.length - 1,
      ch.id = Fin.cast count_eq.symm (S.childIds ⟨pos, hp⟩) ∧
      ch.entry = S.entry (S.childIds ⟨pos, hp⟩) ∧
      ch.stop = S.stop (S.childIds ⟨pos, hp⟩)
  head_eq : ∀ d : Fin dense.length,
    (q.reader.tables.head (Fin.cast count_eq.symm d)).val = (S.head d).val
  domParent_eq : ∀ d : Fin dense.length,
    (q.reader.tables.parent (Fin.cast count_eq.symm d)).val = (S.domParent d).val
  domDepth_eq : ∀ d : Fin dense.length,
    q.reader.tables.depth (Fin.cast count_eq.symm d) = S.domDepth d
  entry_eq : ∀ d : Fin dense.length,
    q.reader.entry (Fin.cast count_eq.symm d) = S.entry d
  stop_eq : ∀ d : Fin dense.length,
    q.reader.stop (Fin.cast count_eq.symm d) = S.stop d
  inv_eq_denseOfEntry : ∀ k : Fin dense.length,
    (inv.slots.read (Fin.cast count_eq.symm k)).val = (S.denseOfEntry k).val

/-- Construct `StaticReaderBridge` directly from `(order, S)` when `S` matches
`PackedStaticLayout.build S.packedInput`. -/
def StaticReaderBridge.ofSlice {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    (g : Digraph) (r : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (hLen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order)
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice mem treeBase g r dense)
    (hPack : MatchesPackedLayout S) :
    StaticReaderBridge g r order hLen hTopo S :=
  let xs := order.toArray
  have hxs : xs.size = g.vertexCount := by simpa [xs] using hLen
  let rank : Fin g.vertexCount → Nat := fun v => (KahnInverse.rank xs hxs v).val
  have progress : ∀ i j, g.HasArc i j → rank i < rank j :=
    fun i j hij => KahnInverse.rank_arc g xs hxs hTopo hij
  have injRank : ∀ ⦃i j⦄, rank i = rank j → i = j :=
    fun _ _ h => KahnInverse.rank_injective g xs hxs hTopo (Fin.ext h)
  let q := originalReaderOfSlice S hPack
  let originalRows := (StaticOriginalSiblingEmitter.emitAll q).1
  let buckets : ChildLists dense.length := bucketsOfSlice S
  have hBktChildren : ∀ u : Fin dense.length,
      buckets.get u = bucketChildren S.packedInput.root S.packedInput.parent.read u := by
    intro u
    change (bucketsOfSlice S).get u = _
    rw [bucketsOfSlice_get, hPack.childSlice_eq u, PackedStaticLayout.bucket_read]
  let rows : DenseQuotientRows.Layout buckets :=
    DenseQuotientRows.ofBuckets S.packedInput.root S.packedInput.parent.read buckets hBktChildren
  have childOK : ∀ d c : Fin dense.length,
      c ∈ buckets.get d ↔ c ≠ S.packedInput.root ∧ S.packedInput.parent.read c = d := by
    intro d c
    rw [hBktChildren d, mem_bucketChildren_iff]
  let inv := invOfSlice S hPack
  have hMatch : S.MatchesReader q :=
    { count_eq := rfl
      originals_eq := fun i => by
        change (idsOfSlice S).originals.read i = dense[i.val]'i.isLt
        exact idsOfSlice_originals_read S i
      root_eq := rfl
      parent_eq := fun i => by
        change (S.packedInput.parent.read i).val = (S.domParent i).val
        rw [packedInput_parent_read]
      entry_eq := fun i => originalReader_entry_eq S hPack i
      stop_eq := fun i => originalReader_stop_eq S hPack i }
  have hRootSz : q.reader.tables.size q.reader.tables.root ≤ q.count := by
    have hTbl : q.reader.tables =
        StaticHeadSweep.tables (PackedStaticLayout.build S.packedInput).packed := by
      change (StaticTreeReader.build S.packedInput S.packedInput_ok).tables = _
      rw [(StaticTreeReader.build S.packedInput S.packedInput_ok).tables_exact,
        (StaticTreeReader.build S.packedInput S.packedInput_ok).layout_exact]
    rw [hTbl]
    change (PackedStaticLayout.build S.packedInput).packed.size.read
        (PackedStaticLayout.build S.packedInput).packed.root ≤ dense.length
    rw [PackedStaticLayout.size_read]
    have hStop := S.entry_lt_stop (PackedStaticLayout.build S.packedInput).packed.root
    have hStopLe : (PackedStaticLayout.build S.packedInput).endpoints.stop.read
        (PackedStaticLayout.build S.packedInput).packed.root ≤ dense.length := by
      rw [← hPack.stop_eq]; exact hStop.2
    omega
  have hRangesEq : ∀ d : Fin dense.length,
      (StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d =
        ExactOrderedChildIntervals.packList
          ((PackedStaticLayout.build S.packedInput).buckets.get d)
          (PackedStaticLayout.build S.packedInput).endpoints.entry.read
          (PackedStaticLayout.build S.packedInput).endpoints.stop.read := by
    intro d
    let gr := StaticGroupedTreeReader.build S.packedInput S.packedInput_ok
    have hGrp : gr = StaticTreeReader.build S.packedInput S.packedInput_ok :=
      StaticGroupedTreeReader.build_eq S.packedInput S.packedInput_ok
    have hFin := (StaticGroupedTreeReader.finish_rows S.packedInput S.packedInput_ok).2.2.2 d
    have hLayEq : gr.layout = PackedStaticLayout.build S.packedInput := by
      rw [hGrp]
      exact (StaticTreeReader.build S.packedInput S.packedInput_ok).layout_exact
    have hBkt : gr.layout.buckets = (PackedStaticLayout.build S.packedInput).buckets :=
      congrArg Built.buckets hLayEq
    have hEnt : ∀ c : Fin dense.length,
        gr.layout.endpoints.entry.data[c.val]'(by rw [gr.layout.endpoints.entry.len]; exact c.isLt) =
        (PackedStaticLayout.build S.packedInput).endpoints.entry.read c := by
      intro c
      change gr.layout.endpoints.entry.read c = _
      rw [hLayEq]
    have hStop : ∀ c : Fin dense.length,
        gr.layout.endpoints.stop.data[c.val]'(by rw [gr.layout.endpoints.stop.len]; exact c.isLt) =
        (PackedStaticLayout.build S.packedInput).endpoints.stop.read c := by
      intro c
      change gr.layout.endpoints.stop.read c = _
      rw [hLayEq]
    rw [← hGrp, hFin.2.2]
    unfold ExactOrderedChildIntervals.fromCompleted
    rw [hBkt]
    congr 1
    · funext c; exact hEnt c
    · funext c; exact hStop c
  have hRangesIds : ∀ d : Fin dense.length,
      ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d).toList.map
        (fun c => c.id) = buckets.get d := by
    intro d
    rw [hRangesEq d, ExactOrderedChildIntervals.packList_ids, PackedStaticLayout.bucket_read]
    exact (hBktChildren d).symm
  have hRangesValid : ∀ d : Fin dense.length,
      StaticChildLookup.Valid ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d) := by
    intro d
    rw [hRangesEq d, PackedStaticLayout.bucket_read]
    have hEnt : ∀ v : Fin dense.length,
        (PackedStaticLayout.build S.packedInput).endpoints.entry.read v =
        LabelledQuotient.entry S.packedInput.root S.packedInput.parent.read S.packedInput.depth.read v :=
      fun v => PackedStaticLayout.entry_exact S.packedInput S.packedInput_ok v
    have hOut : ∀ v : Fin dense.length,
        (PackedStaticLayout.build S.packedInput).endpoints.stop.read v =
        LabelledQuotient.entry S.packedInput.root S.packedInput.parent.read S.packedInput.depth.read v +
          (LabelledQuotient.dfsSubtree S.packedInput.root S.packedInput.parent.read
            S.packedInput.depth.read v).length :=
      fun v => PackedStaticLayout.stop_exact S.packedInput S.packedInput_ok v
    exact (ExactOrderedChildIntervals.bucket_correct S.packedInput_ok d _ _ hEnt hOut).valid
  have hRangesSize : ∀ d : Fin dense.length,
      ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d).size =
        S.childStart (d.val + 1) - S.childStart d.val := by
    intro d
    have hMapLen : ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d).size =
        (buckets.get d).length := by
      simpa using congrArg List.length (hRangesIds d)
    rw [hMapLen, bucketsOfSlice_get]
    simp [StaticTreeSlice.childSlice]
  have hRangesAt : ∀ (d : Fin dense.length) (j : Nat)
      (hj : j < ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d).size),
      let pos := S.childStart d.val + j
      let ch := ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d)[j]'hj
      ∃ hp : pos < dense.length - 1,
        ch.id = S.childIds ⟨pos, hp⟩ ∧
        ch.entry = S.entry (S.childIds ⟨pos, hp⟩) ∧
        ch.stop = S.stop (S.childIds ⟨pos, hp⟩) := by
    intro d j hj
    have hjLen : j < (S.childSlice d).length := by
      rw [hRangesSize d] at hj
      simpa [StaticTreeSlice.childSlice] using hj
    have hEnd := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
    rw [S.childStart_end] at hEnd
    have hSpan : j < S.childStart (d.val + 1) - S.childStart d.val := by
      simpa [StaticTreeSlice.childSlice] using hjLen
    have hp : S.childStart d.val + j < dense.length - 1 := by omega
    let arr := ExactOrderedChildIntervals.packList (S.childSlice d)
      (PackedStaticLayout.build S.packedInput).endpoints.entry.read
      (PackedStaticLayout.build S.packedInput).endpoints.stop.read
    have hArrEq : (StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d = arr := by
      dsimp only [arr]
      rw [hRangesEq d]
      rw [← hPack.childSlice_eq d]
    have hSzArr : j < arr.size := by
      rw [← hArrEq]; exact hj
    have hChildAt := ExactOrderedChildIntervals.packList_at (S.childSlice d)
      (PackedStaticLayout.build S.packedInput).endpoints.entry.read
      (PackedStaticLayout.build S.packedInput).endpoints.stop.read
      ⟨j, hSzArr⟩ hjLen
    have hElemEq : ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d)[j]'hj =
        StaticChildLookup.childAt arr ⟨j, hSzArr⟩ := by
      change ((StaticTreeReader.build S.packedInput S.packedInput_ok).ranges.read d)[j]'hj = arr[j]'hSzArr
      have hGet : ∀ {α : Type} (a b : Array α) (hab : a = b) (k : Nat) (hk : k < a.size),
          a[k]'hk = b[k]'(hab ▸ hk) := fun _ _ hab _ _ => by cases hab; rfl
      exact hGet _ arr hArrEq j hj
    have hSliceAt : (S.childSlice d)[j]'hjLen = S.childIds ⟨S.childStart d.val + j, hp⟩ := by
      simp [StaticTreeSlice.childSlice, List.getElem_ofFn]
    refine ⟨hp, ?_⟩
    rw [hElemEq, hChildAt, hSliceAt]
    exact ⟨rfl, (hPack.entry_eq _).symm, (hPack.stop_eq _).symm⟩
  have hHeadEq : ∀ d : Fin dense.length, (q.reader.tables.head d).val = (S.head d).val := by
    intro d
    have hTbl : q.reader.tables =
        StaticHeadSweep.tables (PackedStaticLayout.build S.packedInput).packed := by
      change (StaticTreeReader.build S.packedInput S.packedInput_ok).tables = _
      rw [(StaticTreeReader.build S.packedInput S.packedInput_ok).tables_exact,
        (StaticTreeReader.build S.packedInput S.packedInput_ok).layout_exact]
    rw [hTbl]
    exact congrArg Fin.val (hPack.head_eq d).symm
  have hDomParentEq : ∀ d : Fin dense.length,
      (q.reader.tables.parent d).val = (S.domParent d).val := by
    intro d
    have hTbl : q.reader.tables =
        StaticHeadSweep.tables (PackedStaticLayout.build S.packedInput).packed := by
      change (StaticTreeReader.build S.packedInput S.packedInput_ok).tables = _
      rw [(StaticTreeReader.build S.packedInput S.packedInput_ok).tables_exact,
        (StaticTreeReader.build S.packedInput S.packedInput_ok).layout_exact]
    rw [hTbl]
    change (S.packedInput.parent.read d).val = (S.domParent d).val
    rw [packedInput_parent_read]
  have hDomDepthEq : ∀ d : Fin dense.length,
      q.reader.tables.depth d = S.domDepth d := by
    intro d
    have hTbl : q.reader.tables =
        StaticHeadSweep.tables (PackedStaticLayout.build S.packedInput).packed := by
      change (StaticTreeReader.build S.packedInput S.packedInput_ok).tables = _
      rw [(StaticTreeReader.build S.packedInput S.packedInput_ok).tables_exact,
        (StaticTreeReader.build S.packedInput S.packedInput_ok).layout_exact]
    rw [hTbl]
    change S.packedInput.depth.read d = S.domDepth d
    rw [packedInput_depth_read]
  { rank := rank
    progress := progress
    injRank := injRank
    q := q
    originalRows := originalRows
    hRows := rfl
    buckets := buckets
    rows := rows
    childOK := childOK
    inv := inv
    count_eq := rfl
    root_eq := rfl
    root_size_le := hRootSz
    buckets_eq := fun d => by
      change (bucketsOfSlice S).get d = (S.childSlice d).map id
      rw [bucketsOfSlice_get, List.map_id]
    matchesReader := hMatch
    ranges_ids := hRangesIds
    ranges_valid := hRangesValid
    ranges_size_eq := hRangesSize
    ranges_at_eq := hRangesAt
    head_eq := hHeadEq
    domParent_eq := hDomParentEq
    domDepth_eq := hDomDepthEq
    entry_eq := fun d => originalReader_entry_eq S hPack d
    stop_eq := fun d => originalReader_stop_eq S hPack d
    inv_eq_denseOfEntry := fun k => by
      change ((Array.ofFn S.denseOfEntry)[k.val]'(by simp)).val = (S.denseOfEntry k).val
      simp [Array.getElem_ofFn] }

end SliceBridge

/-! ### 3. Sealed Header & Global Static Table Agreement -/

section HeaderAgreement

/-- Agreement of the sealed word array `I` with the global tables of `S` under
`StaticHeaderSpec I g.vertexCount dense.length`. -/
structure StaticTreeSliceHeaderData {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (I : Array (Word bits)) {n qCount : Nat}
    (Hdr : StaticHeaderSpec I n qCount) : Prop where
  head_mem : ∀ d : Fin dense.length,
    (I[Hdr.headBase + d.val]?).map Fin.val = some (S.head d).val
  domParent_mem : ∀ d : Fin dense.length,
    (I[Hdr.domParentBase + d.val]?).map Fin.val = some (S.domParent d).val
  domDepth_mem : ∀ d : Fin dense.length,
    (I[Hdr.domDepthBase + d.val]?).map Fin.val = some (S.domDepth d)
  origToDense_mem : ∀ v : Fin g.vertexCount,
    (I[Hdr.origToDenseBase + v.val]?).map Fin.val =
      some (if _ : v ∈ dense then dense.idxOf v + 1 else 0)
  denseToOrig_mem : ∀ d : Fin dense.length,
    (I[Hdr.denseToOrigBase + d.val]?).map Fin.val = some (dense[d.val]'d.isLt).val
  entry_mem : ∀ d : Fin dense.length,
    (I[Hdr.entryBase + d.val]?).map Fin.val = some (S.entry d)
  stop_mem : ∀ d : Fin dense.length,
    (I[Hdr.stopBase + d.val]?).map Fin.val = some (S.stop d)
  denseOfEntry_mem : ∀ k : Fin dense.length,
    (I[Hdr.origOfEntryBase + k.val]?).map Fin.val = some (S.denseOfEntry k).val
  childStart_mem : ∀ idx : Fin (dense.length + 1),
    (I[Hdr.childStartBase + idx.val]?).map Fin.val = some (S.childStart idx.val)
  childEntries_mem : ∀ pos : Fin (dense.length - 1),
    (I[Hdr.childEntriesBase + pos.val]?).map Fin.val = some (S.entry (S.childIds pos))
  childStops_mem : ∀ pos : Fin (dense.length - 1),
    (I[Hdr.childStopsBase + pos.val]?).map Fin.val = some (S.stop (S.childIds pos))
  childIds_mem : ∀ pos : Fin (dense.length - 1),
    (I[Hdr.childIdsBase + pos.val]?).map Fin.val = some (S.childIds pos).val

/-- Construct `StaticTreeSliceHeaderData` directly when `I` copies the static
tree banks from `S`'s backing memory `mem[treeBase .. treeBase + staticTreeWords Q)`
together with `origToDensePlusOne` and `denseToOrig`. -/
theorem StaticTreeSliceHeaderData.ofSliceCopy {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (I : Array (Word bits)) (Hdr : StaticHeaderSpec I g.vertexCount dense.length)
    (hHead : ∀ d : Fin dense.length,
      I[Hdr.headBase + d.val]? = mem[treeBase + 3 * dense.length + d.val]?)
    (hPar : ∀ d : Fin dense.length,
      I[Hdr.domParentBase + d.val]? = mem[treeBase + d.val]?)
    (hDep : ∀ d : Fin dense.length,
      I[Hdr.domDepthBase + d.val]? = mem[treeBase + dense.length + d.val]?)
    (hEnt : ∀ d : Fin dense.length,
      I[Hdr.entryBase + d.val]? = mem[treeBase + 4 * dense.length + d.val]?)
    (hStop : ∀ d : Fin dense.length,
      I[Hdr.stopBase + d.val]? = mem[treeBase + 5 * dense.length + d.val]?)
    (hDofE : ∀ k : Fin dense.length,
      I[Hdr.origOfEntryBase + k.val]? = mem[treeBase + 6 * dense.length + k.val]?)
    (hCStart : ∀ idx : Fin (dense.length + 1),
      I[Hdr.childStartBase + idx.val]? = mem[treeBase + 7 * dense.length + idx.val]?)
    (hCEnt : ∀ pos : Fin (dense.length - 1),
      I[Hdr.childEntriesBase + pos.val]? = mem[treeBase + (8 * dense.length + 1) + pos.val]?)
    (hCStop : ∀ pos : Fin (dense.length - 1),
      I[Hdr.childStopsBase + pos.val]? = mem[treeBase + (9 * dense.length + 1) + pos.val]?)
    (hCId : ∀ pos : Fin (dense.length - 1),
      I[Hdr.childIdsBase + pos.val]? = mem[treeBase + (10 * dense.length + 1) + pos.val]?)
    (hOrigToDense : ∀ v : Fin g.vertexCount,
      (I[Hdr.origToDenseBase + v.val]?).map Fin.val =
        some (if _ : v ∈ dense then dense.idxOf v + 1 else 0))
    (hDenseToOrig : ∀ d : Fin dense.length,
      (I[Hdr.denseToOrigBase + d.val]?).map Fin.val = some (dense[d.val]'d.isLt).val) :
    StaticTreeSliceHeaderData S I Hdr where
  head_mem d := by rw [hHead d]; exact S.head_mem d
  domParent_mem d := by rw [hPar d]; exact S.domParent_mem d
  domDepth_mem d := by rw [hDep d]; exact S.domDepth_mem d
  origToDense_mem := hOrigToDense
  denseToOrig_mem := hDenseToOrig
  entry_mem d := by rw [hEnt d]; exact S.entry_mem d
  stop_mem d := by rw [hStop d]; exact S.stop_mem d
  denseOfEntry_mem k := by rw [hDofE k]; exact S.denseOfEntry_mem k
  childStart_mem idx := by rw [hCStart idx]; exact S.childStart_mem idx.val (Nat.le_of_lt_succ idx.isLt)
  childEntries_mem pos := by rw [hCEnt pos]; exact S.childEntries_mem pos
  childStops_mem pos := by rw [hCStop pos]; exact S.childStops_mem pos
  childIds_mem pos := by rw [hCId pos]; exact S.childIds_mem pos

/-- Global table and `StaticChildLookup` agreement between `StaticReaderBridge`
and `StaticHeaderSpec I g.vertexCount B.q.count`. -/
theorem StaticReaderBridge.headerAgreement {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S)
    {I : Array (Word bits)} (Hdr : StaticHeaderSpec I g.vertexCount B.q.count)
    (hData : StaticTreeSliceHeaderData S I Hdr) :
    NatSliceAt I Hdr.headBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.reader.tables.head ⟨d, hd⟩).val else 0) ∧
    NatSliceAt I Hdr.domParentBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.reader.tables.parent ⟨d, hd⟩).val else 0) ∧
    NatSliceAt I Hdr.domDepthBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.tables.depth ⟨d, hd⟩ else 0) ∧
    NatSliceAt I Hdr.origToDenseBase g.vertexCount
      (fun v => if hv : v < g.vertexCount then
        match B.q.ids.find ⟨v, hv⟩ with | none => 0 | some d => d.val + 1 else 0) ∧
    NatSliceAt I Hdr.denseToOrigBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.ids.originals.read ⟨d, hd⟩).val else 0) ∧
    NatSliceAt I Hdr.entryBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.entry ⟨d, hd⟩ else 0) ∧
    NatSliceAt I Hdr.stopBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.stop ⟨d, hd⟩ else 0) ∧
    NatSliceAt I Hdr.origOfEntryBase B.q.count
      (fun rk => if hr : rk < B.q.count then (B.inv.slots.read ⟨rk, hr⟩).val else 0) ∧
    (∃ cStart : Fin (B.q.count + 1) → Nat,
      cStart ⟨0, Nat.zero_lt_succ B.q.count⟩ = 0 ∧
      (∀ d : Fin B.q.count,
        cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
          cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (B.q.reader.ranges.read d).size) ∧
      NatSliceAt I Hdr.childStartBase (B.q.count + 1)
        (fun idx => if hi : idx < B.q.count + 1 then cStart ⟨idx, hi⟩ else 0) ∧
      (∀ (d : Fin B.q.count) (j : Nat) (hj : j < (B.q.reader.ranges.read d).size),
        let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
        let ch := (B.q.reader.ranges.read d)[j]'hj
        pos < B.q.count ∧
        (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
        (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
        (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)) := by
  have hCount := B.count_eq
  have hHead : NatSliceAt I Hdr.headBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.reader.tables.head ⟨d, hd⟩).val else 0) := by
    refine ⟨Hdr.head_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.head_eq dj]
    exact hData.head_mem dj
  have hPar : NatSliceAt I Hdr.domParentBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.reader.tables.parent ⟨d, hd⟩).val else 0) := by
    refine ⟨Hdr.domParent_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.domParent_eq dj]
    exact hData.domParent_mem dj
  have hDep : NatSliceAt I Hdr.domDepthBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.tables.depth ⟨d, hd⟩ else 0) := by
    refine ⟨Hdr.domDepth_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.domDepth_eq dj]
    exact hData.domDepth_mem dj
  have hOrigToDense : NatSliceAt I Hdr.origToDenseBase g.vertexCount
      (fun v => if hv : v < g.vertexCount then
        match B.q.ids.find ⟨v, hv⟩ with | none => 0 | some d => d.val + 1 else 0) := by
    refine ⟨Hdr.origToDense_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let vj : Fin g.vertexCount := ⟨j, hj⟩
    rw [hData.origToDense_mem vj]
    congr 1
    by_cases hv : vj ∈ dense
    · rw [dite_eq_left hv]
      have hIdxLt : dense.idxOf vj < dense.length := List.idxOf_lt_length_of_mem hv
      let dk : Fin dense.length := ⟨dense.idxOf vj, hIdxLt⟩
      have hOrigEq : B.q.ids.originals.read (Fin.cast hCount.symm dk) = vj := by
        rw [B.matchesReader.originals_eq dk]
        exact List.getElem_idxOf hIdxLt
      have hFind := B.q.ids.slot_of_original (Fin.cast hCount.symm dk)
      rw [hOrigEq] at hFind
      rw [hFind]
      rfl
    · rw [dite_eq_right hv]
      have hNotReach : ¬ g.InitiallyReachable r vj := by
        intro hReach
        exact hv (S.mem_reach vj hReach)
      rw [(B.q.ids.miss_iff vj).mpr hNotReach]
  have hDenseToOrig : NatSliceAt I Hdr.denseToOrigBase B.q.count
      (fun d => if hd : d < B.q.count then (B.q.ids.originals.read ⟨d, hd⟩).val else 0) := by
    refine ⟨Hdr.denseToOrig_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.matchesReader.originals_eq dj]
    exact hData.denseToOrig_mem dj
  have hEnt : NatSliceAt I Hdr.entryBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.entry ⟨d, hd⟩ else 0) := by
    refine ⟨Hdr.entry_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.entry_eq dj]
    exact hData.entry_mem dj
  have hStop : NatSliceAt I Hdr.stopBase B.q.count
      (fun d => if hd : d < B.q.count then B.q.reader.stop ⟨d, hd⟩ else 0) := by
    refine ⟨Hdr.stop_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let dj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm dj := Fin.ext rfl
    rw [hCast, B.stop_eq dj]
    exact hData.stop_mem dj
  have hOrigOfEnt : NatSliceAt I Hdr.origOfEntryBase B.q.count
      (fun rk => if hr : rk < B.q.count then (B.inv.slots.read ⟨rk, hr⟩).val else 0) := by
    refine ⟨Hdr.origOfEntry_fit, fun j hj => ?_⟩
    dsimp only
    rw [dite_eq_left hj]
    let kj : Fin dense.length := ⟨j, hCount ▸ hj⟩
    have hCast : (⟨j, hj⟩ : Fin B.q.count) = Fin.cast hCount.symm kj := Fin.ext rfl
    rw [hCast, B.inv_eq_denseOfEntry kj]
    exact hData.denseOfEntry_mem kj
  refine ⟨hHead, hPar, hDep, hOrigToDense, hDenseToOrig, hEnt, hStop, hOrigOfEnt, ?_⟩
  let cStart : Fin (B.q.count + 1) → Nat := fun idx => S.childStart idx.val
  refine ⟨cStart, S.childStart_zero, ?_, ?_, ?_⟩
  · intro d
    let dd : Fin dense.length := Fin.cast hCount d
    have hCastD : d = Fin.cast hCount.symm dd := Fin.ext rfl
    rw [hCastD, B.ranges_size_eq dd]
    have hMono : S.childStart dd.val ≤ S.childStart (dd.val + 1) :=
      S.childStart_mono dd.val (dd.val + 1) (Nat.le_succ _) dd.isLt
    change S.childStart (dd.val + 1) = S.childStart dd.val + (S.childStart (dd.val + 1) - S.childStart dd.val)
    omega
  · refine ⟨Hdr.childStart_fit, fun idx hidx => ?_⟩
    dsimp only
    rw [dite_eq_left hidx]
    exact hData.childStart_mem ⟨idx, hCount ▸ hidx⟩
  · intro d j hj
    let dd : Fin dense.length := Fin.cast hCount d
    have hCastD : d = Fin.cast hCount.symm dd := Fin.ext rfl
    have hj' : j < (B.q.reader.ranges.read (Fin.cast hCount.symm dd)).size := by
      simpa [hCastD] using hj
    obtain ⟨hp, hId, hEntry, hStop⟩ := B.ranges_at_eq dd j hj'
    have hPosLt : S.childStart dd.val + j < B.q.count := by
      have := S.qPos
      omega
    have hChEq : (B.q.reader.ranges.read d)[j]'hj =
        (B.q.reader.ranges.read (Fin.cast hCount.symm dd))[j]'hj' := by
      congr 1
    have hPosEq : cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j = S.childStart dd.val + j := rfl
    refine ⟨hPosLt, ?_, ?_, ?_⟩
    · rw [hPosEq, hChEq, hEntry]
      exact hData.childEntries_mem ⟨S.childStart dd.val + j, hp⟩
    · rw [hPosEq, hChEq, hStop]
      exact hData.childStops_mem ⟨S.childStart dd.val + j, hp⟩
    · rw [hPosEq, hChEq, hId]
      simpa using hData.childIds_mem ⟨S.childStart dd.val + j, hp⟩

end HeaderAgreement

/-! ### 4. Quotient Flatness, Acyclicity, and `SealedOwnerRecord` Transport -/

section QuotientTransport

theorem StaticReaderBridge.ramQuotient_isFlat
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S) (d : Fin dense.length) :
    (S.ramQuotient d).IsFlat :=
  B.matchesReader.ramQuotient_isFlat B.progress B.injRank B.originalRows B.hRows
    B.rows B.childOK B.buckets_eq d

theorem StaticReaderBridge.ramQuotient_isAcyclic
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (_B : StaticReaderBridge g r order hLen hTopo S)
    (acyc : g.IsAcyclic) (d : Fin dense.length) :
    (S.ramQuotient d).IsAcyclic :=
  S.ramQuotient_isAcyclic acyc d

theorem StaticReaderBridge.denseQuotient_isFlat
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S) (d : Fin B.q.count) :
    (denseQuotient B.progress B.injRank B.q B.originalRows B.hRows B.rows B.childOK d).IsFlat := by
  have hd : g.InitiallyReachable r (B.q.ids.originals.read d) :=
    B.q.ids.original_reachable d
  have hFind : B.q.ids.find (B.q.ids.originals.read d) = some d :=
    B.q.ids.slot_of_original d
  have hzero : 0 < B.rows.length d := by
    rw [B.rows.length_exact]
    omega
  have spec := B.q.parentSpec
  exact DenseOriginalQuotient.Transport.build_isFlat B.progress B.injRank B.q
    B.originalRows B.hRows d hd hFind B.rows B.childOK hzero spec

/-- Dense entry rank of an original vertex `v` computed directly from `S`. -/
def denseRank {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (v : Fin g.vertexCount) : Nat :=
  if hv : v ∈ dense then S.entry ⟨dense.idxOf v, List.idxOf_lt_length_of_mem hv⟩ else 0

theorem StaticReaderBridge.originalRank_eq_denseRank
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S) (v : Fin g.vertexCount) :
    (OriginalEntryInverse.originalRank B.q v).getD 0 = denseRank S v := by
  unfold denseRank
  by_cases hv : v ∈ dense
  · rw [dite_eq_left hv]
    have hIdxLt : dense.idxOf v < dense.length := List.idxOf_lt_length_of_mem hv
    let d : Fin dense.length := ⟨dense.idxOf v, hIdxLt⟩
    have hOrig : B.q.ids.originals.read (Fin.cast B.count_eq.symm d) = v := by
      rw [B.matchesReader.originals_eq d]
      exact List.getElem_idxOf hIdxLt
    have hFind : B.q.ids.find v = some (Fin.cast B.count_eq.symm d) := by
      have hs := B.q.ids.slot_of_original (Fin.cast B.count_eq.symm d)
      rwa [hOrig] at hs
    rw [OriginalEntryInverse.originalRank_of_find B.q hFind, Option.getD_some]
    exact B.entry_eq d
  · rw [dite_eq_right hv]
    have hNotReach : ¬ g.InitiallyReachable r v := fun hr => hv (S.mem_reach v hr)
    have hMiss : B.q.ids.find v = none := (B.q.ids.miss_iff v).mpr hNotReach
    have hRankNone : OriginalEntryInverse.originalRank B.q v = none := by
      cases hR : OriginalEntryInverse.originalRank B.q v with
      | none => rfl
      | some rk =>
        have : B.q.ids.find v ≠ none := by
          intro hm
          simp [OriginalEntryInverse.originalRank, hm] at hR
        exact False.elim (this hMiss)
    rw [hRankNone, Option.getD_none]

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

private theorem summary_eq_of_mem_iff {xs ys : List Nat}
    (hMem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    ExitSummary.summary xs = ExitSummary.summary ys := by
  by_cases hxs : xs = []
  · have hys : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y _ =>
        have : y ∈ xs := (hMem y).mpr List.mem_cons_self
        rw [hxs] at this
        simp at this
    rw [hxs, hys]
  · have hys : ys ≠ [] := by
      intro hNil
      cases xs with
      | nil => exact hxs rfl
      | cons x _ =>
        have : x ∈ ys := (hMem x).mp List.mem_cons_self
        rw [hNil] at this
        simp at this
    obtain ⟨lo1, hi1, hs1, hlo1, hhi1, hb1⟩ := summary_has_extrema_local xs hxs
    obtain ⟨lo2, hi2, hs2, hlo2, hhi2, hb2⟩ := summary_has_extrema_local ys hys
    have h1 := hb2 lo1 ((hMem lo1).mp hlo1)
    have h2 := hb1 lo2 ((hMem lo2).mpr hlo2)
    have h3 := hb2 hi1 ((hMem hi1).mp hhi1)
    have h4 := hb1 hi2 ((hMem hi2).mpr hhi2)
    rw [hs1, hs2]
    congr 1 <;> omega

private def mapCutPair {H1 H2 : LabelledQuotient}
    (hV : H1.vertexCount = H2.vertexCount)
    (hR : Fin.cast hV H1.root = H2.root)
    (q : H1.CutPair) : H2.CutPair where
  fst := Fin.cast hV q.fst
  snd := Fin.cast hV q.snd
  fst_ne_root h := q.fst_ne_root (Fin.ext (by
    have := congrArg Fin.val (h.trans hR.symm)
    simpa using this))
  snd_ne_root h := q.snd_ne_root (Fin.ext (by
    have := congrArg Fin.val (h.trans hR.symm)
    simpa using this))
  ne h := q.ne (Fin.ext (by simpa using congrArg Fin.val h))

private theorem mapCutPair_symm {H1 H2 : LabelledQuotient}
    (hV : H1.vertexCount = H2.vertexCount)
    (hR : Fin.cast hV H1.root = H2.root)
    (q : H2.CutPair) :
    mapCutPair hV hR
      (mapCutPair hV.symm (Fin.ext (by simpa using (congrArg Fin.val hR).symm)) q) = q := by
  cases q
  rfl

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hinj : ∀ a b, f a = f b → a = b) {xs : List α} (hnd : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨fun hm => ?_, ih hnd.2⟩
    obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp hm
    exact hnd.1 (hinj y x hyEq ▸ hy)

private def rowsCast {H1 H2 : LabelledQuotient}
    (hV : H1.vertexCount = H2.vertexCount)
    (hN : H1.origVertexCount = H2.origVertexCount)
    (hAdj : Transport.ExactAdj (Fin.cast hV) hN)
    (p : ForestDictionary.Rows H1) : ForestDictionary.Rows H2 where
  row y := (p.row (Fin.cast hV.symm y)).map (Fin.cast hV)
  spec y := by
    refine ⟨nodup_map_of_inj (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (p.spec (Fin.cast hV.symm y)).nodup, ?_⟩
    intro u
    constructor
    · intro hu
      obtain ⟨u0, hu0, huEq⟩ := List.mem_map.mp hu
      have hArc := (p.spec (Fin.cast hV.symm y)).cover u0 |>.mp hu0
      have hArc2 := (Transport.arc_iff (Fin.cast hV) hN hAdj u0 (Fin.cast hV.symm y)).mp hArc
      have hCastY : Fin.cast hV (Fin.cast hV.symm y) = y := Fin.ext rfl
      rw [hCastY, huEq] at hArc2
      exact hArc2
    · intro hu
      have hCastY : Fin.cast hV (Fin.cast hV.symm y) = y := Fin.ext rfl
      have hCastU : Fin.cast hV (Fin.cast hV.symm u) = u := Fin.ext rfl
      have hArc2 : H2.HasQuotientArc (Fin.cast hV (Fin.cast hV.symm u))
          (Fin.cast hV (Fin.cast hV.symm y)) := by
        simpa [hCastY, hCastU] using hu
      have hArc1 := (Transport.arc_iff (Fin.cast hV) hN hAdj (Fin.cast hV.symm u)
        (Fin.cast hV.symm y)).mpr hArc2
      have hMem := (p.spec (Fin.cast hV.symm y)).cover (Fin.cast hV.symm u) |>.mpr hArc1
      exact List.mem_map.mpr ⟨Fin.cast hV.symm u, hMem, hCastU⟩

private theorem preparedKey_eq_same_shape (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (xs : List (Fin n)) :
    let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
    let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
    ForestHead.preparedKey H2 xs =
      (ForestHead.preparedKey H1 xs).map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl) := by
  intro H1 H2
  dsimp only [ForestHead.preparedKey]
  cases xs with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l2 =>
      cases l2 with
      | nil =>
        dsimp only [LabelledQuotient.candidatePairOfPreds]
        by_cases hab : a < b
        · rw [ite_eq_left hab]
          dsimp only
          by_cases ha : a ≠ r0
          · have ha1 : a ≠ H1.root := ha
            have ha2 : a ≠ H2.root := ha
            rw [dite_eq_left ha1, dite_eq_left ha2]
            by_cases hb : b ≠ r0
            · have hb1 : b ≠ H1.root := hb
              have hb2 : b ≠ H2.root := hb
              have hab1 : (a : Vertex H1) < b := hab
              have hab2 : (a : Vertex H2) < b := hab
              rw [dite_eq_left hb1, dite_eq_left hb2, dite_eq_left hab1, dite_eq_left hab2]; rfl
            · have hb1 : ¬ b ≠ H1.root := hb
              have hb2 : ¬ b ≠ H2.root := hb
              rw [dite_eq_right hb1, dite_eq_right hb2]; rfl
          · have ha1 : ¬ a ≠ H1.root := ha
            have ha2 : ¬ a ≠ H2.root := ha
            rw [dite_eq_right ha1, dite_eq_right ha2]; rfl
        · rw [ite_eq_right hab]
          dsimp only
          by_cases hb : b ≠ r0
          · have hb1 : b ≠ H1.root := hb
            have hb2 : b ≠ H2.root := hb
            rw [dite_eq_left hb1, dite_eq_left hb2]
            by_cases ha : a ≠ r0
            · have ha1 : a ≠ H1.root := ha
              have ha2 : a ≠ H2.root := ha
              rw [dite_eq_left ha1, dite_eq_left ha2]
              by_cases hba : b < a
              · have hba1 : (b : Vertex H1) < a := hba
                have hba2 : (b : Vertex H2) < a := hba
                rw [dite_eq_left hba1, dite_eq_left hba2]; rfl
              · have hba1 : ¬ (b : Vertex H1) < a := hba
                have hba2 : ¬ (b : Vertex H2) < a := hba
                rw [dite_eq_right hba1, dite_eq_right hba2]; rfl
            · have ha1 : ¬ a ≠ H1.root := ha
              have ha2 : ¬ a ≠ H2.root := ha
              rw [dite_eq_right ha1, dite_eq_right ha2]; rfl
          · have hb1 : ¬ b ≠ H1.root := hb
            have hb2 : ¬ b ≠ H2.root := hb
            rw [dite_eq_right hb1, dite_eq_right hb2]; rfl
      | cons _ _ => rfl

private theorem orderedConfig_dict_eq_same_shape (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (row : Fin n → List (Fin n))
    (sp1 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj1, hs1⟩) y (row y))
    (sp2 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj2, hs2⟩) y (row y))
    (large : 3 ≤ n) :
    let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
    let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
    let p1 : ForestDictionary.Rows H1 := ⟨row, sp1⟩
    let p2 : ForestDictionary.Rows H2 := ⟨row, sp2⟩
    (EX24.PreparedSweep.orderedConfig p2 large).dict =
      (EX24.PreparedSweep.orderedConfig p1 large).dict := by
  intro H1 H2 p1 p2
  dsimp only [EX24.PreparedSweep.orderedConfig, EX24.Config.usePackedWords,
    ForestDictionary.dictionary, ForestDictionary.collect, ForestDictionary.collectFrom]
  congr 1
  generalize List.finRange n = ys
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.filterMap_cons]
    rw [ih]
    congr 1
    change Option.map (@EX24.PreparedSweep.orderedPairCode H2) (ForestHead.preparedKey H2 (row y)) =
      Option.map (@EX24.PreparedSweep.orderedPairCode H1) (ForestHead.preparedKey H1 (row y))
    rw [preparedKey_eq_same_shape N n r0 adj1 adj2 hs1 hs2 (row y)]
    cases ForestHead.preparedKey H1 (row y) with
    | none => rfl
    | some P => rfl

private def stateView {H : LabelledQuotient} (s : EX24.State H) :
    Array Nat × Array Nat × Nat × Array Nat × Array (Option (Nat × Nat)) :=
  (s.tables.mem, s.tables.slots, s.tables.next, s.labels,
    s.tables.back.map (Option.map fun q : H.CutPair => (q.fst.val, q.snd.val)))

private theorem stateView_eq {H1 H2 : LabelledQuotient}
    {s1 : EX24.State H1} {s2 : EX24.State H2}
    (h1 : s1.tables.mem = s2.tables.mem)
    (h2 : s1.tables.slots = s2.tables.slots)
    (h3 : s1.tables.next = s2.tables.next)
    (h4 : s1.labels = s2.labels)
    (h5 : s1.tables.back.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val)) =
          s2.tables.back.map (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))) :
    stateView s1 = stateView s2 := by
  unfold stateView
  rw [h1, h2, h3, h4, h5]

private theorem back_eq_of_view_eq {H1 H2 : LabelledQuotient}
    (hV : H1.vertexCount = H2.vertexCount) (hR : Fin.cast hV H1.root = H2.root)
    {a1 : Array (Option H1.CutPair)} {a2 : Array (Option H2.CutPair)}
    (h : a1.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val)) =
         a2.map (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))) :
    a2 = a1.map (Option.map (mapCutPair hV hR)) := by
  apply Array.ext
  · have hs := congrArg Array.size h
    simpa using hs.symm
  · intro i hi2 hi1
    have hSz : i < (a1.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val))).size := by
      simpa using hi1
    have hLt1 : i < a1.size := by simpa using hi1
    have hi := congrArg (fun arr => arr[i]?) h
    rw [Array.getElem?_eq_getElem hSz, Array.getElem?_eq_getElem (by simpa using hi2)] at hi
    simp only [Array.getElem_map] at hi
    cases ha1 : a1[i]'hLt1 with
    | none =>
      cases ha2 : a2[i]'hi2 with
      | none =>
        rw [Array.getElem_map, ha1]
        rfl
      | some q2 => rw [ha1, ha2] at hi; cases hi
    | some q1 =>
      cases ha2 : a2[i]'hi2 with
      | none => rw [ha1, ha2] at hi; cases hi
      | some q2 =>
        rw [ha1, ha2] at hi
        rw [Array.getElem_map, ha1]
        dsimp only [Option.map]
        congr 1
        rcases q1 with ⟨f1, s1, fn1, sn1, ne1⟩
        rcases q2 with ⟨f2, s2, fn2, sn2, ne2⟩
        have hPair : (f1.val, s1.val) = (f2.val, s2.val) :=
          Option.some.inj (Option.some.inj (by simpa using hi))
        have hf : f2 = Fin.cast hV f1 := Fin.ext (Prod.mk.inj hPair).1.symm
        have hs : s2 = Fin.cast hV s1 := Fin.ext (Prod.mk.inj hPair).2.symm
        subst hf
        subst hs
        rfl

private theorem scan_congr {α : Type} (f1 f2 : α → Bool × Nat) (hf : ∀ x, f1 x = f2 x)
    (xs : List α) : ForestHead.scan f1 xs = ForestHead.scan f2 xs := by
  have hfEq : f1 = f2 := funext hf
  rw [hfEq]

private theorem install_same_shape (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (row : Fin n → List (Fin n))
    (sp1 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj1, hs1⟩) y (row y))
    (sp2 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj2, hs2⟩) y (row y))
    (large : 3 ≤ n)
    (t1 : EX24.Tables ⟨N, n, r0, adj1, hs1⟩)
    (req1 : ForestHead.Step ⟨N, n, r0, adj1, hs1⟩) :
    let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
    let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
    let c1 := EX24.PreparedSweep.orderedConfig (H := H1) ⟨row, sp1⟩ large
    let c2 := EX24.PreparedSweep.orderedConfig (H := H2) ⟨row, sp2⟩ large
    let t2 : EX24.Tables H2 :=
      ⟨t1.mem, t1.slots, t1.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)), t1.next⟩
    let req2 : ForestHead.Step H2 :=
      ⟨req1.newPair.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl), req1.parent,
        match req1.assigned with | .existing p => .existing p | .fresh => .fresh⟩
    Option.map (fun ins => (ins.node, ins.tables.mem, ins.tables.slots, ins.tables.next,
        ins.tables.back.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val))))
      (EX24.install c1 t1 req1) =
    Option.map (fun ins => (ins.node, ins.tables.mem, ins.tables.slots, ins.tables.next,
        ins.tables.back.map (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))))
      (EX24.install c2 t2 req2) := by
  intro H1 H2 c1 c2 t2 req2
  have hDict : c2.dict = c1.dict :=
    orderedConfig_dict_eq_same_shape N n r0 adj1 adj2 hs1 hs2 row sp1 sp2 large
  dsimp only [EX24.install]
  by_cases hp : req1.parent < t1.next
  · have hp2 : req2.parent < t2.next := hp
    dsimp only [req2, t2] at hp2 ⊢
    rw [ite_eq_left hp, ite_eq_left hp2]
    cases hnp : req1.newPair with
    | none =>
      simp only [Option.map_none, Option.map_some]
      refine congrArg some (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
      change t1.back.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val)) =
        (t1.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl))).map
          (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))
      rw [Array.map_map]
      congr 1
      funext o
      cases o <;> rfl
    | some q =>
      simp only [Option.map_some]
      have hCode : c2.code (mapCutPair (H1 := H1) (H2 := H2) rfl rfl q) = c1.code q := rfl
      rw [hCode, hDict]
      cases hLook : PairLookup.lookup c1.dict (c1.code q) with
      | mk fst snd =>
        cases fst with
        | none => rfl
        | some i =>
          dsimp only
          let t2' : EX24.Tables H2 :=
            ⟨t1.mem, t1.slots, t1.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)), t1.next⟩
          change Option.map _
              (if hi : i < t1.slots.size then
                if t1.slotAt i = 0 then
                  if hn : t1.next < t1.back.size then _ else none
                else _ else none) =
            Option.map _
              (if hi : i < t2'.slots.size then
                if t2'.slotAt i = 0 then
                  if hn : t1.next < t2'.back.size then _ else none
                else _ else none)
          by_cases hi : i < t1.slots.size
          · have hi2 : i < t2'.slots.size := hi
            rw [dite_eq_left hi, dite_eq_left hi2]
            by_cases hn0 : t1.slotAt i = 0
            · have hn02 : t2'.slotAt i = 0 := hn0
              rw [ite_eq_left hn0, ite_eq_left hn02]
              by_cases hnx : t1.next < t1.back.size
              · have hnx2 : t1.next < t2'.back.size := by
                  simpa [t2'] using hnx
                rw [dite_eq_left hnx, dite_eq_left hnx2]
                simp only [Option.map_some]
                refine congrArg some (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
                change (t1.back.set t1.next (some q) hnx).map
                    (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val)) =
                  (t2'.back.set t1.next (some (mapCutPair (H1 := H1) (H2 := H2) rfl rfl q)) hnx2).map
                    (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))
                dsimp only [t2']
                apply Array.ext
                · simp [Array.size_set]
                · intro k hk1 hk2
                  have hk0 : k < t1.back.size := by simpa using hk1
                  simp only [Array.getElem_map, Array.getElem_set]
                  split
                  · rfl
                  · cases t1.back[k]'hk0 <;> rfl
              · have hnx2 : ¬ t1.next < t2'.back.size := by
                  simpa [t2'] using hnx
                rw [dite_eq_right hnx, dite_eq_right hnx2]
                rfl
            · have hn02 : t2'.slotAt i ≠ 0 := hn0
              rw [ite_eq_right hn0, ite_eq_right hn02]
              simp only [Option.map_some]
              refine congrArg some (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
              change t1.back.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val)) =
                t2'.back.map (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))
              dsimp only [t2']
              rw [Array.map_map]
              congr 1
              funext o
              cases o <;> rfl
          · have hi2 : ¬ i < t2'.slots.size := hi
            rw [dite_eq_right hi, dite_eq_right hi2]
            rfl
  · have hp2 : ¬ req2.parent < t2.next := hp
    dsimp only [req2, t2] at hp2 ⊢
    rw [ite_eq_right hp, ite_eq_right hp2]
    rfl

private theorem zeroKey_same_shape (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (large : 3 ≤ n) :
    let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
    let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
    (SmallQuotient.sentinelDefaultCutPair H2 large).fst =
      (SmallQuotient.sentinelDefaultCutPair H1 large).fst ∧
    (SmallQuotient.sentinelDefaultCutPair H2 large).snd =
      (SmallQuotient.sentinelDefaultCutPair H1 large).snd := by
  intro H1 H2
  dsimp only [SmallQuotient.sentinelDefaultCutPair]
  by_cases h0 : (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) large⟩ : Fin n) = r0
  · have h01 : (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) large⟩ : Fin H1.vertexCount) = H1.root := h0
    have h02 : (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) large⟩ : Fin H2.vertexCount) = H2.root := h0
    rw [dite_eq_left h02, dite_eq_left h01]
    exact ⟨rfl, rfl⟩
  · have h01 : (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) large⟩ : Fin H1.vertexCount) ≠ H1.root := h0
    have h02 : (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) large⟩ : Fin H2.vertexCount) ≠ H2.root := h0
    rw [dite_eq_right h02, dite_eq_right h01]
    by_cases h1 : (⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) large⟩ : Fin n) = r0
    · have h11 : (⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) large⟩ : Fin H1.vertexCount) = H1.root := h1
      have h12 : (⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) large⟩ : Fin H2.vertexCount) = H2.root := h1
      rw [dite_eq_left h12, dite_eq_left h11]
      exact ⟨rfl, rfl⟩
    · have h11 : (⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) large⟩ : Fin H1.vertexCount) ≠ H1.root := h1
      have h12 : (⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) large⟩ : Fin H2.vertexCount) ≠ H2.root := h1
      rw [dite_eq_right h12, dite_eq_right h11]
      exact ⟨rfl, rfl⟩

private theorem foldRowsAux_same_shape (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (row : Fin n → List (Fin n))
    (sp1 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj1, hs1⟩) y (row y))
    (sp2 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj2, hs2⟩) y (row y))
    (rank : Fin n → Nat) (large : 3 ≤ n) :
    let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
    let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
    let c1 := EX24.PreparedSweep.orderedConfig (H := H1) ⟨row, sp1⟩ large
    let c2 := EX24.PreparedSweep.orderedConfig (H := H2) ⟨row, sp2⟩ large
    let mapSt : EX24.State H1 → EX24.State H2 := fun s =>
      { tables := ⟨s.tables.mem, s.tables.slots,
          s.tables.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)), s.tables.next⟩
        labels := s.labels }
    ∀ (pairs : List (Fin n × List (Fin n))) (s1 : EX24.State H1)
      (acc1 : EX24.PreparedSweep.Log H1) (acc2 : EX24.PreparedSweep.Log H2),
      Option.map (fun p => stateView p.1)
        (EX24.PreparedSweep.foldRowsAux c1 rank
          (pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H1))
          s1 acc1) =
      Option.map (fun p => stateView p.1)
        (EX24.PreparedSweep.foldRowsAux c2 rank
          (pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H2))
          (mapSt s1) acc2) := by
  intro H1 H2 c1 c2 mapSt pairs
  induction pairs with
  | nil =>
    intro s1 acc1 acc2
    change some (stateView s1) = some (stateView (mapSt s1))
    apply congrArg some
    apply stateView_eq (H1 := H1) (H2 := H2) rfl rfl rfl rfl
    dsimp only [mapSt]
    rw [Array.map_map]
    congr 1
    funext o
    cases o <;> rfl
  | cons pr rest ih =>
    intro s1 acc1 acc2
    change Option.map (fun p => stateView p.1)
        (match EX24.stepPrepared c1 s1 rank pr.1 pr.2 with
          | none => none
          | some r => EX24.PreparedSweep.foldRowsAux c1 rank
              (rest.map fun q => ⟨q.1, q.2⟩) r.state (EX24.PreparedSweep.Event.ofResult pr.1 r :: acc1)) =
      Option.map (fun p => stateView p.1)
        (match EX24.stepPrepared c2 (mapSt s1) rank pr.1 pr.2 with
          | none => none
          | some r => EX24.PreparedSweep.foldRowsAux c2 rank
              (rest.map fun q => ⟨q.1, q.2⟩) r.state (EX24.PreparedSweep.Event.ofResult pr.1 r :: acc2))
    have hPlan : ForestHead.planPrepared (H := H2) rank pr.1 pr.2 =
        Option.map (fun pk => (pk.1, pk.2.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)))
          (ForestHead.planPrepared (H := H1) rank pr.1 pr.2) := by
      dsimp only [ForestHead.planPrepared]
      by_cases hr : pr.1 = r0
      · have hr1 : pr.1 = H1.root := hr
        have hr2 : pr.1 = H2.root := hr
        rw [ite_eq_left hr1, ite_eq_left hr2]
        rfl
      · have hr1 : pr.1 ≠ H1.root := hr
        have hr2 : pr.1 ≠ H2.root := hr
        rw [ite_eq_right hr1, ite_eq_right hr2]
        have hRootEq : H2.root = H1.root := rfl
        conv => lhs; rw [hRootEq]
        split
        · rfl
        · cases LabelledQuotient.maxByRank rank pr.2 with
          | none => rfl
          | some m =>
            simp only [Option.map_some]
            congr 1
            exact congrArg (m, ·) (preparedKey_eq_same_shape N n r0 adj1 adj2 hs1 hs2 pr.2)
    have hProbe : ∀ m d,
        ForestHead.probe (EX24.selectors c2 (mapSt s1)) pr.2 m d =
        ForestHead.probe (EX24.selectors c1 s1) pr.2 m d := by
      intro m d
      dsimp only [ForestHead.probe]
      have hLbl : (EX24.selectors c2 (mapSt s1)).label m = (EX24.selectors c1 s1).label m := rfl
      have hDep : (EX24.selectors c2 (mapSt s1)).depth = (EX24.selectors c1 s1).depth := rfl
      rw [hLbl, hDep]
      split
      · rfl
      · split
        · have hAt : (EX24.selectors c2 (mapSt s1)).atDepth = (EX24.selectors c1 s1).atDepth := rfl
          rw [hAt]
          have hRaw : ForestHead.raw (EX24.selectors c2 (mapSt s1))
              ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)
              ((EX24.selectors c2 (mapSt s1)).key
                ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)) =
            ForestHead.raw (EX24.selectors c1 s1)
              ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)
              ((EX24.selectors c1 s1).key
                ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)) := by
            funext u
            dsimp only [ForestHead.raw]
            have hKeyMem :
                ((EX24.selectors c2 (mapSt s1)).key
                    ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)).Mem u ↔
                ((EX24.selectors c1 s1).key
                    ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)).Mem u := by
              dsimp only [EX24.selectors, mapSt]
              have hGet : ∀ idx : Nat,
                  (s1.tables.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)))[idx]? =
                  (s1.tables.back[idx]?).map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)) := by
                intro idx
                rw [Array.getElem?_map]
              rw [hGet]
              generalize s1.tables.back[c1.atDepth c1.region s1.tables.mem (s1.labelAt (c1.vertexIndex m)) d]? = bk
              cases bk with
              | none =>
                change (u = c2.zeroKey.fst ∨ u = c2.zeroKey.snd) ↔ (u = c1.zeroKey.fst ∨ u = c1.zeroKey.snd)
                have ⟨hF, hS⟩ := zeroKey_same_shape N n r0 adj1 adj2 hs1 hs2 large
                change c2.zeroKey.fst = c1.zeroKey.fst at hF
                change c2.zeroKey.snd = c1.zeroKey.snd at hS
                rw [hF, hS]
              | some o =>
                cases o with
                | none =>
                  change (u = c2.zeroKey.fst ∨ u = c2.zeroKey.snd) ↔ (u = c1.zeroKey.fst ∨ u = c1.zeroKey.snd)
                  have ⟨hF, hS⟩ := zeroKey_same_shape N n r0 adj1 adj2 hs1 hs2 large
                  change c2.zeroKey.fst = c1.zeroKey.fst at hF
                  change c2.zeroKey.snd = c1.zeroKey.snd at hS
                  rw [hF, hS]
                | some q => rfl
            by_cases hm :
                ((EX24.selectors c1 s1).key
                  ((EX24.selectors c1 s1).atDepth ((EX24.selectors c1 s1).label m) d)).Mem u
            · rw [ite_eq_left hm, ite_eq_left (hKeyMem.mpr hm)]
            · rw [ite_eq_right hm, ite_eq_right (fun h => hm (hKeyMem.mp h))]
              rfl
          rw [scan_congr _ _ (fun u => congrFun hRaw u)]
        · rfl
    have hMeas :
        let m1 := ForestHead.runPrepared (EX24.selectors c1 s1) rank pr.1 pr.2
        let m2 := ForestHead.runPrepared (EX24.selectors c2 (mapSt s1)) rank pr.1 pr.2
        m2.step.parent = m1.step.parent ∧
        m2.step.newPair = m1.step.newPair.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl) ∧
        m2.step.assigned =
          match m1.step.assigned with | .existing p => .existing p | .fresh => .fresh := by
      dsimp only [ForestHead.runPrepared]
      rw [hPlan]
      cases ForestHead.planPrepared (H := H1) rank pr.1 pr.2 with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some mk =>
        dsimp only [Option.map_some, ForestHead.active, ForestHead.finish]
        have hmProbe : ForestHead.probe (EX24.selectors c2 (mapSt s1)) pr.2 mk.1 =
          ForestHead.probe (EX24.selectors c1 s1) pr.2 mk.1 := funext (hProbe mk.1)
        have hCutEq :
            (ForestHead.measuredLog (ForestHead.probe (EX24.selectors c2 (mapSt s1)) pr.2 mk.1)
              ((EX24.selectors c2 (mapSt s1)).depth ((EX24.selectors c2 (mapSt s1)).label mk.1) + 1)).cut =
            (ForestHead.measuredLog (ForestHead.probe (EX24.selectors c1 s1) pr.2 mk.1)
              ((EX24.selectors c1 s1).depth ((EX24.selectors c1 s1).label mk.1) + 1)).cut := by
          rw [hmProbe]; rfl
        have hAtEq : ∀ l c,
            (EX24.selectors c2 (mapSt s1)).atDepth l c =
            (EX24.selectors c1 s1).atDepth l c := fun _ _ => rfl
        have hLblEq :
            (EX24.selectors c2 (mapSt s1)).label mk.1 =
            (EX24.selectors c1 s1).label mk.1 := rfl
        have hNodeEq :
            ForestHead.nodeAt (EX24.selectors c2 (mapSt s1)) ((EX24.selectors c2 (mapSt s1)).label mk.1)
              (ForestHead.measuredLog (ForestHead.probe (EX24.selectors c2 (mapSt s1)) pr.2 mk.1)
                ((EX24.selectors c2 (mapSt s1)).depth ((EX24.selectors c2 (mapSt s1)).label mk.1) + 1)).cut =
            ForestHead.nodeAt (EX24.selectors c1 s1) ((EX24.selectors c1 s1).label mk.1)
              (ForestHead.measuredLog (ForestHead.probe (EX24.selectors c1 s1) pr.2 mk.1)
                ((EX24.selectors c1 s1).depth ((EX24.selectors c1 s1).label mk.1) + 1)).cut := by
          unfold ForestHead.nodeAt
          rw [hCutEq, hLblEq]
          split
          · rfl
          · exact hAtEq _ _
        refine ⟨hNodeEq, rfl, ?_⟩
        cases mk.2 with
        | none => exact congrArg ForestHead.LabelSelector.existing hNodeEq
        | some _ => rfl
    dsimp only [EX24.stepPrepared]
    by_cases hy : c1.vertexIndex pr.1 < s1.labels.size
    · have hy2 : c2.vertexIndex pr.1 < (mapSt s1).labels.size := hy
      rw [dite_eq_left hy, dite_eq_left hy2]
      let m1 := ForestHead.runPrepared (EX24.selectors c1 s1) rank pr.1 pr.2
      let m2 := ForestHead.runPrepared (EX24.selectors c2 (mapSt s1)) rank pr.1 pr.2
      have hInst :
          Option.map (fun ins : EX24.Installed H1 =>
              (ins.node, ins.tables.mem, ins.tables.slots, ins.tables.next,
                ins.tables.back.map (Option.map fun q : H1.CutPair => (q.fst.val, q.snd.val))))
            (EX24.install c1 s1.tables m1.step) =
          Option.map (fun ins : EX24.Installed H2 =>
              (ins.node, ins.tables.mem, ins.tables.slots, ins.tables.next,
                ins.tables.back.map (Option.map fun q : H2.CutPair => (q.fst.val, q.snd.val))))
            (EX24.install c2 (mapSt s1).tables
              ⟨m1.step.newPair.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl), m1.step.parent,
                match m1.step.assigned with | .existing p => .existing p | .fresh => .fresh⟩) :=
        install_same_shape N n r0 adj1 adj2 hs1 hs2 row sp1 sp2 large s1.tables m1.step
      have hmStep : m2.step =
          ⟨m1.step.newPair.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl), m1.step.parent,
            match m1.step.assigned with | .existing p => .existing p | .fresh => .fresh⟩ := by
        have hP := hMeas.1
        have hNP := hMeas.2.1
        have hAs := hMeas.2.2
        cases hm2 : m2.step with
        | mk np2 pr2 as2 =>
          rw [hm2] at hP hNP hAs
          dsimp only at hP hNP hAs
          subst hP hNP hAs
          rfl
      have hmStep' :
          (ForestHead.runPrepared (EX24.selectors c2 (mapSt s1)) rank pr.1 pr.2).step =
          ⟨m1.step.newPair.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl), m1.step.parent,
            match m1.step.assigned with | .existing p => .existing p | .fresh => .fresh⟩ := hmStep
      rw [hmStep']
      cases hi1 : EX24.install c1 s1.tables m1.step with
      | none =>
        cases hi2 : EX24.install c2 (mapSt s1).tables _ with
        | none => rfl
        | some ins2 => rw [hi1, hi2] at hInst; simp at hInst
      | some ins1 =>
        cases hi2 : EX24.install c2 (mapSt s1).tables _ with
        | none => rw [hi1, hi2] at hInst; simp at hInst
        | some ins2 =>
          rw [hi1, hi2] at hInst
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hInst
          obtain ⟨hNode, hMem, hSlots, hNext, hBack⟩ := hInst
          have hBack' : ins2.tables.back =
              ins1.tables.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)) :=
            back_eq_of_view_eq (H1 := H1) (H2 := H2) rfl rfl hBack
          have hStEq :
              (⟨ins2.tables, (mapSt s1).labels.set (c2.vertexIndex pr.1) ins2.node hy2⟩ :
                  EX24.State H2) =
              mapSt ⟨ins1.tables, s1.labels.set (c1.vertexIndex pr.1) ins1.node hy⟩ := by
            dsimp only [mapSt]
            congr 1
            · rcases hT1 : ins1.tables with ⟨m1', sl1', b1', n1'⟩
              rcases hT2 : ins2.tables with ⟨m2', sl2', b2', n2'⟩
              simp only [hT1, hT2] at hMem hSlots hNext hBack'
              simp only [hMem, hSlots, hNext, hBack']
            · rw [hNode]
              rfl
          change Option.map (fun p => stateView p.1)
              (EX24.PreparedSweep.foldRowsAux c1 rank (rest.map fun q => ⟨q.1, q.2⟩)
                { tables := ins1.tables, labels := s1.labels.set (c1.vertexIndex pr.1) ins1.node hy } _) =
            Option.map (fun p => stateView p.1)
              (EX24.PreparedSweep.foldRowsAux c2 rank (rest.map fun q => ⟨q.1, q.2⟩)
                { tables := ins2.tables, labels := (mapSt s1).labels.set (c2.vertexIndex pr.1) ins2.node hy2 } _)
          rw [hStEq]
          exact ih _ _ _
    · have hy2 : ¬ c2.vertexIndex pr.1 < (mapSt s1).labels.size := hy
      rw [dite_eq_right hy, dite_eq_right hy2]
      rfl

private theorem runOrdered_same_shape_eq (N n : Nat) (r0 : Fin n)
    (adj1 adj2 : Array (List (QuotientArc N n))) (hs1 : adj1.size = n) (hs2 : adj2.size = n)
    (row : Fin n → List (Fin n))
    (sp1 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj1, hs1⟩) y (row y))
    (sp2 : ∀ y : Fin n, ForestHead.TestSpec (H := ⟨N, n, r0, adj2, hs2⟩) y (row y))
    (data : Array (Fin n)) (hdata : data.size = n) (rank : Fin n → Nat) (large : 3 ≤ n)
    {out1 : EX24.State ⟨N, n, r0, adj1, hs1⟩} {log1 : EX24.PreparedSweep.Log ⟨N, n, r0, adj1, hs1⟩}
    {out2 : EX24.State ⟨N, n, r0, adj2, hs2⟩} {log2 : EX24.PreparedSweep.Log ⟨N, n, r0, adj2, hs2⟩}
    (hRan1 : EX24.PreparedSweep.runOrdered ⟨row, sp1⟩ data hdata rank large = some (out1, log1))
    (hRan2 : EX24.PreparedSweep.runOrdered ⟨row, sp2⟩ data hdata rank large = some (out2, log2)) :
    out2.tables.mem = out1.tables.mem ∧
    out2.tables.slots = out1.tables.slots ∧
    out2.tables.next = out1.tables.next ∧
    out2.labels = out1.labels ∧
    out2.tables.back =
      out1.tables.back.map (Option.map (mapCutPair
        (H1 := ⟨N, n, r0, adj1, hs1⟩) (H2 := ⟨N, n, r0, adj2, hs2⟩) rfl rfl)) := by
  let H1 : LabelledQuotient := ⟨N, n, r0, adj1, hs1⟩
  let H2 : LabelledQuotient := ⟨N, n, r0, adj2, hs2⟩
  let p1 : ForestDictionary.Rows H1 := ⟨row, sp1⟩
  let p2 : ForestDictionary.Rows H2 := ⟨row, sp2⟩
  let c1 := EX24.PreparedSweep.orderedConfig p1 large
  let c2 := EX24.PreparedSweep.orderedConfig p2 large
  let mapSt : EX24.State H1 → EX24.State H2 := fun s =>
    { tables := ⟨s.tables.mem, s.tables.slots,
        s.tables.back.map (Option.map (mapCutPair (H1 := H1) (H2 := H2) rfl rfl)), s.tables.next⟩
      labels := s.labels }
  let pairs : List (Fin n × List (Fin n)) :=
    List.ofFn fun i : Fin n =>
      (data[i.val]'(Nat.lt_of_lt_of_eq i.isLt hdata.symm),
       row (data[i.val]'(Nat.lt_of_lt_of_eq i.isLt hdata.symm)))
  have hRows1 : EX24.PreparedSweep.orderedRows p1 data hdata =
      pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H1) := by
    unfold EX24.PreparedSweep.orderedRows
    rw [List.map_ofFn]
    rfl
  have hRows2 : EX24.PreparedSweep.orderedRows p2 data hdata =
      pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H2) := by
    unfold EX24.PreparedSweep.orderedRows
    rw [List.map_ofFn]
    rfl
  have hDictSz : c2.dict.size = c1.dict.size :=
    congrArg Array.size (orderedConfig_dict_eq_same_shape N n r0 adj1 adj2 hs1 hs2 row sp1 sp2 large)
  have hInit : EX24.initial c2 (PaperB.Jumps.ConcreteInit.initImage n).fst n =
      mapSt (EX24.initial c1 (PaperB.Jumps.ConcreteInit.initImage n).fst n) := by
    dsimp only [EX24.initial, mapSt]
    simp only [Array.map_replicate, hDictSz]
    rfl
  have hFold := foldRowsAux_same_shape N n r0 adj1 adj2 hs1 hs2 row sp1 sp2 rank large
    pairs (EX24.initial c1 (PaperB.Jumps.ConcreteInit.initImage n).fst n) [] []
  have hr1' : EX24.PreparedSweep.foldRowsAux c1 rank
      (pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H1))
      (EX24.initial c1 (PaperB.Jumps.ConcreteInit.initImage n).fst n) [] = some (out1, log1) := by
    dsimp only [EX24.PreparedSweep.runOrdered, EX24.PreparedSweep.fromRoot,
      EX24.PreparedSweep.foldRows] at hRan1
    rw [hRows1] at hRan1
    exact hRan1
  have hr2' : EX24.PreparedSweep.foldRowsAux c2 rank
      (pairs.map fun pr => ({ head := pr.1, tests := pr.2 } : EX24.PreparedSweep.Row H2))
      (mapSt (EX24.initial c1 (PaperB.Jumps.ConcreteInit.initImage n).fst n)) [] = some (out2, log2) := by
    rw [← hInit]
    dsimp only [EX24.PreparedSweep.runOrdered, EX24.PreparedSweep.fromRoot,
      EX24.PreparedSweep.foldRows] at hRan2
    rw [hRows2] at hRan2
    exact hRan2
  rw [hr1', hr2'] at hFold
  simp only [Option.map_some, Option.some.injEq] at hFold
  have hv := hFold.symm
  unfold stateView at hv
  simp only [Prod.mk.injEq] at hv
  refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
  exact back_eq_of_view_eq (H1 := H1) (H2 := H2) rfl rfl hv.2.2.2.2.symm

private theorem rows_ext {H : LabelledQuotient} {a b : ForestDictionary.Rows H}
    (h : a.row = b.row) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

private theorem packedStaticEndpoints_eq_of_mem_eq
    (R : JumpWordRegion) {m1 m2 : Array Nat} (hm : m2 = m1)
    (h2 : ∃ F, JumpWordLayout R F m2)
    (h1 : ∃ F, JumpWordLayout R F m1) :
    (PackedStaticLayout.build (EX15.WholeScan.PackedInput.ofWords R m2 h2)).endpoints.entry.data =
      (PackedStaticLayout.build (EX15.WholeScan.PackedInput.ofWords R m1 h1)).endpoints.entry.data ∧
    (PackedStaticLayout.build (EX15.WholeScan.PackedInput.ofWords R m2 h2)).endpoints.stop.data =
      (PackedStaticLayout.build (EX15.WholeScan.PackedInput.ofWords R m1 h1)).endpoints.stop.data := by
  subst hm
  exact ⟨rfl, rfl⟩

private theorem runOrdered_cast_eq
    {H1 H2 : LabelledQuotient}
    (hV : H1.vertexCount = H2.vertexCount)
    (hOrig : H1.origVertexCount = H2.origVertexCount)
    (hR : Fin.cast hV H1.root = H2.root)
    (hAdj : Transport.ExactAdj (Fin.cast hV) hOrig)
    {p1 : ForestDictionary.Rows H1} {data1 : Array (Vertex H1)}
    {size1 : data1.size = H1.vertexCount} {rank1 : Vertex H1 → Nat} {large1 : 3 ≤ H1.vertexCount}
    [DecidableEq H1.CutPair] [DecidableEq H2.CutPair]
    (r1 : PaperB.OrderedReaderResult p1 data1 size1 rank1 large1)
    (inc1 : ∀ i j : Fin H1.vertexCount, i.val < j.val →
      rank1 (EX24.PreparedSweep.orderedVertexAt data1 size1 i) <
      rank1 (EX24.PreparedSweep.orderedVertexAt data1 size1 j))
    (cov1 : ∀ v : Vertex H1, ∃ i : Fin H1.vertexCount,
      EX24.PreparedSweep.orderedVertexAt data1 size1 i = v)
    (rArc1 : ∀ u v : Vertex H1, H1.HasQuotientArc u v → rank1 u < rank1 v)
    (flat2 : H2.IsFlat) :
    let p2 := rowsCast hV hOrig hAdj p1
    let data2 : Array (Vertex H2) := data1.map (Fin.cast hV)
    have size2 : data2.size = H2.vertexCount := by simpa [data2, hV] using size1
    let rank2 : Vertex H2 → Nat := fun v => rank1 (Fin.cast hV.symm v)
    have large2 : 3 ≤ H2.vertexCount := by rw [← hV]; exact large1
    let inc2 : ∀ i j : Fin H2.vertexCount, i.val < j.val →
        rank2 (EX24.PreparedSweep.orderedVertexAt data2 size2 i) <
        rank2 (EX24.PreparedSweep.orderedVertexAt data2 size2 j) := fun i j hij => by
      have h1 := inc1 (Fin.cast hV.symm i) (Fin.cast hV.symm j) hij
      simpa [rank2, data2, EX24.PreparedSweep.orderedVertexAt, Array.getElem_map] using h1
    let cov2 : ∀ v : Vertex H2, ∃ i : Fin H2.vertexCount,
        EX24.PreparedSweep.orderedVertexAt data2 size2 i = v := fun v => by
      obtain ⟨i, hi⟩ := cov1 (Fin.cast hV.symm v)
      refine ⟨Fin.cast hV i, ?_⟩
      have hi' : (data1[i.val]'(Nat.lt_of_lt_of_eq i.isLt size1.symm)) = Fin.cast hV.symm v := hi
      apply Fin.ext
      simpa [data2, EX24.PreparedSweep.orderedVertexAt, Array.getElem_map] using
        congrArg Fin.val hi'
    let rArc2 : ∀ u v : Vertex H2, H2.HasQuotientArc u v → rank2 u < rank2 v := fun u v huv => by
      have hu : Fin.cast hV (Fin.cast hV.symm u) = u := Fin.ext rfl
      have hv : Fin.cast hV (Fin.cast hV.symm v) = v := Fin.ext rfl
      have hArc := (Transport.arc_iff (Fin.cast hV) hOrig hAdj
        (Fin.cast hV.symm u) (Fin.cast hV.symm v)).mpr (by simpa [hu, hv] using huv)
      exact rArc1 _ _ hArc
    let r2 := runOrderedReaderFast p2 data2 size2 rank2 large2 inc2 cov2 rArc2 flat2
    r2.out.tables.mem = r1.out.tables.mem ∧
    r2.out.tables.slots = r1.out.tables.slots ∧
    r2.out.tables.next = r1.out.tables.next ∧
    r2.out.labels = r1.out.labels ∧
    (EX24.PreparedSweep.orderedConfig p2 large2).dict =
      (EX24.PreparedSweep.orderedConfig p1 large1).dict ∧
    r2.out.tables.back.size = r1.out.tables.back.size ∧
    (∀ (j : Nat) (P : H2.CutPair),
      r2.out.tables.back[j]? = some (some P) ↔
        r1.out.tables.back[j]? = some (some
          (mapCutPair hV.symm (Fin.ext (by simpa using (congrArg Fin.val hR).symm)) P))) ∧
    (∀ a v, (ofOrderedReader r2).known a v = (ofOrderedReader r1).known a v) ∧
    (∀ (P : H2.CutPair),
      checkedHit r2 P =
        checkedHit r1 (mapCutPair hV.symm (Fin.ext (by simpa using (congrArg Fin.val hR).symm)) P)) ∧
    r2.index.reader.layout.endpoints.entry.data = r1.index.reader.layout.endpoints.entry.data ∧
    r2.index.reader.layout.endpoints.stop.data = r1.index.reader.layout.endpoints.stop.data := by
  intro p2 data2 size2 rank2 large2 inc2 cov2 rArc2 r2
  rcases H1 with ⟨N1, n1, r1₀, adj1, hs1⟩
  rcases H2 with ⟨N2, n2, r2₀, adj2, hs2⟩
  dsimp only at hOrig hV
  subst hOrig
  subst hV
  have hR' : r1₀ = r2₀ := Fin.ext (by simpa using congrArg Fin.val hR)
  subst hR'
  have hData : data2 = data1 := by
    apply Array.ext
    · simp [data2]
    · intro i hi2 hi1
      simp [data2]
  have hRow : p2.row = p1.row := by
    funext y
    change (p1.row y).map id = p1.row y
    simp
  have hRank : rank2 = rank1 := rfl
  let p1' : ForestDictionary.Rows ⟨N1, n1, r1₀, adj1, hs1⟩ := ⟨p1.row, p1.spec⟩
  let p2' : ForestDictionary.Rows ⟨N1, n1, r1₀, adj2, hs2⟩ := ⟨p1.row, by rw [← hRow]; exact p2.spec⟩
  have hDict : (EX24.PreparedSweep.orderedConfig p2' large2).dict =
      (EX24.PreparedSweep.orderedConfig p1' large1).dict :=
    orderedConfig_dict_eq_same_shape N1 n1 r1₀ adj1 adj2 hs1 hs2 p1.row p1.spec p2'.spec large1
  have hp2 : p2 = p2' := rows_ext hRow
  have hp1 : p1 = p1' := rows_ext rfl
  have hDict' : (EX24.PreparedSweep.orderedConfig p2 large2).dict =
      (EX24.PreparedSweep.orderedConfig p1 large1).dict := by
    rw [hp2, hp1]
    exact hDict
  have hRan1' : EX24.PreparedSweep.runOrdered p1' data1 size1 rank1 large1 = some (r1.out, r1.log) :=
    r1.ran
  have hRan2' : EX24.PreparedSweep.runOrdered p2' data1 size1 rank1 large1 = some (r2.out, r2.log) := by
    simpa only [hp2, hData, hRank] using r2.ran
  obtain ⟨hMem, hSlots, hNext, hLabels, hBack⟩ :=
    runOrdered_same_shape_eq N1 n1 r1₀ adj1 adj2 hs1 hs2 p1.row p1.spec p2'.spec data1 size1 rank1 large1
      hRan1' hRan2'
  have hBackSz : r2.out.tables.back.size = r1.out.tables.back.size := by
    rw [hBack]; simp
  have hBackIff : ∀ (j : Nat) (P : LabelledQuotient.CutPair ⟨N1, n1, r1₀, adj2, hs2⟩),
      r2.out.tables.back[j]? = some (some P) ↔
        r1.out.tables.back[j]? = some (some
          (@mapCutPair ⟨N1, n1, r1₀, adj2, hs2⟩ ⟨N1, n1, r1₀, adj1, hs1⟩ rfl rfl P)) := by
    intro j P
    rw [hBack, Array.getElem?_map]
    cases r1.out.tables.back[j]? with
    | none => simp
    | some opt =>
      cases opt with
      | none => simp
      | some Q =>
        simp only [Option.map_some, Option.some.injEq]
        constructor
        · intro hEq
          cases Q; cases P
          simp only [mapCutPair, CutPair.mk.injEq, Fin.ext_iff] at hEq ⊢
          exact ⟨hEq.1, hEq.2⟩
        · intro hEq
          cases Q; cases P
          simp only [mapCutPair, CutPair.mk.injEq, Fin.ext_iff] at hEq ⊢
          exact ⟨hEq.1, hEq.2⟩
  have hEndpoints :
      r2.index.reader.layout.endpoints.entry.data = r1.index.reader.layout.endpoints.entry.data ∧
      r2.index.reader.layout.endpoints.stop.data = r1.index.reader.layout.endpoints.stop.data := by
    rw [r2.index.reader.layout_exact, r1.index.reader.layout_exact]
    have hl2 : ∃ F, JumpWordLayout (PaperB.Jumps.ConcreteInit.region n1) F r2.out.tables.mem := by
      obtain ⟨F, _, G, _, _⟩ := r2.index.ok.2.2; exact ⟨F, G.layout⟩
    have hl1 : ∃ F, JumpWordLayout (PaperB.Jumps.ConcreteInit.region n1) F r1.out.tables.mem := by
      obtain ⟨F, _, G, _, _⟩ := r1.index.ok.2.2; exact ⟨F, G.layout⟩
    exact packedStaticEndpoints_eq_of_mem_eq (PaperB.Jumps.ConcreteInit.region n1) hMem hl2 hl1
  have hKnown : ∀ a v, (ofOrderedReader r2).known a v = (ofOrderedReader r1).known a v := by
    intro a v
    dsimp only [ofOrderedReader, RetainedProperLoss.Columns.known, RetainedProperLoss.Columns.labelAt]
    rw [hLabels, hEndpoints.1, hEndpoints.2]
    rfl
  have hHit : ∀ P : LabelledQuotient.CutPair ⟨N1, n1, r1₀, adj2, hs2⟩,
      checkedHit r2 P = checkedHit r1
        (@mapCutPair ⟨N1, n1, r1₀, adj2, hs2⟩ ⟨N1, n1, r1₀, adj1, hs1⟩ rfl rfl P) := by
    intro P
    cases hc2 : checkedHit r2 P with
    | none =>
      cases hc1 : checkedHit r1
          (@mapCutPair ⟨N1, n1, r1₀, adj2, hs2⟩ ⟨N1, n1, r1₀, adj1, hs1⟩ rfl rfl P) with
      | none => rfl
      | some a =>
        have hb1 := (checked_iff_back r1 _ a).mp hc1
        have hb2 := (hBackIff a P).mpr hb1
        have hc2' := (checked_iff_back r2 P a).mpr hb2
        simp only [checkedHit] at hc2 hc2'
        rw [hc2] at hc2'; cases hc2'
    | some a =>
      symm
      exact (checked_iff_back r1 _ a).mpr ((hBackIff a P).mp ((checked_iff_back r2 P a).mp hc2))
  exact ⟨hMem, hSlots, hNext, hLabels, hDict', hBackSz, hBackIff, hKnown, hHit,
    hEndpoints.1, hEndpoints.2⟩

/-- Word-RAM sealed owner record witness expressed natively over `S.ramQuotient d`,
matching `RamFamilyForestLoop` (`WordColumns`), `OrderedReaderResult`, and
`ExitMap.JumpMapRoute.StoredExit` (`Occupied` / `Placed` / `PriorBase.run`). -/
structure RamQuotientOwnerRecord {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (I : Array (Word bits)) {n qCount : Nat}
    (Hdr : StaticHeaderSpec I n qCount) (d : Fin dense.length) : Type where
  nD : Nat
  nD_eq : nD = (S.ramQuotient d).vertexCount
  dictPtr : Nat
  backFstPtr : Nat
  backSndPtr : Nat
  labelsPtr : Nat
  fEntryPtr : Nat
  fStopPtr : Nat
  exitDepthPtr : Nat
  exitStoredPtr : Nat
  exitPriorPtr : Nat
  descBase : Nat
  descBase_val : descBase = Hdr.ownerDescBase + ownerDescStride * d.val
  descFits : descBase + ownerDescStride ≤ I.size
  hDescN : (I[descBase + descN]?).map Fin.val = some nD
  hDescDict : (I[descBase + descDict]?).map Fin.val = some dictPtr
  hDescBackFst : (I[descBase + descBackFst]?).map Fin.val = some backFstPtr
  hDescBackSnd : (I[descBase + descBackSnd]?).map Fin.val = some backSndPtr
  hDescLabels : (I[descBase + descLabels]?).map Fin.val = some labelsPtr
  hDescFEntry : (I[descBase + descFEntry]?).map Fin.val = some fEntryPtr
  hDescFStop : (I[descBase + descFStop]?).map Fin.val = some fStopPtr
  hDescExitDepth : (I[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr
  hDescExitStored : (I[descBase + descExitStored]?).map Fin.val = some exitStoredPtr
  hDescExitPrior : (I[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr
  large_spec :
    let H := S.ramQuotient d
    ∀ (large : 3 ≤ H.vertexCount),
      ∃ (pH : ForestDictionary.Rows H)
        (dataH : Array (Vertex H)) (sizeH : dataH.size = H.vertexCount) (rankH : Vertex H → Nat)
        (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH large)
        (wCols : WordColumns bits) (endpoints : Nat)
        (R : Region bits I.size) (F : JumpForest) (ref : Nat → ExitMap.CheckedFold.Stored)
        (wFit : Width bits (max R.slots endpoints))
        (_ok : Occupied I R F ref wFit)
        (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
        (B : BaseView prior.size I.size) (_hPlaced : Placed wFit prior hb I B),
        (∀ i j : Fin H.vertexCount, i.val < j.val →
          rankH (EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
          rankH (EX24.PreparedSweep.orderedVertexAt dataH sizeH j)) ∧
        (∀ v : Vertex H, ∃ i : Fin H.vertexCount,
          EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v) ∧
        (∀ u v : Vertex H, H.HasQuotientArc u v → rankH u < rankH v) ∧
        SliceAt I dictPtr wCols.dictionary ∧
        FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordResH) ∧
        SliceAt I backFstPtr wCols.back.tagAndFirst ∧
        SliceAt I backSndPtr wCols.back.second ∧
        SliceAt I labelsPtr wCols.labels ∧
        SliceAt I fEntryPtr wCols.entry ∧
        SliceAt I fStopPtr wCols.stop ∧
        wCols.labels.size = H.vertexCount ∧
        wCols.entry.size = wCols.stop.size ∧
        wCols.back.tagAndFirst.size = wCols.back.second.size ∧
        (∀ a v, wCols.known a v = (ofOrderedReader ordResH).known a v) ∧
        (∀ j (P : CutPair H),
          wCols.back.read j = some (encodeBackPair (some P)) ↔
            (ofOrderedReader ordResH).back[j]? = some (some P)) ∧
        (∀ v : Vertex H, (EX24.PreparedSweep.orderedConfig pH large).vertexIndex v = v.val) ∧
        (∀ y : Fin H.vertexCount, wCols.labelAt y.val < F.size ∧ wCols.labelAt y.val < wCols.entry.size) ∧
        (∀ (P : CutPair H), P.fst < P.snd → ∀ aNode : Nat, checkedHit ordResH P = some aNode →
          aNode < wCols.entry.size ∧ aNode < wCols.stop.size ∧
          aNode < F.size ∧ aNode < wCols.back.tagAndFirst.size ∧
          aNode < wCols.back.second.size) ∧
        prior.size = H.vertexCount ∧
        R.base.val = exitStoredPtr ∧
        B.start = exitPriorPtr ∧
        (∀ x : Fin R.slots, (R.depthAddr x).val = exitDepthPtr + x.val) ∧
        (∀ (P : CutPair H), P.fst < P.snd → ∀ aNode : Nat, checkedHit ordResH P = some aNode →
          ∀ y : Vertex H, H.ProperLoss P y →
            let u := wCols.labelAt y.val
            let dDepth := depthAt I R aNode
            (foldStored I R wFit.tags u dDepth).steps ≤ 3 * ceilLog2 (g.vertexCount + 2) ∧
            ∀ hPrior : y.val < prior.size,
              (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x0 =
                ExitSummary.summary
                  ((lemma22ExitTails H P P.fst y).map (denseRank S)) ∧
              (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x1 =
                ExitSummary.summary
                  ((lemma22ExitTails H P P.snd y).map (denseRank S)))

/-- Transport a `RamQuotientOwnerRecord` on `S.ramQuotient d` to a
`SealedOwnerRecord` on `ActualOnlineOracle.denseQuotient` (handling both
`n_d < 3` and `3 ≤ n_d`). -/
noncomputable def RamQuotientOwnerRecord.toSealedOwnerRecord
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S)
    {I : Array (Word bits)} {Hdr : StaticHeaderSpec I g.vertexCount B.q.count}
    {d : Fin dense.length} (rec : RamQuotientOwnerRecord S I Hdr d) :
    SealedOwnerRecord B.progress B.injRank B.q B.originalRows B.hRows B.rows B.childOK I Hdr
      (Fin.cast B.count_eq.symm d) :=
  let d' : Fin B.q.count := Fin.cast B.count_eq.symm d
  let H := S.ramQuotient d
  let K := denseQuotient B.progress B.injRank B.q B.originalRows B.hRows B.rows B.childOK d'
  have hV : H.vertexCount = K.vertexCount := by
    have h1 : H.vertexCount = 1 + (S.childSlice d).length := rfl
    have h2 : K.vertexCount = B.rows.length d' := rfl
    rw [h1, h2, B.rows.length_exact d', B.buckets_eq d, List.length_map]
    omega
  have hRoot : Fin.cast hV H.root = K.root := by
    apply Fin.ext
    have hHr : H.root.val = 0 := rfl
    have hKr : K.root.val = 0 := rfl
    simp [hHr, hKr]
  have hAdj : Transport.ExactAdj (Fin.cast hV) (rfl : H.origVertexCount = K.origVertexCount) := by
    intro u v x
    exact B.matchesReader.mem_outArcs_denseQuotient_iff B.progress B.injRank B.originalRows B.hRows
      B.rows B.childOK B.buckets_eq d u ⟨v, x⟩
  { nD := rec.nD
    nD_eq := rec.nD_eq.trans hV
    dictPtr := rec.dictPtr
    backFstPtr := rec.backFstPtr
    backSndPtr := rec.backSndPtr
    labelsPtr := rec.labelsPtr
    fEntryPtr := rec.fEntryPtr
    fStopPtr := rec.fStopPtr
    exitDepthPtr := rec.exitDepthPtr
    exitStoredPtr := rec.exitStoredPtr
    exitPriorPtr := rec.exitPriorPtr
    descBase := rec.descBase
    descBase_val := by simpa [d'] using rec.descBase_val
    descFits := rec.descFits
    hDescN := rec.hDescN
    hDescDict := rec.hDescDict
    hDescBackFst := rec.hDescBackFst
    hDescBackSnd := rec.hDescBackSnd
    hDescLabels := rec.hDescLabels
    hDescFEntry := rec.hDescFEntry
    hDescFStop := rec.hDescFStop
    hDescExitDepth := rec.hDescExitDepth
    hDescExitStored := rec.hDescExitStored
    hDescExitPrior := rec.hDescExitPrior
    large_spec := fun largeK => by
      have largeH : 3 ≤ H.vertexCount := hV ▸ largeK
      rcases rec.large_spec largeH with
        ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R, F, ref, wFit, ok,
          prior, hb, BV, hPlaced, incH, covH, rArcH, hDictSlice, hRepH, hBackFst, hBackSnd,
          hLabels, hFEntry, hFStop, hLabelsSz, hEntryStopSz, hBackSz, hKnownEqH, hBackReadH,
          hVIdxH, hLabBoundsH, hHitBoundsH, hPriorSzH, hRBase, hBStart, hDepthContig, hExitSpecH⟩
      let pK := rowsCast hV rfl hAdj pH
      let dataK : Array (Vertex K) := dataH.map (Fin.cast hV)
      have sizeK : dataK.size = K.vertexCount := by
        simp only [dataK, Array.size_map]
        rw [← hV]
        exact sizeH
      let rankK : Vertex K → Nat := fun v => rankH (Fin.cast hV.symm v)
      let incK : ∀ i j : Fin K.vertexCount, i.val < j.val →
          rankK (EX24.PreparedSweep.orderedVertexAt dataK sizeK i) <
          rankK (EX24.PreparedSweep.orderedVertexAt dataK sizeK j) := fun i j hij => by
        have h1 := incH (Fin.cast hV.symm i) (Fin.cast hV.symm j) hij
        simpa [rankK, dataK, EX24.PreparedSweep.orderedVertexAt, Array.getElem_map] using h1
      let covK : ∀ v : Vertex K, ∃ i : Fin K.vertexCount,
          EX24.PreparedSweep.orderedVertexAt dataK sizeK i = v := fun v => by
        obtain ⟨i, hi⟩ := covH (Fin.cast hV.symm v)
        refine ⟨Fin.cast hV i, ?_⟩
        apply Fin.ext
        simpa [dataK, EX24.PreparedSweep.orderedVertexAt, Array.getElem_map] using
          congrArg Fin.val hi
      let rArcK : ∀ u v : Vertex K, K.HasQuotientArc u v → rankK u < rankK v := fun u v huv => by
        have hu : Fin.cast hV (Fin.cast hV.symm u) = u := Fin.ext rfl
        have hv : Fin.cast hV (Fin.cast hV.symm v) = v := Fin.ext rfl
        have hArc := (Transport.arc_iff (Fin.cast hV) rfl hAdj
          (Fin.cast hV.symm u) (Fin.cast hV.symm v)).mpr (by simpa [hu, hv] using huv)
        exact rArcH _ _ hArc
      let ordResK : PaperB.OrderedReaderResult pK dataK sizeK rankK largeK :=
        runOrderedReaderFast pK dataK sizeK rankK largeK incK covK rArcK (B.denseQuotient_isFlat d')
      obtain ⟨hMem, hSlots, hNext, hLabelsEq, hDictEq, hBackSizeEq, hBackIff,
          hKnown, hHit, hEntData, hStopData⟩ :=
        runOrdered_cast_eq hV rfl hRoot hAdj ordResH incH covH rArcH (B.denseQuotient_isFlat d')
      let backCut : CutPair K → CutPair H :=
        mapCutPair hV.symm (Fin.ext (by simpa using (congrArg Fin.val hRoot).symm))
      have hDictEq' : (ofOrderedReader ordResK).dict = (ofOrderedReader ordResH).dict := by
        dsimp [ofOrderedReader]; rw [hDictEq]
      have hSlots' : (ofOrderedReader ordResK).slots = (ofOrderedReader ordResH).slots := by
        dsimp [ofOrderedReader]; rw [hSlots]
      have hRepK : FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordResK) := by
        refine
          { valid := hRepH.valid
            rows := hRepH.rows.trans (by rw [hDictEq'])
            slot_len := hRepH.slot_len.trans (by rw [hSlots'])
            first_eq := fun j hj1 hj2 => by
              have hj2' : j < (ofOrderedReader ordResH).dict.size := by
                rw [← hDictEq']; exact hj2
              refine (hRepH.first_eq j hj1 hj2').trans ?_
              simp only [hDictEq']
            second_eq := fun j hj1 hj2 => by
              have hj2' : j < (ofOrderedReader ordResH).dict.size := by
                rw [← hDictEq']; exact hj2
              refine (hRepH.second_eq j hj1 hj2').trans ?_
              simp only [hDictEq']
            slot_eq := fun j hj1 hj2 => by
              have hj2' : j < (ofOrderedReader ordResH).slots.size := by
                rw [← hSlots']; exact hj2
              refine (hRepH.slot_eq j hj1 hj2').trans ?_
              simp only [hSlots'] }
      have hVIdxK : ∀ v : Vertex K, (EX24.PreparedSweep.orderedConfig pK largeK).vertexIndex v = v.val :=
        fun _ => rfl
      refine ⟨pK, dataK, sizeK, rankK, ordResK, wCols, endpoints, R, F, ref, wFit, ok,
        prior, hb, BV, hPlaced, hDictSlice, hRepK, hBackFst, hBackSnd, hLabels, hFEntry, hFStop,
        hLabelsSz.trans hV, hEntryStopSz, hBackSz, ?_, ?_, hVIdxK, ?_, ?_, hPriorSzH.trans hV,
        hRBase, hBStart, hDepthContig, ?_⟩
      · intro a v
        rw [hKnown a v, hKnownEqH a v]
      · intro j P
        rw [show encodeBackPair (some P) = encodeBackPair (some (backCut P)) by cases P; rfl,
          hBackReadH j (backCut P)]
        exact (hBackIff j P).symm
      · intro y
        exact hLabBoundsH (Fin.cast hV.symm y)
      · intro P hLt aNode hCh
        have hLt' : (backCut P).fst < (backCut P).snd := hLt
        have hCh' : checkedHit ordResH (backCut P) = some aNode := (hHit P).symm.trans hCh
        exact hHitBoundsH (backCut P) hLt' aNode hCh'
      · intro P hLt aNode hCh yK hProper
        have hLt' : (backCut P).fst < (backCut P).snd := hLt
        have hCh' : checkedHit ordResH (backCut P) = some aNode := (hHit P).symm.trans hCh
        let yH : Vertex H := Fin.cast hV.symm yK
        have hProperH : H.ProperLoss (backCut P) yH := by
          have hP : P = Transport.cutPair (Fin.cast hV) (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
              hRoot (backCut P) := by
            cases P; rfl
          have hY : yK = Fin.cast hV yH := Fin.ext rfl
          exact (Transport.properLoss_iff (Fin.cast hV)
            (fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)) hRoot
            (fun v => ⟨Fin.cast hV.symm v, Fin.ext rfl⟩) rfl hAdj (backCut P) yH).mpr
            (by simpa only [← hP, ← hY] using hProper)
        obtain ⟨hSteps, hRun⟩ := hExitSpecH (backCut P) hLt' aNode hCh' yH hProperH
        refine ⟨hSteps, fun hPriorK => ?_⟩
        have hPriorH : yH.val < prior.size := hPriorK
        obtain ⟨hx0, hx1⟩ := hRun hPriorH
        have hInj : ∀ ⦃u v : Fin H.vertexCount⦄, Fin.cast hV u = Fin.cast hV v → u = v :=
          fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)
        have hSurj : ∀ v : Fin K.vertexCount, ∃ u : Fin H.vertexCount, Fin.cast hV u = v :=
          fun v => ⟨Fin.cast hV.symm v, Fin.ext rfl⟩
        have hCut : P = Transport.cutPair (Fin.cast hV) hInj hRoot (backCut P) := by
          cases P; rfl
        have hY : yK = Fin.cast hV yH := Fin.ext rfl
        have hMemFst : ∀ v : Fin g.vertexCount,
            K.ExitTailMem P P.fst yK v ↔ H.ExitTailMem (backCut P) (backCut P).fst yH v := by
          intro v
          rw [hCut, hY]
          exact (Transport.exitTailMem_iff (Fin.cast hV) hInj hRoot hSurj rfl hAdj
            (backCut P) (backCut P).fst yH v).symm
        have hMemSnd : ∀ v : Fin g.vertexCount,
            K.ExitTailMem P P.snd yK v ↔ H.ExitTailMem (backCut P) (backCut P).snd yH v := by
          intro v
          rw [hCut, hY]
          exact (Transport.exitTailMem_iff (Fin.cast hV) hInj hRoot hSurj rfl hAdj
            (backCut P) (backCut P).snd yH v).symm
        have hMapFst : ∀ rk,
            rk ∈ (lemma22ExitTails K P P.fst yK).map (fun v => (OriginalEntryInverse.originalRank B.q v).getD 0) ↔
              rk ∈ (lemma22ExitTails H (backCut P) (backCut P).fst yH).map (denseRank S) := by
          intro rk
          constructor
          · intro hMem
            rcases List.mem_map.mp hMem with ⟨v, hv, hrk⟩
            have hv1 : K.ExitTailMem P P.fst yK v := (mem_lemma22ExitTails (H := K)).mp hv
            have hv2 : H.ExitTailMem (backCut P) (backCut P).fst yH v := (hMemFst v).mp hv1
            refine List.mem_map.mpr ⟨v, (mem_lemma22ExitTails (H := H)).mpr hv2, ?_⟩
            rw [← hrk]
            exact (B.originalRank_eq_denseRank v).symm
          · intro hMem
            rcases List.mem_map.mp hMem with ⟨v, hv, hrk⟩
            have hv2 : H.ExitTailMem (backCut P) (backCut P).fst yH v := (mem_lemma22ExitTails (H := H)).mp hv
            have hv1 : K.ExitTailMem P P.fst yK v := (hMemFst v).mpr hv2
            refine List.mem_map.mpr ⟨v, (mem_lemma22ExitTails (H := K)).mpr hv1, ?_⟩
            rw [← hrk]
            exact B.originalRank_eq_denseRank v
        have hMapSnd : ∀ rk,
            rk ∈ (lemma22ExitTails K P P.snd yK).map (fun v => (OriginalEntryInverse.originalRank B.q v).getD 0) ↔
              rk ∈ (lemma22ExitTails H (backCut P) (backCut P).snd yH).map (denseRank S) := by
          intro rk
          constructor
          · intro hMem
            rcases List.mem_map.mp hMem with ⟨v, hv, hrk⟩
            have hv1 : K.ExitTailMem P P.snd yK v := (mem_lemma22ExitTails (H := K)).mp hv
            have hv2 : H.ExitTailMem (backCut P) (backCut P).snd yH v := (hMemSnd v).mp hv1
            refine List.mem_map.mpr ⟨v, (mem_lemma22ExitTails (H := H)).mpr hv2, ?_⟩
            rw [← hrk]
            exact (B.originalRank_eq_denseRank v).symm
          · intro hMem
            rcases List.mem_map.mp hMem with ⟨v, hv, hrk⟩
            have hv2 : H.ExitTailMem (backCut P) (backCut P).snd yH v := (mem_lemma22ExitTails (H := H)).mp hv
            have hv1 : K.ExitTailMem P P.snd yK v := (hMemSnd v).mpr hv2
            refine List.mem_map.mpr ⟨v, (mem_lemma22ExitTails (H := K)).mpr hv1, ?_⟩
            rw [← hrk]
            exact B.originalRank_eq_denseRank v
        refine ⟨?_, ?_⟩
        · change (PriorBase.run I R wFit.tags prior ⟨yH.val, hPriorH⟩ (wCols.labelAt yH.val)
              (depthAt I R aNode)).x0 = _
          rw [hx0]
          exact (summary_eq_of_mem_iff hMapFst).symm
        · change (PriorBase.run I R wFit.tags prior ⟨yH.val, hPriorH⟩ (wCols.labelAt yH.val)
              (depthAt I R aNode)).x1 = _
          rw [hx1]
          exact (summary_eq_of_mem_iff hMapSnd).symm }

/-- End-to-end assembly of `ValidSealedOracleIndex g r I` from a `StaticReaderBridge`,
header data `StaticTreeSliceHeaderData`, and per-owner `RamQuotientOwnerRecord` witnesses. -/
theorem StaticReaderBridge.validSealedOracleIndex
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hLen : order.length = g.vertexCount} {hTopo : g.IsTopologicalList order}
    {dense : List (Fin g.vertexCount)} {S : StaticTreeSlice mem treeBase g r dense}
    (B : StaticReaderBridge g r order hLen hTopo S)
    {I : Array (Word bits)}
    (hTag : TagsFit bits) (hWork : queryWorkCap ≤ 2 ^ bits)
    (Hdr : StaticHeaderSpec I g.vertexCount B.q.count)
    (hData : StaticTreeSliceHeaderData S I Hdr)
    (hRecs : ∀ d : Fin dense.length, Nonempty (RamQuotientOwnerRecord S I Hdr d)) :
    ValidSealedOracleIndex g r I := by
  refine ⟨hTag, hWork, B.rank, B.progress, B.injRank, B.q, B.originalRows, B.hRows,
    B.buckets, B.rows, B.childOK, B.inv, Hdr, B.root_eq, B.root_size_le, ?_, ?_⟩
  · intro d
    exact ⟨B.ranges_ids d, B.ranges_valid d⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := B.headerAgreement Hdr hData
    refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9, ?_⟩
    · refine ⟨h4.1, fun j hj => ?_⟩
      have hjEq := h4.2 j hj
      dsimp only at hjEq ⊢
      rw [dite_eq_left hj] at hjEq ⊢
      rw [hjEq]
      congr 1
      cases B.q.ids.find ⟨j, hj⟩ <;> rfl
    intro d'
    let d : Fin dense.length := Fin.cast B.count_eq d'
    obtain ⟨rec⟩ := hRecs d
    have hCast : d' = Fin.cast B.count_eq.symm d := Fin.ext rfl
    rw [hCast]
    exact ⟨rec.toSealedOwnerRecord B⟩

end QuotientTransport

end PaperB.RamStaticReaderBridge
