module

public import PaperB.ExitActualInputsBuild
public import PaperB.ExitSealedBase
public import PaperB.ExitCountedBase
public import PaperB.ExitSweepWorkSum
public import PaperB.SmallQuotient
public import PaperB.OracleContract
public import PaperB.ForestBuildPackedWords

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX4.2 + EX4.3 end-to-end contract for the packed exit-map forest over raw
quotient inputs (`LabelledQuotient`).

Exports:
1. `ActualSealedContract` & `buildActualSealedContract`: builds `ActualBuiltBank`,
   certifies `SealedPriorBase.BaseBound`, and seals `built.bases.data` into
   `6 * H.vertexCount` words via `SealedPriorBase.serialize`.
2. `actualBuildWork_bound` & `actualBuildWork_v12_bound`: EX4.2+EX4.3 build cost
   `≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount`
   (`O((n_H + m_H) * L)`), working space `O(n_H + m_H)`, and retained words
   `≤ 25 * H.vertexCount + 19 ≤ 44 * H.vertexCount + 19` (`O(n_H)`).
3. `query_canonical_exact`, `query_exact`, `query_v12_bound`: EX4.3 query theorem
   showing `SealedPriorBase.run` recovers `built.model.ref B y` in
   `≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ≤ 60 * OracleContract.L H.vertexCount + 3`
   word jumps/reads (`O(L)`) plus `6` sealed base reads.
4. `small_quotient_vacuous`: handles `H.vertexCount < 3` via
   `SmallQuotient.cutPair_impossible_of_small`.
5. `nonvacuous_diamond_contract`: concrete 4-vertex flat acyclic diamond quotient
   instantiating `ActualSealedContract`, witnessing non-vacuous `LiveStoreOK`,
   `ActualBuiltBank`, and `SealedPriorBase.run` query equality.
-/

namespace PaperB.ExitActualContract

open PaperB PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open _root_.EX24.PreparedSweep
open PaperB.ExitMap PaperB.ExitSummary
open PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.BuiltExit
open PaperB.ExitMap.JumpMapRoute PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.BuiltExit.PackedRuntime.ExactCount
open PaperB.EX24.InputPrepCheckpoint
open PaperB.Exit.OrderedReaderResult

section Helpers

theorem ceilLog2_add_two_le_L (n : Nat) :
    ceilLog2 (n + 2) ≤ OracleContract.L n := by
  apply ceilLog2_le_of_pow2_ge
  have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hlt : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) :=
    (Nat.log2_lt hn).mp (Nat.lt_succ_self (Nat.log2 (n + 1)))
  change n + 2 ≤ 2 ^ (Nat.log2 (n + 1) + 1)
  omega

theorem L_le_pow_three (n : Nat) :
    OracleContract.L n ≤ OracleContract.L n ^ 3 := by
  have h1 : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have h2 : OracleContract.L n ≤ OracleContract.L n * OracleContract.L n := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left (OracleContract.L n) h1
  have h3 : OracleContract.L n * OracleContract.L n ≤
      OracleContract.L n * (OracleContract.L n * OracleContract.L n) :=
    Nat.mul_le_mul_left (OracleContract.L n) h2
  calc
    OracleContract.L n ≤ OracleContract.L n * OracleContract.L n := h2
    _ ≤ OracleContract.L n * (OracleContract.L n * OracleContract.L n) := h3
    _ = OracleContract.L n ^ 3 := by
      simp [Nat.pow_succ, Nat.mul_assoc]

private theorem rankBound_summary_contract {limit : Nat} (xs : List Nat)
    (h : ∀ k ∈ xs, k < limit) : RankBound limit (ExitSummary.summary xs) := by
  induction xs with
  | nil => simp [ExitSummary.summary, RankBound]
  | cons k ks ih =>
    have h0 : k < limit := h k (by simp)
    have h1 : RankBound limit (ExitSummary.summary ks) :=
      ih (fun x hx => h x (by simp [hx]))
    have hs : RankBound limit (ExitSummary.singleton k) := ⟨h0, h0⟩
    simpa [ExitSummary.summary] using rankBound_join hs h1

private theorem rankBound_ref_contract {H : LabelledQuotient} {m endpoints : Nat}
    (W : BuiltExit.Model H m)
    (hRank : ∀ x : Fin H.origVertexCount, W.rank x < endpoints)
    (Bcut : CutPair H) (y : Vertex H) (j : Fin 2) :
    RankBound endpoints (Two.get (W.ref Bcut y) j) := by
  rw [Model.ref, BuiltExit.get_tab]
  refine rankBound_summary_contract _ ?_
  intro k hk
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hk
  exact hRank x

private theorem rankBound_wantBase_contract {H : LabelledQuotient} {m endpoints : Nat}
    (W : BuiltExit.Model H m)
    (hRank : ∀ x : Fin H.origVertexCount, W.rank x < endpoints)
    (y : Vertex H) :
    RankBound endpoints (W.wantBase y).x0 ∧ RankBound endpoints (W.wantBase y).x1 := by
  unfold Model.wantBase
  cases hOwn : W.owner y with
  | none =>
    change RankBound endpoints BuiltExit.zero.x0 ∧ RankBound endpoints BuiltExit.zero.x1
    exact ⟨trivial, trivial⟩
  | some Bcut =>
    change RankBound endpoints (W.ref Bcut y).x0 ∧ RankBound endpoints (W.ref Bcut y).x1
    exact ⟨rankBound_ref_contract W hRank Bcut y 0, rankBound_ref_contract W hRank Bcut y 1⟩

private theorem interval_test_ext {a b : Interval}
    (e : ∀ l h, Test l h a ↔ Test l h b) : a = b := by
  cases a with
  | empty =>
    cases b with
    | empty => rfl
    | span bl bh =>
      obtain ⟨bad, _⟩ :=
        (endpointsInside_span_iff (bl + 1) (bh + 1) bl bh).mp
          ((e (bl + 1) (bh + 1)).mp True.intro)
      omega
  | span al ah =>
    cases b with
    | empty =>
      obtain ⟨bad, _⟩ :=
        (endpointsInside_span_iff (al + 1) (ah + 1) al ah).mp
          ((e (al + 1) (ah + 1)).mpr True.intro)
      omega
    | span bl bh =>
      have ha : Test al (ah + 1) (.span al ah) :=
        (endpointsInside_span_iff al (ah + 1) al ah).mpr ⟨Nat.le_refl _, by omega⟩
      have hb : Test bl (bh + 1) (.span bl bh) :=
        (endpointsInside_span_iff bl (bh + 1) bl bh).mpr ⟨Nat.le_refl _, by omega⟩
      obtain ⟨hl₁, hh₁⟩ :=
        (endpointsInside_span_iff al (ah + 1) bl bh).mp ((e al (ah + 1)).mp ha)
      obtain ⟨hl₂, hh₂⟩ :=
        (endpointsInside_span_iff bl (bh + 1) al ah).mp ((e bl (bh + 1)).mpr hb)
      have el : al = bl := by omega
      have eh : ah = bh := by omega
      rw [el, eh]

private theorem parentPath_rank_le {read : Store} {rank : Nat → Nat}
    {u a : Nat} {m : Map} (hp : ParentPath read rank u a m) :
    rank a ≤ rank u := by
  induction hp with
  | nil _ => exact Nat.le_refl _
  | cons _ down _ ih => exact Nat.le_trans ih (Nat.le_of_lt down)

private theorem model_ref_canonical_swap {H : LabelledQuotient} {m : Nat}
    (W : BuiltExit.Model H m)
    (hEnds : ∀ (C : CutPair H) (j : Fin 2), W.endpoint C j = if j = 0 then C.fst else C.snd)
    (B : CutPair H) (hNotLt : ¬ B.fst < B.snd)
    (y : Vertex H) :
    W.ref B y = swapTwo (W.ref B.canonical y) := by
  have hCanon : B.canonical =
      ⟨B.snd, B.fst, B.snd_ne_root, B.fst_ne_root, B.ne.symm⟩ := by
    unfold CutPair.canonical
    exact ite_eq_right hNotLt
  have hExitEq : ∀ (s : Vertex H) (x : Fin H.origVertexCount),
      B.Mem s → (H.ExitTailMem B s y x ↔ H.ExitTailMem B.canonical s y x) := by
    intro s x hs
    have hsC : B.canonical.Mem s := (B.canonical_mem_iff s).mpr hs
    rw [W.exit_iff B s y x hs, W.exit_iff B.canonical s y x hsC]
    constructor
    · rintro ⟨w, a, ha, hsa, hxa, hp⟩
      exact ⟨w, a, ha, hsa, hxa, AvoidPath.mono hp (fun z hz => (B.canonical_mem_iff z).mp hz)⟩
    · rintro ⟨w, a, ha, hsa, hxa, hp⟩
      exact ⟨w, a, ha, hsa, hxa, AvoidPath.mono hp (fun z hz => (B.canonical_mem_iff z).mpr hz)⟩
  have hEnd0 : W.endpoint B 0 = W.endpoint B.canonical 1 := by
    rw [hEnds B 0, hEnds B.canonical 1, hCanon]
    rfl
  have hEnd1 : W.endpoint B 1 = W.endpoint B.canonical 0 := by
    rw [hEnds B 1, hEnds B.canonical 0, hCanon]
    rfl
  have h0 : (W.ref B y).x0 = (swapTwo (W.ref B.canonical y)).x0 := by
    change Two.get (W.ref B y) 0 = Two.get (W.ref B.canonical y) 1
    apply interval_test_ext
    intro l h
    rw [W.ref_test B y 0 l h, W.ref_test B.canonical y 1 l h]
    simp only [Model.Fits]
    have hm1 : B.Mem (W.endpoint B.canonical 1) :=
      (B.canonical_mem_iff _).mp (W.endpoint_mem B.canonical 1)
    rw [hEnd0]
    constructor
    · intro hf x hx
      exact hf x ((hExitEq _ x hm1).mpr hx)
    · intro hf x hx
      exact hf x ((hExitEq _ x hm1).mp hx)
  have h1 : (W.ref B y).x1 = (swapTwo (W.ref B.canonical y)).x1 := by
    change Two.get (W.ref B y) 1 = Two.get (W.ref B.canonical y) 0
    apply interval_test_ext
    intro l h
    rw [W.ref_test B y 1 l h, W.ref_test B.canonical y 0 l h]
    simp only [Model.Fits]
    have hm0 : B.Mem (W.endpoint B.canonical 0) :=
      (B.canonical_mem_iff _).mp (W.endpoint_mem B.canonical 0)
    rw [hEnd1]
    constructor
    · intro hf x hx
      exact hf x ((hExitEq _ x hm0).mpr hx)
    · intro hf x hx
      exact hf x ((hExitEq _ x hm0).mp hx)
  cases hA : W.ref B y
  cases hB : swapTwo (W.ref B.canonical y)
  rw [hA] at h0
  rw [hB] at h0
  rw [hA] at h1
  rw [hB] at h1
  exact congr (congrArg Two.mk h0) h1

end Helpers

section Contract

theorem baseBound_of_actualBuiltBank
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (built : ActualBuiltBank H p data size_data rank large r entryRank rankArc flat bits endpoints) :
    SealedPriorBase.BaseBound endpoints built.bases.data := by
  intro v
  have hvLt : v.val < H.vertexCount := by simpa only [built.bases.size_data] using v.isLt
  let y : Vertex H := ⟨v.val, hvLt⟩
  have hExact := built.bases_exact y
  change built.bases.data[v.val]'v.isLt = some (built.model.wantBase y) at hExact
  change RankBound endpoints ((built.bases.data[v.val]'v.isLt).getD zero).x0 ∧
    RankBound endpoints ((built.bases.data[v.val]'v.isLt).getD zero).x1
  rw [hExact]
  have hW : ∀ x : Fin H.origVertexCount, built.model.rank x < endpoints := by
    intro x
    rw [built.model_eq]
    exact hRank x
  exact rankBound_wantBase_contract built.model hW y

/-- Sealed EX4.2 + EX4.3 oracle package built from a validated topological reader
on a flat acyclic quotient `H`. -/
structure ActualSealedContract
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (bits endpoints : Nat) where
  hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints
  wFit : Width bits (max r.out.tables.next endpoints)
  hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits
  built : ActualBuiltBank H p data size_data rank large r entryRank rankArc flat bits endpoints
  wEndpoints : Width bits endpoints
  baseBound : SealedPriorBase.BaseBound endpoints built.bases.data
  sealed : Array (Machine.Word bits)
  sealed_eq : sealed = SealedPriorBase.serialize wEndpoints built.bases.data baseBound
  sealed_size : sealed.size = 6 * H.vertexCount
  sealView : SealedPriorBase.BaseView H.vertexCount sealed.size
  sealView_eq : sealView =
    ⟨0, by rw [sealed_size, Nat.zero_add]; exact Nat.le_refl _⟩
  placed : SealedPriorBase.Placed wEndpoints built.bases.data baseBound sealed
    ⟨sealView.start, by simpa only [built.bases.size_data] using sealView.fits⟩
  bankMem_size_le : built.bank.mem.size ≤ 19 * (H.vertexCount + 1)
  retainedWords : Nat
  retainedWords_eq : retainedWords = built.bank.mem.size + sealed.size
  retainedWords_le : retainedWords ≤ 25 * H.vertexCount + 19
  retainedWords_slack_le : retainedWords ≤ 44 * H.vertexCount + 19
  bankWrites_le : built.bank.writes ≤ 37 * H.vertexCount + 19

noncomputable def buildActualSealedContract
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
    ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints := by
  let built := buildActualDirectBank H flat increasing covers rankArc r entryRank hRank wFit hLayout
  let wEnd : Width bits endpoints :=
    ⟨Nat.le_trans (Nat.le_max_right _ _) wFit.ranks, wFit.tags⟩
  have hBase := baseBound_of_actualBuiltBank hRank built
  let sealed := SealedPriorBase.serialize wEnd built.bases.data hBase
  have hSealSize : sealed.size = 6 * H.vertexCount := by
    simp [sealed, built.bases.size_data]
  let sv : SealedPriorBase.BaseView H.vertexCount sealed.size :=
    ⟨0, by rw [hSealSize, Nat.zero_add]; exact Nat.le_refl _⟩
  have hPlaced : SealedPriorBase.Placed wEnd built.bases.data hBase sealed
      ⟨sv.start, by simpa only [built.bases.size_data] using sv.fits⟩ := by
    intro j
    dsimp only [sv]
    simp only [Nat.zero_add]
    rfl
  have hBankSize : built.bank.mem.size ≤ 19 * (H.vertexCount + 1) := by
    have hNext := bundle_next_le (r := r)
    have hSz := built.bank.size_eq
    omega
  have hRetLe : built.bank.mem.size + sealed.size ≤ 25 * H.vertexCount + 19 := by
    omega
  have hRetSlack : built.bank.mem.size + sealed.size ≤ 44 * H.vertexCount + 19 := by
    omega
  have hWrites : built.bank.writes ≤ 37 * H.vertexCount + 19 := by
    have h1 := built.totalWrites_eq
    have h2 := built.seedWrites_le
    have h3 := built.sweepWrites_le
    omega
  exact
    { hRank := hRank
      wFit := wFit
      hLayout := hLayout
      built := built
      wEndpoints := wEnd
      baseBound := hBase
      sealed := sealed
      sealed_eq := rfl
      sealView := sv
      sealView_eq := rfl
      sealed_size := hSealSize
      placed := hPlaced
      bankMem_size_le := hBankSize
      retainedWords := built.bank.mem.size + sealed.size
      retainedWords_eq := rfl
      retainedWords_le := hRetLe
      retainedWords_slack_le := hRetSlack
      bankWrites_le := hWrites }

/-- Adapter viewing `EX42.ArraySweep.Slots Values H.vertexCount` as the dense
`StaticHeadSweep.Slots H.vertexCount (Option Values)` array expected by `ExactCount.countedBase`
without copying. -/
def toStaticSlots {n : Nat} (s : _root_.EX42.ArraySweep.Slots Values n) :
    PaperB.StaticHeadSweep.Slots n (Option Values) :=
  ⟨s.data, s.size_data⟩

/-- Construction work model for a single vertex event of the EX4.2+EX4.3 packed sweep:
charges up to 18 slot-record words + 1 base-cell write (`19`), exact raw occurrence
visits via `ExitCountedBase.countedBase`, and `60 * L H.vertexCount + 3` word steps
per fused call (covering both incoming-row `countedBase` calls and up to 2 installer
fresh-tail calls via `install_count_le_two`). -/
def sweepEventWork {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (y : Vertex H) : Nat :=
  let S := actualCompactArraySchedule r increasing covers
    (g := C.built.bundle.g0) C.built.bundle.full C.built.bundle.ch
  let inp := actualInput C.built.bundle C.wFit.tags C.built.bank C.hLayout entryRank
  let cb := countedBase inp (toStaticSlots C.built.bases) y
  let instCalls :=
    match S.mapSlot.read y with
    | none => 0
    | some i =>
      install_count inp
        (actualLookup C.built.bundle i).1
        (actualLookup C.built.bundle i).2
  let perCall := 60 * OracleContract.L H.vertexCount + 3
  19 + cb.labelledOccurrenceVisits + perCall * (cb.fusedCalls + instCalls)

/-- Every live slot queried by `foldStored` during construction (or query) executes at most
`60 * OracleContract.L H.vertexCount + 3` word reads/steps. -/
theorem live_slot_word_charge_le_L
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints)
    {u : Nat} (hu : u < C.built.bundle.F.size) (d : Nat) :
    ∃ c, WordCharge
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank))
        (recordAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
          C.wFit.tags)
        d
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank) u - d)
        u 0 c ∧
      1 + c ≤ 20 * (foldStored C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank) C.wFit.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ∧
      1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount + 3 := by
  obtain ⟨c, hCharge, hSteps, hLog⟩ :=
    live_run_read_charge C.built.decoded C.built.liveOK (C.built.all_live u hu)
      (bundle_numInserted_le C.built.bundle) d
  have hLeL : ceilLog2 (H.vertexCount + 2) ≤ OracleContract.L H.vertexCount :=
    ceilLog2_add_two_le_L H.vertexCount
  exact ⟨c, hCharge, hSteps, hLog, Nat.le_trans hLog (by omega)⟩

/-- EX4.2 + EX4.3 construction time, working space, and retained space theorem. -/
theorem actualBuildWork_bound
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v) :
    let S := actualCompactArraySchedule r increasing covers
      (g := C.built.bundle.g0) C.built.bundle.full C.built.bundle.ch
    let inp := actualInput C.built.bundle C.wFit.tags C.built.bank C.hLayout entryRank
    let basesStatic := toStaticSlots C.built.bases
    let sweepWork := ListWork.total (List.ofFn S.vertex) (fun y =>
      let cb := countedBase inp basesStatic y
      let instCalls :=
        match S.mapSlot.read y with
        | none => 0
        | some i =>
          install_count inp
            (actualLookup C.built.bundle i).1
            (actualLookup C.built.bundle i).2
      19 + cb.labelledOccurrenceVisits +
        (60 * OracleContract.L H.vertexCount + 3) * (cb.fusedCalls + instCalls))
    let totalBuildSteps :=
      ForestIncomingRaw.rawTotal H (ForestIncomingRaw.prepare H) +
        C.built.seedWrites + C.built.sweepWrites + sweepWork + C.sealed.size
    (∀ y, (countedBase inp basesStatic y).values = inp.base basesStatic y) ∧
    ForestIncomingRaw.rawTotal H (ForestIncomingRaw.prepare H) = H.arcCount ∧
    sweepWork ≤
      (19 + (60 * OracleContract.L H.vertexCount + 3) * 2) * H.vertexCount +
        (1 + (60 * OracleContract.L H.vertexCount + 3)) * H.arcCount ∧
    totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount ∧
    totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount ^ 3 ∧
    C.retainedWords ≤ 25 * H.vertexCount + 19 ∧
    C.retainedWords ≤ 44 * H.vertexCount + 19 := by
  intro S inp basesStatic sweepWork totalBuildSteps
  have hBaseEq : ∀ y, (countedBase inp basesStatic y).values = inp.base basesStatic y :=
    fun y => countedBase_value inp basesStatic y
  have hPrep : ForestIncomingRaw.rawTotal H (ForestIncomingRaw.prepare H) = H.arcCount := by
    rw [ForestIncomingRaw.rawTotal_prepare H]
    exact ForestPreparedBuild.arcTotal_eq_arcCount H
  let work : Vertex H → Nat := fun y =>
    let cb := countedBase inp basesStatic y
    let instCalls :=
      match S.mapSlot.read y with
      | none => 0
      | some i =>
        install_count inp
          (actualLookup C.built.bundle i).1
          (actualLookup C.built.bundle i).2
    19 + cb.labelledOccurrenceVisits +
      (60 * OracleContract.L H.vertexCount + 3) * (cb.fusedCalls + instCalls)
  let fusedCalls : Vertex H → Nat := fun y =>
    (countedBase inp basesStatic y).fusedCalls +
      match S.mapSlot.read y with
      | none => 0
      | some i =>
        install_count inp
          (actualLookup C.built.bundle i).1
          (actualLookup C.built.bundle i).2
  have hCallBound : ∀ y, fusedCalls y ≤ ((ForestIncomingRaw.prepare H).1.row y).length + 2 := by
    intro y
    have hcb : (countedBase inp basesStatic y).fusedCalls ≤
        (ForestIncomingRaw.row H inp.rows y).length :=
      countedBase_calls_le inp basesStatic y
    have hcb' : (countedBase inp basesStatic y).fusedCalls ≤
        ((ForestIncomingRaw.prepare H).1.row y).length := hcb
    have hinst :
        (match S.mapSlot.read y with
        | none => 0
        | some i =>
          install_count inp
            (actualLookup C.built.bundle i).1
            (actualLookup C.built.bundle i).2) ≤ 2 := by
      cases hs : S.mapSlot.read y with
      | none => exact Nat.zero_le 2
      | some i =>
        exact install_count_le_two inp
          (actualLookup C.built.bundle i).1
          (actualLookup C.built.bundle i).2
    dsimp only [fusedCalls]
    omega
  have hCharge : ∀ y, work y ≤
      19 + 1 * ((ForestIncomingRaw.prepare H).1.row y).length +
        (60 * OracleContract.L H.vertexCount + 3) * fusedCalls y := by
    intro y
    have hvis : (countedBase inp basesStatic y).labelledOccurrenceVisits ≤
        ((ForestIncomingRaw.prepare H).1.row y).length :=
      countedBase_visits_le inp basesStatic y
    dsimp only [work, fusedCalls]
    omega
  have hSweep :
      sweepWork ≤
        (19 + (60 * OracleContract.L H.vertexCount + 3) * 2) * H.vertexCount +
          (1 + (60 * OracleContract.L H.vertexCount + 3)) * H.arcCount :=
    schedule_exit_charges_le H S work fusedCalls 19 1 (60 * OracleContract.L H.vertexCount + 3)
      hCallBound hCharge
  have hL : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  have hTotal : totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount := by
    dsimp only [totalBuildSteps]
    rw [hPrep]
    have hSeed : C.built.seedWrites ≤ 19 * (H.vertexCount + 1) := C.built.seedWrites_le
    have hSwept : C.built.sweepWrites ≤ 18 * H.vertexCount := C.built.sweepWrites_le
    have hSeal : C.sealed.size = 6 * H.vertexCount := C.sealed_size
    have hLarge : 3 ≤ H.vertexCount := large
    have hSeed' : C.built.seedWrites ≤ 38 * H.vertexCount := by omega
    have hVCoef : 19 + (60 * OracleContract.L H.vertexCount + 3) * 2 + 38 + 18 + 6 ≤
        209 * OracleContract.L H.vertexCount := by omega
    have hACoef : 1 + (60 * OracleContract.L H.vertexCount + 3) + 1 ≤
        209 * OracleContract.L H.vertexCount := by omega
    have hvMul := Nat.mul_le_mul_right H.vertexCount hVCoef
    have haMul := Nat.mul_le_mul_right H.arcCount hACoef
    have hDistrib :
        209 * OracleContract.L H.vertexCount * H.vertexCount +
          209 * OracleContract.L H.vertexCount * H.arcCount =
        209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount := by
      rw [← Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (OracleContract.L H.vertexCount) (H.vertexCount + H.arcCount),
        ← Nat.mul_assoc]
    have hc1 :
        (19 + (60 * OracleContract.L H.vertexCount + 3) * 2) * H.vertexCount +
          38 * H.vertexCount + 18 * H.vertexCount + 6 * H.vertexCount =
        (19 + (60 * OracleContract.L H.vertexCount + 3) * 2 + 38 + 18 + 6) * H.vertexCount := by
      simp only [Nat.add_mul]
    have ha1 :
        (1 + (60 * OracleContract.L H.vertexCount + 3)) * H.arcCount + H.arcCount =
        (1 + (60 * OracleContract.L H.vertexCount + 3) + 1) * H.arcCount := by
      simp only [Nat.add_mul, Nat.one_mul]
    have hUpper : H.arcCount + C.built.seedWrites + C.built.sweepWrites + sweepWork + C.sealed.size ≤
        209 * OracleContract.L H.vertexCount * H.vertexCount +
          209 * OracleContract.L H.vertexCount * H.arcCount := by
      omega
    exact Nat.le_trans hUpper (Nat.le_of_eq hDistrib)
  have hV12 :
      totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount ^ 3 :=
    Nat.le_trans hTotal
      (Nat.mul_le_mul_left (209 * (H.vertexCount + H.arcCount)) (L_le_pow_three H.vertexCount))
  exact ⟨hBaseEq, hPrep, hSweep, hTotal, hV12, C.retainedWords_le, C.retainedWords_slack_le⟩

/-- EX4.3 Query Theorem (canonical `CutPair H`): for every `B` with `B.fst < B.snd`
and `y` with `H.ProperLoss B y`, `SealedPriorBase.run` over `C.built.bank`,
`actualBankRegion`, and `C.sealed` recovers `C.built.model.ref B y` in
`≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ≤ 60 * OracleContract.L H.vertexCount + 3`
word steps (`O(L)`) plus `6` sealed base reads. -/
theorem query_canonical_exact
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints)
    (B : CutPair H) (hCan : B.fst < B.snd) (y : Vertex H) (hProp : H.ProperLoss B y) :
    ∃ (u d c : Nat),
      u < C.built.bundle.F.size ∧
      SealedPriorBase.run C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
        C.wFit.tags C.sealed C.sealView y u d = C.built.model.ref B y ∧
      C.sealView.start + (6 * y.val + 5) < C.sealed.size ∧
      Function.Injective (fun k : Fin 6 => C.sealView.start + (6 * y.val + k.val)) ∧
      WordCharge
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank))
        (recordAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
          C.wFit.tags)
        d
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank) u - d)
        u 0 c ∧
      1 + c ≤ 20 * (foldStored C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank) C.wFit.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ∧
      1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount + 3 ∧
      1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount ^ 3 + 3 := by
  let W := actualModel C.built.bundle entryRank rankArc flat
  have hMod : C.built.model = W := C.built.model_eq
  have hForestAnc :=
    (buildProperLossForest_properLoss_iff_ancestor rankArc C.built.bundle.distinctRanks
      flat hCan y).mp hProp
  obtain ⟨a, ha, hAnc⟩ := hForestAnc
  have hLabelNE : (buildProperLossForest H rank).label y ≠
      (buildProperLossForest H rank).rootNode := by
    intro hRoot
    have hAnc' : IsForestAncestor (buildProperLossForest H rank).parent a
        (buildProperLossForest H rank).rootNode := by
      rw [← hRoot]; exact hAnc
    have aEq : a = (buildProperLossForest H rank).rootNode := by
      have aux : ∀ {x z : Fin ((buildProperLossForest H rank).realNodeCount + 1)},
          IsForestAncestor (buildProperLossForest H rank).parent x z →
          z = (buildProperLossForest H rank).rootNode →
          x = (buildProperLossForest H rank).rootNode := by
        intro x z h
        induction h with
        | refl => intro hz; exact hz
        | step k _ ih =>
          intro hk
          rw [hk, buildProperLossForest_parent_root H rank] at ih
          exact ih rfl
      exact aux hAnc' rfl
    rw [aEq, buildProperLossForest_nodeKey?_root] at ha
    cases ha
  have hLabKey : ∃ Acut : CutPair H,
      (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y) =
        some Acut := by
    cases hq : (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).label y) with
    | some Acut => exact ⟨Acut, rfl⟩
    | none =>
      have hEqRoot := buildProperLossForest_nodeKey?_inj H rank
        (hq.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      exact (hLabelNE hEqRoot).elim
  obtain ⟨Acut, hLabKey⟩ := hLabKey
  have hOwnEq : W.owner y = W.forest.nodeKey? (W.forest.label y) := by
    rw [← hMod]
    exact C.built.owner_eq y
  have hOwn : W.owner y = some Acut := hOwnEq.trans hLabKey
  have facts : RouteForestFacts W.forest :=
    RouteForestFacts.of_build rankArc C.built.bundle.distinctRanks flat
  have hLive : RoutePathEdgeLive W (fun _ => True) a y :=
    RoutePathEdgeLive.of_driverCoverage
      (fun k {_ _} hk hp => actualModel_driverCoverage C.built.bundle entryRank rankArc flat hk hp)
      (fun _ _ _ => True.intro)
  obtain ⟨rt⟩ := Route.nonempty_of_forestAncestor facts hOwnEq ha hAnc hLive
  let q : Query W (fun _ => True) (fun _ => True) B y := ⟨True.intro, rt⟩
  let rb : BaseReader (fun _ : Fin H.vertexCount => True) := fun z _ => some (W.wantBase z)
  let rm : MapReader (fun _ : Fin (exitTransferDrivers r).size => True) := fun i _ => some (W.wantMap i)
  let u := C.built.slotOf Acut
  let d := C.built.bundle.F.depthOf (C.built.slotOf B)
  have huLt : u < C.built.bundle.F.size := by
    have hLabKeyBuilt : C.built.model.forest.nodeKey? (C.built.model.forest.label y) = some Acut := by
      rw [hMod]
      exact hLabKey
    exact C.built.slot_key_lt Acut hLabKeyBuilt
  have huLive : C.built.live u := C.built.all_live u huLt
  have hEdgesW : @RouteSlotEdges H (exitTransferDrivers r).size W (fun _ => True)
      (fun i _ => some (W.wantMap i)) C.built.slotOf C.built.bundle.F C.built.ref := by
    simpa only [hMod] using C.built.edges
  have hPath : ParentPath C.built.ref C.built.bundle.F.depthOf u (C.built.slotOf B)
      (q.route.actual rm) :=
    route_parentPath q.route hEdgesW hOwn
  have hDepthLe : d ≤ C.built.bundle.F.depthOf u := parentPath_rank_le hPath
  have hDepthAnc : C.built.bundle.F.depthOf (C.built.bundle.F.ancestorAtDepth u d) = d :=
    (C.built.bundle.G.layout.valid.ancestorAtDepth_spec huLt hDepthLe).2.2
  let v : Fin C.built.bases.data.size :=
    ⟨y.val, by simpa only [C.built.bases.size_data] using y.isLt⟩
  have hBase : C.built.bases.data[v.val]'v.isLt = rb y q.readOK := by
    have hb := C.built.bases_exact y
    dsimp only [v, rb]
    change C.built.bases.data[y.val]'_ = some (W.wantBase y)
    rw [← hMod]
    exact hb
  let reg := actualBankRegion r.out.tables.next C.hLayout C.built.bank
  have hPrior :
      PriorBase.run C.built.bank.mem reg C.wFit.tags C.built.bases.data v u d =
        q.run rb rm :=
    live_run_eq_query_of_route q rb rm C.built.slotOf hOwn hEdgesW C.built.decoded
      C.built.liveOK huLive d hDepthAnc rfl C.built.bases.data v hBase
  have hQuery : q.run rb rm = C.built.model.ref B y := by
    rw [hMod]
    change Map.eval (rt.actual rm) ((rb y True.intro).getD zero) = W.ref B y
    exact rt.actual_exact rm (fun _ _ => rfl)
  have hSealedEq :
      SealedPriorBase.run C.built.bank.mem reg C.wFit.tags C.sealed C.sealView y u d =
        PriorBase.run C.built.bank.mem reg C.wFit.tags C.built.bases.data v u d := by
    let sv' : SealedPriorBase.BaseView C.built.bases.data.size C.sealed.size :=
      ⟨C.sealView.start, by simpa only [C.built.bases.size_data] using C.sealView.fits⟩
    have hSealRun :
        SealedPriorBase.run C.built.bank.mem reg C.wFit.tags C.sealed C.sealView y u d =
          SealedPriorBase.run C.built.bank.mem reg C.wEndpoints.tags C.sealed sv' v u d :=
      rfl
    rw [hSealRun]
    exact SealedPriorBase.run_eq_priorBase C.built.bank.mem reg C.wEndpoints C.built.bases.data
      C.baseBound C.sealed sv' C.placed v u d
  obtain ⟨c, hCharge, hSteps, hCeil, hL⟩ := live_slot_word_charge_le_L C huLt d
  have hPhysReads := SealedPriorBase.physical_reads C.sealed C.sealView y
  have hReadLt : C.sealView.start + (6 * y.val + 5) < C.sealed.size := by
    have hFits := C.sealView.fits
    have hy := y.isLt
    omega
  have hReadInj : Function.Injective (fun k : Fin 6 => C.sealView.start + (6 * y.val + k.val)) := by
    intro k1 k2 hk
    dsimp only at hk
    apply Fin.ext
    omega
  exact ⟨u, d, c, huLt, hSealedEq.trans (hPrior.trans hQuery), hReadLt, hReadInj,
    hCharge, hSteps, hCeil, hL, Nat.le_trans hL (by
      have hPow := L_le_pow_three H.vertexCount
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 60 hPow) 3)⟩

/-- EX4.3 Query Theorem (arbitrary `CutPair H`, canonical or reversed):
evaluating `SealedPriorBase.run` at `B.canonical` and conditionally swapping
the two 3-word endpoint summaries recovers `C.built.model.ref B y` in
`≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ≤ 60 * OracleContract.L H.vertexCount + 3`
word steps (`O(L)`) plus `6` sealed base reads. -/
theorem query_exact
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat}
    {rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v}
    {flat : H.IsFlat} {bits endpoints : Nat}
    (C : ActualSealedContract H p data size_data rank large r entryRank rankArc flat bits endpoints)
    (B : CutPair H) (y : Vertex H) (hProp : H.ProperLoss B y) :
    ∃ (u d c : Nat),
      u < C.built.bundle.F.size ∧
      (let raw := SealedPriorBase.run C.built.bank.mem
          (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
          C.wFit.tags C.sealed C.sealView y u d
        if B.fst < B.snd then raw else swapTwo raw) = C.built.model.ref B y ∧
      C.sealView.start + (6 * y.val + 5) < C.sealed.size ∧
      Function.Injective (fun k : Fin 6 => C.sealView.start + (6 * y.val + k.val)) ∧
      WordCharge
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank))
        (recordAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
          C.wFit.tags)
        d
        (depthAt C.built.bank.mem (actualBankRegion r.out.tables.next C.hLayout C.built.bank) u - d)
        u 0 c ∧
      1 + c ≤ 20 * (foldStored C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank) C.wFit.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (H.vertexCount + 2) + 3 ∧
      1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount + 3 ∧
      1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount ^ 3 + 3 := by
  have hPropCan : H.ProperLoss B.canonical y :=
    (properLoss_canonical_iff H B y).mpr hProp
  obtain ⟨u, d, c, huLt, hRun, hReadLt, hReadInj, hCharge, hSteps, hCeil, hL, hV12⟩ :=
    query_canonical_exact C B.canonical (CutPair.canonical_lt B) y hPropCan
  refine ⟨u, d, c, huLt, ?_, hReadLt, hReadInj, hCharge, hSteps, hCeil, hL, hV12⟩
  by_cases hLt : B.fst < B.snd
  · rw [ite_eq_left hLt, hRun, CutPair.canonical_eq_self hLt]
  · rw [ite_eq_right hLt, hRun]
    exact (model_ref_canonical_swap C.built.model
      (fun D j => by rw [C.built.model_eq]; rfl) B hLt y).symm

/-- Small-quotient theorem (`H.vertexCount < 3`): no valid cut-pair exists, so
proper-loss exit queries are vacuously empty via `SmallQuotient.cutPair_impossible_of_small`. -/
theorem small_quotient_vacuous {H : LabelledQuotient}
    (hSmall : H.vertexCount < 3) (B : CutPair H) (y : Vertex H) :
    ¬ H.ProperLoss B y :=
  fun _ => SmallQuotient.cutPair_impossible_of_small (by omega) B

end Contract

section NonVacuity

private def diamondQuotient : LabelledQuotient where
  origVertexCount := 5
  vertexCount := 4
  root := ⟨0, by decide⟩
  adj := #[
    [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨3, by decide⟩, ⟨4, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩],
    []
  ]
  adj_size := rfl

private def diamondOrder : Array (Vertex diamondQuotient) :=
  #[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

private theorem diamondOrder_size :
    diamondOrder.size = diamondQuotient.vertexCount := rfl

private theorem diamond_flat : diamondQuotient.IsFlat := by
  have arc01 : diamondQuotient.HasQuotientArc ⟨0, by decide⟩ ⟨1, by decide⟩ :=
    ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩
  have arc02 : diamondQuotient.HasQuotientArc ⟨0, by decide⟩ ⟨2, by decide⟩ :=
    ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩
  have arc13 : diamondQuotient.HasQuotientArc ⟨1, by decide⟩ ⟨3, by decide⟩ :=
    ⟨⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, by decide, rfl⟩
  have arc23 : diamondQuotient.HasQuotientArc ⟨2, by decide⟩ ⟨3, by decide⟩ :=
    ⟨⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩, by decide, rfl⟩
  constructor
  · intro v
    rcases v with ⟨_ | _ | _ | _ | k, hv⟩
    · exact AvoidPath.refl _ not_false
    · exact AvoidPath.step _ _ _ not_false arc01 (AvoidPath.refl _ not_false)
    · exact AvoidPath.step _ _ _ not_false arc02 (AvoidPath.refl _ not_false)
    · exact AvoidPath.step _ _ _ not_false arc01
        (AvoidPath.step _ _ _ not_false arc13 (AvoidPath.refl _ not_false))
    · exfalso; have : k + 4 < 4 := hv; omega
  · intro u v hu hvu
    have h01 : diamondQuotient.root ≠ ⟨1, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h02 : diamondQuotient.root ≠ ⟨2, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h03 : diamondQuotient.root ≠ ⟨3, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h12 : (⟨1, by decide⟩ : Vertex diamondQuotient) ≠ ⟨2, by decide⟩ :=
      Fin.ne_of_val_ne (by decide)
    have h13 : (⟨1, by decide⟩ : Vertex diamondQuotient) ≠ ⟨3, by decide⟩ :=
      Fin.ne_of_val_ne (by decide)
    have h23 : (⟨2, by decide⟩ : Vertex diamondQuotient) ≠ ⟨3, by decide⟩ :=
      Fin.ne_of_val_ne (by decide)
    rcases u with ⟨_ | _ | _ | _ | ku, huLt⟩
    · exact (hu rfl).elim
    · have hu1 : (⟨0 + 1, huLt⟩ : Vertex diamondQuotient) = ⟨1, by decide⟩ := rfl
      rw [hu1]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h01
      · exact (hvu rfl).elim
      · exact AvoidPath.step _ _ _ h01 arc02 (AvoidPath.refl _ (Ne.symm h12))
      · exact AvoidPath.step _ _ _ h01 arc02
          (AvoidPath.step _ _ _ (Ne.symm h12) arc23 (AvoidPath.refl _ (Ne.symm h13)))
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · have hu2 : (⟨0 + 1 + 1, huLt⟩ : Vertex diamondQuotient) = ⟨2, by decide⟩ := rfl
      rw [hu2]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h02
      · exact AvoidPath.step _ _ _ h02 arc01 (AvoidPath.refl _ h12)
      · exact (hvu rfl).elim
      · exact AvoidPath.step _ _ _ h02 arc01
          (AvoidPath.step _ _ _ h12 arc13 (AvoidPath.refl _ (Ne.symm h23)))
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · have hu3 : (⟨0 + 1 + 1 + 1, huLt⟩ : Vertex diamondQuotient) = ⟨3, by decide⟩ := rfl
      rw [hu3]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h03
      · exact AvoidPath.step _ _ _ h03 arc01 (AvoidPath.refl _ h13)
      · exact AvoidPath.step _ _ _ h03 arc02 (AvoidPath.refl _ h23)
      · exact (hvu rfl).elim
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · exfalso; have : ku + 4 < 4 := huLt; omega

private def diamondCut : CutPair diamondQuotient :=
  ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide, by decide, by decide⟩

private theorem diamond_properLoss_3 :
    diamondQuotient.ProperLoss diamondCut ⟨3, by decide⟩ := by
  constructor
  · intro hp
    have aux : ∀ (w z : Vertex diamondQuotient),
        AvoidPath diamondQuotient.HasQuotientArc diamondCut.Mem w z →
        z = ⟨3, by decide⟩ → w = ⟨0, by decide⟩ → False := by
      intro w z hw
      induction hw with
      | refl _ =>
        intro hz hw0
        rw [hw0] at hz
        have hv := congrArg Fin.val hz
        change (0 : Nat) = 3 at hv
        omega
      | @step a b c _ hab hrest _ =>
        intro hc ha
        subst ha
        obtain ⟨e, he, hhead⟩ := hab
        have out0 : diamondQuotient.outArcs ⟨0, by decide⟩ =
            [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩] := rfl
        rw [out0] at he
        have hbAlive : ¬ diamondCut.Mem b := by
          cases hrest with
          | refl _ hnb => exact hnb
          | step _ _ _ hnb _ _ => exact hnb
        rcases List.mem_cons.mp he with rfl | he
        · exact hbAlive (by rw [← hhead]; exact Or.inl rfl)
        · rcases List.mem_cons.mp he with rfl | he
          · exact hbAlive (by rw [← hhead]; exact Or.inr rfl)
          · cases he
    exact aux ⟨0, by decide⟩ ⟨3, by decide⟩ hp rfl rfl
  · decide

private def diamondRank : Vertex diamondQuotient → Nat := fun v => v.val

private theorem diamondLarge : 3 ≤ diamondQuotient.vertexCount := by decide

private theorem diamondOrdVal (k : Fin diamondQuotient.vertexCount) :
    (orderedVertexAt diamondOrder diamondOrder_size k).val = k.val := by
  rcases k with ⟨_ | _ | _ | _ | m, hm⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exfalso; change m + 4 < 4 at hm; omega

private theorem diamondIncreasing :
    ∀ i j : Fin diamondQuotient.vertexCount, i.val < j.val →
      diamondRank (orderedVertexAt diamondOrder diamondOrder_size i) <
        diamondRank (orderedVertexAt diamondOrder diamondOrder_size j) := by
  intro i j hij
  change (orderedVertexAt diamondOrder diamondOrder_size i).val <
    (orderedVertexAt diamondOrder diamondOrder_size j).val
  rw [diamondOrdVal i, diamondOrdVal j]
  exact hij

private theorem diamondCovers :
    ∀ v : Vertex diamondQuotient, ∃ i : Fin diamondQuotient.vertexCount,
      orderedVertexAt diamondOrder diamondOrder_size i = v :=
  fun v => ⟨v, Fin.ext (diamondOrdVal v)⟩

private theorem diamondRankArc :
    ∀ u v : Vertex diamondQuotient,
      diamondQuotient.HasQuotientArc u v → diamondRank u < diamondRank v := by
  intro u v ⟨e, he, hhead⟩
  subst hhead
  rcases u with ⟨_ | _ | _ | _ | k, hk⟩
  · have out0 : diamondQuotient.outArcs ⟨0, by decide⟩ =
        [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩] := rfl
    rw [out0] at he
    rcases List.mem_cons.mp he with rfl | he
    · change (0 : Nat) < 1; decide
    · rcases List.mem_cons.mp he with rfl | he
      · change (0 : Nat) < 2; decide
      · cases he
  · have out1 : diamondQuotient.outArcs ⟨0 + 1, hk⟩ =
        [⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨3, by decide⟩, ⟨4, by decide⟩⟩] := rfl
    rw [out1] at he
    rcases List.mem_cons.mp he with rfl | he
    · change (1 : Nat) < 3; decide
    · rcases List.mem_cons.mp he with rfl | he
      · change (1 : Nat) < 3; decide
      · cases he
  · have out2 : diamondQuotient.outArcs ⟨0 + 1 + 1, hk⟩ =
        [⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩] := rfl
    rw [out2] at he
    rcases List.mem_cons.mp he with rfl | he
    · change (2 : Nat) < 3; decide
    · cases he
  · have out3 : diamondQuotient.outArcs ⟨0 + 1 + 1 + 1, hk⟩ = [] := rfl
    rw [out3] at he
    cases he
  · exfalso; change k + 4 < 4 at hk; omega

private noncomputable def diamondReader :=
  ForestPreparedBuild.readerForWords diamondOrder diamondOrder_size
    diamondRank diamondIncreasing diamondCovers diamondRankArc diamond_flat diamondLarge

private def diamondEntryRank : Fin diamondQuotient.origVertexCount → Nat := fun x => x.val

private theorem diamondHRank : ∀ x : Fin diamondQuotient.origVertexCount, diamondEntryRank x < 5 :=
  fun x => x.isLt

private theorem diamondWFit : Width 10 (max diamondReader.out.tables.next 5) := by
  have hNext : diamondReader.out.tables.next ≤ 5 := bundle_next_le (r := diamondReader)
  have hPow : 2 ^ 10 = 1024 := rfl
  have hBound : max diamondReader.out.tables.next 5 ≤ 2 ^ 10 := by omega
  exact ⟨hBound, by unfold TagsFit; decide⟩

private theorem diamondHLayout :
    diamondReader.out.tables.next + 18 * diamondReader.out.tables.next ≤ 2 ^ 10 := by
  have hNext : diamondReader.out.tables.next ≤ 5 := bundle_next_le (r := diamondReader)
  have hPow : 2 ^ 10 = 1024 := rfl
  omega

private noncomputable def diamondContract :=
  buildActualSealedContract diamondQuotient diamond_flat diamondIncreasing diamondCovers
    diamondRankArc diamondReader diamondEntryRank diamondHRank diamondWFit diamondHLayout

/-- Concrete non-vacuity witness on a 4-vertex flat acyclic diamond quotient:
builds `ActualSealedContract`, confirms `LiveStoreOK` and `sealed.size = 24`,
and executes the `EX4.3` query theorem on `(diamondCut, 3)`. -/
theorem nonvacuous_diamond_contract :
    diamondContract.sealed.size = 24 ∧
    diamondContract.retainedWords ≤ 195 ∧
    (∃ (u d c : Nat),
      u < diamondContract.built.bundle.F.size ∧
      SealedPriorBase.run diamondContract.built.bank.mem
        (actualBankRegion diamondReader.out.tables.next diamondHLayout diamondContract.built.bank)
        diamondContract.wFit.tags diamondContract.sealed diamondContract.sealView
        ⟨3, by decide⟩ u d =
        diamondContract.built.model.ref diamondCut ⟨3, by decide⟩ ∧
      1 + c + 1 ≤ 60 * OracleContract.L 4 + 3) := by
  have hCan : diamondCut.fst < diamondCut.snd := by decide
  obtain ⟨u, d, c, huLt, hRun, _, _, _, _, _, hL, _⟩ :=
    query_canonical_exact diamondContract diamondCut hCan ⟨3, by decide⟩ diamond_properLoss_3
  have hRet : diamondContract.retainedWords ≤ 195 := by
    have hr := diamondContract.retainedWords_slack_le
    change diamondContract.retainedWords ≤ 44 * 4 + 19 at hr
    exact hr
  exact ⟨diamondContract.sealed_size, hRet, u, d, c, huLt, hRun, hL⟩

end NonVacuity

end PaperB.ExitActualContract
