module

public import PaperB.OriginalBothTables
public import PaperB.OriginalStaticConnector
public import PaperB.OriginalStaticFull
public import PaperB.OriginalEntryInverse
public import PaperB.ActualThirdForestGeometry
public import PaperB.DenseLabelledArcIso
public import PaperB.ExitDenseLookupTransport
public import PaperB.ExitSpanBridge
public import PaperB.ThirdReachableRoute
public import PaperB.AllOrigOracleCases
public import PaperB.OracleRuntimeProof
public import PaperB.DenseQuotientLocalOrder

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.EX44.ActualOnlineOracle

open PaperB
open PaperB.Digraph
open PaperB.Digraph.EX44
open PaperB.EX16Assembly
open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.DenseOriginalQuotient.Transport
open PaperB.EX44.RetainedRouteProof
open PaperB.EX44.RetainedRouteProof.OriginalStaticConnector

noncomputable section

section Helpers

private theorem denseRowPosOK {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ChildLists q.count}
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count) :
    c ∈ buckets.get d ↔ q.input.parent.read c = d ∧ c ≠ d := by
  constructor
  · intro hc
    obtain ⟨hnonroot, hparent⟩ := (childOK d c).mp hc
    refine ⟨hparent, ?_⟩
    intro hcd
    have hself : q.input.parent.read c = c := hparent.trans hcd.symm
    have hdepth := q.reader.input_ok.depth_step c hnonroot
    rw [hself] at hdepth
    omega
  · rintro ⟨hparent, hne⟩
    refine (childOK d c).mpr ⟨?_, hparent⟩
    intro hc
    apply hne
    subst c
    exact q.reader.input_ok.parent_root.symm.trans hparent

private theorem denseRowLengthPos {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ChildLists q.count}
    (rows : Layout buckets) (d : Fin q.count) :
    0 < rows.length d := by
  rw [rows.length_exact]
  omega

/-- Dense local quotient at retained vertex `d : Fin q.count`. -/
abbrev denseQuotient {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d : Fin q.count) : LabelledQuotient :=
  DenseOriginalQuotient.build progress injRank q originalRows hRows d
    (q.ids.original_reachable d) (q.ids.slot_of_original d)
    rows childOK (denseRowLengthPos q rows d)

/-- Dense local position of retained child `c` in `d`'s dense quotient. -/
def denseChild {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count)
    (hp : q.input.parent.read c = d) (hne : c ≠ d) :
    Fin (rows.length d) :=
  rows.encode d ⟨.inr c, (denseRowPosOK q childOK d c).mpr ⟨hp, hne⟩⟩

private theorem denseForward_inj {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (d : Fin q.count)
    {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get d ↔ q.input.parent.read c = d ∧ c ≠ d)
    (rows : Layout buckets) :
    ∀ ⦃a b : Fin (rows.length d)⦄,
      denseToOld q d childOK rows a = denseToOld q d childOK rows b → a = b := by
  intro a b hab
  have h := congrArg (oldToDense q d childOK rows) hab
  simpa only [oldToDense_denseToOld] using h

private theorem denseForward_surj {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (d : Fin q.count)
    {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get d ↔ q.input.parent.read c = d ∧ c ≠ d)
    (rows : Layout buckets) :
    ∀ b : Fin (siblingBlockKeys g r (q.ids.originals.read d) q.parent).length,
      ∃ a : Fin (rows.length d), denseToOld q d childOK rows a = b := by
  intro b
  exact ⟨oldToDense q d childOK rows b, denseToOld_oldToDense q d childOK rows b⟩

private theorem denseForward_denseChild_val {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count) (hp : q.input.parent.read c = d) (hne : c ≠ d) :
    (decodeSiblingBlockKey g r (q.ids.originals.read d) q.parent
      (denseToOld q d (denseRowPosOK q childOK d) rows
        (denseChild q rows childOK d c hp hne))).val =
      q.ids.originals.read c := by
  unfold denseToOld denseChild positionToOriginal
  rw [decodeSiblingBlockKey_encodeSiblingBlockKey, Layout.decode_encode]
  rfl

private theorem denseChild_ne_root {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count) (hp : q.input.parent.read c = d) (hne : c ≠ d) :
    denseChild q rows childOK d c hp hne ≠
      (denseQuotient progress injRank q originalRows hRows rows childOK d).root := by
  intro hEq
  have hKey : rows.key d (denseChild q rows childOK d c hp hne) =
      rows.key d ⟨0, denseRowLengthPos q rows d⟩ :=
    congrArg (rows.key d) hEq
  have hL : rows.key d (denseChild q rows childOK d c hp hne) = .inr c :=
    congrArg Subtype.val (rows.decode_encode d ⟨.inr c, (denseRowPosOK q childOK d c).mpr ⟨hp, hne⟩⟩)
  rw [hL, rows.key_zero d] at hKey
  cases hKey

private theorem denseChild_ne {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {d c₁ c₂ : Fin q.count}
    (hp₁ : q.input.parent.read c₁ = d) (hne₁ : c₁ ≠ d)
    (hp₂ : q.input.parent.read c₂ = d) (hne₂ : c₂ ≠ d)
    (hDiff : c₁ ≠ c₂) :
    denseChild q rows childOK d c₁ hp₁ hne₁ ≠
      denseChild q rows childOK d c₂ hp₂ hne₂ := by
  intro hEq
  apply hDiff
  have hVal := congrArg
    (fun i => (decodeSiblingBlockKey g r (q.ids.originals.read d) q.parent
      (denseToOld q d (denseRowPosOK q childOK d) rows i)).val) hEq
  rw [denseForward_denseChild_val, denseForward_denseChild_val] at hVal
  exact Full.vertexInj q hVal

private theorem mem_summary_has_extrema (xs : List Nat) (hne : xs ≠ []) :
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
      · simp [hab, ExitSummary.singleton, ExitMap.Interval.join]
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

private theorem finiteSiblingQuotient_exitTailMem_reachable
    {g : Digraph} {r d : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat} {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g r parent)
    (hd : g.InitiallyReachable r d)
    {B : CutPair (finiteSiblingQuotient progress injRank spec hd)}
    {s y : Fin (finiteSiblingQuotient progress injRank spec hd).vertexCount}
    {x : Fin g.vertexCount}
    (hx : (finiteSiblingQuotient progress injRank spec hd).ExitTailMem B s y x) :
    g.InitiallyReachable r x := by
  obtain ⟨e, he, htail, _⟩ := hx
  change e.origTail = x at htail
  have he' := (mem_outArcs_finiteSiblingQuotient_iff_raw progress injRank spec hd s e).mp he
  obtain ⟨raw, _, hraw⟩ := he'
  obtain ⟨hu, _, _, hEq⟩ :=
    (PaperB.Digraph.siblingEmission?_eq_some_iff progress injRank spec raw _).mp hraw
  have hxEq : raw.1 = x := by
    have ht := congrArg PaperB.Digraph.SiblingEmission.tail hEq
    exact ht.trans htail
  rw [← hxEq]
  exact hu.1

end Helpers

/-- Minimal dense per-owner evaluator interface matching Lemma 5.1 /
`LocalOrderedChecked.query` + `WordColumns.knownProbed` + `PriorBase.run`.
The `ExitSpanBridge.toSpan` step is applied cleanly when instantiating the
runtime's `exitExtrema` callback. -/
structure DenseOwnerExitEvaluator
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (k B E : Nat) where
  pairKey : (d : Fin q.count) →
    CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d) →
    Sample B (Option (Hit k))
  pairMember : Fin k → Fin q.count → Sample B Bool
  exitIntervals : Fin k → Fin q.count → Sample E (ExitMap.Interval × ExitMap.Interval)
  missing_spec : ∀ (d : Fin q.count)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d)),
    (pairKey d P).value = none →
    ∀ y : Fin (rows.length d),
      ¬ (denseQuotient progress injRank q originalRows hRows rows childOK d).ProperLoss P y
  hit_orientation : ∀ (d : Fin q.count)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
    (hit : Hit k),
    (pairKey d P).value = some hit →
    hit.orientation = LocalOrderedChecked.suppliedOrientation P
  member_spec : ∀ (d : Fin q.count)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
    (hit : Hit k),
    (pairKey d P).value = some hit →
    ∀ (y : Fin q.count) (hyP : q.input.parent.read y = d) (hyNe : y ≠ d),
      (pairMember hit.key y).value = true ↔
        (denseQuotient progress injRank q originalRows hRows rows childOK d).ProperLoss P
          (denseChild q rows childOK d y hyP hyNe)
  extrema_spec : ∀ (d : Fin q.count)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
    (hit : Hit k),
    (pairKey d P).value = some hit →
    ∀ (y : Fin q.count) (hyP : q.input.parent.read y = d) (hyNe : y ≠ d),
      (pairMember hit.key y).value = true →
      let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d
      let yd := denseChild q rows childOK d y hyP hyNe
      (exitIntervals hit.key y).value.1 =
        ExitSummary.summary
          ((lemma22ExitTails Dq P.canonical P.canonical.fst yd).map
            (fun v => (OriginalEntryInverse.originalRank q v).getD 0)) ∧
      (exitIntervals hit.key y).value.2 =
        ExitSummary.summary
          ((lemma22ExitTails Dq P.canonical P.canonical.snd yd).map
            (fun v => (OriginalEntryInverse.originalRank q v).getD 0))

namespace DenseOwnerExitEvaluator

/-- Construct a `DenseOwnerExitEvaluator` from per-owner `OrderedReaderResult`
certificates (`LocalOrderedChecked.query` / `known`) together with an
`ExitSummary`-exact interval evaluator (such as `PriorBase.run`). -/
def ofOrderedReader
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {p : ∀ d : Fin q.count,
      ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK d)}
    {data : ∀ d : Fin q.count,
      Array (ForestHead.Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d))}
    {size_data : ∀ d : Fin q.count,
      (data d).size = (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount}
    {qRank : ∀ d : Fin q.count,
      ForestHead.Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d) → Nat}
    {large : ∀ d : Fin q.count,
      3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount}
    (res : ∀ d : Fin q.count,
      PaperB.OrderedReaderResult (p d) (data d) (size_data d) (qRank d) (large d))
    (k B E : Nat)
    (encodeKey : (d : Fin q.count) → Nat → Fin k)
    (pairMember : Fin k → Fin q.count → Sample B Bool)
    (exitIntervals : Fin k → Fin q.count → Sample E (ExitMap.Interval × ExitMap.Interval))
    (pairKeyDebit : Nat) (hDebit : pairKeyDebit ≤ B)
    (member_eq : ∀ (d : Fin q.count)
      (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
      (hit : LocalOrderedChecked.CheckedNode),
      LocalOrderedChecked.query (res d) P = some hit →
      ∀ (y : Fin q.count) (hyP : q.input.parent.read y = d) (hyNe : y ≠ d),
        (pairMember (encodeKey d hit.node) y).value =
          (RetainedProperLoss.ofOrderedReader (res d)).known hit.node
            ((_root_.EX24.PreparedSweep.orderedConfig (p d) (large d)).vertexIndex
              (denseChild q rows childOK d y hyP hyNe)))
    (extrema_eq : ∀ (d : Fin q.count)
      (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
      (hit : LocalOrderedChecked.CheckedNode),
      LocalOrderedChecked.query (res d) P = some hit →
      ∀ (y : Fin q.count) (hyP : q.input.parent.read y = d) (hyNe : y ≠ d),
        (pairMember (encodeKey d hit.node) y).value = true →
        let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d
        let yd := denseChild q rows childOK d y hyP hyNe
        (exitIntervals (encodeKey d hit.node) y).value.1 =
          ExitSummary.summary
            ((lemma22ExitTails Dq P.canonical P.canonical.fst yd).map
              (fun v => (OriginalEntryInverse.originalRank q v).getD 0)) ∧
        (exitIntervals (encodeKey d hit.node) y).value.2 =
          ExitSummary.summary
            ((lemma22ExitTails Dq P.canonical P.canonical.snd yd).map
              (fun v => (OriginalEntryInverse.originalRank q v).getD 0))) :
    DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E where
  pairKey d P :=
    ⟨(LocalOrderedChecked.query (res d) P).map fun h =>
        ⟨encodeKey d h.node, h.orientation⟩,
      pairKeyDebit, hDebit⟩
  pairMember := pairMember
  exitIntervals := exitIntervals
  missing_spec d P hNone y := by
    have hqNone : LocalOrderedChecked.query (res d) P = none := by
      cases hq : LocalOrderedChecked.query (res d) P with
      | none => rfl
      | some hit => simp [hq] at hNone
    exact LocalOrderedChecked.not_properLoss_of_query_none (res d) P y hqNone
  hit_orientation d P hit hSome := by
    cases hq : LocalOrderedChecked.query (res d) P with
    | none => simp [hq] at hSome
    | some cHit =>
      simp only [hq, Option.map_some, Option.some.injEq] at hSome
      have hc : (⟨encodeKey d cHit.node, cHit.orientation⟩ : Hit k) = hit := hSome
      rw [← hc]
      exact ((LocalOrderedChecked.query_some_iff (res d) P cHit).mp hq).2
  member_spec d P hit hSome y hyP hyNe := by
    cases hq : LocalOrderedChecked.query (res d) P with
    | none => simp [hq] at hSome
    | some cHit =>
      simp only [hq, Option.map_some, Option.some.injEq] at hSome
      have hc : encodeKey d cHit.node = hit.key := by
        simpa using congrArg Hit.key hSome
      rw [← hc, member_eq d P cHit hq y hyP hyNe]
      exact LocalOrderedChecked.known_true_iff_properLoss_of_query_some
        (res d) P (denseChild q rows childOK d y hyP hyNe) cHit hq
  extrema_spec d P hit hSome y hyP hyNe hm := by
    cases hq : LocalOrderedChecked.query (res d) P with
    | none => simp [hq] at hSome
    | some cHit =>
      simp only [hq, Option.map_some, Option.some.injEq] at hSome
      have hc : encodeKey d cHit.node = hit.key := by
        simpa using congrArg Hit.key hSome
      rw [← hc] at hm ⊢
      exact extrema_eq d P cHit hq y hyP hyNe hm

/-- Convert physical interval summaries via `ExitSpanBridge.toSpan` and the
inverse-DFS-entry index `inv`. -/
def exitExtrema
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {progress : ∀ i j, g.HasArc i j → rank i < rank j}
    {injRank : ∀ ⦃i j⦄, rank i = rank j → i = j}
    {q : OriginalReader g r}
    {originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count))}
    {hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1}
    {buckets : ChildLists q.count}
    {rows : Layout buckets}
    {childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d}
    {k B E : Nat}
    (eval : DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E)
    (inv : OriginalEntryInverse.Index q)
    (key : Fin k) (y : Fin q.count) :
    Sample E (Span q.count × Span q.count) :=
  let ivs := eval.exitIntervals key y
  let read := ExitSpanBridge.readEntry inv.slots.read some
  ⟨(ExitSpanBridge.toSpan read ivs.value.1, ExitSpanBridge.toSpan read ivs.value.2),
    ivs.debit, ivs.bounded⟩

/-- Base `Runtime` carrying the reader's `lca`/`childBelow` and the dense
evaluator's `pairKey`/`pairMember`/`exitExtrema` callbacks. Installing with
`OriginalStaticConnector.install` (`thirdInstalledRuntime`) gives a runtime
definitionally equal to `OriginalStaticConnector.Full.install`. -/
def toBaseRuntime
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {progress : ∀ i j, g.HasArc i j → rank i < rank j}
    {injRank : ∀ ⦃i j⦄, rank i = rank j → i = j}
    {q : OriginalReader g r}
    {originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count))}
    {hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1}
    {buckets : ChildLists q.count}
    {rows : Layout buckets}
    {childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d}
    {k B E : Nat}
    (eval : DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E)
    (inv : OriginalEntryInverse.Index q)
    (debit : Nat) (hdebit : debit ≤ B) :
    Runtime g.vertexCount q.count k B E where
  source := q.input.root
  translate := fun _ => ⟨none, 0, Nat.zero_le _⟩
  ancestor := fun _ _ => ⟨false, 0, Nat.zero_le _⟩
  lca := fun a b => ⟨(q.reader.lca a b).node, debit, hdebit⟩
  childBelow := fun d x => ⟨q.reader.child d x, debit, hdebit⟩
  pairKey := fun d u v =>
    if hu : q.input.parent.read u = d ∧ u ≠ d then
      if hv : q.input.parent.read v = d ∧ v ≠ d then
        if huv : u ≠ v then
          let u' := denseChild q rows childOK d u hu.1 hu.2
          let v' := denseChild q rows childOK d v hv.1 hv.2
          let P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d) :=
            { fst := u'
              snd := v'
              fst_ne_root := denseChild_ne_root progress injRank q originalRows hRows rows childOK d u hu.1 hu.2
              snd_ne_root := denseChild_ne_root progress injRank q originalRows hRows rows childOK d v hv.1 hv.2
              ne := denseChild_ne q rows childOK hu.1 hu.2 hv.1 hv.2 huv }
          eval.pairKey d P
        else ⟨none, 0, Nat.zero_le _⟩
      else ⟨none, 0, Nat.zero_le _⟩
    else ⟨none, 0, Nat.zero_le _⟩
  pairMember := eval.pairMember
  exitExtrema := eval.exitExtrema inv

end DenseOwnerExitEvaluator

section TransportProof

private theorem refSpanExact_of_denseCoord
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (inv : OriginalEntryInverse.Index q)
    (d : Fin q.count)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d))
    (coord yd : Fin (rows.length d))
    (J : CutPair (finiteSiblingQuotient progress injRank q.parentSpec (q.ids.original_reachable d)))
    (hMemEq : ∀ v, (Transport.cutPair
        (denseToOld q d (denseRowPosOK q childOK d) rows)
        (denseForward_inj q d (denseRowPosOK q childOK d) rows)
        (denseToOld_build_root progress injRank q originalRows hRows d
          (q.ids.original_reachable d) (q.ids.slot_of_original d) rows childOK
          (denseRowLengthPos q rows d) q.parentSpec)
        P).Mem v ↔ J.Mem v)
    (s : ExitMap.Interval)
    (hs : s = ExitSummary.summary
      ((lemma22ExitTails
        (denseQuotient progress injRank q originalRows hRows rows childOK d)
        P.canonical coord yd).map
        (fun v => (OriginalEntryInverse.originalRank q v).getD 0))) :
    SpanExact (world q).entry
      (fun i => (world q).vertex i ∈
        lemma22ExitTails
          (finiteSiblingQuotient progress injRank q.parentSpec (q.ids.original_reachable d))
          J
          (denseToOld q d (denseRowPosOK q childOK d) rows coord)
          (denseToOld q d (denseRowPosOK q childOK d) rows yd))
      (ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) s) := by
  let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d
  let Sq := finiteSiblingQuotient progress injRank q.parentSpec (q.ids.original_reachable d)
  let posOK := denseRowPosOK q childOK d
  let f := denseToOld q d posOK rows
  have hf := denseForward_inj q d posOK rows
  have hsurj := denseForward_surj q d posOK rows
  have hroot : f Dq.root = Sq.root :=
    denseToOld_build_root progress injRank q originalRows hRows d
      (q.ids.original_reachable d) (q.ids.slot_of_original d) rows childOK
      (denseRowLengthPos q rows d) q.parentSpec
  have ha : Transport.ExactAdj (H := Dq) (K := Sq) f (rfl : Dq.origVertexCount = Sq.origVertexCount) :=
    exactAdj_build_denseToOld progress injRank q originalRows hRows d
      (q.ids.original_reachable d) (q.ids.slot_of_original d) rows childOK
      (denseRowLengthPos q rows d) q.parentSpec
  let tsOrig : List (Fin g.vertexCount) := lemma22ExitTails Dq P.canonical coord yd
  have hReach : ∀ v ∈ tsOrig, g.InitiallyReachable r v := by
    intro v hv
    have hMemD : Dq.ExitTailMem P.canonical coord yd v := mem_lemma22ExitTails.mp hv
    have hMemS : Sq.ExitTailMem (Transport.cutPair (H := Dq) (K := Sq) f hf hroot P) (f coord) (f yd) v :=
      (Transport.exitTailMem_iff (H := Dq) (K := Sq) f hf hroot hsurj
        (rfl : Dq.origVertexCount = Sq.origVertexCount) ha P coord yd v).mp
        ((LocalOrderedChecked.exitTailMem_canonical_iff P coord yd v).mp hMemD)
    exact finiteSiblingQuotient_exitTailMem_reachable progress injRank q.parentSpec
      (q.ids.original_reachable d) hMemS
  let tsHeld : List (Fin q.count) := tsOrig.filterMap q.ids.find
  have hListEq :
      tsOrig.map (fun v => (OriginalEntryInverse.originalRank q v).getD 0) =
        tsHeld.map (fun i => (OriginalEntryInverse.entryRank q i).val) := by
    have aux : ∀ (l : List (Fin g.vertexCount)),
        (∀ v ∈ l, g.InitiallyReachable r v) →
        l.map (fun v => (OriginalEntryInverse.originalRank q v).getD 0) =
          (l.filterMap q.ids.find).map (fun i => (OriginalEntryInverse.entryRank q i).val) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons v vs ih =>
        have hv : g.InitiallyReachable r v := hl v (List.mem_cons.mpr (Or.inl rfl))
        have hvs : ∀ u ∈ vs, g.InitiallyReachable r u := fun u hu =>
          hl u (List.mem_cons.mpr (Or.inr hu))
        have hFind : q.ids.find v = some (q.slot v hv) := q.find_slot v hv
        simp only [List.map_cons, List.filterMap_cons, hFind, Option.getD_some,
          OriginalEntryInverse.originalRank_of_find q hFind,
          OriginalEntryInverse.entryRank_val, ih hvs]
    exact aux tsOrig hReach
  have hs' : s = ExitSummary.summary
      (tsHeld.map fun i => (OriginalEntryInverse.entryRank q i).val) := by
    rw [hs, hListEq]
  have hMemHeld : ∀ i : Fin q.count, i ∈ tsHeld ↔ (world q).vertex i ∈ tsOrig := by
    intro i
    change i ∈ List.filterMap q.ids.find tsOrig ↔ q.ids.originals.read i ∈ tsOrig
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨v, hv, hfi⟩
      have hvo : q.ids.originals.read i = v := (q.find_eq_some_iff_original v i).mp hfi
      rwa [hvo]
    · intro ho
      exact ⟨q.ids.originals.read i, ho, q.ids.slot_of_original i⟩
  have hMemTarget : ∀ i : Fin q.count,
      ((world q).vertex i ∈ lemma22ExitTails Sq J (f coord) (f yd)) ↔ i ∈ tsHeld := by
    intro i
    rw [hMemHeld i]
    have hMemSq : (world q).vertex i ∈ lemma22ExitTails Sq J (f coord) (f yd) ↔
        Sq.ExitTailMem J (f coord) (f yd) ((world q).vertex i) := mem_lemma22ExitTails
    have hMemDq : (world q).vertex i ∈ tsOrig ↔
        Dq.ExitTailMem P.canonical coord yd ((world q).vertex i) := mem_lemma22ExitTails
    rw [hMemSq, hMemDq]
    have hCut : Sq.ExitTailMem J (f coord) (f yd) ((world q).vertex i) ↔
        Sq.ExitTailMem (Transport.cutPair (H := Dq) (K := Sq) f hf hroot P) (f coord) (f yd)
          ((world q).vertex i) := by
      constructor
      · rintro ⟨e, he, htail, hp⟩
        exact ⟨e, he, htail, AvoidPath.mono hp (fun z hz => (hMemEq z).mp hz)⟩
      · rintro ⟨e, he, htail, hp⟩
        exact ⟨e, he, htail, AvoidPath.mono hp (fun z hz => (hMemEq z).mpr hz)⟩
    exact hCut.trans
      ((Transport.exitTailMem_iff (H := Dq) (K := Sq) f hf hroot hsurj
        (rfl : Dq.origVertexCount = Sq.origVertexCount)
        ha P coord yd ((world q).vertex i)).symm.trans
        (LocalOrderedChecked.exitTailMem_canonical_iff P coord yd ((world q).vertex i)).symm)
  refine ExitSpanBridge.refCoordinate_exact
    (OriginalEntryInverse.entryRank q) inv.slots.read inv.read_rank
    some id (world q).entry (fun _ => rfl) (fun _ => True)
    (fun v _ => ⟨v, rfl, rfl⟩)
    tsHeld (fun _ _ => trivial)
    (fun i => (world q).vertex i ∈ lemma22ExitTails Sq J (f coord) (f yd))
    hMemTarget s hs' ?_
    (fun hEmpty i => hEmpty i)
    (fun i j hi hj hBnd => ⟨hi, hj, hBnd⟩)
  intro hne
  have hmne : tsHeld.map (fun i => (OriginalEntryInverse.entryRank q i).val) ≠ [] := by
    simpa [List.map_eq_nil_iff] using hne
  obtain ⟨lo, hi, hspan, hlo, hhi, hbounds⟩ := mem_summary_has_extrema _ hmne
  obtain ⟨a, ha, hloa⟩ := List.mem_map.mp hlo
  obtain ⟨b, hb, hhib⟩ := List.mem_map.mp hhi
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · simpa only [← hloa, ← hhib] using hspan
  · intro v hv
    have hv' := hbounds (OriginalEntryInverse.entryRank q v).val (List.mem_map.mpr ⟨v, hv, rfl⟩)
    simpa only [← hloa, ← hhib] using hv'

private theorem directThirdFacts_transport
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {k B E : Nat}
    (eval : DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E)
    (inv : OriginalEntryInverse.Index q)
    (debit : Nat) (hdebit : debit ≤ B)
    (d u v y : Fin q.count)
    (huP : q.input.parent.read u = d) (huNe : u ≠ d)
    (hvP : q.input.parent.read v = d) (hvNe : v ≠ d)
    (hyP : q.input.parent.read y = d) (hyNe : y ≠ d)
    (huv : u ≠ v)
    (r₀ : Fin g.vertexCount) (hr₀ : r₀ = r)
    (spec₀ : ParentSpec g r₀ q.parent)
    (hd₀ : g.InitiallyReachable r₀ ((world q).vertex d))
    (kU kV kZ : SiblingBlockKey g r₀ ((world q).vertex d) q.parent)
    (hkU : kU.val = (world q).vertex u)
    (hkV : kV.val = (world q).vertex v)
    (hkZ : kZ.val = (world q).vertex y)
    (J : CutPair (finiteSiblingQuotient progress injRank spec₀ hd₀))
    (jEnds :
      (J.fst = encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kU ∧
        J.snd = encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kV) ∨
      (J.fst = encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kV ∧
        J.snd = encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kU)) :
    DirectThirdFacts
      (thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit)
      (world q) d u v y
      (finiteSiblingQuotient progress injRank spec₀ hd₀) J rfl
      (encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kU)
      (encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kV)
      (encodeSiblingBlockKey g r₀ ((world q).vertex d) q.parent kZ) := by
  subst hr₀
  let R := thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit
  let W := world q
  let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d
  let Sq := finiteSiblingQuotient progress injRank spec₀ hd₀
  let posOK := denseRowPosOK q childOK d
  let f := denseToOld q d posOK rows
  have hf := denseForward_inj q d posOK rows
  have hsurj := denseForward_surj q d posOK rows
  have hroot : f Dq.root = Sq.root :=
    denseToOld_build_root progress injRank q originalRows hRows d
      (q.ids.original_reachable d) (q.ids.slot_of_original d) rows childOK
      (denseRowLengthPos q rows d) spec₀
  have ha : Transport.ExactAdj (H := Dq) (K := Sq) f (rfl : Dq.origVertexCount = Sq.origVertexCount) :=
    exactAdj_build_denseToOld progress injRank q originalRows hRows d
      (q.ids.original_reachable d) (q.ids.slot_of_original d) rows childOK
      (denseRowLengthPos q rows d) spec₀
  let u' := denseChild q rows childOK d u huP huNe
  let v' := denseChild q rows childOK d v hvP hvNe
  let y' := denseChild q rows childOK d y hyP hyNe
  let P : CutPair Dq :=
    { fst := u'
      snd := v'
      fst_ne_root := denseChild_ne_root progress injRank q originalRows hRows rows childOK d u huP huNe
      snd_ne_root := denseChild_ne_root progress injRank q originalRows hRows rows childOK d v hvP hvNe
      ne := denseChild_ne q rows childOK huP huNe hvP hvNe huv }
  have hFu : f u' = encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kU := by
    have hDec : decodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent (f u') = kU := by
      apply Subtype.ext
      exact (denseForward_denseChild_val q rows childOK d u huP huNe).trans hkU.symm
    have hEnc := congrArg (encodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent) hDec
    rw [encodeSiblingBlockKey_decodeSiblingBlockKey] at hEnc
    exact hEnc
  have hFv : f v' = encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kV := by
    have hDec : decodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent (f v') = kV := by
      apply Subtype.ext
      exact (denseForward_denseChild_val q rows childOK d v hvP hvNe).trans hkV.symm
    have hEnc := congrArg (encodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent) hDec
    rw [encodeSiblingBlockKey_decodeSiblingBlockKey] at hEnc
    exact hEnc
  have hFy : f y' = encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kZ := by
    have hDec : decodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent (f y') = kZ := by
      apply Subtype.ext
      exact (denseForward_denseChild_val q rows childOK d y hyP hyNe).trans hkZ.symm
    have hEnc := congrArg (encodeSiblingBlockKey g r₀ (q.ids.originals.read d) q.parent) hDec
    rw [encodeSiblingBlockKey_decodeSiblingBlockKey] at hEnc
    exact hEnc
  have hKeyEq : (R.pairKey d u v).value = (eval.pairKey d P).value := by
    dsimp only [R, thirdInstalledRuntime, install, DenseOwnerExitEvaluator.toBaseRuntime]
    rw [dite_eq_left_of_eq_true (eq_true ⟨huP, huNe⟩),
        dite_eq_left_of_eq_true (eq_true ⟨hvP, hvNe⟩),
        dite_eq_left_of_eq_true (eq_true huv)]
  have hMemEq : ∀ z, (Transport.cutPair (H := Dq) (K := Sq) f hf hroot P).Mem z ↔ J.Mem z := by
    intro z
    change (z = f u' ∨ z = f v') ↔ (z = J.fst ∨ z = J.snd)
    rw [hFu, hFv]
    rcases jEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, or_comm]
  have hLossEq : Sq.ProperLoss (Transport.cutPair (H := Dq) (K := Sq) f hf hroot P) (f y') ↔
      Sq.ProperLoss J (f y') := by
    have hMemFun : (Transport.cutPair (H := Dq) (K := Sq) f hf hroot P).Mem = J.Mem :=
      funext (fun z => propext (hMemEq z))
    unfold LabelledQuotient.ProperLoss LabelledQuotient.Lost
    rw [hMemFun]
  have hProper : Dq.ProperLoss P y' ↔ Sq.ProperLoss J (f y') :=
    (Transport.properLoss_iff (H := Dq) (K := Sq) f hf hroot hsurj
      (rfl : Dq.origVertexCount = Sq.origVertexCount) ha P y').trans hLossEq
  refine ⟨?_, ?_, ?_⟩
  · intro hNone loss
    rw [hKeyEq] at hNone
    exact eval.missing_spec d P hNone y' (hProper.mpr (hFy ▸ loss))
  · intro hit hSome
    rw [hKeyEq] at hSome
    change (eval.pairMember hit.key y).value = true ↔ _
    exact (eval.member_spec d P hit hSome y hyP hyNe).trans (hFy ▸ hProper)
  · intro hit hSome hm
    rw [hKeyEq] at hSome
    have hOrient := eval.hit_orientation d P hit hSome
    have hExtrema := eval.extrema_spec d P hit hSome y hyP hyNe hm
    have hCastMap : ∀ xs : List (Fin Sq.origVertexCount),
        xs.map (Fin.cast (rfl : Sq.origVertexCount = g.vertexCount)) = xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons a as ih =>
        have ha' : Fin.cast (rfl : Sq.origVertexCount = g.vertexCount) a = a := by
          cases a; rfl
        simp only [List.map_cons, ha', ih]
    dsimp only [requested, DenseOwnerExitEvaluator.exitExtrema]
    change SpanExact W.entry
        (fun i => W.vertex i ∈
          (lemma22ExitTails Sq J (encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kU)
            (encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kZ)).map
            (Fin.cast (rfl : Sq.origVertexCount = g.vertexCount)))
        (hit.orientation.order _).1 ∧
      SpanExact W.entry
        (fun i => W.vertex i ∈
          (lemma22ExitTails Sq J (encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kV)
            (encodeSiblingBlockKey g r₀ (W.vertex d) q.parent kZ)).map
            (Fin.cast (rfl : Sq.origVertexCount = g.vertexCount)))
        (hit.orientation.order _).2
    rw [hCastMap, hCastMap, ← hFu, ← hFv, ← hFy]
    have hSpan1 := refSpanExact_of_denseCoord progress injRank q originalRows hRows rows childOK inv
      d P P.canonical.fst y' J hMemEq (eval.exitIntervals hit.key y).value.1 hExtrema.1
    have hSpan2 := refSpanExact_of_denseCoord progress injRank q originalRows hRows rows childOK inv
      d P P.canonical.snd y' J hMemEq (eval.exitIntervals hit.key y).value.2 hExtrema.2
    rw [hOrient]
    by_cases hCmp : P.fst < P.snd
    · have hCanFst : P.canonical.fst = P.fst := by
        simp [CutPair.canonical, hCmp]
      have hCanSnd : P.canonical.snd = P.snd := by
        simp [CutPair.canonical, hCmp]
      rw [hCanFst] at hSpan1
      rw [hCanSnd] at hSpan2
      simpa [LocalOrderedChecked.suppliedOrientation, hCmp, Orientation.order,
        DenseOwnerExitEvaluator.exitExtrema, P] using ⟨hSpan1, hSpan2⟩
    · have hCanFst : P.canonical.fst = P.snd := by
        simp [CutPair.canonical, hCmp]
      have hCanSnd : P.canonical.snd = P.fst := by
        simp [CutPair.canonical, hCmp]
      rw [hCanFst] at hSpan1
      rw [hCanSnd] at hSpan2
      simpa [LocalOrderedChecked.suppliedOrientation, hCmp, Orientation.order,
        DenseOwnerExitEvaluator.exitExtrema, P] using ⟨hSpan2, hSpan1⟩

/-- Transport a `DenseOwnerExitEvaluator` across `dForward` (`denseToOld`) to
produce `DirectThirdTables` for `thirdInstalledRuntime` and `world q`. -/
theorem directThirdTables_of_denseOwnerExitEvaluator
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {k B E : Nat}
    (eval : DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E)
    (inv : OriginalEntryInverse.Index q)
    (debit : Nat) (hdebit : debit ≤ B)
    (spec : ParentSpec g
      ((world q).vertex (thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit).source)
      q.parent)
    (T : BothTables (thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit)
      (world q) progress injRank spec) :
    DirectThirdTables (R := thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit)
      (W := world q) progress injRank spec := by
  let base := eval.toBaseRuntime inv debit hdebit
  let R := thirdInstalledRuntime q base debit hdebit
  let W := world q
  have hs : W.vertex R.source = r :=
    thirdInstalled_source_vertex q base debit hdebit
  have geom := installedThirdGeometry q base debit hdebit progress injRank q.parentSpec
  refine ⟨?_, ?_⟩
  · intro d hd
    exact geom.geometry.rooted d hd
  · intro d hd a b u v x y U V Z J repU repV repZ jEnds
    have hChildBlock : ∀ (c z : Fin q.count) (C : SiblingVertex g (W.vertex R.source) (W.vertex d)),
        C.val = W.vertex c →
        (R.fetch (.child d c)).value = some z →
        z ≠ d ∧ q.input.parent.read z = d ∧
          ((siblingBlockSystem progress injRank spec hd).block C).val = W.vertex z := by
      intro c z C hCval hChild
      have hrSelf : g.InitiallyReachable r r := AvoidPath.refl r (fun h => h)
      have hChildFull : ((Full.install q hrSelf base debit hdebit).fetch (.child d c)).value = some z := hChild
      obtain ⟨hne, hp, ha⟩ :=
        Full.childLabel q hrSelf base debit hdebit progress injRank d c z hChildFull
      have hpIn : q.input.parent.read z = d := by
        apply Full.vertexInj q
        exact (q.parent_at_original z).symm.trans hp
      have hzc : W.vertex z ≠ W.vertex d := fun h => hne (Full.vertexInj q h)
      have hzReach : g.InitiallyReachable (W.vertex R.source) (W.vertex z) := by
        rw [hs]
        exact q.ids.original_reachable z
      let kz : SiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent :=
        ⟨W.vertex z, Or.inr ⟨hp, hzc, hzReach⟩⟩
      have hDom : g.Dominates (W.vertex R.source) kz.val C.val := by
        rw [hCval]
        exact (T.domInterval z c).1 ((T.treeInterval z c).2 ha)
      have hBlk : siblingBlockOf progress injRank spec C = kz :=
        (siblingBlockOf_eq_child_iff progress injRank spec C kz hzc).2 hDom
      exact ⟨hne, hpIn, congrArg Subtype.val hBlk⟩
    obtain ⟨huNe, huP, hkU⟩ := hChildBlock a u U repU.1 repU.2
    obtain ⟨hvNe, hvP, hkV⟩ := hChildBlock b v V repV.1 repV.2
    obtain ⟨hyNe, hyP, hkZ⟩ := hChildBlock x y Z repZ.1 repZ.2
    have huv : u ≠ v := by
      intro huvEq
      have hBlkEq :
          encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent
            ((siblingBlockSystem progress injRank spec hd).block U) =
          encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent
            ((siblingBlockSystem progress injRank spec hd).block V) := by
        apply congrArg (encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent)
        apply Subtype.ext
        rw [hkU, hkV, huvEq]
      rcases jEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact J.ne (h1.trans (hBlkEq.trans h2.symm))
      · exact J.ne (h1.trans (hBlkEq.symm.trans h2.symm))
    exact directThirdFacts_transport progress injRank q originalRows hRows rows childOK
      eval inv debit hdebit d u v y huP huNe hvP hvNe hyP hyNe huv
      (W.vertex R.source) hs spec hd
      ((siblingBlockSystem progress injRank spec hd).block U)
      ((siblingBlockSystem progress injRank spec hd).block V)
      ((siblingBlockSystem progress injRank spec hd).block Z)
      hkU hkV hkZ J jEnds

end TransportProof

section OnlineOracle

/-- Map any `FailureSet` to the two optional original-vertex slots expected by
`OracleRuntime.query`. -/
def failurePair {N : Nat} : FailureSet N → Option (Fin N) × Option (Fin N)
  | .none => (none, none)
  | .one a => (some a, none)
  | .two a b => (some a, some b)

private theorem fails_failurePair_iff {N : Nat} (F : FailureSet N) (x : Fin N) :
    Fails (failurePair F).1 (failurePair F).2 x ↔ F.Mem x := by
  cases F <;> simp [failurePair, Fails, FailureSet.Mem]

private theorem goal_failurePair_iff
    {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {k B E : Nat} (R : Runtime g.vertexCount q.count k B E)
    (hs : (world q).vertex R.source = r)
    (F : FailureSet g.vertexCount) (t : Fin g.vertexCount) :
    Goal R (world q) (failurePair F).1 (failurePair F).2 t ↔
      g.ReachableAvoiding F r t := by
  have hMem : Fails (failurePair F).1 (failurePair F).2 = F.Mem :=
    funext (fun x => propext (fails_failurePair_iff F x))
  change g.SurvivingPath (Fails (failurePair F).1 (failurePair F).2)
      ((world q).vertex R.source) t ↔
    g.SurvivingPath F.Mem r t
  rw [hMem, hs]

/-- **EX4.4 Online Query Correctness & Cost Bridge**:
Given any `DenseOwnerExitEvaluator` on the materialized dense quotients `Dq`,
the installed runtime `thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit`
answers `g.ReachableAvoiding F r t` **for every** `F : FailureSet g.vertexCount`
and every target `t : Fin g.vertexCount`, in `≤ 16` runtime events, `≤ 1` extrema call,
and `≤ 15 * B + E` work. -/
theorem online_oracle_correct_and_bounded
    {g : Digraph} {r : Fin g.vertexCount}
    (acyc : g.IsAcyclic)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {k B E : Nat}
    (eval : DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK k B E)
    (inv : OriginalEntryInverse.Index q)
    (debit : Nat) (hdebit : debit ≤ B) :
    let R := thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit
    ∀ (F : FailureSet g.vertexCount) (t : Fin g.vertexCount),
      let res := query R (failurePair F).1 (failurePair F).2 t
      (res.survives = true ↔ g.ReachableAvoiding F r t) ∧
      res.events.length ≤ 16 ∧
      slowCalls res.events ≤ 1 ∧
      work res.events ≤ 15 * B + E := by
  intro R F t res
  have hrReach : g.InitiallyReachable r r := by
    change AvoidPath g.HasArc (fun _ => False) r r
    exact AvoidPath.refl r (fun h => h)
  obtain ⟨spec, T⟩ := Full.bothTables_actual q hrReach
    (eval.toBaseRuntime inv debit hdebit) debit hdebit progress injRank
  have hInstall : R = Full.install q hrReach (eval.toBaseRuntime inv debit hdebit) debit hdebit := rfl
  have T' : BothTables R (world q) progress injRank spec := by
    change BothTables R (world q) progress injRank spec at T
    exact T
  have D := directThirdTables_of_denseOwnerExitEvaluator progress injRank q originalRows hRows
    rows childOK eval inv debit hdebit spec T'
  have hCorrect := original_routed_answer_correct_direct (R := R) (W := world q)
    progress injRank spec D T' acyc
    (failurePair F).1 (failurePair F).2 t
  have hs : (world q).vertex R.source = r :=
    thirdInstalled_source_vertex q (eval.toBaseRuntime inv debit hdebit) debit hdebit
  have hGoal := goal_failurePair_iff q R hs F t
  have hBounds := query_bounds R (failurePair F).1 (failurePair F).2 t
  exact ⟨hCorrect.trans hGoal, hBounds⟩

/-- Canonical `PaperB.EX16Assembly.fromOriginal` + `BoundKahnOrder.ofRun`
specialization of the EX4.4 online query correctness & cost bridge. -/
theorem canonical_online_oracle_correct_and_bounded
    (g : Digraph) (r : Fin g.vertexCount) (acyc : g.IsAcyclic) :
    let b := DenseQuotientLocalOrder.BoundKahnOrder.ofRun acyc
    let progress : ∀ i j, g.HasArc i j → b.rankRead i < b.rankRead j := fun i j h => by
      exact KahnInverse.rank_arc g b.result.order b.size_eq b.top h
    let injRank : ∀ ⦃i j⦄, b.rankRead i = b.rankRead j → i = j := fun i j h => by
      apply KahnInverse.rank_injective g b.result.order b.size_eq b.top
      simpa only [DenseQuotientLocalOrder.BoundKahnOrder.rankRead, b.slots_eq,
        KahnInverse.rank, Fin.ext_iff] using h
    let L := Nat.log2 (g.vertexCount + 2) + 1
    let hL : g.vertexCount + 2 ≤ 2 ^ L :=
      Nat.le_of_lt ((Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _))
    let hrReach : g.InitiallyReachable r r := AvoidPath.refl r (fun h => h)
    let hrDom : ∀ d, g.Dominates r d r ↔ d = r := fun _ => dominates_source_iff
    let q := PaperB.EX16Assembly.fromOriginal g r acyc hL hrReach hrDom
    let inv := OriginalEntryInverse.build q
    let rows := DenseQuotientRows.build q.input
    let childOK : ∀ d c : Fin q.count,
        c ∈ (bucketChildLists q.input.root q.input.parent.read).get d ↔
          c ≠ q.input.root ∧ q.input.parent.read c = d := by
      intro d c
      rw [bucketChildLists_get, mem_bucketChildren_iff]
    ∀ {k B E : Nat}
      (eval : DenseOwnerExitEvaluator progress injRank q
        (StaticOriginalSiblingEmitter.emitAll q).1 rfl rows childOK k B E)
      (debit : Nat) (hdebit : debit ≤ B),
      let R := thirdInstalledRuntime q (eval.toBaseRuntime inv debit hdebit) debit hdebit
      ∀ (F : FailureSet g.vertexCount) (t : Fin g.vertexCount),
        let res := query R (failurePair F).1 (failurePair F).2 t
        (res.survives = true ↔ g.ReachableAvoiding F r t) ∧
        res.events.length ≤ 16 ∧
        slowCalls res.events ≤ 1 ∧
        work res.events ≤ 15 * B + E := by
  intro b progress injRank L hL hrReach hrDom q inv rows childOK k B E eval debit hdebit R F t res
  exact online_oracle_correct_and_bounded acyc progress injRank q
    (StaticOriginalSiblingEmitter.emitAll q).1 rfl rows childOK eval inv debit hdebit F t

end OnlineOracle

end

end PaperB.EX44.ActualOnlineOracle
