module

public import PaperB.LabelledTransport
public import PaperB.FiniteSiblingFlat
public import PaperB.DenseRuntimeGraph
public import PaperB.DensePackingCode

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseOriginalQuotient

open Digraph PaperB.EX16Assembly
open PackedStaticLayout StaticOriginalSiblingEmitter
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PaperB.DenseQuotientRows PaperB.DenseArcRecode PaperB.Digraph.GlobalSibling

variable {g : Digraph} {r : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (q : OriginalReader g r) (u : Fin q.count)
variable {buckets : ChildLists q.count}
variable (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)

private theorem positionChildOK
    (h : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (c : Fin q.count) :
    c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u := by
  constructor
  · intro hc
    obtain ⟨hnonroot, hparent⟩ := (h u c).mp hc
    refine ⟨hparent, ?_⟩
    intro hcu
    have hself : q.input.parent.read c = c := hparent.trans hcu.symm
    have hdepth := q.reader.input_ok.depth_step c hnonroot
    first
    | rw [hself] at hdepth <;> omega
    | erw [hself] at hdepth <;> omega
  · rintro ⟨hparent, hne⟩
    refine (h u c).mpr ⟨?_, hparent⟩
    intro hc
    apply hne
    subst c
    have hroot : q.input.parent.read q.input.root = q.input.root :=
      q.reader.input_ok.parent_root
    exact hroot.symm.trans hparent

private def canonicalEntry (a : Arc g)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount) : Digraph.GlobalSibling.Entry g (2 * q.count) :=
  ⟨{ source := StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src
     destination := StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst
     tail := tail }, a⟩

/-- The shared emitter row in its original order, with all occurrences retained. -/
private theorem emitted_eq_canonical
    (originalRows : EX51.Rows g.vertexCount
      (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    (spec : _) :
    emitted q originalRows u =
      g.originalArcOccurrences.filterMap (fun a =>
        (siblingEmission? (d := q.ids.originals.read u)
          progress injective spec a).map (fun s =>
            canonicalEntry q u a s.source s.destination s.tail)) := by
  unfold emitted
  rw [hRows]
  unfold canonicalEntry
  exact Digraph.GlobalSibling.emitAll_row progress injective spec
    (getters q) (packing q) (checked progress injective q)
    (q.ids.originals.read u)

private theorem slots_and_label_iff
    (s t : Fin (2 * q.count))
    (hs : Occurs buckets u ((halves q.count).unpack s))
    (ht : Occurs buckets u ((halves q.count).unpack t))
    (label : Fin g.vertexCount)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount)
    (hsrc : s = StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src)
    (hdst : t = StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst)
    (htail : label = tail)
    (v w : Fin (rows.length u)) (l : Fin g.vertexCount) :
    (DenseArcRecode.slot (halves q.count) rows u s hs = v ∧
      DenseArcRecode.slot (halves q.count) rows u t ht = w ∧ label = l) ↔
    (src = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
      dst = positionToOriginal q u (positionChildOK q u childOK) rows w ∧
      tail = l) := by
  subst s
  subst t
  subst label
  have hp := packedEmission_positions (q := q) (u := u)
    (childOK := positionChildOK q u childOK) (rows := rows) src dst hs ht
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  dsimp only at hp₁ hp₂
  rw [hp₁, hp₂]
  constructor
  · rintro ⟨hv, hw, hl⟩
    refine ⟨?_, ?_, hl⟩
    · simpa only [positionToOriginal_originalToPosition] using
        congrArg (positionToOriginal q u (positionChildOK q u childOK) rows) hv
    · simpa only [positionToOriginal_originalToPosition] using
        congrArg (positionToOriginal q u (positionChildOK q u childOK) rows) hw
  · rintro ⟨hv, hw, hl⟩
    refine ⟨?_, ?_, hl⟩
    · simpa only [originalToPosition_positionToOriginal] using
        congrArg (originalToPosition q u (positionChildOK q u childOK) rows) hv
    · simpa only [originalToPosition_positionToOriginal] using
        congrArg (originalToPosition q u (positionChildOK q u childOK) rows) hw

private theorem occurrenceAt_canonical_iff
    (xs : List (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (own : PackedLocalArcs.Valid (physical xs) q.input.root q.input.parent.read u)
    (i : Fin (physical xs).size)
    (a : Arc g)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount)
    (hi : xs[i.val]'(by simpa [physical] using i.isLt) =
      canonicalEntry q u a src dst tail)
    (v w : Fin (rows.length u)) (l : Fin g.vertexCount) :
    (let o := occurrenceAt (q := q) u rows childOK (physical xs) own i
     o.«from» = v ∧ o.«to» = w ∧ o.origTail = l) ↔
    (src = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
      dst = positionToOriginal q u (positionChildOK q u childOK) rows w ∧
      tail = l) := by
  dsimp only [occurrenceAt, PackedLocalArcs.induced]
  apply slots_and_label_iff (q := q) (u := u) (rows := rows) (childOK := childOK)
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.source) hi
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.destination) hi
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.tail) hi

/-- Exact labeled membership in the fast quotient built from the shared original
rows. The witness uses the original keys decoded at both dense positions and
the unchanged original tail. -/
theorem mem_outArcs_build_iff
    (originalRows : EX51.Rows g.vertexCount
      (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    (hzero : 0 < rows.length u)
    (v : Fin (rows.length u)) (e : QuotientArc g.vertexCount (rows.length u))
    (spec : _) :
    e ∈ (build progress injective q originalRows hRows u hd hFind
      rows childOK hzero).outArcs v ↔
      ∃ a ∈ g.originalArcOccurrences, ∃ s,
        siblingEmission? (d := q.ids.originals.read u) progress injective spec a =
          some s ∧
        s.source = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
        s.destination = positionToOriginal q u (positionChildOK q u childOK) rows e.head ∧
        s.tail = e.origTail := by
  let xs := emitted q originalRows u
  have hrow := emitted_eq_canonical progress injective q u originalRows hRows hd hFind spec
  change xs = _ at hrow
  have own : PackedLocalArcs.Valid (physical xs)
      q.input.root q.input.parent.read u := by
    intro i
    have hi : i.val < xs.length := by simpa [physical] using i.isLt
    have hm : xs[i.val]'hi ∈
        (StaticOriginalSiblingEmitter.emitAll q).1.row (q.ids.originals.read u) := by
      rw [← hRows]
      exact List.getElem_mem hi
    simpa [physical, hFind] using
      (Digraph.GlobalSibling.ActualOwnership.emitAll_row_own
        progress injective q hd hm)
  unfold build
  rw [FastQuotientRows.mem_outArcs_ofOccurrences]
  change (∃ o ∈ List.ofFn (occurrenceAt (q := q) u rows childOK (physical xs) own),
    o.«from» = v ∧ o.«to» = e.head ∧ o.origTail = e.origTail) ↔ _
  constructor
  · rintro ⟨o, ho, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
    have hi : i.val < xs.length := by simpa [physical] using i.isLt
    have hm : xs[i.val]'hi ∈ xs := List.getElem_mem hi
    have hm' := Eq.mp (congrArg (fun ys => xs[i.val]'hi ∈ ys) hrow) hm
    obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hm'
    cases hs : siblingEmission? (d := q.ids.originals.read u)
        progress injective spec a with
    | none => simp [hs] at he
    | some s =>
      have hentry : xs[i.val]'hi =
          canonicalEntry q u a s.source s.destination s.tail := by
        symm
        simpa [hs] using he
      exact ⟨a, ha, s, hs,
        (occurrenceAt_canonical_iff q u rows childOK xs own i
          a s.source s.destination s.tail hentry v e.head e.origTail).mp h⟩
  · rintro ⟨a, ha, s, hs, h⟩
    have hm : canonicalEntry q u a s.source s.destination s.tail ∈ xs := by
      rw [hrow]
      exact List.mem_filterMap.mpr ⟨a, ha, by simp [hs]⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
    let i : Fin (physical xs).size := ⟨j, by simpa [physical] using hj⟩
    have hentry : xs[i.val]'(by simpa [physical] using i.isLt) =
        canonicalEntry q u a s.source s.destination s.tail := by
      first | exact hget | exact hget.symm
    exact ⟨occurrenceAt (q := q) u rows childOK (physical xs) own i,
      List.mem_ofFn.mpr ⟨i, rfl⟩,
      (occurrenceAt_canonical_iff q u rows childOK xs own i
        a s.source s.destination s.tail hentry v e.head e.origTail).mpr h⟩

end PaperB.DenseOriginalQuotient


namespace PaperB.DenseOriginalQuotient.Transport

open PaperB.Digraph PaperB.DenseQuotientRows PaperB.EX16Assembly PaperB.ForestLayout

noncomputable def denseToOld {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (u : Fin q.count) {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (rows : Layout buckets) :=
  fun (i : Fin (rows.length u)) =>
    encodeSiblingBlockKey g r _ _
      (positionToOriginal q u childOK rows i)

noncomputable def oldToDense {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (u : Fin q.count) {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (rows : Layout buckets) :=
  fun (j : Fin (siblingBlockKeys g r (q.ids.originals.read u) q.parent).length) =>
    originalToPosition q u childOK rows
      (decodeSiblingBlockKey g r _ _ j)

private theorem decode_encode {g : Digraph} {r d : Fin g.vertexCount}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (k : SiblingBlockKey g r d parent) :
    decodeSiblingBlockKey g r d parent
      (encodeSiblingBlockKey g r d parent k) = k := by
  first
  | apply decodeSiblingBlockKey_encodeSiblingBlockKey
  | exact?

@[simp] theorem oldToDense_denseToOld {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (u : Fin q.count) {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (rows : Layout buckets) (i : Fin (rows.length u)) :
    oldToDense (g := g) (r := r) q u childOK rows
      (denseToOld (g := g) (r := r) q u childOK rows i) = i := by
  simp only [oldToDense, denseToOld, decode_encode,
    originalToPosition_positionToOriginal]

@[simp] theorem denseToOld_oldToDense {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (u : Fin q.count) {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (rows : Layout buckets) (j : Fin (siblingBlockKeys g r (q.ids.originals.read u) q.parent).length) :
    denseToOld (g := g) (r := r) q u childOK rows
      (oldToDense (g := g) (r := r) q u childOK rows j) = j := by
  simp only [denseToOld, oldToDense, positionToOriginal_originalToPosition,
    encodeSiblingBlockKey_decodeSiblingBlockKey]

/-- Read the original rank directly from the decoded key, without enumerating
the sibling block keys. -/
def denseRank {g : Digraph} {r : Fin g.vertexCount}
    (rank : Fin g.vertexCount → Nat) (q : OriginalReader g r) (u : Fin q.count) {buckets : ChildLists q.count}
    (childOK : ∀ c : Fin q.count, c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (rows : Layout buckets) :=
  fun (i : Fin (rows.length u)) =>
    rank (positionToOriginal q u childOK rows i :
      SiblingBlockKey g r _ _).val

/-- Transport both quotient endpoints and keep the physical tail unchanged. -/
theorem mem_outArcs_build_denseToOld_iff
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (u : Fin q.count) (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    {buckets : ChildLists q.count} (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hzero : 0 < rows.length u) (spec : ParentSpec g r q.parent)
    (v : Fin (rows.length u)) (e : QuotientArc g.vertexCount (rows.length u)) :
    e ∈ (build progress injective q originalRows hRows u hd hFind
      rows childOK hzero).outArcs v ↔
    (⟨denseToOld (g := g) (r := r) q u (positionChildOK q u childOK)
        rows e.head, e.origTail⟩ : QuotientArc g.vertexCount _) ∈
      (finiteSiblingQuotient progress injective spec hd).outArcs
        (denseToOld (g := g) (r := r) q u (positionChildOK q u childOK)
          rows v) := by
  rw [mem_outArcs_build_iff (spec := spec),
    mem_outArcs_finiteSiblingQuotient_iff_raw]
  simp only [denseToOld, decode_encode]
  constructor
  · rintro ⟨a, ha, ⟨s, t, x⟩, he, hs, ht, hx⟩
    change s = _ at hs
    change t = _ at ht
    change x = _ at hx
    subst s
    subst t
    subst x
    exact ⟨a, ha, he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, _, he, rfl, rfl, rfl⟩

end PaperB.DenseOriginalQuotient.Transport

namespace PaperB.DenseOriginalQuotient.Transport

open PaperB.Digraph PaperB.DenseQuotientRows PaperB.EX16Assembly PaperB.ForestLayout

private theorem hasQuotientArc_iff_origTail
    (H : LabelledQuotient) (v w : Fin H.vertexCount) :
    H.HasQuotientArc v w ↔ ∃ x, ⟨w, x⟩ ∈ H.outArcs v := by
  first
  | rfl
  | constructor
    · rintro ⟨⟨t, x⟩, ha, hb⟩
      have ht : t = w := by
        first | exact ha | exact hb | exact ha.symm | exact hb.symm
      subst t
      exact ⟨x, by first | exact ha | exact hb⟩
    · rintro ⟨x, hx⟩
      first
      | exact ⟨⟨w, x⟩, hx, rfl⟩
      | exact ⟨⟨w, x⟩, rfl, hx⟩

private theorem mapAvoidPathAlong
    {A B : Type} {srcEdge : A → A → Prop} {dstEdge : B → B → Prop}
    (f : A → B) (mapEdge : ∀ a b, srcEdge a b → dstEdge (f a) (f b))
    {failed : B → Prop} {s t : A}
    (p : AvoidPath srcEdge (fun a => failed (f a)) s t) :
    AvoidPath dstEdge failed (f s) (f t) := by
  induction p with
  | refl a ha =>
      exact AvoidPath.refl (f a) ha
  | step a b c ha hab rest ih =>
      exact AvoidPath.step (f a) (f b) (f c) ha (mapEdge a b hab) ih

section DenseRootRankFlatness

variable {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (u : Fin q.count) (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    {buckets : ChildLists q.count} (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hzero : 0 < rows.length u) (spec : ParentSpec g r q.parent)

local notation "posOK" => positionChildOK q u childOK
local notation "Dq" =>
  build progress injective q originalRows hRows u hd hFind rows childOK hzero
local notation "Sq" => finiteSiblingQuotient progress injective spec hd
local notation "dForward" => denseToOld (g := g) (r := r) q u posOK rows
local notation "dBackward" => oldToDense (g := g) (r := r) q u posOK rows
local notation "dRank" => denseRank rank q u posOK rows

theorem denseToOld_build_root : dForward ((Dq).root) = (Sq).root := by
  have hDense :
      positionToOriginal q u posOK rows ((Dq).root) =
        SiblingBlockKey.root g r (q.ids.originals.read u) q.parent := by
    let i₀ : Fin (rows.length u) := ⟨0, hzero⟩
    have hk : rows.key u i₀ = .inl u := rows.key_zero u
    change positionToOriginal q u posOK rows i₀ =
      SiblingBlockKey.root g r (q.ids.originals.read u) q.parent
    first
    | simp only [positionToOriginal] <;> rfl
    | have hv : (rows.decode u i₀).val = .inl u := hk
      have hdec : rows.decode u i₀ = ⟨.inl u, by
          have hp := (rows.decode u i₀).property
          rw [hv] at hp
          exact hp⟩ := Subtype.ext hv
      simp only [positionToOriginal, hdec] <;> rfl
    | simp [positionToOriginal, Layout.decode, hk] <;> rfl
  have hStructural :
      (Sq).root = encodeSiblingBlockKey g r (q.ids.originals.read u) q.parent
        (SiblingBlockKey.root g r (q.ids.originals.read u) q.parent) := by
    have hk := siblingBlockOf_leader progress injective spec hd
      (SiblingBlockKey.root g r (q.ids.originals.read u) q.parent)
    exact congrArg (encodeSiblingBlockKey g r (q.ids.originals.read u) q.parent) hk
  change encodeSiblingBlockKey g r (q.ids.originals.read u) q.parent
    (positionToOriginal q u posOK rows ((Dq).root)) = (Sq).root
  exact (congrArg (encodeSiblingBlockKey g r (q.ids.originals.read u) q.parent)
    hDense).trans hStructural.symm

theorem mem_outArcs_build_mk_denseToOld_iff
    (v w : Fin (rows.length u)) (x : Fin g.vertexCount) :
    (⟨w, x⟩ : QuotientArc g.vertexCount (rows.length u)) ∈ (Dq).outArcs v ↔
      ⟨dForward w, x⟩ ∈ (Sq).outArcs (dForward v) :=
  mem_outArcs_build_denseToOld_iff progress injective q originalRows hRows
    u hd hFind rows childOK hzero spec v ⟨w, x⟩

theorem hasQuotientArc_build_denseToOld_iff (v w : Fin (rows.length u)) :
    (Dq).HasQuotientArc v w ↔ (Sq).HasQuotientArc (dForward v) (dForward w) := by
  rw [hasQuotientArc_iff_origTail (Dq) v w,
    hasQuotientArc_iff_origTail (Sq) (dForward v) (dForward w)]
  exact exists_congr (fun x =>
    mem_outArcs_build_mk_denseToOld_iff progress injective q originalRows hRows
      u hd hFind rows childOK hzero spec v w x)

theorem denseRank_eq_finiteSiblingRank_denseToOld (v : Fin (rows.length u)) :
    dRank v = finiteSiblingRank progress injective spec hd (dForward v) := by
  simp only [denseRank, finiteSiblingRank, denseToOld, decode_encode] <;> rfl

include progress injective hd spec in
theorem denseRank_injective : Function.Injective dRank := by
  intro v w h
  have he : dForward v = dForward w :=
    finiteSiblingRank_injective progress injective spec hd
      ((denseRank_eq_finiteSiblingRank_denseToOld progress injective
        q u hd rows childOK spec v).symm.trans
        (h.trans (denseRank_eq_finiteSiblingRank_denseToOld progress injective
          q u hd rows childOK spec w)))
  exact (oldToDense_denseToOld q u posOK rows v).symm.trans
    ((congrArg dBackward he).trans (oldToDense_denseToOld q u posOK rows w))

include spec in
theorem denseRank_lt_of_mem_outArcs_build
    {v : Fin (rows.length u)} {e : QuotientArc g.vertexCount (rows.length u)}
    (he : e ∈ (Dq).outArcs v) :
    dRank v < dRank e.head := by
  have hm := (mem_outArcs_build_denseToOld_iff progress injective q originalRows
    hRows u hd hFind rows childOK hzero spec v e).mp he
  have ha : (Sq).HasQuotientArc (dForward v) (dForward e.head) :=
    (hasQuotientArc_iff_origTail (Sq) (dForward v) (dForward e.head)).mpr
      ⟨e.origTail, hm⟩
  rw [denseRank_eq_finiteSiblingRank_denseToOld progress injective
      q u hd rows childOK spec v,
    denseRank_eq_finiteSiblingRank_denseToOld progress injective
      q u hd rows childOK spec e.head]
  exact finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd ha

include spec in
theorem denseRank_lt_of_hasQuotientArc_build
    {v w : Fin (rows.length u)} (h : (Dq).HasQuotientArc v w) :
    dRank v < dRank w := by
  obtain ⟨x, hx⟩ := (hasQuotientArc_iff_origTail (Dq) v w).mp h
  exact denseRank_lt_of_mem_outArcs_build progress injective q originalRows
    hRows u hd hFind rows childOK hzero spec (v := v) (e := ⟨w, x⟩) hx

include spec in
theorem build_isFlat : (Dq).IsFlat := by
  have hroot : dForward ((Dq).root) = (Sq).root :=
    denseToOld_build_root progress injective q originalRows hRows
      u hd hFind rows childOK hzero spec
  have hleft (a : Fin (rows.length u)) : dBackward (dForward a) = a :=
    oldToDense_denseToOld q u posOK rows a
  have hright (a : Fin ((Sq).vertexCount)) : dForward (dBackward a) = a :=
    denseToOld_oldToDense q u posOK rows a
  have hrootBack : dBackward ((Sq).root) = (Dq).root :=
    (congrArg dBackward hroot.symm).trans (hleft ((Dq).root))
  have back (a b : Fin ((Sq).vertexCount)) (h : (Sq).HasQuotientArc a b) :
      (Dq).HasQuotientArc (dBackward a) (dBackward b) := by
    apply (hasQuotientArc_build_denseToOld_iff progress injective q originalRows
      hRows u hd hFind rows childOK hzero spec (dBackward a) (dBackward b)).mpr
    rw [hright a, hright b]
    exact h
  have pull (failed : Fin ((Dq).vertexCount) → Prop) (v : Fin ((Dq).vertexCount))
      (p : AvoidPath (Sq).HasQuotientArc (fun j => failed (dBackward j))
        (Sq).root (dForward v)) :
      AvoidPath (Dq).HasQuotientArc failed (Dq).root v := by
    have hp : AvoidPath (Dq).HasQuotientArc failed
        (dBackward ((Sq).root)) (dBackward (dForward v)) :=
      mapAvoidPathAlong dBackward back (failed := failed) p
    rw [hrootBack, hleft v] at hp
    exact hp
  obtain ⟨reach, avoid⟩ := finiteSiblingQuotient_isFlat progress injective spec hd
  constructor
  · intro v
    exact pull (fun _ => False) v (reach (dForward v))
  · intro b v hb hv
    have hb' : dForward b ≠ (Sq).root := by
      intro h
      exact hb ((hleft b).symm.trans ((congrArg dBackward h).trans hrootBack))
    have hv' : dForward v ≠ dForward b := by
      intro h
      exact hv ((hleft v).symm.trans ((congrArg dBackward h).trans (hleft b)))
    apply pull (fun z => z = b) v
    apply AvoidPath.mono (avoid (dForward b) (dForward v) hb' hv')
    intro j hj
    change dBackward j = b at hj
    exact (hright j).symm.trans (congrArg dForward hj)

theorem exactAdj_build_denseToOld :
    LabelledQuotient.Transport.ExactAdj dForward
      (show (Dq).origVertexCount = (Sq).origVertexCount from rfl) := by
  intro v w x
  change
    (⟨w, x⟩ : QuotientArc g.vertexCount (rows.length u)) ∈ (Dq).outArcs v ↔
      ⟨dForward w, x⟩ ∈ (Sq).outArcs (dForward v)
  exact mem_outArcs_build_mk_denseToOld_iff progress injective q originalRows hRows
    u hd hFind rows childOK hzero spec v w x

end DenseRootRankFlatness

end PaperB.DenseOriginalQuotient.Transport
