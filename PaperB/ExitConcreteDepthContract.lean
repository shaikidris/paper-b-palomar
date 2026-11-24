module

public import PaperB.ExitPackedRuntime
public import PaperB.ExitDirectDepthInv
public import PaperB.ExitPartialOccupancy
public import PaperB.ExitPhysicalDepthColumn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.BuiltExit.PackedRuntime.DirectIntegration

open PaperB.Machine (Word)
open PaperB.LabelledQuotient PaperB.ExitSummary PaperB.ExitMap
open PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open EX42.ArraySweep EX42.ArraySweep.Packed

variable {H : LabelledQuotient} {N m bits words : Nat}
variable {P : Plan H.vertexCount m}

private def castRegion {a b : Nat} (h : a = b) (R : Region bits a) :
    Region bits b :=
  h ▸ R

/-- The template's region, indexed by the physical bank width. -/
def layoutRegion (r : Input H N bits) (hlen : r.arena.mem.size = words) :
    Region bits words :=
  castRegion hlen r.arena.region

private def bankRegion (R : Region bits words) (bank : WriteResult bits words) :
    Region bits bank.mem.size :=
  regionIn bank R

/-- Replace only the memory. The region change is an index transport;
tags, rows, owners, orientations, and all other columns are unchanged. -/
@[inline] def rebind (r : Input H N bits) (hlen : r.arena.mem.size = words)
    (bank : WriteResult bits words) : Input H N bits :=
  { r with
    arena := ⟨bank.mem, bankRegion (layoutRegion r hlen) bank, r.arena.tags⟩ }

 /-- `priorSlotsView` reuses the sweep's dense array. The installer does
not inspect a row; the base callback uses the template's prepared rows. -/
def callbacks (r : Input H N bits) (hlen : r.arena.mem.size = words)
    (lookup : Fin m → Fin N × Fin N) :
    DirectCallbacks H.vertexCount m bits words Map Values where
  install := fun _ i s =>
    let r' := rebind r hlen s.bank
    let ids := lookup i
    r'.install (priorSlotsView s.bases) ids.1 ids.2
  base := fun y bank bases =>
    (rebind r hlen bank).base (priorSlotsView bases) y

/-- Fixed agreement with the original graph. No association between
unused chronological IDs and model cuts is required. -/
structure Geometry (r : Input H N bits) (W : Model H m)
    (lookup : Fin m → Fin N × Fin N) : Prop where
  child : ∀ i j,
    (r.orientation.read (lookup i).1).endpoint j = W.endpoint (W.child i) j
  parent : ∀ i j,
    (r.orientation.read (lookup i).2).endpoint j = W.endpoint (W.parent i) j
  owner_none : ∀ y, r.owners.read y = none → W.owner y = none
  owner_some : ∀ y cut, r.owners.read y = some cut →
    ∃ B : CutPair H, W.owner y = some B ∧
      ∀ j, (r.orientation.read cut).endpoint j = W.endpoint B j

/-- Forest facts needed to decode the occupied part of each bank. -/
structure ForestStages (R : Region bits words) (F : JumpForest)
    (occ : Nat → Nat → Prop) (old : Nat → Nat → CheckedFold.Stored) : Prop where
  size_le : F.size ≤ R.slots
  valid : ValidJumpForest F
  live_lt : ∀ k u, occ k u → u < F.size
  parent_eq : ∀ k u, occ k u → (old k u).parent = F.parentOf u
  jump_eq : ∀ k u, occ k u → (old k u).jump = F.jumpOf u
  parent_live : ∀ k u, occ k u → occ k (F.parentOf u)
  jump_live : ∀ k u, occ k u → occ k (F.jumpOf u)

private theorem decoded
    {R : Region bits words} {F : JumpForest} {tags : TagsFit bits}
    {L : Layout R.base words R.slots}
    {occ : Nat → Nat → Prop} {old : Nat → Nat → CheckedFold.Stored}
    (forest : ForestStages R F occ old) (k : Nat)
    (bank : WriteResult bits words)
    (occupied : OccupiedExact tags R.base L bank (occ k) (old k))
    (depth : DepthAgrees bank R (fun v => F.depthOf v.val)) :
    DecodedOccupied bank.mem (bankRegion R bank) F (old k) tags (occ k) := by
  refine DecodedOccupied.ofOccupiedExact occupied forest.size_le
    forest.valid (forest.live_lt k) ?_
    (forest.parent_eq k) (forest.jump_eq k)
    (forest.parent_live k) (forest.jump_live k)
  intro v _
  cases v with
  | mk i hi =>
    have hslot : i < R.slots := hi
    simpa [depthAt, bankRegion, regionIn, hslot] using depth (⟨i, hslot⟩ : Fin R.slots)

/-- One demanded source needs an earlier base cell, a live owning slot,
and agreement of the forest path evaluation with the model reference.
There is no condition on sources that the callback does not read. -/
structure SourceAt (r : Input H N bits) (W : Model H m) (S : Schedule P)
    (F : JumpForest) (live : Nat → Prop) (ref : Nat → CheckedFold.Stored)
    (a : Fin H.vertexCount) (cut : Fin N) (B : CutPair H)
    (s : Fin H.vertexCount) : Prop where
  earlier : ∃ b : Fin H.vertexCount, b.val < a.val ∧ S.vertex b = s
  path : ∃ u : Fin N, r.owners.read s = some u ∧ live u.val ∧
    Map.eval (PriorBase.accumulated (foldFused F ref u.val (r.depth.read cut)))
      (W.wantBase s) = W.ref B s

private theorem source_exact
    {r : Input H N bits} {hlen : r.arena.mem.size = words}
    {W : Model H m} {S : Schedule P} {F : JumpForest}
    {live : Nat → Prop} {ref : Nat → CheckedFold.Stored}
    {a : Fin H.vertexCount} {cut : Fin N} {B : CutPair H}
    {s : Fin H.vertexCount} {bank : WriteResult bits words}
    (ok : DecodedOccupied bank.mem (bankRegion (layoutRegion r hlen) bank)
      F ref r.arena.tags live)
    (bases : EX42.ArraySweep.Slots Values H.vertexCount)
    (priorBases : ∀ b : Fin H.vertexCount, Cell (b.val < a.val)
      (bases.read (S.vertex b)) (W.wantBase (S.vertex b)))
    (source : SourceAt r W S F live ref a cut B s) :
    (rebind r hlen bank).fused (priorSlotsView bases) cut s = W.ref B s := by
  obtain ⟨b, hb, hbs⟩ := source.earlier
  have hseed : bases.read s = some (W.wantBase s) := by
    have hcell : bases.read (S.vertex b) = some (W.wantBase (S.vertex b)) := by
      simpa [Cell, hb] using priorBases b
    simpa only [hbs] using hcell
  obtain ⟨u, hu, hlu, hpath⟩ := source.path
  have ho : (rebind r hlen bank).owners.read s = some u := hu
  unfold Input.fused
  rw [ho]
  exact (ok.run_exact_arraySweep_live hlu (r.depth.read cut)
    bases s (W.wantBase s) hseed).trans hpath

/-- The source footprint of the actual row: only endpoint misses that
pass its loss test can consult a prior base. This predicate is proof-only. -/
def RowSource (r : Input H N bits) (cut : Fin N) (y s : Fin H.vertexCount)
    (endpoint : Fin 2 → Fin H.vertexCount) : Prop :=
  (∃ e ∈ ForestIncomingRaw.row H r.rows y, (r.arcFields e).1 = s) ∧
    s ≠ endpoint 0 ∧ s ≠ endpoint 1 ∧ r.knownLoss cut s = true

/-- The remaining graph invariant is the incoming-row recurrence. It
uses the actual row, physical tails, entry ranks, and loss test, with an
abstract source reader constrained only on the row's source footprint.
It mentions neither a bank nor either runtime callback. -/
def IncomingLaw (r : Input H N bits) (W : Model H m)
    (cut : Fin N) (B : CutPair H) (y : Fin H.vertexCount) : Prop :=
  ∀ read : Fin H.vertexCount → Values,
    (∀ s, RowSource r cut y s (W.endpoint B) → read s = W.ref B s) →
    RawIncoming.run (W.endpoint B) r.entryRank.read r.arcFields
      (r.knownLoss cut) read (ForestIncomingRaw.row H r.rows y) = W.ref B y

theorem directDepthContract
    (r : Input H N bits) (hlen : r.arena.mem.size = words)
    (lookup : Fin m → Fin N × Fin N)
    {W : Model H m} {D : Deps H.vertexCount m} (kernel : Kernel W D)
    (geom : Geometry r W lookup) (S : Schedule P)
    {F : JumpForest} {occ : Nat → Nat → Prop}
    {old : Nat → Nat → CheckedFold.Stored}
    (forest : ForestStages (layoutRegion r hlen) F occ old)
    (L : Layout (layoutRegion r hlen).base words (layoutRegion r hlen).slots)
    (packing : Packing H.vertexCount m (layoutRegion r hlen).slots Map)
    {depthBase : Word bits} (column : Column (layoutRegion r hlen) depthBase)
    (before : depthBase.val + (layoutRegion r hlen).slots ≤
      (layoutRegion r hlen).base.val)
    (installSource : ∀ (a : Fin H.vertexCount) (i : Fin m),
      S.mapSlot.read (S.vertex a) = some i → ∀ j : Fin 2,
      W.slot (W.parent i) (W.endpoint (W.child i) j) = none →
      SourceAt r W S F (occ a.val) (old a.val) a (lookup i).2
        (W.parent i) (W.endpoint (W.child i) j))
    (baseSource : ∀ (a : Fin H.vertexCount) (cut : Fin N) (B : CutPair H),
      r.owners.read (S.vertex a) = some cut → W.owner (S.vertex a) = some B →
      ∀ s, RowSource r cut (S.vertex a) s (W.endpoint B) →
        SourceAt r W S F (occ (a.val + 1)) (old (a.val + 1)) a cut B s)
    (incoming : ∀ y cut B, r.owners.read y = some cut → W.owner y = some B →
      IncomingLaw r W cut B y)
    (keep : ∀ a : Fin H.vertexCount, S.mapSlot.read (S.vertex a) = none →
      occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val)
    (put : ∀ (a : Fin H.vertexCount) (i : Fin m),
      S.mapSlot.read (S.vertex a) = some i →
      let j := packing.jobAt (S.vertex a) i (W.wantMap i)
      PaperB.ExitPhysicalPass.Ready r.arena.tags (layoutRegion r hlen).slots
        j (occ a.val) (old a.val) ∧
        occ (a.val + 1) = j.occupy (occ a.val) ∧
        old (a.val + 1) = j.overlay (old a.val)) :
    DirectDepthContract r.arena.tags (layoutRegion r hlen).base L packing S
      (callbacks r hlen lookup)
      (fun bank => DepthAgrees bank (layoutRegion r hlen) (fun v => F.depthOf v.val))
      occ old W.wantMap W.wantBase := by
  refine ⟨?_, ?_, keep, put, ?_⟩
  · intro a i hi s occupied priorBases depth
    let r' := rebind r hlen s.bank
    let bases := priorSlotsView s.bases
    have ok := decoded forest a.val s.bank occupied depth
    have hf : ∀ j : Fin 2,
        W.slot (W.parent i) (W.endpoint (W.child i) j) = none →
        r'.fused bases (lookup i).2 (W.endpoint (W.child i) j) =
          W.ref (W.parent i) (W.endpoint (W.child i) j) := by
      intro j hj
      exact source_exact (hlen := hlen) ok s.bases priorBases (installSource a i hi j hj)
    -- These readers are proof witnesses for Kernel exactness, not runtime inputs.
    let rb : BaseReader (D.installBase i) := fun v _ => some (W.wantBase v)
    let rm : MapReader (D.installMap i) := fun j _ => some (W.wantMap j)
    change r'.install bases (lookup i).1 (lookup i).2 = W.wantMap i
    exact (r'.install_exact bases (lookup i).1 (lookup i).2 kernel (S.vertex a) i
      rb rm (geom.child i) (geom.parent i) hf (fun _ _ => rfl) (fun _ _ => rfl)).trans
      (kernel.install_exact (S.vertex a) i rb rm (fun _ _ => rfl) (fun _ _ => rfl))
  · intro a bank bases occupied priorBases depth
    let y := S.vertex a
    let r' := rebind r hlen bank
    let dense := priorSlotsView bases
    let rb : BaseReader (D.vertexBase y) := fun v _ => some (W.wantBase v)
    let rm : MapReader (D.vertexMap y) := fun j _ => some (W.wantMap j)
    have hk := kernel.base_exact y rb rm (fun _ _ => rfl) (fun _ _ => rfl)
    change r'.base dense y = W.wantBase y
    refine Eq.trans ?_ hk
    rw [hk]
    cases ho : r.owners.read y with
    | none =>
      have ho' : r'.owners.read y = none := ho
      simp only [Input.base, ho', Model.wantBase, geom.owner_none y ho]
    | some cut =>
      obtain ⟨B, hB, hend⟩ := geom.owner_some y cut ho
      have ho' : r'.owners.read y = some cut := ho
      simp only [Input.base, ho', Model.wantBase, hB]
      change RawIncoming.run (r.orientation.read cut).endpoint
        r.entryRank.read r.arcFields (r.knownLoss cut) (r'.fused dense cut)
        (ForestIncomingRaw.row H r.rows y) = W.ref B y
      rw [show (r.orientation.read cut).endpoint = W.endpoint B from funext hend]
      have ok := decoded forest (a.val + 1) bank occupied depth
      refine incoming y cut B ho hB (r'.fused dense cut) ?_
      intro s hs
      exact source_exact (hlen := hlen) ok bases priorBases (baseSource a cut B ho hB s hs)
  · intro a s inv i _ depth
    dsimp only
    intro ready _
    exact step_preserves_depthAgrees column r.arena.tags L before s.bank _
      ready.bound
      (buildFromBank_fit r.arena.tags (layoutRegion r hlen).base L s.bank _
        inv.maps ready.deps ready.fit) depth

end PaperB.BuiltExit.PackedRuntime.DirectIntegration
