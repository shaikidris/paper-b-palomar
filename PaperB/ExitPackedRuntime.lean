module

public import PaperB.ExitKernels
public import PaperB.ExitRawIncoming
public import PaperB.ExitPriorBase
public import PaperB.ForestIncomingRaw
public import PaperB.StaticHeadSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
`ExitRawIncoming` and `ExitPriorBase` are the assumed file names for the
two namespace bodies in the question; their import headers were not shown.

The runtime takes the actual dense `Slots` backing the base prefix, not a
`BaseReader` or a reconstructed array. The `Slice` declaration was not
included, so this module makes no assumption about its fields: a sweep with
a `Slice` wrapper should pass its dense backing slots here without copying.

Likewise, `physicalTail` is the projection for the stored arc's physical
original tail. Its field name was not included in the excerpts.
-/

namespace PaperB.BuiltExit.PackedRuntime

open PaperB.Machine (Word)
open PaperB.LabelledQuotient PaperB.ExitSummary PaperB.ExitMap
open PaperB.StoredPacking PaperB.ExitMap.Retention
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.StaticHeadSweep (Slots)

structure Ends (V : Type) where
  left : V
  right : V

@[inline] def Ends.endpoint {V : Type} (e : Ends V) (j : Fin 2) : V :=
  if j = 0 then e.left else e.right

@[inline] def Ends.slot {V : Type} [DecidableEq V]
    (e : Ends V) (s : V) : Option (Fin 2) :=
  if e.endpoint 0 = s then some 0
  else if e.endpoint 1 = s then some 1
  else none

@[inline] def pack {V : Type} [DecidableEq V]
    (child parent : Ends V) (a b : Values) : Map :=
  let c := vjoin a b
  tab fun j => ⟨Two.get c j, child.slot (parent.endpoint j)⟩

structure Arena (bits : Nat) where
  mem : Array (Word bits)
  region : Region bits mem.size
  tags : TagsFit bits

structure Input (H : LabelledQuotient) (n bits : Nat) where
  rows : ForestIncomingRaw.Prepared H
  owners : Slots H.vertexCount (Option (Fin n))
  orientation : Slots n (Ends (Fin H.vertexCount))
  depth : Slots n Nat
  knownLoss : Fin n → Fin H.vertexCount → Bool
  entryRank : Slots H.origVertexCount Nat
  physicalTail :
    QuotientArc H.origVertexCount H.vertexCount → Fin H.origVertexCount
  arena : Arena bits

namespace Input

variable {H : LabelledQuotient} {n bits : Nat}

@[inline] def arcFields (r : Input H n bits) (a : ForestIncomingRaw.Entry H) :
    Fin H.vertexCount × Fin H.origVertexCount :=
  (a.1, r.physicalTail a.2)

@[inline] def fused (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (cut : Fin n) (s : Fin H.vertexCount) : Values :=
  match r.owners.read s with
  | none => zero
  | some u =>
    PriorBase.run r.arena.mem r.arena.region r.arena.tags bases.data
      ⟨s.val, by simpa only [bases.len] using s.isLt⟩
      u.val (r.depth.read cut)

@[inline] def rowRun (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (cut : Fin n) (y : Fin H.vertexCount) : Values :=
  RawIncoming.run (r.orientation.read cut).endpoint r.entryRank.read
    r.arcFields (r.knownLoss cut) (r.fused bases cut)
    (ForestIncomingRaw.row H r.rows y)

@[inline] def fresh (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (child parent : Fin n) (k : Fin 2) : Values :=
  let s := (r.orientation.read child).endpoint k
  if (r.orientation.read parent).slot s = none then
    r.fused bases parent s
  else
    zero

/-- Install one exit map. Each missing child endpoint makes one fused
query; neither lane scans an incoming row. -/
def install (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (driver parent : Fin n) : Map :=
  let a := r.fresh bases driver parent 0
  let b := r.fresh bases driver parent 1
  pack (r.orientation.read driver) (r.orientation.read parent) a b

/-- Count the calls to `fused` made by `install`: zero, one, or two,
one per missing lane. This uses the same guards as `fresh` and needs
neither base slots nor incoming rows. -/
@[inline] def installFreshCalls (r : Input H n bits)
    (driver parent : Fin n) : Nat :=
  let c := r.orientation.read driver
  let p := r.orientation.read parent
  (if p.slot (c.endpoint 0) = none then 1 else 0) +
    (if p.slot (c.endpoint 1) = none then 1 else 0)

/-- Build one vertex base. The owner selects the cut, not the row:
the only incoming row visited is the row headed by `y`. This is the
only runtime caller of `rowRun`. -/
def base (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (y : Fin H.vertexCount) : Values :=
  match r.owners.read y with
  | none => zero
  | some cut => r.rowRun bases cut y

end Input

/-! Everything below is proof-only; none of the runtime definitions above
depends on `Model`, `Kernel`, or a reference reader. -/

section Packing

variable {H : LabelledQuotient} {m : Nat}

theorem slot_eq_model (W : Model H m) (B : CutPair H)
    (e : Ends (Fin H.vertexCount))
    (he : ∀ j, e.endpoint j = W.endpoint B j)
    (s : Fin H.vertexCount) :
    e.slot s = W.slot B s := by
  simp only [Ends.slot, Model.slot, he]

theorem pack_eq_model (W : Model H m) (i : Fin m)
    (child parent : Ends (Fin H.vertexCount))
    (hc : ∀ j, child.endpoint j = W.endpoint (W.child i) j)
    (hp : ∀ j, parent.endpoint j = W.endpoint (W.parent i) j)
    (a b : Values) :
    pack child parent a b = W.pack i a b := by
  simp only [pack, Model.pack, slot_eq_model W (W.child i) child hc, hp]

end Packing

namespace Input

variable {H : LabelledQuotient} {n bits : Nat}

/-- Discharge one fused-read obligation from the checked arena theorem.
Only this source's base cell is required to contain the specified seed. -/
theorem fused_exact_of_occupied
    (r : Input H n bits) (bases : Slots H.vertexCount (Option Values))
    (cut : Fin n) (s : Fin H.vertexCount) (u : Fin n)
    {endpoints : Nat} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
    {w : Width bits (max r.arena.region.slots endpoints)}
    (ok : Occupied r.arena.mem r.arena.region F ref w)

    (hOwner : r.owners.read s = some u) (hu : u.val < F.size)
    (seed want : Values) (hSeed : bases.read s = some seed)
    (hEval :
      Map.eval
        (PriorBase.accumulated (PaperB.ExitMap.JumpMapRoute.foldFused F ref u.val (r.depth.read cut)))
        seed = want) :
    r.fused bases cut s = want := by
  simp only [fused, hOwner, PriorBase.run_exact_fold ok hu]
  change
    Map.eval
      (PriorBase.accumulated (PaperB.ExitMap.JumpMapRoute.foldFused F ref u.val (r.depth.read cut)))
      ((bases.read s).getD zero) = want
  rw [hSeed]
  exact hEval

private def hit (endpoint : Fin 2 → Fin H.vertexCount)
    (s : Fin H.vertexCount) : Bool :=
  decide (s = endpoint 0) || decide (s = endpoint 1)

/-- The local bridge to the reference raw-row computation. The last
conjunct is about reference readers, not `rowRun`. Rank is needed only
on endpoint hits, DFS only on misses, and fused refinement only on
misses for which the reference DFS test is true. -/
def RowRefines (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (cut : Fin n) (y : Fin H.vertexCount)
    (endpoint : Fin 2 → Fin H.vertexCount)
    (rank : Fin H.origVertexCount → Nat) (want : Values) : Prop :=
  let row := ForestIncomingRaw.row H r.rows y
  ∃ (read : ForestIncomingRaw.Entry H →
        Fin H.vertexCount × Fin H.origVertexCount)
    (loss : Fin H.vertexCount → Bool)
    (jump : Fin H.vertexCount → Values),
    (∀ a ∈ row, r.arcFields a = read a) ∧
    (∀ a ∈ row, hit endpoint (read a).1 = true →
      r.entryRank.read (read a).2 = rank (read a).2) ∧
    (∀ a ∈ row, hit endpoint (read a).1 = false →
      r.knownLoss cut (read a).1 = loss (read a).1) ∧
    (∀ a ∈ row, hit endpoint (read a).1 = false →
      loss (read a).1 = true → r.fused bases cut (read a).1 = jump (read a).1) ∧
    RawIncoming.run endpoint rank read loss jump row = want

private theorem foldl_eq_on {α β : Type} (f g : β → α → β)
    (xs : List α) (acc : β)
    (h : ∀ a ∈ xs, ∀ z, f z a = g z a) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp) acc]
    exact ih _ (fun b hb z => h b (List.mem_cons_of_mem a hb) z)

theorem rowRun_exact (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (cut : Fin n) (y : Fin H.vertexCount)
    (endpoint : Fin 2 → Fin H.vertexCount)
    (rank : Fin H.origVertexCount → Nat) (want : Values)
    (he : ∀ j, (r.orientation.read cut).endpoint j = endpoint j)
    (h : r.RowRefines bases cut y endpoint rank want) :
    r.rowRun bases cut y = want := by
  unfold RowRefines at h
  rcases h with ⟨read, loss, jump, hRead, hRank, hLoss, hJump, hRef⟩
  refine Eq.trans ?_ hRef
  unfold rowRun RawIncoming.run
  rw [show (r.orientation.read cut).endpoint = endpoint from funext he]
  apply foldl_eq_on
  intro a ha acc
  apply congrArg (vjoin acc)
  cases hh : hit endpoint (read a).1 with
  | false =>
    have hb :
        (decide ((read a).1 = endpoint 0) ||
          decide ((read a).1 = endpoint 1)) = false := hh
    cases hl : loss (read a).1 with
    | false =>
      simp only [RawIncoming.arcValue, hRead a ha, hb, hLoss a ha hh, hl]
    | true =>
      simp only [RawIncoming.arcValue, hRead a ha, hb, hLoss a ha hh, hl,
        hJump a ha hh hl]
  | true =>
    have hb :
        (decide ((read a).1 = endpoint 0) ||
          decide ((read a).1 = endpoint 1)) = true := hh
    simp only [RawIncoming.arcValue, hRead a ha, hb, hRank a ha hh]

section KernelAgreement

variable {m : Nat} {W : Model H m} {D : Deps H.vertexCount m}

/-- A missing lane needs only the exact fused read at its endpoint.
A retained lane needs no read obligation. -/
theorem install_exact (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (driver parent : Fin n) (K : Kernel W D)
    (y : Fin H.vertexCount) (i : Fin m)
    (rb : BaseReader (D.installBase i)) (rm : MapReader (D.installMap i))
    (hc : ∀ j, (r.orientation.read driver).endpoint j = W.endpoint (W.child i) j)
    (hp : ∀ j, (r.orientation.read parent).endpoint j = W.endpoint (W.parent i) j)
    (hFused : ∀ k : Fin 2,
      W.slot (W.parent i) (W.endpoint (W.child i) k) = none →
      r.fused bases parent (W.endpoint (W.child i) k) =
        W.ref (W.parent i) (W.endpoint (W.child i) k))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a)) :
    r.install bases driver parent = K.install y i rb rm := by
  have hf (k : Fin 2) :
      r.fresh bases driver parent k = W.refFresh i k := by
    have hs :
        (r.orientation.read parent).slot ((r.orientation.read driver).endpoint k) =
          W.slot (W.parent i) (W.endpoint (W.child i) k) := by
      rw [hc k]
      exact slot_eq_model W (W.parent i) (r.orientation.read parent) hp _
    by_cases e : W.slot (W.parent i) (W.endpoint (W.child i) k) = none
    · rw [fresh, hs, if_pos e, Model.refFresh, if_pos e, hc k]
      exact hFused k e
    · simp only [fresh, hs, Model.refFresh, if_neg e]
  calc
    r.install bases driver parent = W.wantMap i := by
      simp only [install, hf, Model.wantMap]
      exact pack_eq_model W i (r.orientation.read driver)
        (r.orientation.read parent) hc hp (W.refFresh i 0) (W.refFresh i 1)
    _ = K.install y i rb rm := (K.install_exact y i rb rm hb hm).symm

/-- Only the label at `y` is inspected. With no owner there is no row
obligation; with an owner there is exactly one. -/
theorem base_exact (r : Input H n bits)
    (bases : Slots H.vertexCount (Option Values))
    (K : Kernel W D) (y : Fin H.vertexCount)
    (rb : BaseReader (D.vertexBase y)) (rm : MapReader (D.vertexMap y))
    (hNone : r.owners.read y = none → W.owner y = none)
    (hSome : ∀ cut, r.owners.read y = some cut →
      ∃ B : CutPair H, W.owner y = some B ∧
        (∀ j, (r.orientation.read cut).endpoint j = W.endpoint B j) ∧
        r.RowRefines bases cut y (W.endpoint B) W.rank (W.ref B y))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a)) :
    r.base bases y = K.base y rb rm := by
  calc
    r.base bases y = W.wantBase y := by
      cases e : r.owners.read y with
      | none =>
        simp only [base, e, Model.wantBase, hNone e]
      | some cut =>
        obtain ⟨B, hB, he, hr⟩ := hSome cut e
        simpa only [base, e, Model.wantBase, hB] using
          r.rowRun_exact bases cut y (W.endpoint B) W.rank (W.ref B y) he hr
    _ = K.base y rb rm := (K.base_exact y rb rm hb hm).symm

end KernelAgreement
end Input
end PaperB.BuiltExit.PackedRuntime
