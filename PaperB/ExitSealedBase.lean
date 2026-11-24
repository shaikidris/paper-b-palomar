module

-- Use the import path of the file defining PriorBase.run if it differs
-- in your tree; that path was not included in the excerpt.
public import PaperB.ExitPriorBase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.SealedPriorBase

open PaperB.Machine (Word)
open PaperB.ExitMap.Retention PaperB.StoredPacking PaperB.BuiltExit
open PaperB.ExitMap.JumpMapRoute.StoredExit
open CheckedFold

private def seed (prior : Array (Option Values)) (v : Fin prior.size) :
    Values :=
  (prior[v.val]'(v.isLt)).getD zero

/-- Bounds on the actual seeds used by PriorBase.run, including its
default seed for absent cells. -/
def BaseBound (n : Nat) (prior : Array (Option Values)) : Prop :=
  ∀ v : Fin prior.size,
    RankBound n (seed prior v).x0 ∧ RankBound n (seed prior v).x1

private def rowWord {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (v : Fin prior.size) (k : Fin 6) : Word bits :=
  let C := intervalCodec w.tags
  if hk : k.val < 3 then
    C.encode (seed prior v).x0 (rankBound_mono w.ranks (hb v).1)
      ⟨k.val, hk⟩
  else
    C.encode (seed prior v).x1 (rankBound_mono w.ranks (hb v).2)
      ⟨k.val - 3, by have h := k.isLt; omega⟩

/-- One-time sealing. An absent cell encodes `zero`, not a presence tag. -/
def serialize {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior) :
    Array (Word bits) :=
  Array.ofFn fun j : Fin (6 * prior.size) =>
    rowWord w prior hb
      ⟨j.val / 6, by have h := j.isLt; omega⟩
      ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩

@[simp] theorem seal_size {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior) :
    (serialize w prior hb).size = 6 * prior.size := by
  simp [serialize]

private def flat {N : Nat} (v : Fin N) (k : Fin 6) : Fin (6 * N) :=
  ⟨6 * v.val + k.val, by
    have hv := v.isLt
    have hk := k.isLt
    omega⟩

private theorem seal_get {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (v : Fin prior.size) (k : Fin 6) :
    (serialize w prior hb)[(flat v k).val]'(
      by simpa only [seal_size] using (flat v k).isLt) =
      rowWord w prior hb v k := by
  have hv :
      (⟨(flat v k).val / 6, by have h := (flat v k).isLt; omega⟩ :
        Fin prior.size) = v := by
    apply Fin.ext
    change (6 * v.val + k.val) / 6 = v.val
    have h := k.isLt
    omega
  have hk :
      (⟨(flat v k).val % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) = k := by
    apply Fin.ext
    change (6 * v.val + k.val) % 6 = k.val
    have h := k.isLt
    omega
  simp only [serialize, Array.getElem_ofFn, hv, hk]

/-- A contiguous base view in an existing word bank. This is an offset
and a bounds proof, not a slice or a copy. The packed-map worker still
uses its original `Region bits mem.size`. -/
structure BaseView (N bankSize : Nat) where
  start : Nat
  fits : start + 6 * N ≤ bankSize

@[inline] private def address {N bankSize : Nat}
    (B : BaseView N bankSize) (v : Fin N) (k : Fin 6) : Fin bankSize :=
  ⟨B.start + (flat v k).val, by
    have hj := (flat v k).isLt
    have hB := B.fits
    omega⟩

private theorem address_injective {N bankSize : Nat}
    (B : BaseView N bankSize) (v : Fin N) :
    Function.Injective (address B v) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (fun a : Fin bankSize => a.val) hij
  change B.start + (6 * v.val + i.val) =
    B.start + (6 * v.val + j.val) at h
  omega

/-- The same six-read schedule is used by the production and traced
interpreters. Both triples are fetched before interval decoding. -/
@[inline] private def fetchM {m : Type → Type} [Monad m] {bits : Nat}
    (load : Fin 6 → m (Word bits)) : m (Block bits 3 × Block bits 3) := do
  let a ← load 0
  let b ← load 1
  let c ← load 2
  let d ← load 3
  let e ← load 4
  let f ← load 5
  pure (three a b c, three d e f)

@[inline] private def fetch {bits N : Nat} (bank : Array (Word bits))
    (B : BaseView N bank.size) (v : Fin N) :
    Block bits 3 × Block bits 3 :=
  fetchM (m := Id) fun k =>
    let a := address B v k
    bank[a.val]'(a.isLt)

/-- Proof interpreter only. The log is in reverse read order. -/
private def fetchTrace {bits N : Nat} (bank : Array (Word bits))
    (B : BaseView N bank.size) (v : Fin N) :
    StateM (List Nat) (Block bits 3 × Block bits 3) :=
  fetchM (m := StateM (List Nat)) fun k log =>
    let a := address B v k
    (bank[a.val]'(a.isLt), a.val :: log)

/-- Exactly six array-word reads at the known target, at six distinct
physical indices. This counts calls to the bank load in the Lean reader,
not compiled instructions or cache transactions. -/
theorem physical_reads {bits N : Nat} (bank : Array (Word bits))
    (B : BaseView N bank.size) (v : Fin N) :
    fetchTrace bank B v [] =
      (fetch bank B v,
        [B.start + (6 * v.val + 5), B.start + (6 * v.val + 4),
         B.start + (6 * v.val + 3), B.start + (6 * v.val + 2),
         B.start + (6 * v.val + 1), B.start + (6 * v.val + 0)]) ∧
    Function.Injective (address B v) :=
  ⟨rfl, address_injective B v⟩

/-- The base view contains the sealed words in physical row order. This
is a proof premise, not a comparison performed by a query. -/
def Placed {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (bank : Array (Word bits)) (B : BaseView prior.size bank.size) : Prop :=
  ∀ j : Fin (6 * prior.size),
    bank[B.start + j.val]'(by
      have hj := j.isLt
      have hB := B.fits
      omega) =
    (serialize w prior hb)[j.val]'(by simpa only [seal_size] using j.isLt)

def sealView {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior) :
    BaseView prior.size (serialize w prior hb).size :=
  ⟨0, by simp⟩

theorem seal_placed {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior) :
    Placed w prior hb (serialize w prior hb) (sealView w prior hb) := by
  intro j
  simp only [sealView, Nat.zero_add]

private theorem three_eta {bits : Nat} (b : Block bits 3) :
    three (b 0) (b 1) (b 2) = b := by
  funext j
  have hj := j.isLt
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases h with h | h | h
  · have e : j = 0 := Fin.ext h
    subst j
    rfl
  · have e : j = 1 := Fin.ext h
    subst j
    rfl
  · have e : j = 2 := Fin.ext h
    subst j
    rfl

private theorem fetch_exact {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (bank : Array (Word bits)) (B : BaseView prior.size bank.size)
    (ok : Placed w prior hb bank B) (v : Fin prior.size) :
    fetch bank B v =
      ((intervalCodec w.tags).encode (seed prior v).x0
          (rankBound_mono w.ranks (hb v).1),
       (intervalCodec w.tags).encode (seed prior v).x1
          (rankBound_mono w.ranks (hb v).2)) := by
  have hload :
      (fun k : Fin 6 =>
        bank[(address B v k).val]'((address B v k).isLt)) =
      rowWord w prior hb v := by
    funext k
    exact (ok (flat v k)).trans (seal_get w prior hb v k)
  change fetchM (m := Id) (fun k : Fin 6 =>
      bank[(address B v k).val]'((address B v k).isLt)) = _
  rw [hload]
  let a := (intervalCodec w.tags).encode (seed prior v).x0
    (rankBound_mono w.ranks (hb v).1)
  let b := (intervalCodec w.tags).encode (seed prior v).x1
    (rankBound_mono w.ranks (hb v).2)
  change (three (a 0) (a 1) (a 2), three (b 0) (b 1) (b 2)) = (a, b)
  simp only [three_eta]

@[inline] def readSeed {bits N : Nat} (bank : Array (Word bits))
    (B : BaseView N bank.size) (tags : TagsFit bits) (v : Fin N) :
    Values :=
  let blocks := fetch bank B v
  let C := intervalCodec tags
  ⟨C.decode blocks.1, C.decode blocks.2⟩

theorem readSeed_exact {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (bank : Array (Word bits)) (B : BaseView prior.size bank.size)
    (ok : Placed w prior hb bank B) (v : Fin prior.size) :
    readSeed bank B w.tags v = (prior[v.val]'(v.isLt)).getD zero := by
  change readSeed bank B w.tags v = seed prior v
  unfold readSeed
  rw [fetch_exact w prior hb bank B ok v]
  let x := seed prior v
  let C := intervalCodec w.tags
  let a := C.encode x.x0 (rankBound_mono w.ranks (hb v).1)
  let b := C.encode x.x1 (rankBound_mono w.ranks (hb v).2)
  change (⟨C.decode a, C.decode b⟩ : Values) = x
  have ha : C.decode a = x.x0 := C.decode_encode _ _
  have hb' : C.decode b = x.x1 := C.decode_encode _ _
  rw [ha, hb']


theorem readSeed_none {bits n : Nat} (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (bank : Array (Word bits)) (B : BaseView prior.size bank.size)
    (ok : Placed w prior hb bank B) (v : Fin prior.size)
    (hv : prior[v.val]'(v.isLt) = none) :
    readSeed bank B w.tags v = zero := by
  rw [readSeed_exact w prior hb bank B ok v, hv]
  rfl

/-- Pass `mem` again as `bank` for a base placed in the same word bank,
or pass the separately sealed buffer. Neither case copies a region. -/
@[inline] def run {bits N : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits)
    (bank : Array (Word bits)) (B : BaseView N bank.size)
    (v : Fin N) (u d : Nat) : Values :=
  let folded := foldStored mem R tags u d
  Map.eval (PriorBase.accumulated folded) (readSeed bank B tags v)

theorem run_eq_priorBase {bits n : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (bank : Array (Word bits)) (B : BaseView prior.size bank.size)
    (ok : Placed w prior hb bank B)
    (v : Fin prior.size) (u d : Nat) :
    run mem R w.tags bank B v u d =
      PriorBase.run mem R w.tags prior v u d := by
  simp only [run, PriorBase.run, readSeed_exact w prior hb bank B ok v]

theorem run_eq_priorBase_separate {bits n : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (w : Width bits n)
    (prior : Array (Option Values)) (hb : BaseBound n prior)
    (v : Fin prior.size) (u d : Nat) :
    run mem R w.tags (serialize w prior hb) (sealView w prior hb) v u d =
      PriorBase.run mem R w.tags prior v u d :=
  run_eq_priorBase mem R w prior hb
    (serialize w prior hb) (sealView w prior hb) (seal_placed w prior hb) v u d

end PaperB.ExitMap.SealedPriorBase
