module

public import PaperB.ExitMap
public import PaperB.Machine
public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.Retention

open PaperB.Machine

/-!
EX4.1. A block has one machine word per cell. The layout is:

* interval (3): tag, low rank, high rank;
* coordinate (4): interval, optional-slot tag;
* map (8): coordinate 0, coordinate 1;
* oriented maps (17): physical map 0, physical map 1, orientation;
* retained record (20): summary, oriented maps.

The orientation bit does not change the physical storage order. Decoding is
total; the reverse roundtrip is asserted only for canonical blocks.
-/

abbrev Block (bits k : Nat) := Fin k → Word bits

def TagsFit (bits : Nat) : Prop := 2 < 2 ^ bits

/-- The generic bounds for zero-based ranks in a declared size `n`. -/
structure Width (bits n : Nat) : Prop where
  ranks : n ≤ 2 ^ bits
  tags : TagsFit bits

def bitsFor (n : Nat) : Nat := Nat.log2 (max n 2) + 1

theorem bitsFor_capacity (n : Nat) : max n 2 < 2 ^ bitsFor n := by
  have h₂ : 2 ≤ max n 2 := Nat.le_max_right _ _
  have hn : max n 2 ≠ 0 := by omega
  unfold bitsFor
  exact (Nat.log2_lt hn).mp (Nat.lt_succ_self _)

theorem bitsFor_width (n : Nat) : Width (bitsFor n) n := by
  have hc := bitsFor_capacity n
  exact ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_lt hc),
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hc⟩

def word {bits : Nat} (x : Nat) (hx : x < 2 ^ bits) : Word bits :=
  ⟨x, hx⟩

def rankWord {bits n : Nat} (h : Width bits n) (r : Fin n) : Word bits :=
  word r.val (Nat.lt_of_lt_of_le r.isLt h.ranks)

@[simp] theorem rankWord_exact {bits n : Nat} (h : Width bits n) (r : Fin n) :
    (rankWord h r).val = r.val := rfl

def tag {bits : Nat} (h : TagsFit bits) (t : Nat) (ht : t ≤ 2) : Word bits :=
  word t (Nat.lt_of_le_of_lt ht h)

@[simp] theorem tag_exact {bits : Nat} (h : TagsFit bits) (t : Nat)
    (ht : t ≤ 2) : (tag h t ht).val = t := rfl

def append {bits a b : Nat} (x : Block bits a) (y : Block bits b) :
    Block bits (a + b) :=
  fun i =>
    if h : i.val < a then x ⟨i.val, h⟩
    else y ⟨i.val - a, by have hi := i.isLt; omega⟩

def front {bits a b : Nat} (r : Block bits (a + b)) : Block bits a :=
  fun i => r ⟨i.val, by have hi := i.isLt; omega⟩

def back {bits a b : Nat} (r : Block bits (a + b)) : Block bits b :=
  fun i => r ⟨a + i.val, by have hi := i.isLt; omega⟩

@[simp] theorem front_append {bits a b : Nat}
    (x : Block bits a) (y : Block bits b) :
    front (a := a) (b := b) (append x y) = x := by
  funext i
  have hi : i.val < a := i.isLt
  simp [front, append, hi]

@[simp] theorem back_append {bits a b : Nat}
    (x : Block bits a) (y : Block bits b) :
    back (a := a) (b := b) (append x y) = y := by
  funext i
  have hn : ¬ a + i.val < a := by omega
  have hv : a + i.val - a = i.val := by omega
  simp [back, append, hn, hv]

structure Codec (bits k : Nat) (α : Type) where
  valid : α → Prop
  encode : (a : α) → valid a → Block bits k
  decode : Block bits k → α
  decode_valid : ∀ r, valid (decode r)
  decode_encode : ∀ a h, decode (encode a h) = a

namespace Codec

variable {bits a b k : Nat} {α β : Type}

def prod (A : Codec bits a α) (B : Codec bits b β) :
    Codec bits (a + b) (α × β) where
  valid p := A.valid p.1 ∧ B.valid p.2
  encode p h := append (A.encode p.1 h.1) (B.encode p.2 h.2)
  decode r := (A.decode (front (b := b) r), B.decode (back (a := a) r))
  decode_valid r := ⟨A.decode_valid _, B.decode_valid _⟩
  decode_encode := by
    intro p h
    cases p
    simp only [front_append, back_append, Codec.decode_encode]

def via (A : Codec bits k α) (f : β → α) (g : α → β)
    (fg : ∀ a, f (g a) = a) (gf : ∀ b, g (f b) = b) :
    Codec bits k β where
  valid b := A.valid (f b)
  encode b h := A.encode (f b) h
  decode r := g (A.decode r)
  decode_valid r := by
    change A.valid (f (g (A.decode r)))
    rw [fg]
    exact A.decode_valid r
  decode_encode b h := by
    change g (A.decode (A.encode (f b) h)) = b
    rw [A.decode_encode, gf]

def two (A : Codec bits k α) : Codec bits (k + k) (Two α) :=
  (prod A A).via
    (fun p : Two α => (p.x0, p.x1))
    (fun p => ⟨p.1, p.2⟩)
    (by intro p; cases p; rfl)
    (by intro p; cases p; rfl)

def Canonical (C : Codec bits k α) (r : Block bits k) : Prop :=
  ∃ a, ∃ h : C.valid a, C.encode a h = r

theorem encode_congr (C : Codec bits k α) {x y : α} (e : x = y)
    (hx : C.valid x) (hy : C.valid y) : C.encode x hx = C.encode y hy := by
  cases e
  rfl

theorem encode_decode (C : Codec bits k α) (r : Block bits k)
    (hr : C.Canonical r) : C.encode (C.decode r) (C.decode_valid r) = r := by
  obtain ⟨x, hx, hr⟩ := hr
  subst r
  exact C.encode_congr (C.decode_encode x hx) _ _

theorem canonical_iff_reencode (C : Codec bits k α) (r : Block bits k) :
    C.Canonical r ↔ C.encode (C.decode r) (C.decode_valid r) = r :=
  ⟨C.encode_decode r, fun h => ⟨C.decode r, C.decode_valid r, h⟩⟩

end Codec

/-- Bounds only: the encoding imposes no new `lo ≤ hi` invariant. -/
def RankBound (limit : Nat) : Interval → Prop
  | .empty => True
  | .span lo hi => lo < limit ∧ hi < limit

theorem rankBound_mono {n m : Nat} (h : n ≤ m) {s : Interval}
    (hs : RankBound n s) : RankBound m s := by
  cases s with
  | empty => trivial
  | span lo hi =>
    change lo < n ∧ hi < n at hs
    exact ⟨Nat.lt_of_lt_of_le hs.1 h, Nat.lt_of_lt_of_le hs.2 h⟩

/-- Min and max select existing ranks; no rank arithmetic can wrap. -/
theorem rankBound_join {n : Nat} {a b : Interval}
    (ha : RankBound n a) (hb : RankBound n b) :
    RankBound n (Interval.join a b) := by
  cases a with
  | empty => exact hb
  | span al ah =>
    cases b with
    | empty => exact ha
    | span bl bh =>
      change al < n ∧ ah < n at ha
      change bl < n ∧ bh < n at hb
      obtain ⟨hal, hah⟩ := ha
      obtain ⟨hbl, hbh⟩ := hb
      change min al bl < n ∧ max ah bh < n
      simp only [Nat.min_def, Nat.max_def]
      constructor <;> split <;> omega

def three {bits : Nat} (a b c : Word bits) : Block bits 3 :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c

def encodeInterval {bits : Nat} (h : TagsFit bits) :
    (s : Interval) → RankBound (2 ^ bits) s → Block bits 3
  | .empty, _ =>
    let z := tag h 0 (by decide)
    three z z z
  | .span lo hi, hs =>
    three (tag h 1 (by decide)) (word lo hs.1) (word hi hs.2)

def decodeInterval {bits : Nat} (r : Block bits 3) : Interval :=
  if (r 0).val = 1 then .span (r 1).val (r 2).val else .empty

def intervalCodec {bits : Nat} (h : TagsFit bits) : Codec bits 3 Interval where
  valid := RankBound (2 ^ bits)
  encode := encodeInterval h
  decode := decodeInterval
  decode_valid r := by
    unfold decodeInterval
    split
    · exact ⟨(r 1).isLt, (r 2).isLt⟩
    · trivial
  decode_encode := by
    intro s hs
    cases s <;> rfl

def joinWords {bits : Nat} (h : TagsFit bits) (a b : Block bits 3) :
    Block bits 3 :=
  let C := intervalCodec h
  C.encode (Interval.join (C.decode a) (C.decode b))
    (rankBound_join (C.decode_valid a) (C.decode_valid b))

theorem decode_joinWords {bits : Nat} (h : TagsFit bits) (a b : Block bits 3) :
    (intervalCodec h).decode (joinWords h a b) =
      Interval.join ((intervalCodec h).decode a) ((intervalCodec h).decode b) :=
  (intervalCodec h).decode_encode _ _

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with hz | ho
  · left
    apply Fin.ext
    exact hz
  · right
    apply Fin.ext
    exact ho

def encodeSlot {bits : Nat} (h : TagsFit bits) (s : Option (Fin 2)) :
    Block bits 1 :=
  fun _ =>
    match s with
    | none => tag h 0 (by decide)
    | some i => if i = 0 then tag h 1 (by decide) else tag h 2 (by decide)

def decodeSlot {bits : Nat} (r : Block bits 1) : Option (Fin 2) :=
  match (r 0).val with
  | 1 => some 0
  | 2 => some 1
  | _ => none

def slotCodec {bits : Nat} (h : TagsFit bits) :
    Codec bits 1 (Option (Fin 2)) where
  valid _ := True
  encode s _ := encodeSlot h s
  decode := decodeSlot
  decode_valid _ := True.intro
  decode_encode := by
    intro s hs
    cases s with
    | none => rfl
    | some i =>
      rcases fin2_cases i with e | e <;> subst i <;> rfl

theorem slot_tags {bits : Nat} (h : TagsFit bits) :
    (encodeSlot h none 0).val = 0 ∧
    (encodeSlot h (some 0) 0).val = 1 ∧
    (encodeSlot h (some 1) 0).val = 2 :=
  ⟨rfl, rfl, rfl⟩

def orientationCodec {bits : Nat} (h : TagsFit bits) : Codec bits 1 Bool where
  valid _ := True
  encode b _ := fun _ => if b then tag h 1 (by decide) else tag h 0 (by decide)
  decode r := (r 0).val == 1
  decode_valid _ := True.intro
  decode_encode := by
    intro b hb
    cases b <;> rfl

def coordCodec {bits : Nat} (h : TagsFit bits) : Codec bits 4 Coord :=
  (Codec.prod (intervalCodec h) (slotCodec h)).via
    (fun c : Coord => (c.base, c.slot))
    (fun p => ⟨p.1, p.2⟩)
    (by intro p; cases p; rfl)
    (by intro c; cases c; rfl)

def mapCodec {bits : Nat} (h : TagsFit bits) : Codec bits 8 Map :=
  Codec.two (coordCodec h)

structure OrientedMaps where
  physical : Two Map
  /-- When true, logical endpoint 0 is physical endpoint 1. -/
  reversed : Bool

def orientedCodec {bits : Nat} (h : TagsFit bits) :
    Codec bits 17 OrientedMaps :=
  (Codec.prod (Codec.two (mapCodec h)) (orientationCodec h)).via
    (fun p : OrientedMaps => (p.physical, p.reversed))
    (fun p => ⟨p.1, p.2⟩)
    (by intro p; cases p; rfl)
    (by intro p; cases p; rfl)

structure Retained where
  summary : Interval
  exits : OrientedMaps

def retainedCodec {bits : Nat} (h : TagsFit bits) : Codec bits 20 Retained :=
  (Codec.prod (intervalCodec h) (orientedCodec h)).via
    (fun r : Retained => (r.summary, r.exits))
    (fun p => ⟨p.1, p.2⟩)
    (by intro p; cases p; rfl)
    (by intro r; cases r; rfl)

def MapBound (n : Nat) (m : Map) : Prop :=
  RankBound n m.x0.base ∧ RankBound n m.x1.base

theorem coord_fits {bits n : Nat} (w : Width bits n) (c : Coord)
    (hc : RankBound n c.base) : (coordCodec w.tags).valid c := by
  change RankBound (2 ^ bits) c.base ∧ True
  exact ⟨rankBound_mono w.ranks hc, True.intro⟩

theorem map_fits {bits n : Nat} (w : Width bits n) (m : Map)
    (hm : MapBound n m) : (mapCodec w.tags).valid m := by
  change (coordCodec w.tags).valid m.x0 ∧ (coordCodec w.tags).valid m.x1
  exact ⟨coord_fits w m.x0 hm.1, coord_fits w m.x1 hm.2⟩

theorem retained_fits {bits n : Nat} (w : Width bits n) (r : Retained)
    (hs : RankBound n r.summary)
    (h₀ : MapBound n r.exits.physical.x0)
    (h₁ : MapBound n r.exits.physical.x1) :
    (retainedCodec w.tags).valid r := by
  change RankBound (2 ^ bits) r.summary ∧
    (((mapCodec w.tags).valid r.exits.physical.x0 ∧
      (mapCodec w.tags).valid r.exits.physical.x1) ∧ True)
  exact ⟨rankBound_mono w.ranks hs,
    ⟨⟨map_fits w _ h₀, map_fits w _ h₁⟩, True.intro⟩⟩

def flip (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def swapTwo {α : Type} (x : Two α) : Two α := ⟨x.x1, x.x0⟩

/-- Rename the input coordinates, leaving an absent slot absent. -/
def swapCoord (c : Coord) : Coord := ⟨c.base, c.slot.map flip⟩

@[simp] theorem swapCoord_none (b : Interval) :
    (swapCoord ⟨b, none⟩).slot = none := rfl

@[simp] theorem swapCoord_zero (b : Interval) :
    (swapCoord ⟨b, some 0⟩).slot = some 1 := rfl

@[simp] theorem swapCoord_one (b : Interval) :
    (swapCoord ⟨b, some 1⟩).slot = some 0 := rfl

/-- Rename both the input and the output coordinates. -/
def swapMap (m : Map) : Map := ⟨swapCoord m.x1, swapCoord m.x0⟩

theorem eval_swapCoord (c : Coord) (xs : Values) :
    Coord.eval (swapCoord c) (swapTwo xs) = Coord.eval c xs := by
  rcases c with ⟨b, s⟩
  cases s with
  | none => rfl
  | some i =>
    rcases fin2_cases i with e | e <;> subst i <;> rfl

theorem eval_swapMap (m : Map) (xs : Values) :
    Map.eval (swapMap m) (swapTwo xs) = swapTwo (Map.eval m xs) := by
  change
    Two.mk (Coord.eval (swapCoord m.x1) (swapTwo xs))
      (Coord.eval (swapCoord m.x0) (swapTwo xs)) =
    Two.mk (Coord.eval m.x1 xs) (Coord.eval m.x0 xs)
  simp only [eval_swapCoord]

theorem swapMap_valid {bits : Nat} (h : TagsFit bits) (m : Map)
    (hm : (mapCodec h).valid m) : (mapCodec h).valid (swapMap m) := by
  change (RankBound (2 ^ bits) m.x0.base ∧ True) ∧
    (RankBound (2 ^ bits) m.x1.base ∧ True) at hm
  change (RankBound (2 ^ bits) m.x1.base ∧ True) ∧
    (RankBound (2 ^ bits) m.x0.base ∧ True)
  exact ⟨hm.2, hm.1⟩

def swapMapWords {bits : Nat} (h : TagsFit bits) (r : Block bits 8) :
    Block bits 8 :=
  let C := mapCodec h
  C.encode (swapMap (C.decode r)) (swapMap_valid h _ (C.decode_valid r))

theorem decode_swapMapWords {bits : Nat} (h : TagsFit bits) (r : Block bits 8) :
    (mapCodec h).decode (swapMapWords h r) = swapMap ((mapCodec h).decode r) :=
  (mapCodec h).decode_encode _ _

def orientedEnd (rev : Bool) (i : Fin 2) : Fin 2 :=
  if rev then flip i else i

def orientedValues (rev : Bool) (xs : Values) : Values :=
  if rev then swapTwo xs else xs

def atPhysical (p : OrientedMaps) (i : Fin 2) : Map := Two.get p.physical i

/-- A logical view of maps whose inputs and outputs use physical names. -/
def atLogical (p : OrientedMaps) (i : Fin 2) : Map :=
  let m := atPhysical p (orientedEnd p.reversed i)
  if p.reversed then swapMap m else m

theorem eval_atLogical (p : OrientedMaps) (i : Fin 2) (xs : Values) :
    Map.eval (atLogical p i) (orientedValues p.reversed xs) =
      orientedValues p.reversed
        (Map.eval (atPhysical p (orientedEnd p.reversed i)) xs) := by
  rcases p with ⟨m, rev⟩
  cases rev with
  | false => rfl
  | true => exact eval_swapMap _ _

theorem retained_eval_exact {bits : Nat} (h : TagsFit bits) (r : Retained)
    (hr : (retainedCodec h).valid r) (i : Fin 2) (xs : Values) :
    Map.eval
        (atLogical ((retainedCodec h).decode ((retainedCodec h).encode r hr)).exits i)
        xs =
      Map.eval (atLogical r.exits i) xs := by
  rw [Codec.decode_encode]

/-!
The I/O model charges one request per cell read or written. A block load
stages its words before decoding; a block store takes staged words as input.
Traces are indexed by request number, not by word data.
-/

inductive Access (k : Nat) where
  | read (i : Fin k)
  | write (i : Fin k)

def readCell {bits k : Nat} (mem : Block bits k) (i : Fin k) :
    Word bits × Access k :=
  (mem i, .read i)

def writeCell {bits k : Nat} (mem : Block bits k) (i : Fin k) (w : Word bits) :
    Block bits k × Access k :=
  ((fun j => if j = i then w else mem j), .write i)

@[simp] theorem writeCell_at {bits k : Nat} (mem : Block bits k)
    (i : Fin k) (w : Word bits) : (writeCell mem i w).1 i = w := by
  simp [writeCell]

theorem writeCell_other {bits k : Nat} (mem : Block bits k)
    (i j : Fin k) (w : Word bits) (h : j ≠ i) :
    (writeCell mem i w).1 j = mem j := by
  simp [writeCell, h]

def readAll {bits k : Nat} (mem : Block bits k) :
    Block bits k × (Fin k → Access k) :=
  (fun i => (readCell mem i).1, fun i => (readCell mem i).2)

/-- These writes are to disjoint cells, so the final value at each cell
is the result of its own write. -/
def writeAll {bits k : Nat} (mem src : Block bits k) :
    Block bits k × (Fin k → Access k) :=
  (fun i => (writeCell mem i (src i)).1 i,
   fun i => (writeCell mem i (src i)).2)

@[simp] theorem readAll_data {bits k : Nat} (mem : Block bits k) :
    (readAll mem).1 = mem := rfl

@[simp] theorem writeAll_data {bits k : Nat} (mem src : Block bits k) :
    (writeAll mem src).1 = src := by
  funext i
  exact writeCell_at mem i (src i)

theorem readAll_field {bits k : Nat} (mem : Block bits k) (i j : Fin k) :
    (readAll mem).2 i = Access.read j ↔ i = j := by
  simp [readAll, readCell]

theorem writeAll_field {bits k : Nat} (mem src : Block bits k) (i j : Fin k) :
    (writeAll mem src).2 i = Access.write j ↔ i = j := by
  simp [writeAll, writeCell]

def requestCount {k : Nat} (trace : Fin k → Access k) : Nat :=
  (List.ofFn trace).length

@[simp] theorem requestCount_eq {k : Nat} (trace : Fin k → Access k) :
    requestCount trace = k := by
  simp only [requestCount, List.length_ofFn]

theorem io_roundtrip {bits k : Nat} {α : Type} (C : Codec bits k α)
    (mem : Block bits k) (a : α) (ha : C.valid a) :
    C.decode (readAll (writeAll mem (C.encode a ha)).1).1 = a := by
  simp only [readAll_data, writeAll_data, Codec.decode_encode]

theorem retained_io_counts {bits : Nat} (h : TagsFit bits)
    (r : Retained) (hr : (retainedCodec h).valid r) (mem : Block bits 20) :
    requestCount (writeAll mem ((retainedCodec h).encode r hr)).2 = 20 ∧
    requestCount (readAll mem).2 = 20 :=
  ⟨requestCount_eq _, requestCount_eq _⟩

/-- Optional flat-memory addressing. Address capacity is separate from
the rank/tag bound: the allocated block must fit after `base`. -/
def offsetWord {bits k : Nat} (base : Word bits) (i : Fin k) : Word bits :=
  word ((base.val + i.val) % (2 ^ bits)) (Nat.mod_lt _ (Nat.two_pow_pos bits))

theorem offsetWord_no_wrap {bits k : Nat} (base : Word bits)
    (h : base.val + k ≤ 2 ^ bits) (i : Fin k) :
    (offsetWord base i).val = base.val + i.val := by
  change (base.val + i.val) % (2 ^ bits) = base.val + i.val
  have hi := i.isLt
  exact Nat.mod_eq_of_lt (by omega)

end PaperB.ExitMap.Retention
