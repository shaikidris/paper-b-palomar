module

public import PaperB.RamExitSummarySetup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Stage 4 reusable Word-RAM slices (`PaperB/RamExitSummarySlices.lean`).
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


/-! ### 8. Stage 4 reusable `Interval` / `Coord` / `Map` Word-RAM slices -/

section Stage4Helpers

section CodecWordPreds

def IntervalWordsAt {bits : Nat} (mem : Array (Word bits)) (addr : Nat) : Interval → Prop
  | .empty =>
    (mem[addr]?).map Fin.val = some 0 ∧
    (mem[addr + 1]?).map Fin.val = some 0 ∧
    (mem[addr + 2]?).map Fin.val = some 0
  | .span lo hi =>
    (mem[addr]?).map Fin.val = some 1 ∧
    (mem[addr + 1]?).map Fin.val = some lo ∧
    (mem[addr + 2]?).map Fin.val = some hi

def ValuesWordsAt {bits : Nat} (mem : Array (Word bits)) (addr : Nat) (xs : Values) : Prop :=
  IntervalWordsAt mem addr xs.x0 ∧ IntervalWordsAt mem (addr + 3) xs.x1

def CoordWordsAt {bits : Nat} (mem : Array (Word bits)) (addr : Nat) (c : Coord) : Prop :=
  IntervalWordsAt mem addr c.base ∧
  (mem[addr + 3]?).map Fin.val =
    some (match c.slot with | none => 0 | some 0 => 1 | some 1 => 2)

def MapWordsAt {bits : Nat} (mem : Array (Word bits)) (addr : Nat) (m : Map) : Prop :=
  CoordWordsAt mem addr m.x0 ∧ CoordWordsAt mem (addr + 4) m.x1

theorem intervalWordsAt_frame {bits : Nat} {m1 m2 : Array (Word bits)} {addr : Nat} {x : Interval}
    (h : ∀ i < 3, m2[addr + i]? = m1[addr + i]?)
    (hx : IntervalWordsAt m1 addr x) : IntervalWordsAt m2 addr x := by
  cases x with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · have h0 := h 0 (by decide)
      rw [Nat.add_zero] at h0
      rw [h0]; exact hx.1
    · rw [h 1 (by decide)]; exact hx.2.1
    · rw [h 2 (by decide)]; exact hx.2.2
  | span lo hi =>
    refine ⟨?_, ?_, ?_⟩
    · have h0 := h 0 (by decide)
      rw [Nat.add_zero] at h0
      rw [h0]; exact hx.1
    · rw [h 1 (by decide)]; exact hx.2.1
    · rw [h 2 (by decide)]; exact hx.2.2

theorem coordWordsAt_frame {bits : Nat} {m1 m2 : Array (Word bits)} {addr : Nat} {c : Coord}
    (h : ∀ i < 4, m2[addr + i]? = m1[addr + i]?)
    (hc : CoordWordsAt m1 addr c) : CoordWordsAt m2 addr c :=
  ⟨intervalWordsAt_frame (fun i hi => h i (by omega)) hc.1, by rw [h 3 (by decide)]; exact hc.2⟩

theorem valuesWordsAt_frame {bits : Nat} {m1 m2 : Array (Word bits)} {addr : Nat} {xs : Values}
    (h : ∀ i < 6, m2[addr + i]? = m1[addr + i]?)
    (hxs : ValuesWordsAt m1 addr xs) : ValuesWordsAt m2 addr xs :=
  ⟨intervalWordsAt_frame (fun i hi => h i (by omega)) hxs.1,
   intervalWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact h (3 + i) (by omega)) hxs.2⟩

theorem mapWordsAt_frame {bits : Nat} {m1 m2 : Array (Word bits)} {addr : Nat} {m : Map}
    (h : ∀ i < 8, m2[addr + i]? = m1[addr + i]?)
    (hm : MapWordsAt m1 addr m) : MapWordsAt m2 addr m :=
  ⟨coordWordsAt_frame (fun i hi => h i (by omega)) hm.1,
   coordWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact h (4 + i) (by omega)) hm.2⟩

private theorem wordAt_iff_val {bits : Nat} (mem : Array (Word bits)) (addr : Nat) (w : Word bits) :
    mem[addr]? = some w ↔ (mem[addr]?).map Fin.val = some w.val := by
  constructor
  · intro h
    exact congrArg (Option.map Fin.val) h
  · intro h
    obtain ⟨u, hu, hval⟩ := Option.map_eq_some_iff.mp h
    exact hu.trans (congrArg some (Fin.ext hval))

private theorem finThreeCases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  exact h.imp (fun h => Fin.ext h) (Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h))

theorem intervalWordsAt_encode_iff {bits : Nat} (hTag : TagsFit bits) (mem : Array (Word bits))
    (addr : Nat) (x : Interval) (hx : RankBound (2 ^ bits) x) :
    IntervalWordsAt mem addr x ↔
      ∀ i : Fin 3, mem[addr + i.val]? = some ((intervalCodec hTag).encode x hx i) := by
  have ha := wordAt_iff_val mem addr ((intervalCodec hTag).encode x hx 0)
  have hb := wordAt_iff_val mem (addr + 1) ((intervalCodec hTag).encode x hx 1)
  have hc := wordAt_iff_val mem (addr + 2) ((intervalCodec hTag).encode x hx 2)
  rw [intervalCodec_encode_0] at ha
  rw [intervalCodec_encode_1] at hb
  rw [intervalCodec_encode_2] at hc
  constructor
  · intro h i
    rcases finThreeCases i with rfl | rfl | rfl
    · exact ha.mpr (by cases x <;> exact h.1)
    · exact hb.mpr (by cases x <;> exact h.2.1)
    · exact hc.mpr (by cases x <;> exact h.2.2)
  · intro h
    have h0 := ha.mp (h 0)
    have h1 := hb.mp (h 1)
    have h2 := hc.mp (h 2)
    cases x <;> exact ⟨h0, h1, h2⟩

theorem intervalWordsAt_encode {bits : Nat} (hTag : TagsFit bits) (mem : Array (Word bits))
    (addr : Nat) (x : Interval) (hx : RankBound (2 ^ bits) x) :
    (∀ i : Fin 3, mem[addr + i.val]? = some ((intervalCodec hTag).encode x hx i)) →
    IntervalWordsAt mem addr x :=
  (intervalWordsAt_encode_iff hTag mem addr x hx).mpr

private theorem coordCodec_lower {bits : Nat} (hTag : TagsFit bits) (c : Coord)
    (hc : (coordCodec hTag).valid c) (i : Fin 3) :
    (coordCodec hTag).encode c hc ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ =
      (intervalCodec hTag).encode c.base hc.1 i := by
  rcases finThreeCases i with rfl | rfl | rfl <;> rfl

theorem coordWordsAt_encode_iff {bits : Nat} (hTag : TagsFit bits) (mem : Array (Word bits))
    (addr : Nat) (c : Coord) (hc : (coordCodec hTag).valid c) :
    CoordWordsAt mem addr c ↔
      ∀ i : Fin 4, mem[addr + i.val]? = some ((coordCodec hTag).encode c hc i) := by
  have hs := wordAt_iff_val mem (addr + 3) ((coordCodec hTag).encode c hc 3)
  rw [coordCodec_encode_at] at hs
  change mem[addr + 3]? = _ ↔ (mem[addr + 3]?).map Fin.val =
    some (match c.slot with | none => 0 | some 0 => 1 | some 1 => 2) at hs
  have hLow := intervalWordsAt_encode_iff hTag mem addr c.base hc.1
  constructor
  · intro h i
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi⟩
      exact (congrArg (fun x => mem[addr + i.val]? = some x)
        (coordCodec_lower hTag c hc j)).mpr (hLow.mp h.1 j)
    · have hiEq : i = 3 := Fin.ext (by have hb := i.isLt; omega)
      subst i
      exact hs.mpr h.2
  · intro h
    refine ⟨hLow.mpr (fun j => ?_), hs.mp (h 3)⟩
    exact (congrArg (fun x => mem[addr + j.val]? = some x)
      (coordCodec_lower hTag c hc j)).mp (h ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩)

theorem mapWordsAt_encode_iff {bits : Nat} (hTag : TagsFit bits) (mem : Array (Word bits))
    (addr : Nat) (m : Map) (hm : MapBound (2 ^ bits) m) :
    MapWordsAt mem addr m ↔
      ∀ i : Fin 8, mem[addr + i.val]? = some ((mapCodec hTag).encode m (mapValid_of_mapBound hTag hm) i) := by
  constructor
  · intro h i
    rw [mapCodec_encode_at hTag m hm i]
    by_cases hi : i.val < 4
    · rw [dite_eq_left hi]
      exact (coordWordsAt_encode_iff hTag mem addr m.x0 ⟨hm.1, trivial⟩).mp h.1 ⟨i.val, hi⟩
    · rw [dite_eq_right hi]
      rw [show addr + i.val = (addr + 4) + (i.val - 4) by omega]
      exact (coordWordsAt_encode_iff hTag mem (addr + 4) m.x1 ⟨hm.2, trivial⟩).mp h.2 ⟨i.val - 4, by omega⟩
  · intro h
    refine ⟨(coordWordsAt_encode_iff hTag mem addr m.x0 ⟨hm.1, trivial⟩).mpr (fun i => ?_),
      (coordWordsAt_encode_iff hTag mem (addr + 4) m.x1 ⟨hm.2, trivial⟩).mpr (fun i => ?_)⟩
    · have hi := h ⟨i.val, by omega⟩
      rw [mapCodec_encode_at hTag m hm ⟨i.val, by omega⟩, dite_eq_left i.isLt] at hi
      exact hi
    · have hi := h ⟨4 + i.val, by omega⟩
      rw [mapCodec_encode_at hTag m hm ⟨4 + i.val, by omega⟩, dite_eq_right (by change ¬ 4 + i.val < 4; omega)] at hi
      simpa [Nat.add_assoc] using hi

end CodecWordPreds

end Stage4Helpers

end PaperB.RamProgram.ExitSummaryBuild
