module

public import PaperB.ExitPhysicalKeys
public import PaperB.ExitPackedRuntime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.BuiltExit.PackedRuntime (Ends)
open StaticHeadSweep.Slots

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)
variable (n : Nat) (fallback : Fin H.vertexCount)

def physicalSlotEnds : Array (Ends (Fin H.vertexCount)) :=
  Array.ofFn fun slot : Fin n =>
    match exitBackKey? r slot.val with
    | some B => ⟨B.fst, B.snd⟩
    | none => ⟨fallback, fallback⟩

@[simp] theorem physicalSlotEnds_size :
    (physicalSlotEnds r n fallback).size = n := by
  simp [physicalSlotEnds]

theorem physicalSlotEnds_fit (slot : Fin n) :
    slot.val < (physicalSlotEnds r n fallback).size := by
  simpa only [physicalSlotEnds_size] using slot.isLt

theorem physicalSlotEnds_read (slot : Fin n) {B : CutPair H}
    (h : exitBackKey? r slot.val = some B) :
    (physicalSlotEnds r n fallback)[slot.val]'(physicalSlotEnds_fit r n fallback slot) =
      ⟨B.fst, B.snd⟩ := by
  simp [physicalSlotEnds, h]

theorem physicalSlotEnds_endpoints (slot : Fin n) {B : CutPair H}
    (h : exitBackKey? r slot.val = some B) :
    let e := (physicalSlotEnds r n fallback)[slot.val]'(physicalSlotEnds_fit r n fallback slot)
    e.endpoint 0 = B.fst ∧ e.endpoint 1 = B.snd := by
  dsimp only
  rw [physicalSlotEnds_read r n fallback slot h]
  exact ⟨rfl, rfl⟩

end PaperB.Exit.OrderedReaderResult
