module

public import PaperB.ExitPhysicalKeys
public import PaperB.StaticHeadSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

section

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)
variable {F : JumpForest} {up : Fin F.size → Fin F.size}

variable (E : _root_.EX24.PreStep.Embedding
  (orderedConfig p large) r.out F rank up (fun _ => True))

def exitDenseOwnerCell (y : Fin H.vertexCount) : Option (Fin F.size) :=
  let label : Nat := (selectors (orderedConfig p large) r.out).label y
  if label = 0 then none else some ⟨label, E.label_lt y True.intro⟩

def exitDenseOwnerSlots : PaperB.StaticHeadSweep.Slots H.vertexCount (Option (Fin F.size)) where
  data := Array.ofFn (fun y : Fin H.vertexCount => exitDenseOwnerCell r E y)
  len := by simp

theorem exitDenseOwnerSlots_read (y : Fin H.vertexCount) :
    (exitDenseOwnerSlots r E).read y = exitDenseOwnerCell r E y := by
  simp [PaperB.StaticHeadSweep.Slots.read, exitDenseOwnerSlots]

theorem exitDenseOwnerSlots_read_none_iff (y : Fin H.vertexCount) :
    (exitDenseOwnerSlots r E).read y = none ↔
      ((selectors (orderedConfig p large) r.out).label y : Nat) = 0 := by
  rw [exitDenseOwnerSlots_read]
  by_cases h : ((selectors (orderedConfig p large) r.out).label y : Nat) = 0 <;>
    simp [exitDenseOwnerCell, h]

end

end PaperB.Exit.OrderedReaderResult
