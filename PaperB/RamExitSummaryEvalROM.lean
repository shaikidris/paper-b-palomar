module

public import PaperB.RamExitSummaryEvalFold

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

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

/-! The evaluator instruction layout and the placement of its reusable slices. -/

section Defs

variable {bits : Nat}

def eval15Prefix (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega) ++
  [ .loadData reg3 reg2 ] ++
  metaLoadInstrs reg4 reg5 mIdxEvalD (by dsimp only [mIdxEvalD]; omega) ++
  [ .branchLt reg4 reg3 (basePc + 8) (basePc + 161) ] ++
  metaLoadInstrs reg6 reg5 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega) ++
  mul18Instrs reg7 reg5 reg2 ++
  [ .add reg6 reg6 reg7
  , .add reg7 reg6 reg1
  , .loadData reg7 reg7
  , .loadData reg8 reg7
  , .branchLt reg8 reg4 (basePc + 27) (basePc + 21)
  , .imm reg5 ⟨10, by omega⟩
  , .add reg2 reg6 reg5
  ] ++
  metaStoreInstrs reg7 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega) ++
  [ .goto (basePc + 33)
  , .loadData reg7 reg6
  , .add reg2 reg1 reg1
  , .add reg2 reg6 reg2
  ] ++
  metaStoreInstrs reg7 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega) ++
  [ .imm reg5 ⟨mIdxEval0, by dsimp only [mIdxEval0]; omega⟩
  , .add reg3 rMeta reg5
  , .imm reg5 ⟨mIdxTmp0, by dsimp only [mIdxTmp0]; omega⟩
  , .add reg4 rMeta reg5
  ]

theorem eval15Prefix_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (eval15Prefix (bits := bits) basePc h100).length = 37 := rfl

def eval15Reload (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg5 ⟨mIdxTmp0, by dsimp only [mIdxTmp0]; omega⟩
  , .add reg4 rMeta reg5
  ]

def eval15Instrs (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  eval15Prefix basePc h100 ++ mapEvalInstrs (basePc + 37) ++ eval15Reload h100 ++
    copy6Instrs reg3 reg4 reg5 ++ [.goto basePc]

theorem eval15Instrs_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (eval15Instrs (bits := bits) basePc h100).length = 161 := by
  rfl

theorem eval15Instrs_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (eval15Instrs (bits := bits) basePc h100).all sliceNonHalt = true := by
  rfl

end Defs

section Placement

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem placed_eval15_mapEval {code : Program DomL} {pc : Nat} {h100 : 100 ≤ 2 ^ bits}
    (h : Placed code pc (eval15Instrs pc h100)) :
    Placed code (pc + 37) (mapEvalInstrs (pc + 37)) := by
  have hs := Placed_append_left (Placed_append_left (Placed_append_left h))
  exact Placed_append_right hs

theorem placed_eval15_copy6 {code : Program DomL} {pc : Nat} {h100 : 100 ≤ 2 ^ bits}
    (h : Placed code pc (eval15Instrs pc h100)) :
    Placed code (pc + 138) (copy6Instrs reg3 reg4 reg5) := by
  have hs := Placed_append_left h
  exact Placed_append_right hs

end Placement

end PaperB.RamProgram.ExitSummaryBuild
