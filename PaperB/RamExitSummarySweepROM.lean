module

public import PaperB.RamExitSummarySweepCount
public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepARun
public import PaperB.RamExitSummaryStage3

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
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

section Stage4Defs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def stage4LoopInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 mIdxKCursor (Nat.lt_of_lt_of_le (by decide) h100) ++
  (metaLoadInstrs reg3 reg4 mIdxN (Nat.lt_of_lt_of_le (by decide) h100) ++
  ([ .branchLt reg2 reg3 10 1615 ] ++
  (metaLoadInstrs reg3 reg4 mIdxOrderBase (Nat.lt_of_lt_of_le (by decide) h100) ++
  ([ .add reg3 reg3 reg2
   , .loadData reg3 reg3
   ] ++
  (metaStoreInstrs reg3 reg4 mIdxCurY (Nat.lt_of_lt_of_le (by decide) h100) ++
  (step4AInstrs 18 h100 ++
  (step4BInstrs 538 h100 ++
  (metaLoadInstrs reg2 reg4 mIdxKCursor (Nat.lt_of_lt_of_le (by decide) h100) ++
  ([ .add reg2 reg2 reg1 ] ++
  (metaStoreInstrs reg2 reg4 mIdxKCursor (Nat.lt_of_lt_of_le (by decide) h100) ++
  [ .goto 3 ]))))))))))

def stage4Instrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg0 reg2 mIdxKCursor (Nat.lt_of_lt_of_le (by decide) h100) ++
  stage4LoopInstrs h100

theorem stage4LoopInstrs_length (h100 : 100 ≤ 2 ^ bits) :
    (stage4LoopInstrs (bits := bits) h100).length = 1612 := by
  dsimp only [stage4LoopInstrs]
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_append, List.length_append, List.length_append]
  rw [step4AInstrs_length, step4BInstrs_length]
  rfl

theorem stage4Instrs_length (h100 : 100 ≤ 2 ^ bits) :
    (stage4Instrs (bits := bits) h100).length = 1615 := by
  dsimp only [stage4Instrs]
  rw [List.length_append, stage4LoopInstrs_length]
  rfl

theorem stage4Instrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (stage4Instrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  have hPred : nonHalt (L := DomL) = sliceNonHalt := by
    funext op
    cases op <;> rfl
  rw [hPred]
  simp [stage4Instrs, stage4LoopInstrs, metaLoadInstrs, metaStoreInstrs,
    sliceNonHalt, step4AInstrs_nonHalt, step4BInstrs_nonHalt]

def stage4Phase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (stage4Instrs (bits := bits) h100) (stage4Instrs_nonHalt (bits := bits) h100)

end Stage4Defs

end PaperB.RamProgram.ExitSummaryBuild
