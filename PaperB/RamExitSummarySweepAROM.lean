module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepMap

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary builder (`PaperB/RamExitSummaryBuild.lean`).

Contains:
1. Mathematical bridges connecting the Word-RAM Stage 4 computations (`Step 4A` incoming-arc
   base fold, `Step 4B` endpoint-lift + `Stored.parentOnly`/`Stored.skew`) to
   `ActualSealedContract`, `DecodedOccupied`, `LiveStoreOK`, `BaseBound`, and
   `SealedPriorBase.Placed`.
2. `stage4Phase` (`run_stage4`), composed via `PhaseChain` & `run_linkNonEmpty` with
   `setupPhases` into the single fixed 15-register Word-RAM program `exitSummaryBuildProgram`,
   proving `run_exitSummaryBuild`.
-/

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

/-! ### 11. `Step4ASlice`: Single-Vertex Prior-Base Sweep (`run_step4A`) -/

section Step4ASlice

section Defs

variable {bits : Nat}

def step4ASetup_selector (basePc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg3 mIdxCurY (by dsimp only [mIdxCurY]; omega) ++
  metaLoadInstrs reg3 reg4 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega) ++
  [ .add reg3 reg3 reg2
  , .loadInput reg3 reg3
  , .branchLt reg0 reg3 (basePc + 9) endPc
  ]

def step4ASetup_backPointers (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg3 reg4 mIdxCurOwner (by dsimp only [mIdxCurOwner]; omega) ++
  metaLoadInstrs reg4 reg5 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega) ++
  [ .add reg4 reg4 reg3, .loadInput reg4 reg4, .sub reg4 reg4 reg1 ] ++
  metaStoreInstrs reg4 reg5 48 (by omega) ++
  metaLoadInstrs reg4 reg5 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega) ++
  [ .add reg4 reg4 reg3, .loadInput reg4 reg4 ] ++
  metaStoreInstrs reg4 reg5 49 (by omega)

def step4ASetup_interval (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg4 reg5 mIdxFEntryInBase (by dsimp only [mIdxFEntryInBase]; omega) ++
  [ .add reg4 reg4 reg3, .loadInput reg4 reg4 ] ++
  metaStoreInstrs reg4 reg5 50 (by omega) ++
  metaLoadInstrs reg4 reg5 mIdxFStopInBase (by dsimp only [mIdxFStopInBase]; omega) ++
  [ .add reg4 reg4 reg3, .loadInput reg4 reg4 ] ++
  metaStoreInstrs reg4 reg5 51 (by omega)

def step4ASetup_accumulators (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .loadData reg4 reg3 ] ++
  metaStoreInstrs reg4 reg5 52 (by omega) ++
  metaStoreInstrs reg0 reg5 30 (by omega) ++
  metaStoreInstrs reg0 reg5 31 (by omega) ++
  metaStoreInstrs reg0 reg5 32 (by omega) ++
  metaStoreInstrs reg0 reg5 33 (by omega) ++
  metaStoreInstrs reg0 reg5 34 (by omega) ++
  metaStoreInstrs reg0 reg5 35 (by omega)

def step4ASetup_arcs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg4 reg5 mIdxInStartBase (by dsimp only [mIdxInStartBase]; omega) ++
  [ .add reg4 reg4 reg2, .loadData reg5 reg4 ] ++
  metaStoreInstrs reg5 reg6 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega) ++
  [ .add reg4 reg4 reg1, .loadData reg5 reg4 ] ++
  metaStoreInstrs reg5 reg6 mIdxArcEnd (by dsimp only [mIdxArcEnd]; omega)

def step4ASetupInstrs (basePc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4ASetup_selector basePc endPc h100 ++
  step4ASetup_backPointers h100 ++
  step4ASetup_interval h100 ++
  step4ASetup_accumulators h100 ++
  step4ASetup_arcs h100

def step4A_decode (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega) ++
  metaLoadInstrs reg3 reg4 mIdxArcEnd (by dsimp only [mIdxArcEnd]; omega) ++
  [ .branchLt reg2 reg3 (loopPc + 7) (loopPc + 406) ] ++
  metaLoadInstrs reg4 reg5 mIdxInArcIdBase (by dsimp only [mIdxInArcIdBase]; omega) ++
  [ .add reg4 reg4 reg2, .loadData reg4 reg4 ] ++
  metaLoadInstrs reg5 reg6 mIdxQSrcInBase (by dsimp only [mIdxQSrcInBase]; omega) ++
  [ .add reg5 reg5 reg4, .loadInput reg5 reg5 ] ++
  metaStoreInstrs reg5 reg6 53 (by omega) ++
  metaLoadInstrs reg6 reg7 mIdxQTailRankInBase (by dsimp only [mIdxQTailRankInBase]; omega) ++
  [ .add reg6 reg6 reg4, .loadInput reg6 reg6 ] ++
  metaStoreInstrs reg6 reg7 54 (by omega) ++
  metaLoadInstrs reg7 reg8 48 (by omega) ++
  [ .branchLt reg5 reg7 (loopPc + 73) (loopPc + 32)
  , .branchLt reg7 reg5 (loopPc + 73) (loopPc + 33)
  ]

def step4ADirectInstrs (entryPc donePc accOff : Nat) (hOff : accOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg1 reg8 42 (by omega) ++
  metaStoreInstrs reg6 reg8 43 (by omega) ++
  metaStoreInstrs reg6 reg8 44 (by omega) ++
  [ .imm reg2 ⟨accOff, hOff⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨42, by omega⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (entryPc + 14) ++
  [ .goto donePc ]

def step4A_firstEndpoint (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4ADirectInstrs (loopPc + 33) (loopPc + 398) 30 (by omega) h100

def step4A_secondEndpoint (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg7 reg8 49 (by omega) ++
  [ .branchLt reg5 reg7 (loopPc + 118) (loopPc + 77)
  , .branchLt reg7 reg5 (loopPc + 118) (loopPc + 78)
  ] ++
  step4ADirectInstrs (loopPc + 78) (loopPc + 398) 33 (by omega) h100

def step4A_ancestryCheck (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg7 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega) ++
  [ .add reg6 reg6 reg5
  , .loadInput reg6 reg6
  , .branchLt reg0 reg6 (loopPc + 124) (loopPc + 398)
  ] ++
  metaLoadInstrs reg7 reg8 mIdxFEntryInBase (by dsimp only [mIdxFEntryInBase]; omega) ++
  [ .add reg7 reg7 reg6, .loadInput reg7 reg7 ] ++
  metaLoadInstrs reg8 reg9 50 (by omega) ++
  [ .branchLt reg7 reg8 (loopPc + 398) (loopPc + 133) ] ++
  metaLoadInstrs reg8 reg9 51 (by omega) ++
  [ .branchLt reg7 reg8 (loopPc + 137) (loopPc + 398) ]

def step4A_liftPreparation (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg6 reg8 mIdxEvalU (by dsimp only [mIdxEvalU]; omega) ++
  metaLoadInstrs reg7 reg8 52 (by omega) ++
  metaStoreInstrs reg7 reg8 mIdxEvalD (by dsimp only [mIdxEvalD]; omega) ++
  metaLoadInstrs reg3 reg8 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega) ++
  mul6Instrs reg4 reg5 ++
  [ .add reg3 reg3 reg4
  , .imm reg2 ⟨36, by omega⟩, .add reg2 rMeta reg2
  ] ++
  copy6Instrs reg2 reg3 reg4

def step4A_ancestry (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4A_ancestryCheck loopPc h100 ++ step4A_liftPreparation h100

def step4A_joinFirst (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg2 ⟨30, by omega⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨36, by omega⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (loopPc + 343)

def step4A_joinSecond (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg2 ⟨33, by omega⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨39, by omega⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (loopPc + 373)

def step4A_evaluate (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  eval15Instrs (loopPc + 177) h100 ++
  step4A_joinFirst loopPc h100 ++ step4A_joinSecond loopPc h100

def step4A_advance (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega) ++
  [ .add reg2 reg2 reg1 ] ++
  metaStoreInstrs reg2 reg4 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega) ++
  [ .goto loopPc ]

def step4ALoopInstrs (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4A_decode loopPc h100 ++
  step4A_firstEndpoint loopPc h100 ++
  step4A_secondEndpoint loopPc h100 ++
  step4A_ancestry loopPc h100 ++
  step4A_evaluate loopPc h100 ++
  step4A_advance loopPc h100

def step4AWritePriorInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg4 reg5 mIdxCurY (by dsimp only [mIdxCurY]; omega) ++
  mul6Instrs reg2 reg4 ++
  metaLoadInstrs reg4 reg5 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega) ++
  [ .add reg2 reg4 reg2
  , .imm reg3 ⟨30, by omega⟩, .add reg3 rMeta reg3
  ] ++
  copy6Instrs reg2 reg3 reg4

def step4AInstrs (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4ASetupInstrs basePc (basePc + 520) h100 ++
  step4ALoopInstrs (basePc + 80) h100 ++
  step4AWritePriorInstrs h100

@[local simp] private theorem metaLoad_len (d t : Fin 15) (off : Nat)
    (h : off < 2 ^ bits) : (metaLoadInstrs d t off h).length = 3 := rfl

@[local simp] private theorem metaStore_len (s t : Fin 15) (off : Nat)
    (h : off < 2 ^ bits) : (metaStoreInstrs s t off h).length = 3 := rfl

@[local simp] private theorem metaLoad_noHalt (d t : Fin 15) (off : Nat)
    (h : off < 2 ^ bits) : (metaLoadInstrs d t off h).all sliceNonHalt = true := rfl

@[local simp] private theorem metaStore_noHalt (s t : Fin 15) (off : Nat)
    (h : off < 2 ^ bits) : (metaStoreInstrs s t off h).all sliceNonHalt = true := rfl

private theorem step4ASetup_selector_len (basePc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_selector (bits := bits) basePc endPc h100).length = 9 := by
  simp only [step4ASetup_selector, List.length_append, metaLoad_len,
    List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem step4ASetup_backPointers_len (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_backPointers (bits := bits) h100).length = 20 := by
  simp only [step4ASetup_backPointers, List.length_append, metaLoad_len, metaStore_len,
    List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem step4ASetup_interval_len (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_interval (bits := bits) h100).length = 16 := by
  simp only [step4ASetup_interval, List.length_append, metaLoad_len, metaStore_len,
    List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem step4ASetup_accumulators_len (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_accumulators (bits := bits) h100).length = 22 := by
  simp only [step4ASetup_accumulators, List.length_append, metaStore_len,
    List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem step4ASetup_arcs_len (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_arcs (bits := bits) h100).length = 13 := by
  simp only [step4ASetup_arcs, List.length_append, metaLoad_len, metaStore_len,
    List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem step4ASetup_selector_nonHalt (basePc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_selector (bits := bits) basePc endPc h100).all sliceNonHalt = true := by
  simp only [step4ASetup_selector, List.all_append, metaLoad_noHalt,
    List.all_cons, List.all_nil, sliceNonHalt, Bool.true_and]

private theorem step4ASetup_backPointers_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_backPointers (bits := bits) h100).all sliceNonHalt = true := by
  simp only [step4ASetup_backPointers, List.all_append, metaLoad_noHalt, metaStore_noHalt,
    List.all_cons, List.all_nil, sliceNonHalt, Bool.true_and]

private theorem step4ASetup_interval_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_interval (bits := bits) h100).all sliceNonHalt = true := by
  simp only [step4ASetup_interval, List.all_append, metaLoad_noHalt, metaStore_noHalt,
    List.all_cons, List.all_nil, sliceNonHalt, Bool.true_and]

private theorem step4ASetup_accumulators_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_accumulators (bits := bits) h100).all sliceNonHalt = true := by
  simp only [step4ASetup_accumulators, List.all_append, metaStore_noHalt,
    List.all_cons, List.all_nil, sliceNonHalt, Bool.true_and]

private theorem step4ASetup_arcs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetup_arcs (bits := bits) h100).all sliceNonHalt = true := by
  simp only [step4ASetup_arcs, List.all_append, metaLoad_noHalt, metaStore_noHalt,
    List.all_cons, List.all_nil, sliceNonHalt, Bool.true_and]

theorem step4ASetupInstrs_length (basePc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetupInstrs (bits := bits) basePc endPc h100).length = 80 := by simp only [step4ASetupInstrs, List.length_append, step4ASetup_selector_len,
    step4ASetup_backPointers_len, step4ASetup_interval_len, step4ASetup_accumulators_len,
    step4ASetup_arcs_len, Nat.reduceAdd]

private theorem step4A_decode_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_decode (bits := bits) pc h100).length = 33 := by simp [step4A_decode]

private theorem step4A_firstEndpoint_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_firstEndpoint (bits := bits) pc h100).length = 40 := by simp [step4A_firstEndpoint, step4ADirectInstrs, intervalJoinInstrs_length]

private theorem step4A_secondEndpoint_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_secondEndpoint (bits := bits) pc h100).length = 45 := by simp [step4A_secondEndpoint, step4ADirectInstrs, intervalJoinInstrs_length]

private theorem step4A_ancestry_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_ancestry (bits := bits) pc h100).length = 59 := by simp [step4A_ancestry, step4A_ancestryCheck, step4A_liftPreparation, mul6Instrs, copy6Instrs_length]

private theorem step4A_evaluate_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_evaluate (bits := bits) pc h100).length = 221 := by simp [step4A_evaluate, step4A_joinFirst, step4A_joinSecond, eval15Instrs_length, intervalJoinInstrs_length]

private theorem step4A_advance_length (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_advance (bits := bits) pc h100).length = 8 := by simp [step4A_advance]

theorem step4ALoopInstrs_length (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4ALoopInstrs (bits := bits) loopPc h100).length = 406 := by
  simp [step4ALoopInstrs, step4A_decode_length,
    step4A_firstEndpoint_length,
    step4A_secondEndpoint_length,
    step4A_ancestry_length,
    step4A_evaluate_length,
    step4A_advance_length]

theorem step4AWritePriorInstrs_length (h100 : 100 ≤ 2 ^ bits) :
    (step4AWritePriorInstrs (bits := bits) h100).length = 34 := by simp [step4AWritePriorInstrs, mul6Instrs, copy6Instrs_length]

theorem step4AInstrs_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4AInstrs (bits := bits) basePc h100).length = 520 := by
  simp [step4AInstrs, step4ASetupInstrs_length, step4ALoopInstrs_length,
    step4AWritePriorInstrs_length]

@[local simp] private theorem step4ASetupInstrs_noHalt (pc endPc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4ASetupInstrs (bits := bits) pc endPc h100).all sliceNonHalt = true := by
  simp only [step4ASetupInstrs, List.all_append, step4ASetup_selector_nonHalt,
    step4ASetup_backPointers_nonHalt, step4ASetup_interval_nonHalt,
    step4ASetup_accumulators_nonHalt, step4ASetup_arcs_nonHalt, Bool.true_and]

@[local simp] private theorem step4A_decode_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_decode (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_decode, sliceNonHalt]

@[local simp] private theorem step4A_firstEndpoint_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_firstEndpoint (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_firstEndpoint, step4ADirectInstrs, sliceNonHalt, intervalJoinInstrs_nonHalt]

@[local simp] private theorem step4A_secondEndpoint_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_secondEndpoint (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_secondEndpoint, step4ADirectInstrs, sliceNonHalt, intervalJoinInstrs_nonHalt]

@[local simp] private theorem step4A_ancestry_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_ancestry (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_ancestry, step4A_ancestryCheck, step4A_liftPreparation, sliceNonHalt, mul6Instrs, copy6Instrs_nonHalt]

@[local simp] private theorem step4A_evaluate_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_evaluate (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_evaluate, step4A_joinFirst, step4A_joinSecond, sliceNonHalt, eval15Instrs_nonHalt, intervalJoinInstrs_nonHalt]

@[local simp] private theorem step4A_advance_noHalt (pc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4A_advance (bits := bits) pc h100).all sliceNonHalt = true := by
  simp [step4A_advance, sliceNonHalt]

@[local simp] private theorem step4AWritePriorInstrs_noHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4AWritePriorInstrs (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4AWritePriorInstrs, sliceNonHalt, mul6Instrs, copy6Instrs_nonHalt]

theorem step4AInstrs_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4AInstrs (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4AInstrs, step4ALoopInstrs]

end Defs

section Specs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4A_advance_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 398) (step4A_advance pc h100) := by
  unfold step4ALoopInstrs at h
  have placed := Placed_append_right h
  simpa only [List.length_append, step4A_decode_length, step4A_firstEndpoint_length,
    step4A_secondEndpoint_length, step4A_ancestry_length, step4A_evaluate_length,
    Nat.reduceAdd] using placed

theorem step4A_decode_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code pc (step4A_decode pc h100) := by
  unfold step4ALoopInstrs at h
  exact Placed_append_left (Placed_append_left (Placed_append_left
    (Placed_append_left (Placed_append_left h))))

theorem step4A_firstEndpoint_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 33) (step4A_firstEndpoint pc h100) := by
  unfold step4ALoopInstrs at h
  have hPrefix := Placed_append_left (Placed_append_left (Placed_append_left (Placed_append_left h)))
  simpa only [step4A_decode_length] using Placed_append_right hPrefix

theorem step4A_secondEndpoint_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 73) (step4A_secondEndpoint pc h100) := by
  unfold step4ALoopInstrs at h
  have hPrefix := Placed_append_left (Placed_append_left (Placed_append_left h))
  simpa only [List.length_append, step4A_decode_length, step4A_firstEndpoint_length, Nat.reduceAdd]
    using Placed_append_right hPrefix

theorem step4A_secondDirect_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 78) (step4ADirectInstrs (pc + 78) (pc + 398) 33 (by omega) h100) := by
  have hSecond := step4A_secondEndpoint_placed h
  exact Placed_append_right hSecond

theorem step4A_ancestry_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 118) (step4A_ancestry pc h100) := by
  unfold step4ALoopInstrs at h
  have hPrefix := Placed_append_left (Placed_append_left h)
  simpa only [List.length_append, step4A_decode_length, step4A_firstEndpoint_length,
    step4A_secondEndpoint_length, Nat.reduceAdd] using Placed_append_right hPrefix

theorem step4A_ancestryCheck_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code (pc + 118) (step4A_ancestry pc h100)) :
    Placed code (pc + 118) (step4A_ancestryCheck pc h100) :=
  Placed_append_left h

theorem step4A_liftPreparation_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code (pc + 118) (step4A_ancestry pc h100)) :
    Placed code (pc + 137) (step4A_liftPreparation h100) := by
  have hLen : (step4A_ancestryCheck pc h100).length = 19 := by
    simp [step4A_ancestryCheck, metaLoad_len]
  unfold step4A_ancestry at h
  simpa only [hLen, Nat.add_assoc, Nat.reduceAdd] using Placed_append_right h

theorem step4A_evaluate_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 177) (step4A_evaluate pc h100) := by
  unfold step4ALoopInstrs at h
  simpa only [List.length_append, step4A_decode_length, step4A_firstEndpoint_length,
    step4A_secondEndpoint_length, step4A_ancestry_length, Nat.reduceAdd]
    using Placed_append_right (Placed_append_left h)

theorem step4A_eval15_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 177) (eval15Instrs (pc + 177) h100) :=
  Placed_append_left (Placed_append_left (step4A_evaluate_placed h))

theorem step4A_joinFirst_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 338) (step4A_joinFirst pc h100) := by
  have hEval := step4A_evaluate_placed h
  unfold step4A_evaluate at hEval
  simpa only [eval15Instrs_length, Nat.add_assoc, Nat.reduceAdd]
    using Placed_append_right (Placed_append_left hEval)

theorem step4A_joinSecond_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ALoopInstrs pc h100)) :
    Placed code (pc + 368) (step4A_joinSecond pc h100) := by
  have hEval := step4A_evaluate_placed h
  unfold step4A_evaluate at hEval
  have hJoin : (step4A_joinFirst pc h100).length = 30 := by
    simp [step4A_joinFirst, intervalJoinInstrs_length]
  simpa only [List.length_append, eval15Instrs_length, hJoin, Nat.add_assoc, Nat.reduceAdd]
    using Placed_append_right hEval

theorem Placed_drop {code : Program DomL} {pc : Nat} {ops : List (Instr bits 15)}
    (h : Placed code pc ops) (n : Nat) : Placed code (pc + n) (ops.drop n) := by
  intro i op hi
  rw [Nat.add_assoc]
  exact h (n + i) op (by simpa only [List.getElem?_drop] using hi)

theorem Placed_window {code : Program DomL} {pc : Nat} {ops block : List (Instr bits 15)}
    (h : Placed code pc ops) (n : Nat)
    (hBlock : (ops.drop n).take block.length = block) : Placed code (pc + n) block := by
  intro i op hi
  have hLt := (List.getElem?_eq_some_iff.mp hi).1
  apply Placed_drop h n i op
  rw [← List.getElem?_take_of_lt hLt, hBlock]
  exact hi

end Specs

end Step4ASlice

end PaperB.RamProgram.ExitSummaryBuild
