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
set_option maxHeartbeats 350000

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

section Step4BSlice

section Defs

variable {bits : Nat}

private theorem metaLoad_length (dst tmp : Fin 15) (off : Nat) (h : off < 2 ^ bits) :
    (metaLoadInstrs dst tmp off h).length = 3 := rfl

private theorem metaStore_length (src tmp : Fin 15) (off : Nat) (h : off < 2 ^ bits) :
    (metaStoreInstrs src tmp off h).length = 3 := rfl

private theorem metaLoad_nonHalt (dst tmp : Fin 15) (off : Nat) (h : off < 2 ^ bits) :
    (metaLoadInstrs dst tmp off h).all sliceNonHalt = true := rfl

private theorem metaStore_nonHalt (src tmp : Fin 15) (off : Nat) (h : off < 2 ^ bits) :
    (metaStoreInstrs src tmp off h).all sliceNonHalt = true := rfl

def copy8Instrs (dst src tmp : Fin 15) : List (Instr bits 15) :=
  [ .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1
  , .loadData tmp src, .storeData dst tmp
  ]

theorem copy8Instrs_length (dst src tmp : Fin 15) :
    (copy8Instrs (bits := bits) dst src tmp).length = 30 := rfl

theorem copy8Instrs_nonHalt (dst src tmp : Fin 15) :
    (copy8Instrs (bits := bits) dst src tmp).all sliceNonHalt = true := by
  rfl

def step4BFresh_endpointCheck (basePc : Nat) (zOff : Nat) (hzOff : zOff < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg7 zOff hzOff ++
  metaLoadInstrs reg3 reg7 52 (by omega) ++
  [ .branchLt reg2 reg3 (basePc + 8) (basePc + 7)
  , .branchLt reg3 reg2 (basePc + 8) (basePc + 220)
  ] ++
  metaLoadInstrs reg3 reg7 53 (by omega) ++
  [ .branchLt reg2 reg3 (basePc + 13) (basePc + 12)
  , .branchLt reg3 reg2 (basePc + 13) (basePc + 220)
  ]

private theorem step4BFresh_endpointCheck_length (basePc : Nat) (zOff : Nat) (hzOff : zOff < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_endpointCheck (bits := bits) basePc zOff hzOff h100).length = 13 := by
  simp [step4BFresh_endpointCheck, List.length_cons, List.length_nil, Nat.reduceAdd, metaLoad_length]

@[local simp] private theorem step4BFresh_endpointCheck_nonHalt (basePc : Nat) (zOff : Nat) (hzOff : zOff < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_endpointCheck (bits := bits) basePc zOff hzOff h100).all sliceNonHalt = true := by
  simp [step4BFresh_endpointCheck, List.all_cons, List.all_nil, sliceNonHalt, metaLoad_nonHalt]


def step4BFresh_prepare (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg4 reg7 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega) ++
  [ .add reg4 reg4 reg2, .loadInput reg4 reg4 ] ++
  metaStoreInstrs reg4 reg7 mIdxEvalU (by dsimp only [mIdxEvalU]; omega) ++
  metaLoadInstrs reg4 reg7 54 (by omega) ++
  metaStoreInstrs reg4 reg7 mIdxEvalD (by dsimp only [mIdxEvalD]; omega) ++
  metaLoadInstrs reg3 reg7 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega) ++
  mul6Instrs reg4 reg2 ++
  [ .add reg3 reg3 reg4
  , .imm reg2 ⟨36, by omega⟩, .add reg2 rMeta reg2
  ]

private theorem step4BFresh_prepare_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_prepare (bits := bits) h100).length = 23 := by
  simp [step4BFresh_prepare, List.length_cons, List.length_nil, Nat.reduceAdd, metaLoad_length, metaStore_length, mul6Instrs]

@[local simp] private theorem step4BFresh_prepare_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_prepare (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BFresh_prepare, List.all_cons, List.all_nil, sliceNonHalt, metaLoad_nonHalt, metaStore_nonHalt, mul6Instrs]


def step4BFresh_evaluate (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  copy6Instrs reg2 reg3 reg4 ++
  eval15Instrs (basePc + 58) h100 ++
  [ .goto (basePc + 238) ]

private theorem step4BFresh_evaluate_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_evaluate (bits := bits) basePc h100).length = 184 := by
  simp [step4BFresh_evaluate, List.length_cons, List.length_nil, Nat.reduceAdd, copy6Instrs_length, eval15Instrs_length]

@[local simp] private theorem step4BFresh_evaluate_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_evaluate (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BFresh_evaluate, List.all_cons, List.all_nil, sliceNonHalt, copy6Instrs_nonHalt, eval15Instrs_nonHalt]


def step4BFresh_clear (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg0 reg7 36 (by omega) ++
  metaStoreInstrs reg0 reg7 37 (by omega) ++
  metaStoreInstrs reg0 reg7 38 (by omega) ++
  metaStoreInstrs reg0 reg7 39 (by omega) ++
  metaStoreInstrs reg0 reg7 40 (by omega) ++
  metaStoreInstrs reg0 reg7 41 (by omega)

private theorem step4BFresh_clear_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_clear (bits := bits) h100).length = 18 := by
  simp [step4BFresh_clear, Nat.reduceAdd, metaStore_length]

@[local simp] private theorem step4BFresh_clear_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BFresh_clear (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BFresh_clear, metaStore_nonHalt]

def step4BFreshInstrs (basePc zOff : Nat) (hzOff : zOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4BFresh_endpointCheck basePc zOff hzOff h100 ++
  step4BFresh_prepare h100 ++
  step4BFresh_evaluate basePc h100 ++
  step4BFresh_clear h100

theorem step4BFreshInstrs_length (basePc zOff : Nat) (hzOff : zOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) :
    (step4BFreshInstrs (bits := bits) basePc zOff hzOff h100).length = 238 := by
  simp only [step4BFreshInstrs, List.length_append, Nat.reduceAdd, step4BFresh_endpointCheck_length,
    step4BFresh_prepare_length,
    step4BFresh_evaluate_length,
    step4BFresh_clear_length]

theorem step4BFreshInstrs_nonHalt (basePc zOff : Nat) (hzOff : zOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) :
    (step4BFreshInstrs (bits := bits) basePc zOff hzOff h100).all sliceNonHalt = true := by
  simp [step4BFreshInstrs]


def step4BSlotTagInstrs (basePc sOff : Nat) (hsOff : sOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg5 sOff hsOff ++
  metaLoadInstrs reg3 reg5 50 (by omega) ++
  [ .branchLt reg2 reg3 (basePc + 9) (basePc + 7)
  , .branchLt reg3 reg2 (basePc + 9) (basePc + 16)
  , .goto (basePc + 9)
  ] ++
  metaLoadInstrs reg3 reg5 51 (by omega) ++
  [ .branchLt reg2 reg3 (basePc + 18) (basePc + 13)
  , .branchLt reg3 reg2 (basePc + 18) (basePc + 14)
  , .add reg4 reg1 reg1
  , .goto (basePc + 19)
  , .mov reg4 reg1
  , .goto (basePc + 19)
  , .mov reg4 reg0
  ]

theorem step4BSlotTagInstrs_length (basePc sOff : Nat) (hsOff : sOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) :
    (step4BSlotTagInstrs (bits := bits) basePc sOff hsOff h100).length = 19 := by
  simp [step4BSlotTagInstrs, metaLoadInstrs]

theorem step4BSlotTagInstrs_nonHalt (basePc sOff : Nat) (hsOff : sOff < 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) :
    (step4BSlotTagInstrs (bits := bits) basePc sOff hsOff h100).all sliceNonHalt = true := by
  simp only [step4BSlotTagInstrs, List.all_append, metaLoadInstrs, sliceNonHalt,
    List.all_cons, List.all_nil, Bool.and_true]

def step4BOneNode_record (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega) ++
  mul18Instrs reg4 reg5 reg2 ++
  metaLoadInstrs reg5 reg6 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega) ++
  [ .add reg4 reg5 reg4 ] ++
  metaStoreInstrs reg4 reg6 55 (by omega) ++
  [ .loadData reg5 reg4 ] ++
  metaStoreInstrs reg5 reg6 48 (by omega) ++
  [ .add reg6 reg4 reg1, .loadData reg6 reg6 ] ++
  metaStoreInstrs reg6 reg7 49 (by omega)

private theorem step4BOneNode_record_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_record (bits := bits) h100).length = 24 := by
  simp [step4BOneNode_record, List.length_cons, Nat.reduceAdd, metaLoad_length, metaStore_length, mul18Instrs]

@[local simp] private theorem step4BOneNode_record_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_record (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BOneNode_record, List.all_cons, sliceNonHalt, metaLoad_nonHalt, metaStore_nonHalt, mul18Instrs]


def step4BOneNode_cutEndpoints (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg7 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega) ++
  [ .add reg6 reg6 reg2, .loadInput reg6 reg6, .sub reg6 reg6 reg1 ] ++
  metaStoreInstrs reg6 reg7 50 (by omega) ++
  metaLoadInstrs reg6 reg7 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega) ++
  [ .add reg6 reg6 reg2, .loadInput reg6 reg6 ] ++
  metaStoreInstrs reg6 reg7 51 (by omega)

private theorem step4BOneNode_cutEndpoints_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_cutEndpoints (bits := bits) h100).length = 17 := by
  simp [step4BOneNode_cutEndpoints, List.length_cons, Nat.reduceAdd, metaLoad_length, metaStore_length]

@[local simp] private theorem step4BOneNode_cutEndpoints_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_cutEndpoints (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BOneNode_cutEndpoints, List.all_cons, sliceNonHalt, metaLoad_nonHalt, metaStore_nonHalt]


def step4BOneNode_parentEndpoints (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg7 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega) ++
  [ .add reg6 reg6 reg5, .loadInput reg6 reg6, .sub reg6 reg6 reg1 ] ++
  metaStoreInstrs reg6 reg7 52 (by omega) ++
  metaLoadInstrs reg6 reg7 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega) ++
  [ .add reg6 reg6 reg5, .loadInput reg6 reg6 ] ++
  metaStoreInstrs reg6 reg7 53 (by omega) ++
  [ .loadData reg6 reg5 ] ++
  metaStoreInstrs reg6 reg7 54 (by omega)

private theorem step4BOneNode_parentEndpoints_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_parentEndpoints (bits := bits) h100).length = 21 := by
  simp [step4BOneNode_parentEndpoints, List.length_cons, Nat.reduceAdd, metaLoad_length, metaStore_length]

@[local simp] private theorem step4BOneNode_parentEndpoints_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_parentEndpoints (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BOneNode_parentEndpoints, List.all_cons, sliceNonHalt, metaLoad_nonHalt, metaStore_nonHalt]


def step4BOneNode_firstLift (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4BFreshInstrs (basePc + 62) 50 (by omega) h100 ++
  [ .imm reg2 ⟨30, by omega⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨36, by omega⟩, .add reg3 rMeta reg3
  ] ++
  copy6Instrs reg2 reg3 reg4

private theorem step4BOneNode_firstLift_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_firstLift (bits := bits) basePc h100).length = 264 := by
  simp [step4BOneNode_firstLift, List.length_cons, Nat.reduceAdd, copy6Instrs_length, step4BFreshInstrs_length]

@[local simp] private theorem step4BOneNode_firstLift_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_firstLift (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_firstLift, List.all_cons, sliceNonHalt, copy6Instrs_nonHalt, step4BFreshInstrs_nonHalt]


def step4BOneNode_secondLift (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4BFreshInstrs (basePc + 326) 51 (by omega) h100

private theorem step4BOneNode_secondLift_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_secondLift (bits := bits) basePc h100).length = 238 := by
  simp [step4BOneNode_secondLift, step4BFreshInstrs_length]

@[local simp] private theorem step4BOneNode_secondLift_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_secondLift (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_secondLift, step4BFreshInstrs_nonHalt]


def step4BOneNode_joinContributions (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg2 ⟨30, by omega⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨36, by omega⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (basePc + 569) ++
  [ .imm reg2 ⟨33, by omega⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨39, by omega⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (basePc + 599)

private theorem step4BOneNode_joinContributions_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_joinContributions (bits := bits) basePc h100).length = 60 := by
  simp [step4BOneNode_joinContributions, List.length_cons, Nat.reduceAdd, intervalJoinInstrs_length]

@[local simp] private theorem step4BOneNode_joinContributions_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_joinContributions (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_joinContributions, List.all_cons, sliceNonHalt, intervalJoinInstrs_nonHalt]


def step4BOneNode_writeFirst (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 55 (by omega) ++
  [ .add reg2 reg2 reg1, .add reg2 reg2 reg1 ] ++
  metaLoadInstrs reg3 reg4 30 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  metaLoadInstrs reg3 reg4 31 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  metaLoadInstrs reg3 reg4 32 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  [ .mov reg6 reg2 ] ++
  step4BSlotTagInstrs (basePc + 645) 52 (by omega) h100

private theorem step4BOneNode_writeFirst_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_writeFirst (bits := bits) basePc h100).length = 40 := by
  simp [step4BOneNode_writeFirst, List.length_cons, Nat.reduceAdd, metaLoad_length, step4BSlotTagInstrs_length]

@[local simp] private theorem step4BOneNode_writeFirst_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_writeFirst (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_writeFirst, List.all_cons, sliceNonHalt, metaLoad_nonHalt, step4BSlotTagInstrs_nonHalt]


def step4BOneNode_writeSecond (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .storeData reg6 reg4, .add reg2 reg6 reg1 ] ++
  metaLoadInstrs reg3 reg4 33 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  metaLoadInstrs reg3 reg4 34 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  metaLoadInstrs reg3 reg4 35 (by omega) ++
  [ .storeData reg2 reg3, .add reg2 reg2 reg1 ] ++
  [ .mov reg6 reg2 ] ++
  step4BSlotTagInstrs (basePc + 682) 53 (by omega) h100 ++
  [ .storeData reg6 reg4, .add reg6 reg6 reg1 ]

private theorem step4BOneNode_writeSecond_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_writeSecond (bits := bits) basePc h100).length = 39 := by
  simp [step4BOneNode_writeSecond, List.length_cons, List.length_nil, Nat.reduceAdd, metaLoad_length, step4BSlotTagInstrs_length]

@[local simp] private theorem step4BOneNode_writeSecond_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_writeSecond (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_writeSecond, List.all_cons, List.all_nil, sliceNonHalt, metaLoad_nonHalt, step4BSlotTagInstrs_nonHalt]


def step4BOneNode_selectJump (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg4 48 (by omega) ++
  metaLoadInstrs reg3 reg4 49 (by omega) ++
  [ .branchLt reg2 reg3 (basePc + 711) (basePc + 710)
  , .branchLt reg3 reg2 (basePc + 711) (basePc + 1002)
  ] ++
  mul18Instrs reg7 reg8 reg2 ++
  metaLoadInstrs reg8 reg9 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega) ++
  [ .add reg7 reg8 reg7
  , .add reg8 reg7 reg1
  , .loadData reg8 reg8
  ] ++
  mul18Instrs reg2 reg9 reg8 ++
  metaLoadInstrs reg8 reg9 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega)

private theorem step4BOneNode_selectJump_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_selectJump (bits := bits) basePc h100).length = 27 := by
  simp [step4BOneNode_selectJump, List.length_cons, Nat.reduceAdd, metaLoad_length, mul18Instrs]

@[local simp] private theorem step4BOneNode_selectJump_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_selectJump (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_selectJump, List.all_cons, sliceNonHalt, metaLoad_nonHalt, mul18Instrs]


def step4BOneNode_composeFirst (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .add reg2 reg8 reg2
  , .imm reg9 ⟨10, by omega⟩
  , .add reg3 reg2 reg9
  , .add reg2 reg7 reg9
  , .imm reg4 ⟨56, by omega⟩
  , .add reg4 rMeta reg4
  ] ++
  mapComposeInstrs (basePc + 736)

private theorem step4BOneNode_composeFirst_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_composeFirst (bits := bits) basePc h100).length = 134 := by
  simp [step4BOneNode_composeFirst, List.length_cons, Nat.reduceAdd, mapComposeInstrs_length]

@[local simp] private theorem step4BOneNode_composeFirst_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_composeFirst (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_composeFirst, List.all_cons, sliceNonHalt, mapComposeInstrs_nonHalt]


def step4BOneNode_composeSecond (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg5 55 (by omega) ++
  [ .add reg2 reg2 reg1, .add reg2 reg2 reg1
  , .imm reg3 ⟨56, by omega⟩, .add reg3 rMeta reg3
  , .imm reg4 ⟨8, by omega⟩, .add reg4 reg2 reg4
  ] ++
  mapComposeInstrs (basePc + 873) ++
  [ .goto (basePc + 1039) ]

private theorem step4BOneNode_composeSecond_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_composeSecond (bits := bits) basePc h100).length = 138 := by
  simp [step4BOneNode_composeSecond, List.length_cons, List.length_nil, Nat.reduceAdd, mapComposeInstrs_length, metaLoad_length]

@[local simp] private theorem step4BOneNode_composeSecond_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_composeSecond (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNode_composeSecond, List.all_cons, List.all_nil, sliceNonHalt, mapComposeInstrs_nonHalt, metaLoad_nonHalt]


def step4BOneNode_copyParent (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg3 reg5 55 (by omega) ++
  [ .add reg3 reg3 reg1, .add reg3 reg3 reg1
  , .imm reg2 ⟨8, by omega⟩, .add reg2 reg3 reg2
  ] ++
  copy8Instrs reg2 reg3 reg4

private theorem step4BOneNode_copyParent_length (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_copyParent (bits := bits) h100).length = 37 := by
  simp [step4BOneNode_copyParent, List.length_cons, Nat.reduceAdd, copy8Instrs_length, metaLoad_length]

@[local simp] private theorem step4BOneNode_copyParent_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNode_copyParent (bits := bits) h100).all sliceNonHalt = true := by
  simp [step4BOneNode_copyParent, List.all_cons, sliceNonHalt, copy8Instrs_nonHalt, metaLoad_nonHalt]

def step4BOneNodeInstrs (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  step4BOneNode_record h100 ++
  step4BOneNode_cutEndpoints h100 ++
  step4BOneNode_parentEndpoints h100 ++
  step4BOneNode_firstLift basePc h100 ++
  step4BOneNode_secondLift basePc h100 ++
  step4BOneNode_joinContributions basePc h100 ++
  step4BOneNode_writeFirst basePc h100 ++
  step4BOneNode_writeSecond basePc h100 ++
  step4BOneNode_selectJump basePc h100 ++
  step4BOneNode_composeFirst basePc h100 ++
  step4BOneNode_composeSecond basePc h100 ++
  step4BOneNode_copyParent h100

theorem step4BOneNodeInstrs_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNodeInstrs (bits := bits) basePc h100).length = 1039 := by
  simp only [step4BOneNodeInstrs, List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
    step4BOneNode_cutEndpoints_length,
    step4BOneNode_parentEndpoints_length,
    step4BOneNode_firstLift_length,
    step4BOneNode_secondLift_length,
    step4BOneNode_joinContributions_length,
    step4BOneNode_writeFirst_length,
    step4BOneNode_writeSecond_length,
    step4BOneNode_selectJump_length,
    step4BOneNode_composeFirst_length,
    step4BOneNode_composeSecond_length,
    step4BOneNode_copyParent_length]

theorem step4BOneNodeInstrs_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BOneNodeInstrs (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp [step4BOneNodeInstrs]


def step4BInstrs (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg3 mIdxKCursor (by dsimp only [mIdxKCursor]; omega) ++
  metaLoadInstrs reg3 reg4 mIdxTrigHeadBase (by dsimp only [mIdxTrigHeadBase]; omega) ++
  [ .add reg3 reg3 reg2, .loadData reg3 reg3 ] ++
  metaStoreInstrs reg3 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega) ++
  metaLoadInstrs reg2 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega) ++
  metaLoadInstrs reg3 reg4 mIdxNH (by dsimp only [mIdxNH]; omega) ++
  [ .branchLt reg2 reg3 (basePc + 18) (basePc + 1069) ] ++
  step4BOneNodeInstrs (basePc + 18) h100 ++
  metaLoadInstrs reg2 reg3 mIdxCCursor (by dsimp only [mIdxCCursor]; omega) ++
  metaLoadInstrs reg3 reg4 mIdxTrigNextBase (by dsimp only [mIdxTrigNextBase]; omega) ++
  [ .add reg3 reg3 reg2, .loadData reg3 reg3 ] ++
  metaStoreInstrs reg3 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega) ++
  [ .goto (basePc + 11) ]

theorem step4BInstrs_length (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BInstrs (bits := bits) basePc h100).length = 1069 := by
  simp [step4BInstrs, metaLoadInstrs, metaStoreInstrs, step4BOneNodeInstrs_length]

theorem step4BInstrs_nonHalt (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (step4BInstrs (bits := bits) basePc h100).all sliceNonHalt = true := by
  simp only [step4BInstrs, List.all_append, step4BOneNodeInstrs_nonHalt,
    metaLoadInstrs, metaStoreInstrs, sliceNonHalt, List.all_cons, List.all_nil,
    Bool.and_true]

end Defs

end Step4BSlice


section JumpPlacements

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4B_jump_placed {code : Program DomL} {basePc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code basePc (step4BOneNodeInstrs basePc h100)) :
    Placed code (basePc + 703) (step4BOneNode_selectJump basePc h100) ∧
    Placed code (basePc + 730) (step4BOneNode_composeFirst basePc h100) ∧
    Placed code (basePc + 864) (step4BOneNode_composeSecond basePc h100) ∧
    Placed code (basePc + 1002) (step4BOneNode_copyParent h100) := by
  unfold step4BOneNodeInstrs at h
  have hP11 := h
  have hP10 := Placed_append_left hP11
  have hP9 := Placed_append_left hP10
  have hP8 := Placed_append_left hP9
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.length_append, Nat.reduceAdd,
      step4BOneNode_record_length, step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length,
      step4BOneNode_firstLift_length, step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length,
      step4BOneNode_writeFirst_length, step4BOneNode_writeSecond_length]
      using Placed_append_right hP8
  · simpa only [List.length_append, Nat.reduceAdd,
      step4BOneNode_record_length, step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length,
      step4BOneNode_firstLift_length, step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length,
      step4BOneNode_writeFirst_length, step4BOneNode_writeSecond_length, step4BOneNode_selectJump_length]
      using Placed_append_right hP9
  · simpa only [List.length_append, Nat.reduceAdd,
      step4BOneNode_record_length, step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length,
      step4BOneNode_firstLift_length, step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length,
      step4BOneNode_writeFirst_length, step4BOneNode_writeSecond_length, step4BOneNode_selectJump_length,
      step4BOneNode_composeFirst_length]
      using Placed_append_right hP10
  · simpa only [List.length_append, Nat.reduceAdd,
      step4BOneNode_record_length, step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length,
      step4BOneNode_firstLift_length, step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length,
      step4BOneNode_writeFirst_length, step4BOneNode_writeSecond_length, step4BOneNode_selectJump_length,
      step4BOneNode_composeFirst_length, step4BOneNode_composeSecond_length]
      using Placed_append_right hP11


theorem step4B_parent_placed {code : Program DomL} {basePc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code basePc (step4BOneNodeInstrs basePc h100)) :
    Placed code (basePc + 0) (step4BOneNode_record h100) ∧
    Placed code (basePc + 24) (step4BOneNode_cutEndpoints h100) ∧
    Placed code (basePc + 41) (step4BOneNode_parentEndpoints h100) ∧
    Placed code (basePc + 62) (step4BOneNode_firstLift basePc h100) ∧
    Placed code (basePc + 326) (step4BOneNode_secondLift basePc h100) ∧
    Placed code (basePc + 564) (step4BOneNode_joinContributions basePc h100) ∧
    Placed code (basePc + 624) (step4BOneNode_writeFirst basePc h100) ∧
    Placed code (basePc + 664) (step4BOneNode_writeSecond basePc h100) := by
  unfold step4BOneNodeInstrs at h
  have hP11 := h
  have hP10 := Placed_append_left hP11
  have hP9 := Placed_append_left hP10
  have hP8 := Placed_append_left hP9
  have hP7 := Placed_append_left hP8
  have hP6 := Placed_append_left hP7
  have hP5 := Placed_append_left hP6
  have hP4 := Placed_append_left hP5
  have hP3 := Placed_append_left hP4
  have hP2 := Placed_append_left hP3
  have hP1 := Placed_append_left hP2
  have hP0 := Placed_append_left hP1
  refine ⟨hP0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [step4BOneNode_record_length]
      using Placed_append_right hP1
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length]
      using Placed_append_right hP2
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length]
      using Placed_append_right hP3
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length, step4BOneNode_firstLift_length]
      using Placed_append_right hP4
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length, step4BOneNode_firstLift_length,
      step4BOneNode_secondLift_length]
      using Placed_append_right hP5
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length, step4BOneNode_firstLift_length,
      step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length]
      using Placed_append_right hP6
  · simpa only [List.length_append, Nat.reduceAdd, step4BOneNode_record_length,
      step4BOneNode_cutEndpoints_length, step4BOneNode_parentEndpoints_length, step4BOneNode_firstLift_length,
      step4BOneNode_secondLift_length, step4BOneNode_joinContributions_length, step4BOneNode_writeFirst_length]
      using Placed_append_right hP7

end JumpPlacements

end PaperB.RamProgram.ExitSummaryBuild
