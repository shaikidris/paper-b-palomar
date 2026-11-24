module

public import PaperB.OracleContract
public import PaperB.OraclePackedWidth
public import PaperB.RamProgram
public import PaperB.RamForestSmallAndLookup
public import PaperB.ExitSealedBase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Canonical sealed index layout constants and structural cell specification shared
between the EX5.1/EX5.2 Word-RAM builder (`SealedBuild`) and the EX5.3 Word-RAM
query program (`SealedQueryR.Phase bits 16`).

No original adjacency lists appear anywhere in the sealed array.
-/

namespace PaperB.OracleSealedIndexLayout

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.ExitMap.Retention (TagsFit)

/-- Header slot indices (`[0..15]`) of the sealed index array `I`.
Slots `0, 1, 2` match `PaperB.EX53.program` (`RamStaticLCA`) directly;
slot `3` matches `RamProgram.sealedTranslation` (`header = 3`). -/
abbrev hdrHead : Nat := 0
abbrev hdrDomParent : Nat := 1
abbrev hdrDomDepth : Nat := 2
abbrev hdrOrigToDense : Nat := 3
abbrev hdrN : Nat := 4
abbrev hdrQCount : Nat := 5
abbrev hdrDenseToOrig : Nat := 6
abbrev hdrEntry : Nat := 7
abbrev hdrStop : Nat := 8
abbrev hdrOrigOfEntry : Nat := 9
abbrev hdrChildStart : Nat := 10
abbrev hdrChildEntries : Nat := 11
abbrev hdrChildStops : Nat := 12
abbrev hdrChildIds : Nat := 13
abbrev hdrOwnerDesc : Nat := 14
abbrev oracleHeaderSize : Nat := 16

/-- Field offsets inside each 10-word per-owner descriptor at
`ownerDescBase + 10 * d`. -/
abbrev descN : Nat := 0
abbrev descDict : Nat := 1
abbrev descBackFst : Nat := 2
abbrev descBackSnd : Nat := 3
abbrev descLabels : Nat := 4
abbrev descFEntry : Nat := 5
abbrev descFStop : Nat := 6
abbrev descExitDepth : Nat := 7
abbrev descExitStored : Nat := 8
abbrev descExitPrior : Nat := 9
abbrev ownerDescStride : Nat := 10

/-- Uniform retained-word linear constant (`≤ 128 * n` for `1 ≤ n`). -/
abbrev retainedLinearFactor : Nat := 128

theorem oracle_tagsFit (n m : Nat) :
    TagsFit (OracleContract.wordBits oracleWordSlack n m) := by
  have hL : 1 ≤ OracleContract.L (n + m) := OracleContract.one_le_L (n + m)
  have hwb : OracleContract.L (n + m) + oracleWordSlack =
      OracleContract.wordBits oracleWordSlack n m := rfl
  have hbits : 2 ≤ OracleContract.wordBits oracleWordSlack n m := by
    change 2 ≤ OracleContract.L (n + m) + 10
    omega
  unfold TagsFit
  calc
    2 < 2 ^ 2 := by decide
    _ ≤ 2 ^ OracleContract.wordBits oracleWordSlack n m :=
      Nat.pow_le_pow_right (by decide) hbits

theorem oracle_retained_fits (n m words : Nat)
    (hWords : words ≤ retainedLinearFactor * n) :
    words < 2 ^ OracleContract.wordBits oracleWordSlack n m := by
  apply oracle_slack_linear_fits n m retainedLinearFactor words (by decide)
  exact Nat.le_trans hWords (Nat.mul_le_mul_left _ (by omega))

/-- Word array equality on a contiguous slice `[base, base + vals.size)`. -/
def SliceAt {bits : Nat} (mem : Array (Word bits)) (base : Nat)
    (vals : Array (Word bits)) : Prop :=
  base + vals.size ≤ mem.size ∧
  ∀ (j : Nat) (hj : j < vals.size), mem[base + j]? = some (vals[j]'hj)

/-- Word array matching a function `f : Nat → Nat` on `[base, base + len)`. -/
def NatSliceAt {bits : Nat} (mem : Array (Word bits)) (base len : Nat)
    (f : Nat → Nat) : Prop :=
  base + len ≤ mem.size ∧
  ∀ (j : Nat), j < len → (mem[base + j]?).map Fin.val = some (f j)

/-- Exact header and static global-table placement inside a sealed index `I`.
Each per-owner descriptor `[descBase + 10 * d .. + 10)` points into disjoint or
valid slices inside `I`. -/
structure StaticHeaderSpec {bits : Nat} (I : Array (Word bits)) (n qCount : Nat) where
  n_pos : 0 < n
  q_pos : 0 < qCount
  q_le : qCount ≤ n
  hdr_fit : oracleHeaderSize ≤ I.size
  hN : (I[hdrN]?).map Fin.val = some n
  hQ : (I[hdrQCount]?).map Fin.val = some qCount
  hTotal : (I[hdrTotalWords]?).map Fin.val = some I.size
  headBase : Nat
  domParentBase : Nat
  domDepthBase : Nat
  origToDenseBase : Nat
  denseToOrigBase : Nat
  entryBase : Nat
  stopBase : Nat
  origOfEntryBase : Nat
  childStartBase : Nat
  childEntriesBase : Nat
  childStopsBase : Nat
  childIdsBase : Nat
  ownerDescBase : Nat
  hHeadBase : (I[hdrHead]?).map Fin.val = some headBase
  hDomParentBase : (I[hdrDomParent]?).map Fin.val = some domParentBase
  hDomDepthBase : (I[hdrDomDepth]?).map Fin.val = some domDepthBase
  hOrigToDenseBase : (I[hdrOrigToDense]?).map Fin.val = some origToDenseBase
  hDenseToOrigBase : (I[hdrDenseToOrig]?).map Fin.val = some denseToOrigBase
  hEntryBase : (I[hdrEntry]?).map Fin.val = some entryBase
  hStopBase : (I[hdrStop]?).map Fin.val = some stopBase
  hOrigOfEntryBase : (I[hdrOrigOfEntry]?).map Fin.val = some origOfEntryBase
  hChildStartBase : (I[hdrChildStart]?).map Fin.val = some childStartBase
  hChildEntriesBase : (I[hdrChildEntries]?).map Fin.val = some childEntriesBase
  hChildStopsBase : (I[hdrChildStops]?).map Fin.val = some childStopsBase
  hChildIdsBase : (I[hdrChildIds]?).map Fin.val = some childIdsBase
  hOwnerDescBase : (I[hdrOwnerDesc]?).map Fin.val = some ownerDescBase
  origToDense_fit : origToDenseBase + n ≤ I.size
  denseToOrig_fit : denseToOrigBase + qCount ≤ I.size
  head_fit : headBase + qCount ≤ I.size
  domParent_fit : domParentBase + qCount ≤ I.size
  domDepth_fit : domDepthBase + qCount ≤ I.size
  entry_fit : entryBase + qCount ≤ I.size
  stop_fit : stopBase + qCount ≤ I.size
  origOfEntry_fit : origOfEntryBase + qCount ≤ I.size
  childStart_fit : childStartBase + (qCount + 1) ≤ I.size
  childEntries_fit : childEntriesBase + qCount ≤ I.size
  childStops_fit : childStopsBase + qCount ≤ I.size
  childIds_fit : childIdsBase + qCount ≤ I.size
  ownerDesc_fit : ownerDescBase + ownerDescStride * qCount ≤ I.size

end PaperB.OracleSealedIndexLayout
