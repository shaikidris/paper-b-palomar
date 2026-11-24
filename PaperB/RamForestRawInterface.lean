module

public import PaperB.RamForestPackedFinish
public import PaperB.RamForestDistinctRow
public import PaperB.RamForestDepthSeek
public import PaperB.RamForestOrderRank
public import PaperB.ForestIncomingRaw

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.ArcParents
open PaperB.RamForestProgram.ArcDecode
open PaperB.ForestHead (Vertex TestSpec)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (WordColumns packWordColumns)
open PaperB.EX24.FinalDFS (packedInput nodeCount)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

/-- Input array length for raw quotient words:
header `[n_H, m_H, root_H]` followed by `m_H` source words and `m_H` head words. -/
def rawInputCap (m : Nat) : Nat := 3 + 2 * m

/-- Linear mutable work-memory capacity for all three stages of Lemma 3.2. -/
def rawWorkCap (n m : Nat) : Nat := 32 * n + 7 * m + 17

theorem rawWorkCap_le (n m : Nat) : rawWorkCap n m ≤ 32 * (n + m + 1) := by
  unfold rawWorkCap
  omega

theorem rawInputCap_le (n m : Nat) : rawInputCap m ≤ 3 * (n + m + 1) := by
  unfold rawInputCap
  omega

theorem rawWordBits_fit (n m : Nat) :
    let bits := OracleContract.wordBits 5 n m
    rawInputCap m ≤ 2 ^ bits ∧
    rawWorkCap n m ≤ 2 ^ bits ∧
    1 + 18 * n < 2 ^ bits := by
  intro bits
  have hIn : rawInputCap m < 2 ^ bits :=
    OracleContract.linear_payload_fits 5 n m 3 (rawInputCap m) (by decide) (rawInputCap_le n m)
  have hWork : rawWorkCap n m < 2 ^ bits :=
    OracleContract.linear_payload_fits 5 n m 32 (rawWorkCap n m) (by decide) (rawWorkCap_le n m)
  have hRet : 1 + 18 * n < 2 ^ bits :=
    OracleContract.linear_payload_fits 5 n m 18 (1 + 18 * n) (by decide) (by omega)
  exact ⟨Nat.le_of_lt hIn, Nat.le_of_lt hWork, hRet⟩

/-- Raw quotient words in immutable RAM input memory. -/
structure RawQuotientInput {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout bits inputCap workCap hi hw))
    (H : LabelledQuotient) : Prop where
  cap_ge : rawInputCap H.arcCount ≤ inputCap
  hdr_n : (input.words[0]?).map Fin.val = some H.vertexCount
  hdr_m : (input.words[1]?).map Fin.val = some H.arcCount
  hdr_root : (input.words[2]?).map Fin.val = some H.root.val
  sources : SourcesAt input 3 (fun e => (rawOccurrence H e).1)
  heads : HeadsAt input (3 + H.arcCount) (rawHead H)

/-! ### Fixed disjoint work-memory bank offsets -/

def csrArenaBase : Nat := 0
def csrArenaWords (n m : Nat) : Nat := 6 * (n + 1 + m) + 1
def indegBase (n m : Nat) : Nat := csrArenaWords n m
def stampsBase (n m : Nat) : Nat := indegBase n m + n
def orderBase (n m : Nat) : Nat := stampsBase n m + n
def ranksBase (n m : Nat) : Nat := orderBase n m + n
def rowStartBase (n m : Nat) : Nat := ranksBase n m + n
def rowEndBase (n m : Nat) : Nat := rowStartBase n m + n
def predBufBase (n m : Nat) : Nat := rowEndBase n m + n

def candFstABase (n m : Nat) : Nat := predBufBase n m + m
def candSndABase (n m : Nat) : Nat := candFstABase n m + n
def candFstBBase (n m : Nat) : Nat := candSndABase n m + n
def candSndBBase (n m : Nat) : Nat := candFstBBase n m + n
def dictBase (n m : Nat) : Nat := candSndBBase n m + n
def jumpBase (n m : Nat) : Nat := dictBase n m + (1 + 3 * n)
def backFstBase (n m : Nat) : Nat := jumpBase n m + 3 * (n + 1)
def backSndBase (n m : Nat) : Nat := backFstBase n m + (n + 1)
def labelsBase (n m : Nat) : Nat := backSndBase n m + (n + 1)
def parentsBase (n m : Nat) : Nat := labelsBase n m + n
def sourceBase (n m : Nat) : Nat := parentsBase n m + (n + 1)

theorem sourceBase_eq (n m : Nat) : sourceBase n m = 26 * n + 7 * m + 14 := by
  unfold sourceBase parentsBase labelsBase backSndBase backFstBase jumpBase dictBase
    candSndBBase candFstBBase candSndABase candFstABase predBufBase rowEndBase
    rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords
  omega

theorem sourceBase_plus_prefix_le (n m len : Nat) (hlen : len ≤ 6 * n + 3) :
    sourceBase n m + len ≤ rawWorkCap n m := by
  rw [sourceBase_eq]
  unfold rawWorkCap
  omega

theorem finish_arena_before_source (n m N prefixLen : Nat)
    (hN : N ≤ n + 1) (hpre : prefixLen ≤ 6 * n + 3) :
    (prefixLen + 2 * N) + 5 * N + 1 + N ≤ sourceBase n m ∧
    prefixLen ≤ sourceBase n m := by
  rw [sourceBase_eq]
  omega

/-- Agreed Stage 1 output contract: topological order, inverse rank table,
and deduplicated predecessor rows written in mutable RAM `s.data`. -/
structure Stage1Output {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) (s : State (layout bits inputCap workCap hi hw))
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (rank : Vertex H → Nat) (rows : PaperB.ForestDictionary.Rows H) : Prop where
  nodup : order.toList.Nodup
  covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt order size_order i = v
  topo : IsTopologicalOrder order size_order
  rank_at : ∀ i : Fin H.vertexCount, rank (orderedVertexAt order size_order i) = i.val
  rank_increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
    rank (orderedVertexAt order size_order i) < rank (orderedVertexAt order size_order j)
  rank_arc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v
  order_mem : ∀ i : Fin H.vertexCount,
    (s.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
      some (orderedVertexAt order size_order i).val
  ranks_mem : ∀ v : Vertex H,
    (s.data[ranksBase H.vertexCount H.arcCount + v.val]?).map Fin.val = some (rank v)
  rows_mem : ∀ y : Vertex H, ∃ lo hi : Nat,
    (s.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
    (s.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
    lo ≤ hi ∧ hi ≤ H.arcCount ∧
    hi - lo = (rows.row y).length ∧
    ∀ j : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
        some ((rows.row y)[j.val]'j.isLt).val

/-- Agreed Stage 2 output contract: exact premises required by
`PaperB.RamForestProgram.Finish.run_ordered_reader_finish`. -/
structure Stage2Output {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    {dictRows : PaperB.ForestDictionary.Rows H}
    {vertices : Array (Vertex H)} {vertexCount : vertices.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw)) : Type where
  arena : Arena bits workCap (nodeCount (orderedConfig dictRows large) r.out)
  ctrl : Control arena s
  rootVal : (reg s cmd).val = (packedInput r.index.ok).root.val
  parents : ParentAt arena (packedInput r.index.ok).parent.read s.data
  mass : (nodeCount (orderedConfig dictRows large) r.out) - 1 ≤ arena.children
  children : arena.children ≤ nodeCount (orderedConfig dictRows large) r.out
  place : arena.base = (packedPrefix (packWordColumns r width)).size +
    2 * nodeCount (orderedConfig dictRows large) r.out
  src : Nat
  fits : src + (packedPrefix (packWordColumns r width)).size ≤ workCap
  apart : (packedPrefix (packWordColumns r width)).size ≤ src
  params : PrefixCopyInput s src (packedPrefix (packWordColumns r width)).size
  sourceAt : ∀ j < (packedPrefix (packWordColumns r width)).size,
    s.data[src + j]? = (packedPrefix (packWordColumns r width))[j]?

end PaperB.RamForestProgram.RawBuild
