module

public import PaperB.RamDagReachKahn
public import PaperB.ActualOnlineOracle
public import PaperB.DenseLabelledArcIso
public import PaperB.RamForestRawInterface

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.1 Quotient Emitter (`RamQuotientEmitter.lean`):
Consumes `RawDagInput`, `denseToOrig`/`origToDensePlusOne` from `RamDagReachKahn`,
and the abstract `StaticTreeSlice` (`[treeBase .. treeBase + 11 * Q)`),
computing `selfSlot[0..Q-1]`, per-owner quotient degrees, `qStart[0..Q]`, and
emitted quotient arcs `(qSrcLocal, qHeadLocal, qOrigEntry)` in `O((n + m) * L)`
word-RAM steps and `O(n + m)` work words, with exact correspondence to
`ActualOnlineOracle.denseQuotient`.
-/

namespace PaperB.RamQuotientEmitter

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestHead
open PaperB.EX16Assembly
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.EX44.ActualOnlineOracle
open PaperB.RamDagReach

/-! ### 1. Bank Offsets & Abstract `StaticTreeSlice` Contract -/

def treeDomParentOff (_Q : Nat) : Nat := 0
def treeDomDepthOff (Q : Nat) : Nat := Q
def treeHeavyOff (Q : Nat) : Nat := 2 * Q
def treeHeadOff (Q : Nat) : Nat := 3 * Q
def treeEntryOff (Q : Nat) : Nat := 4 * Q
def treeStopOff (Q : Nat) : Nat := 5 * Q
def treeDenseOfEntryOff (Q : Nat) : Nat := 6 * Q
def treeChildStartOff (Q : Nat) : Nat := 7 * Q
def treeChildEntriesOff (Q : Nat) : Nat := 8 * Q + 1
def treeChildStopsOff (Q : Nat) : Nat := 9 * Q + 1
def treeChildIdsOff (Q : Nat) : Nat := 10 * Q + 1
def staticTreeWords (Q : Nat) : Nat := 11 * Q

def emitSelfSlotOff (_n _m : Nat) : Nat := 0
def emitQDegOff (n _m : Nat) : Nat := n
def emitQStartOff (n _m : Nat) : Nat := 2 * n
def emitQSrcOff (n _m : Nat) : Nat := 3 * n + 1
def emitQHeadOff (n m : Nat) : Nat := 3 * n + m + 1
def emitQEntryOff (n m : Nat) : Nat := 3 * n + 2 * m + 1
def emitScratch0Off (n m : Nat) : Nat := 3 * n + 3 * m + 1
def emitScratch1Off (n m : Nat) : Nat := 3 * n + 3 * m + 2
def emitterWorkWords (n m : Nat) : Nat := 3 * n + 3 * m + 3

/-- Abstract static dominator-tree slice `[treeBase .. treeBase + 11 * Q)` over
dense reachable vertices `dense` (`1 ≤ Q ≤ n`, `dense[0] = r`, `dense.Nodup`). -/
structure StaticTreeSlice {bits : Nat} (mem : Array (Word bits)) (treeBase : Nat)
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount)) : Type where
  qPos : 0 < dense.length
  nodup : dense.Nodup
  head_eq : dense[0]'qPos = r
  reach_mem : ∀ (i : Nat) (hi : i < dense.length), g.InitiallyReachable r (dense[i]'hi)
  mem_reach : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v → v ∈ dense
  domParent : Fin dense.length → Fin dense.length
  domDepth : Fin dense.length → Nat
  heavy : Fin dense.length → Nat
  head : Fin dense.length → Fin dense.length
  entry : Fin dense.length → Nat
  stop : Fin dense.length → Nat
  denseOfEntry : Fin dense.length → Fin dense.length
  childStart : Nat → Nat
  childIds : Fin (dense.length - 1) → Fin dense.length
  fit : treeBase + staticTreeWords dense.length ≤ mem.size
  domParent_mem : ∀ v : Fin dense.length,
    (mem[treeBase + v.val]?).map Fin.val = some (domParent v).val
  domDepth_mem : ∀ v : Fin dense.length,
    (mem[treeBase + dense.length + v.val]?).map Fin.val = some (domDepth v)
  heavy_mem : ∀ v : Fin dense.length,
    (mem[treeBase + 2 * dense.length + v.val]?).map Fin.val = some (heavy v)
  head_mem : ∀ v : Fin dense.length,
    (mem[treeBase + 3 * dense.length + v.val]?).map Fin.val = some (head v).val
  entry_mem : ∀ v : Fin dense.length,
    (mem[treeBase + 4 * dense.length + v.val]?).map Fin.val = some (entry v)
  stop_mem : ∀ v : Fin dense.length,
    (mem[treeBase + 5 * dense.length + v.val]?).map Fin.val = some (stop v)
  denseOfEntry_mem : ∀ k : Fin dense.length,
    (mem[treeBase + 6 * dense.length + k.val]?).map Fin.val = some (denseOfEntry k).val
  childStart_mem : ∀ d : Nat, d ≤ dense.length →
    (mem[treeBase + 7 * dense.length + d]?).map Fin.val = some (childStart d)
  childEntries_mem : ∀ pos : Fin (dense.length - 1),
    (mem[treeBase + (8 * dense.length + 1) + pos.val]?).map Fin.val = some (entry (childIds pos))
  childStops_mem : ∀ pos : Fin (dense.length - 1),
    (mem[treeBase + (9 * dense.length + 1) + pos.val]?).map Fin.val = some (stop (childIds pos))
  childIds_mem : ∀ pos : Fin (dense.length - 1),
    (mem[treeBase + (10 * dense.length + 1) + pos.val]?).map Fin.val = some (childIds pos).val
  domParent_root : (domParent ⟨0, qPos⟩).val = 0
  domParent_lt : ∀ v : Fin dense.length, 0 < v.val → (domParent v).val < v.val
  domDepth_root : domDepth ⟨0, qPos⟩ = 0
  domDepth_step : ∀ v : Fin dense.length, 0 < v.val → domDepth v = domDepth (domParent v) + 1
  domParent_spec : ∀ v : Fin dense.length, 0 < v.val →
    g.IsImmediateDominator r (dense[(domParent v).val]'(domParent v).isLt) (dense[v.val]'v.isLt)
  entry_lt_stop : ∀ v : Fin dense.length, entry v < stop v ∧ stop v ≤ dense.length
  denseOfEntry_entry : ∀ v : Fin dense.length,
    ∀ hv : entry v < dense.length, denseOfEntry ⟨entry v, hv⟩ = v
  dominates_iff_interval : ∀ a v : Fin dense.length,
    g.Dominates r (dense[a.val]'a.isLt) (dense[v.val]'v.isLt) ↔
      entry a ≤ entry v ∧ entry v < stop a
  childStart_zero : childStart 0 = 0
  childStart_end : childStart dense.length = dense.length - 1
  childStart_mono : ∀ i j : Nat, i ≤ j → j ≤ dense.length → childStart i ≤ childStart j
  childIds_mem_iff : ∀ (d c : Fin dense.length),
    (∃ pos : Nat, childStart d.val ≤ pos ∧ pos < childStart (d.val + 1) ∧
      ∃ hp : pos < dense.length - 1, childIds ⟨pos, hp⟩ = c) ↔
      c.val ≠ 0 ∧ domParent c = d
  childEntries_strict : ∀ (d : Fin dense.length) (i j : Nat),
    childStart d.val ≤ i → i < j → j < childStart (d.val + 1) →
    ∀ (hi : i < dense.length - 1) (hj : j < dense.length - 1),
      entry (childIds ⟨i, hi⟩) < entry (childIds ⟨j, hj⟩)

/-- Transport a `StaticTreeSlice` across memory arrays agreeing on `[treeBase .. treeBase + 11 * Q)`,
preserving every semantic function (`domParent`, `entry`, `childStart`, `childIds`, hence `emittedArcs` and `qStartFn`) definitionally. -/
def StaticTreeSlice.ofMemEq {bits : Nat} {mem₁ mem₂ : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem₁ treeBase g r dense)
    (hSz : mem₂.size = mem₁.size)
    (hMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords dense.length → mem₂[k]? = mem₁[k]?) :
    StaticTreeSlice mem₂ treeBase g r dense :=
  { S with
    fit := hSz ▸ S.fit
    domParent_mem := fun v => by
      have hk := hMem (treeBase + v.val) (Nat.le_add_right _ _)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.domParent_mem v
    domDepth_mem := fun v => by
      have hk := hMem (treeBase + dense.length + v.val) (by omega)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.domDepth_mem v
    heavy_mem := fun v => by
      have hk := hMem (treeBase + 2 * dense.length + v.val) (by omega)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.heavy_mem v
    head_mem := fun v => by
      have hk := hMem (treeBase + 3 * dense.length + v.val) (by omega)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.head_mem v
    entry_mem := fun v => by
      have hk := hMem (treeBase + 4 * dense.length + v.val) (by omega)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.entry_mem v
    stop_mem := fun v => by
      have hk := hMem (treeBase + 5 * dense.length + v.val) (by omega)
        (by unfold staticTreeWords; have := v.isLt; omega)
      rw [hk]; exact S.stop_mem v
    denseOfEntry_mem := fun k => by
      have hk := hMem (treeBase + 6 * dense.length + k.val) (by omega)
        (by unfold staticTreeWords; have := k.isLt; omega)
      rw [hk]; exact S.denseOfEntry_mem k
    childStart_mem := fun d hd => by
      have hk := hMem (treeBase + 7 * dense.length + d) (by omega)
        (by unfold staticTreeWords; have := S.qPos; omega)
      rw [hk]; exact S.childStart_mem d hd
    childEntries_mem := fun pos => by
      have hk := hMem (treeBase + (8 * dense.length + 1) + pos.val) (by omega)
        (by unfold staticTreeWords; have := pos.isLt; omega)
      rw [hk]; exact S.childEntries_mem pos
    childStops_mem := fun pos => by
      have hk := hMem (treeBase + (9 * dense.length + 1) + pos.val) (by omega)
        (by unfold staticTreeWords; have := pos.isLt; omega)
      rw [hk]; exact S.childStops_mem pos
    childIds_mem := fun pos => by
      have hk := hMem (treeBase + (10 * dense.length + 1) + pos.val) (by omega)
        (by unfold staticTreeWords; have := pos.isLt; omega)
      rw [hk]; exact S.childIds_mem pos }

section QuotientModel

variable {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
  {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}

def StaticTreeSlice.childSlice (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) : List (Fin dense.length) :=
  List.ofFn fun j : Fin (S.childStart (d.val + 1) - S.childStart d.val) =>
    S.childIds ⟨S.childStart d.val + j.val, by
      have hm := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
      rw [S.childStart_end] at hm
      omega⟩

theorem StaticTreeSlice.childSlice_nodup (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) : (S.childSlice d).Nodup := by
  unfold StaticTreeSlice.childSlice
  rw [List.nodup_iff_pairwise_ne]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  simp only [List.length_ofFn] at hi hj
  simp only [List.getElem_ofFn] at heq
  have hm := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
  rw [S.childStart_end] at hm
  have hstrict := S.childEntries_strict d (S.childStart d.val + i) (S.childStart d.val + j)
    (Nat.le_add_right _ _) (by omega) (by omega) (by omega) (by omega)
  rw [heq] at hstrict
  exact Nat.lt_irrefl _ hstrict

theorem StaticTreeSlice.mem_childSlice_iff (S : StaticTreeSlice mem treeBase g r dense)
    (d c : Fin dense.length) :
    c ∈ S.childSlice d ↔ c.val ≠ 0 ∧ S.domParent c = d := by
  rw [← S.childIds_mem_iff d c]
  constructor
  · intro hm
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    simp only [StaticTreeSlice.childSlice, List.length_ofFn] at hj
    simp only [StaticTreeSlice.childSlice, List.getElem_ofFn] at heq
    have hEnd := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
    rw [S.childStart_end] at hEnd
    exact ⟨S.childStart d.val + j, Nat.le_add_right _ _, by omega, by omega, heq⟩
  · rintro ⟨pos, hlo, hhi, hp, heq⟩
    apply List.mem_iff_getElem.mpr
    refine ⟨pos - S.childStart d.val, by simp [StaticTreeSlice.childSlice]; omega, ?_⟩
    simp only [StaticTreeSlice.childSlice, List.getElem_ofFn]
    have hPosEq : S.childStart d.val + (pos - S.childStart d.val) = pos := by omega
    rw [← heq]; congr 1; exact Fin.ext hPosEq

/-- Induced `Fin dense.length → Nat` self-slot map matching `selfSlot[0..Q-1]`. -/
def StaticTreeSlice.selfSlotFn (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) : Nat :=
  if _hv : v.val = 0 then 0
  else
    let d := S.domParent v
    ((S.childSlice d).idxOf v) + 1

theorem StaticTreeSlice.selfSlotFn_root (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) (hv : v.val = 0) :
    S.selfSlotFn v = 0 := by
  simp [StaticTreeSlice.selfSlotFn, hv]

theorem StaticTreeSlice.selfSlotFn_pos (S : StaticTreeSlice mem treeBase g r dense)
    {d c : Fin dense.length} {pos : Nat}
    (hlo : S.childStart d.val ≤ pos) (hhi : pos < S.childStart (d.val + 1))
    (hp : pos < dense.length - 1) (hc : S.childIds ⟨pos, hp⟩ = c) :
    S.selfSlotFn c = (pos - S.childStart d.val) + 1 := by
  have hmem : c ∈ S.childSlice d :=
    (S.mem_childSlice_iff d c).mpr ((S.childIds_mem_iff d c).mp ⟨pos, hlo, hhi, hp, hc⟩)
  have hProp := (S.mem_childSlice_iff d c).mp hmem
  unfold StaticTreeSlice.selfSlotFn
  rw [dite_eq_right hProp.1]
  have hdEq : S.domParent c = d := hProp.2
  dsimp only
  rw [hdEq]
  have hIdx : (S.childSlice d).idxOf c = pos - S.childStart d.val := by
    let idx := pos - S.childStart d.val
    have hidxLt : idx < (S.childSlice d).length := by
      simp [StaticTreeSlice.childSlice]; omega
    have hget : (S.childSlice d)[idx]'hidxLt = c := by
      simp only [StaticTreeSlice.childSlice, List.getElem_ofFn]
      have hPosEq : S.childStart d.val + idx = pos := by dsimp only [idx]; omega
      rw [← hc]; congr 1; exact Fin.ext hPosEq
    have hnd := S.childSlice_nodup d
    have hmem : (S.childSlice d)[idx]'hidxLt ∈ S.childSlice d := List.getElem_mem hidxLt
    have hlt : (S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt) < (S.childSlice d).length :=
      List.idxOf_lt_length_of_mem hmem
    have hEqGet : (S.childSlice d)[(S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt)]'hlt =
        (S.childSlice d)[idx]'hidxLt := List.getElem_idxOf hlt
    rw [← hget]
    have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
    by_cases hne : (S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt) = idx
    · exact hne
    · rcases Nat.lt_or_gt_of_ne hne with h1 | h3
      · exact False.elim (hPw _ _ hlt hidxLt h1 hEqGet)
      · exact False.elim (hPw _ _ hidxLt hlt h3 hEqGet.symm)
  rw [hIdx]

theorem StaticTreeSlice.selfSlotFn_lt (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) :
    S.selfSlotFn v < (S.childSlice (S.domParent v)).length + 1 := by
  by_cases hv : v.val = 0
  · rw [S.selfSlotFn_root v hv]; omega
  · have hmem : v ∈ S.childSlice (S.domParent v) :=
      (S.mem_childSlice_iff (S.domParent v) v).mpr ⟨hv, rfl⟩
    unfold StaticTreeSlice.selfSlotFn
    rw [dite_eq_right hv]
    dsimp only
    have hidx := List.idxOf_lt_length_of_mem hmem
    omega

private theorem sum_ofFn_diff_aux (k : Nat) (f : Nat → Nat)
    (hmono : ∀ i < k, f i ≤ f (i + 1)) :
    (List.ofFn fun d : Fin k => f (d.val + 1) - f d.val).sum + f 0 = f k := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.sum_cons]
    have h0 := hmono 0 (Nat.zero_lt_succ k)
    have ih' := ih (fun i => f (i + 1)) (fun i hi => hmono (i + 1) (Nat.succ_lt_succ hi))
    simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add] at *
    omega

theorem StaticTreeSlice.sum_childLengths (S : StaticTreeSlice mem treeBase g r dense) :
    (List.ofFn fun d : Fin dense.length => (S.childSlice d).length).sum = dense.length - 1 := by
  have hLen : (fun d : Fin dense.length => (S.childSlice d).length) =
      (fun d : Fin dense.length => S.childStart (d.val + 1) - S.childStart d.val) := by
    funext d; simp [StaticTreeSlice.childSlice]
  have hSum := sum_ofFn_diff_aux dense.length S.childStart
    (fun i hi => S.childStart_mono i (i + 1) (Nat.le_succ i) hi)
  rw [hLen]
  rw [S.childStart_zero, S.childStart_end] at hSum
  omega

theorem StaticTreeSlice.sum_ownerVertexCounts (S : StaticTreeSlice mem treeBase g r dense) :
    (List.ofFn fun d : Fin dense.length => 1 + (S.childSlice d).length).sum =
      2 * dense.length - 1 := by
  have hPos := S.qPos
  have hSplit : (List.ofFn fun d : Fin dense.length => 1 + (S.childSlice d).length).sum =
      dense.length + (List.ofFn fun d : Fin dense.length => (S.childSlice d).length).sum := by
    clear hPos
    suffices ∀ (k : Nat) (f : Fin k → Nat),
        (List.ofFn fun d : Fin k => 1 + f d).sum = k + (List.ofFn f).sum from
      this dense.length (fun d => (S.childSlice d).length)
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro f
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih (fun d => f d.succ)]
      omega
  rw [hSplit, S.sum_childLengths]
  omega

/-- Construct the `PackedStaticLayout.Input dense.length` induced by `S`. -/
def StaticTreeSlice.packedInput (S : StaticTreeSlice mem treeBase g r dense) :
    PackedStaticLayout.Input dense.length where
  root := ⟨0, S.qPos⟩
  parent := ⟨Array.ofFn S.domParent, by simp⟩
  depth := ⟨Array.ofFn S.domDepth, by simp⟩

theorem StaticTreeSlice.packedInput_ok (S : StaticTreeSlice mem treeBase g r dense) :
    PackedStaticLayout.InputOK S.packedInput := by
  have hp : ∀ v : Fin dense.length, S.packedInput.parent.read v = S.domParent v := by
    intro v; simp [StaticTreeSlice.packedInput, StaticHeadSweep.Slots.read, Array.getElem_ofFn]
  have hd : ∀ v : Fin dense.length, S.packedInput.depth.read v = S.domDepth v := by
    intro v; simp [StaticTreeSlice.packedInput, StaticHeadSweep.Slots.read, Array.getElem_ofFn]
  have hrootP : S.packedInput.parent.read S.packedInput.root = S.packedInput.root := by
    apply Fin.ext; rw [hp]; exact S.domParent_root
  have hrootD : S.packedInput.depth.read S.packedInput.root = 0 := by
    rw [hd]; exact S.domDepth_root
  have hstep : ∀ v : Fin dense.length, v ≠ S.packedInput.root →
      S.packedInput.depth.read v = S.packedInput.depth.read (S.packedInput.parent.read v) + 1 := by
    intro v hv
    have hv0 : 0 < v.val := by
      have : v.val ≠ 0 := fun h => hv (Fin.ext h)
      omega
    rw [hd v, hp v, hd (S.domParent v)]
    exact S.domDepth_step v hv0
  constructor
  all_goals
    try (apply And.intro <;> try (apply And.intro <;> try apply And.intro))
  all_goals
    first
    | exact hrootP
    | exact hrootP.symm
    | exact hrootD
    | exact hrootD.symm
    | exact hstep
    | intro v hv
      have e := hstep v hv
      first | exact e.symm | omega
    | intro v hv
      have hne : v ≠ S.packedInput.root := by
        intro e; subst v; rw [hrootD] at hv; omega
      have e := hstep v hne
      first | exact e | exact e.symm | omega

/-- Agreement predicate linking a runtime `StaticTreeSlice` to a semantic
`OriginalReader g r` (whose `readOriginalParent` is module-private to `StaticOracleTree`). -/
structure StaticTreeSlice.MatchesReader (S : StaticTreeSlice mem treeBase g r dense)
    (q : OriginalReader g r) : Prop where
  count_eq : q.count = dense.length
  originals_eq : ∀ i : Fin dense.length,
    q.ids.originals.read (Fin.cast count_eq.symm i) = dense[i.val]'i.isLt
  root_eq : q.input.root.val = 0
  parent_eq : ∀ i : Fin dense.length,
    (q.input.parent.read (Fin.cast count_eq.symm i)).val = (S.domParent i).val
  entry_eq : ∀ i : Fin dense.length,
    q.reader.entry (Fin.cast count_eq.symm i) = S.entry i
  stop_eq : ∀ i : Fin dense.length,
    q.reader.stop (Fin.cast count_eq.symm i) = S.stop i

/-! ### 2b. Binary Search, Emitted Quotient Arcs, and Correspondence with `denseQuotient` -/

private theorem list_nodup_length_le {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ a ∈ xs, a ∈ ys) → xs.length ≤ ys.length
  | [], ys, _, _ => Nat.zero_le ys.length
  | x :: xs, ys, hnd, hsub => by
    have hxys : x ∈ ys := hsub x (List.mem_cons_self)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ a ∈ xs, a ∈ ys.erase x := by
      intro a ha
      have hne : a ≠ x := fun h => hnd'.1 (h ▸ ha)
      exact List.mem_erase_of_ne hne |>.mpr (hsub a (List.mem_cons_of_mem x ha))
    have hlen := list_nodup_length_le xs (ys.erase x) hnd'.2 hsub'
    have her : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hxys
    have hyPos : 0 < ys.length := by
      cases ys with
      | nil => simp at hxys
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

theorem StaticTreeSlice.length_le (S : StaticTreeSlice mem treeBase g r dense) :
    dense.length ≤ g.vertexCount := by
  have hsub : ∀ a ∈ dense, a ∈ List.finRange g.vertexCount := fun a _ => List.mem_finRange a
  simpa only [List.length_finRange] using list_nodup_length_le dense (List.finRange g.vertexCount) S.nodup hsub

theorem StaticTreeSlice.dense_injective (S : StaticTreeSlice mem treeBase g r dense)
    {i j : Fin dense.length}
    (h : dense[i.val]'i.isLt = dense[j.val]'j.isLt) : i = j := by
  have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp S.nodup)
  apply Fin.ext
  by_cases he : i.val = j.val
  · exact he
  · rcases Nat.lt_or_gt_of_ne he with hlt | hgt
    · exact False.elim (hPw _ _ i.isLt j.isLt hlt h)
    · exact False.elim (hPw _ _ j.isLt i.isLt hgt h.symm)

theorem StaticTreeSlice.domParent_ne_self (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) (hv : 0 < v.val) : S.domParent v ≠ v := by
  have hlt := S.domParent_lt v hv
  intro h; rw [h] at hlt; exact Nat.lt_irrefl _ hlt

theorem StaticTreeSlice.dominates_root (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) : g.Dominates r r (dense[v.val]'v.isLt) := by
  intro p
  cases p with
  | refl _ h => exact h rfl
  | step _ _ _ h _ _ => exact h rfl

theorem StaticTreeSlice.entry_root_le (S : StaticTreeSlice mem treeBase g r dense)
    (v : Fin dense.length) : S.entry ⟨0, S.qPos⟩ ≤ S.entry v := by
  have hdom : g.Dominates r (dense[0]'S.qPos) (dense[v.val]'v.isLt) := by
    rw [S.head_eq]; exact S.dominates_root v
  exact ((S.dominates_iff_interval ⟨0, S.qPos⟩ v).mp hdom).1

theorem StaticTreeSlice.child_interval_disjoint (S : StaticTreeSlice mem treeBase g r dense)
    (acyc : g.IsAcyclic) (d c₁ c₂ : Fin dense.length)
    (hc₁ : c₁ ∈ S.childSlice d) (hc₂ : c₂ ∈ S.childSlice d)
    (hEntry : S.entry c₁ < S.entry c₂) :
    S.stop c₁ ≤ S.entry c₂ := by
  obtain ⟨hc₁_pos, hc₁_p⟩ := (S.mem_childSlice_iff d c₁).mp hc₁
  obtain ⟨hc₂_pos, hc₂_p⟩ := (S.mem_childSlice_iff d c₂).mp hc₂
  have hc₁0 : 0 < c₁.val := Nat.pos_of_ne_zero hc₁_pos
  have hc₂0 : 0 < c₂.val := Nat.pos_of_ne_zero hc₂_pos
  by_cases hlt : S.entry c₂ < S.stop c₁
  · exfalso
    have hdom12 : g.Dominates r (dense[c₁.val]'c₁.isLt) (dense[c₂.val]'c₂.isLt) :=
      (S.dominates_iff_interval c₁ c₂).mpr ⟨Nat.le_of_lt hEntry, hlt⟩
    have hc₁ne : c₁ ≠ c₂ := fun h => by subst h; exact Nat.lt_irrefl _ hEntry
    have hdc₁ne : dense[c₁.val]'c₁.isLt ≠ dense[c₂.val]'c₂.isLt :=
      fun h => hc₁ne (S.dense_injective h)
    have himm2 := S.domParent_spec c₂ hc₂0
    rw [hc₂_p] at himm2
    have hdom1d : g.Dominates r (dense[c₁.val]'c₁.isLt) (dense[d.val]'d.isLt) :=
      himm2.2.2 (dense[c₁.val]'c₁.isLt) hdc₁ne hdom12
    have himm1 := S.domParent_spec c₁ hc₁0
    rw [hc₁_p] at himm1
    have hdomd1 : g.Dominates r (dense[d.val]'d.isLt) (dense[c₁.val]'c₁.isLt) := himm1.2.1
    have hc₁d : c₁ ≠ d := by rw [← hc₁_p]; exact (S.domParent_ne_self c₁ hc₁0).symm
    have hdc₁d : dense[c₁.val]'c₁.isLt ≠ dense[d.val]'d.isLt :=
      fun h => hc₁d (S.dense_injective h)
    obtain ⟨rank, progress⟩ := acyc
    have hr1 : rank (dense[c₁.val]'c₁.isLt) < rank (dense[d.val]'d.isLt) :=
      rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hdom1d hdc₁d
    have hr2 : rank (dense[d.val]'d.isLt) < rank (dense[c₁.val]'c₁.isLt) :=
      rank_lt_of_strict_dominator progress (S.reach_mem c₁.val c₁.isLt) hdomd1 hdc₁d.symm
    exact Nat.lt_irrefl _ (Nat.lt_trans hr1 hr2)
  · omega

def bsearchStep (entryAt : Nat → Nat) (l r target : Nat) : Nat × Nat :=
  let mid := l + (r - l) / 2
  if target < entryAt mid then (l, mid) else (mid, r)

def bsearchRun (entryAt : Nat → Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, l, _, _ => l
  | fuel + 1, l, r, target =>
    if l + 1 < r then
      let p := bsearchStep entryAt l r target
      bsearchRun entryAt fuel p.1 p.2 target
    else l

theorem bsearchRun_mem_range (entryAt : Nat → Nat) :
    ∀ (fuel l r target : Nat), l < r →
      l ≤ bsearchRun entryAt fuel l r target ∧ bsearchRun entryAt fuel l r target < r
  | 0, l, r, _, hlr => ⟨Nat.le_refl l, hlr⟩
  | fuel + 1, l, r, target, hlr => by
    unfold bsearchRun
    by_cases hcond : l + 1 < r
    · simp only [hcond, ↓reduceIte]
      dsimp only [bsearchStep]
      by_cases hcmp : target < entryAt (l + (r - l) / 2)
      · simp only [hcmp, ↓reduceIte]
        have hmid_gt : l < l + (r - l) / 2 := by omega
        have hsub := bsearchRun_mem_range entryAt fuel l (l + (r - l) / 2) target hmid_gt
        have hmid_lt : l + (r - l) / 2 < r := by omega
        exact ⟨hsub.1, Nat.lt_trans hsub.2 hmid_lt⟩
      · simp only [hcmp, ↓reduceIte]
        have hmid_lt : l + (r - l) / 2 < r := by omega
        have hsub := bsearchRun_mem_range entryAt fuel (l + (r - l) / 2) r target hmid_lt
        have hmid_ge : l ≤ l + (r - l) / 2 := Nat.le_add_right _ _
        exact ⟨Nat.le_trans hmid_ge hsub.1, hsub.2⟩
    · simp only [hcond, ↓reduceIte]
      exact ⟨Nat.le_refl l, hlr⟩

theorem bsearchRun_spec (entryAt : Nat → Nat) :
    ∀ (fuel l r hiEnd target : Nat),
      l < r → r ≤ hiEnd → r - l ≤ 2 ^ fuel →
      entryAt l ≤ target →
      (r < hiEnd → target < entryAt r) →
      let pos := bsearchRun entryAt fuel l r target
      l ≤ pos ∧ pos < r ∧ entryAt pos ≤ target ∧ (pos + 1 < hiEnd → target < entryAt (pos + 1))
  | 0, l, r, hiEnd, target, hlr, _, hw, hl, hr => by
    have hrl : r = l + 1 := by simp at hw; omega
    subst hrl
    exact ⟨Nat.le_refl l, Nat.lt_succ_self l, hl, hr⟩
  | fuel + 1, l, r, hiEnd, target, hlr, hrhi, hw, hl, hr => by
    unfold bsearchRun
    by_cases hcond : l + 1 < r
    · simp only [hcond, ↓reduceIte]
      dsimp only [bsearchStep]
      have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hcmp : target < entryAt (l + (r - l) / 2)
      · simp only [hcmp, ↓reduceIte]
        have hmid_gt : l < l + (r - l) / 2 := by omega
        have hmid_le : l + (r - l) / 2 ≤ hiEnd := by omega
        have hw' : (l + (r - l) / 2) - l ≤ 2 ^ fuel := by omega
        have hsub := bsearchRun_spec entryAt fuel l (l + (r - l) / 2) hiEnd target
          hmid_gt hmid_le hw' hl (fun _ => hcmp)
        have hmid_lt : l + (r - l) / 2 < r := by omega
        exact ⟨hsub.1, Nat.lt_trans hsub.2.1 hmid_lt, hsub.2.2⟩
      · simp only [hcmp, ↓reduceIte]
        have hmid_lt : l + (r - l) / 2 < r := by omega
        have hw' : r - (l + (r - l) / 2) ≤ 2 ^ fuel := by omega
        have hmid_le : entryAt (l + (r - l) / 2) ≤ target := Nat.le_of_not_lt hcmp
        have hsub := bsearchRun_spec entryAt fuel (l + (r - l) / 2) r hiEnd target
          hmid_lt hrhi hw' hmid_le hr
        have hmid_ge : l ≤ l + (r - l) / 2 := Nat.le_add_right _ _
        exact ⟨Nat.le_trans hmid_ge hsub.1, hsub.2⟩
    · simp only [hcond, ↓reduceIte]
      have hrl : r = l + 1 := by omega
      subst hrl
      exact ⟨Nat.le_refl l, Nat.lt_succ_self l, hl, hr⟩

def StaticTreeSlice.childEntryAt (S : StaticTreeSlice mem treeBase g r dense) (i : Nat) : Nat :=
  if hi : i < dense.length - 1 then S.entry (S.childIds ⟨i, hi⟩) else 0

def StaticTreeSlice.srcLocalOf (S : StaticTreeSlice mem treeBase g r dense)
    (d u : Fin dense.length) : Nat :=
  if u.val = d.val then 0
  else
    let lo := S.childStart d.val
    let hi := S.childStart (d.val + 1)
    if hi - lo = 0 then 0
    else
      let pos := bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) lo hi (S.entry u)
      pos - lo + 1

theorem StaticTreeSlice.srcLocalOf_lt (S : StaticTreeSlice mem treeBase g r dense)
    (d u : Fin dense.length) :
    S.srcLocalOf d u < 1 + (S.childSlice d).length := by
  unfold StaticTreeSlice.srcLocalOf StaticTreeSlice.childSlice
  simp only [List.length_ofFn]
  by_cases hud : u.val = d.val
  · simp only [hud, ↓reduceIte]; omega
  · simp only [hud, ↓reduceIte]
    by_cases hzero : S.childStart (d.val + 1) - S.childStart d.val = 0
    · simp only [hzero, ↓reduceIte]; omega
    · simp only [hzero, ↓reduceIte]
      have hlt : S.childStart d.val < S.childStart (d.val + 1) := by omega
      have hRange := bsearchRun_mem_range S.childEntryAt (OracleContract.L g.vertexCount)
        (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) hlt
      omega

theorem StaticTreeSlice.srcLocalOf_spec (S : StaticTreeSlice mem treeBase g r dense)
    (acyc : g.IsAcyclic) (d u : Fin dense.length)
    (hdom : g.Dominates r (dense[d.val]'d.isLt) (dense[u.val]'u.isLt)) :
    (u = d ∧ S.srcLocalOf d u = 0) ∨
    (∃ c : Fin dense.length, c ∈ S.childSlice d ∧
      g.Dominates r (dense[c.val]'c.isLt) (dense[u.val]'u.isLt) ∧
      S.srcLocalOf d u = (S.childSlice d).idxOf c + 1) := by
  by_cases hud : u = d
  · left; exact ⟨hud, by unfold StaticTreeSlice.srcLocalOf; simp [hud]⟩
  · right
    have hud_val : u.val ≠ d.val := fun h => hud (Fin.ext h)
    have ⟨rank, progress⟩ := acyc
    have hDom_interval := (S.dominates_iff_interval d u).mp hdom
    have hv_reach : g.InitiallyReachable r (dense[u.val]'u.isLt) := S.reach_mem u.val u.isLt
    -- Every strict descendant of `d` lies in a child subtree of `d`
    have hChildExists : ∃ pos : Nat, S.childStart d.val ≤ pos ∧ pos < S.childStart (d.val + 1) ∧
        ∃ hp : pos < dense.length - 1,
          let c := S.childIds ⟨pos, hp⟩
          g.Dominates r (dense[c.val]'c.isLt) (dense[u.val]'u.isLt) := by
      -- Walk up `domParent` from `u` to find the child of `d`
      suffices ∀ (k : Nat) (w : Fin dense.length),
          w.val ≤ k →
          w ≠ d →
          g.Dominates r (dense[d.val]'d.isLt) (dense[w.val]'w.isLt) →
          ∃ c : Fin dense.length, c ∈ S.childSlice d ∧
            g.Dominates r (dense[c.val]'c.isLt) (dense[w.val]'w.isLt) by
        obtain ⟨c, hc, hcu⟩ := this u.val u (Nat.le_refl _) hud hdom
        obtain ⟨j, hj, hcEq⟩ := List.mem_iff_getElem.mp hc
        simp only [StaticTreeSlice.childSlice, List.length_ofFn, List.getElem_ofFn] at hj hcEq
        have hEnd := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
        rw [S.childStart_end] at hEnd
        exact ⟨S.childStart d.val + j, Nat.le_add_right _ _, by omega, by omega,
          by simpa only [hcEq] using hcu⟩
      intro k
      induction k with
      | zero =>
        intro w hwk hwd hdw
        have hw0 : w.val = 0 := Nat.eq_zero_of_le_zero hwk
        have hdom' : g.Dominates r (dense[d.val]'d.isLt) r := by
          have hwEq : w = ⟨0, S.qPos⟩ := Fin.ext hw0
          rw [hwEq, S.head_eq] at hdw
          exact hdw
        have hdr : dense[d.val]'d.isLt = r := (dominates_source_iff (g := g)).mp hdom'
        have hd0 : d = ⟨0, S.qPos⟩ := by
          apply S.dense_injective
          rw [hdr, S.head_eq]
        exact False.elim (hwd (Fin.ext (hw0.trans (congrArg Fin.val hd0).symm)))
      | succ k ih =>
        intro w hwk hwd hdw
        by_cases hw0 : w.val = 0
        · have hdom' : g.Dominates r (dense[d.val]'d.isLt) r := by
            have hwEq : w = ⟨0, S.qPos⟩ := Fin.ext hw0
            rw [hwEq, S.head_eq] at hdw
            exact hdw
          have hdr : dense[d.val]'d.isLt = r := (dominates_source_iff (g := g)).mp hdom'
          have hd0 : d = ⟨0, S.qPos⟩ := by
            apply S.dense_injective
            rw [hdr, S.head_eq]
          exact False.elim (hwd (Fin.ext (hw0.trans (congrArg Fin.val hd0).symm)))
        · have hwPos : 0 < w.val := Nat.pos_of_ne_zero hw0
          let p := S.domParent w
          by_cases hpd : p = d
          · have hwMem : w ∈ S.childSlice d := (S.mem_childSlice_iff d w).mpr ⟨hw0, hpd⟩
            exact ⟨w, hwMem, dominates_refl⟩
          · have hplt : p.val < w.val := S.domParent_lt w hwPos
            have hpk : p.val ≤ k := by omega
            have himm := S.domParent_spec w hwPos
            have hdw_ne : dense[d.val]'d.isLt ≠ dense[w.val]'w.isLt :=
              fun he => hwd (S.dense_injective he).symm
            have hdp : g.Dominates r (dense[d.val]'d.isLt) (dense[p.val]'p.isLt) :=
              himm.2.2 (dense[d.val]'d.isLt) hdw_ne hdw
            obtain ⟨c, hcMem, hcp⟩ := ih p hpk hpd hdp
            exact ⟨c, hcMem, dominates_trans hcp himm.2.1⟩
    obtain ⟨posStar, hloStar, hhiStar, hpStar, hcDom⟩ := hChildExists
    let lo := S.childStart d.val
    let hi := S.childStart (d.val + 1)
    let cStar := S.childIds ⟨posStar, hpStar⟩
    have hEnd : hi ≤ dense.length - 1 := by
      have hm := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
      rwa [S.childStart_end] at hm
    have hlt : lo < hi := by omega
    have hneZero : hi - lo ≠ 0 := by omega
    have hPowBound : hi - lo ≤ 2 ^ OracleContract.L g.vertexCount := by
      have h1 : hi - lo ≤ dense.length := by omega
      have h2 : dense.length ≤ g.vertexCount := S.length_le
      have h3 : g.vertexCount + 1 < 2 ^ ((g.vertexCount + 1).log2 + 1) :=
        Nat.lt_log2_self (n := g.vertexCount + 1)
      have h4 : 2 ^ ((g.vertexCount + 1).log2 + 1) = 2 ^ OracleContract.L g.vertexCount := rfl
      omega
    have hEntry_mono : ∀ i j, lo ≤ i → i ≤ j → j < hi →
        S.childEntryAt i ≤ S.childEntryAt j := by
      intro i j hij1 hij2 hjhi
      by_cases heq : i = j
      · subst heq; exact Nat.le_refl _
      · have hilt : i < dense.length - 1 := by omega
        have hjlt : j < dense.length - 1 := by omega
        have hst := S.childEntries_strict d i j hij1 (Nat.lt_of_le_of_ne hij2 heq) hjhi hilt hjlt
        simp only [StaticTreeSlice.childEntryAt, hilt, hjlt, ↓reduceDIte]
        exact Nat.le_of_lt hst
    have hcInterval := (S.dominates_iff_interval cStar u).mp hcDom
    have hlo_le_u : S.childEntryAt lo ≤ S.entry u := by
      have hle := hEntry_mono lo posStar (Nat.le_refl _) hloStar hhiStar
      have heq : S.childEntryAt posStar = S.entry cStar := by
        simp [StaticTreeSlice.childEntryAt, hpStar, cStar]
      omega
    have hSpec := bsearchRun_spec S.childEntryAt (OracleContract.L g.vertexCount)
      lo hi hi (S.entry u) hlt (Nat.le_refl _) hPowBound hlo_le_u (fun h => False.elim (Nat.lt_irrefl _ h))
    let pos := bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) lo hi (S.entry u)
    have hpos_ge : lo ≤ pos := hSpec.1
    have hpos_lt : pos < hi := hSpec.2.1
    have hpos_le_u : S.childEntryAt pos ≤ S.entry u := hSpec.2.2.1
    have hpos_next : pos + 1 < hi → S.entry u < S.childEntryAt (pos + 1) := hSpec.2.2.2
    have hposEq : pos = posStar := by
      by_cases he : pos = posStar
      · exact he
      · rcases Nat.lt_or_gt_of_ne he with hlt1 | hgt1
        · have hnextLt : pos + 1 < hi := by omega
          have h1 := hpos_next hnextLt
          have h2 := hEntry_mono (pos + 1) posStar (by omega) (by omega) hhiStar
          have heq : S.childEntryAt posStar = S.entry cStar := by
            simp [StaticTreeSlice.childEntryAt, hpStar, cStar]
          omega
        · have hpPos : pos < dense.length - 1 := by omega
          let cPos := S.childIds ⟨pos, hpPos⟩
          have hcStarMem : cStar ∈ S.childSlice d :=
            (S.mem_childSlice_iff d cStar).mpr ((S.childIds_mem_iff d cStar).mp ⟨posStar, hloStar, hhiStar, hpStar, rfl⟩)
          have hcPosMem : cPos ∈ S.childSlice d :=
            (S.mem_childSlice_iff d cPos).mpr ((S.childIds_mem_iff d cPos).mp ⟨pos, hpos_ge, hpos_lt, hpPos, rfl⟩)
          have hStrict := S.childEntries_strict d posStar pos hloStar hgt1 hpos_lt hpStar hpPos
          have hDisj := S.child_interval_disjoint acyc d cStar cPos hcStarMem hcPosMem hStrict
          have heqPos : S.childEntryAt pos = S.entry cPos := by
            simp [StaticTreeSlice.childEntryAt, hpPos, cPos]
          omega
    have hcStarMem : cStar ∈ S.childSlice d :=
      (S.mem_childSlice_iff d cStar).mpr ((S.childIds_mem_iff d cStar).mp ⟨posStar, hloStar, hhiStar, hpStar, rfl⟩)
    have hIdx : (S.childSlice d).idxOf cStar = posStar - lo := by
      let idx := posStar - lo
      have hidxLt : idx < (S.childSlice d).length := by
        simp [StaticTreeSlice.childSlice]; omega
      have hget : (S.childSlice d)[idx]'hidxLt = cStar := by
        simp only [StaticTreeSlice.childSlice, List.getElem_ofFn]
        have hSum : S.childStart d.val + idx = posStar := by dsimp only [idx, lo]; omega
        congr 1; exact Fin.ext hSum
      have hnd := S.childSlice_nodup d
      have hmem : (S.childSlice d)[idx]'hidxLt ∈ S.childSlice d := List.getElem_mem hidxLt
      have hltIdx : (S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt) < (S.childSlice d).length :=
        List.idxOf_lt_length_of_mem hmem
      have hEqGet : (S.childSlice d)[(S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt)]'hltIdx =
          (S.childSlice d)[idx]'hidxLt := List.getElem_idxOf hltIdx
      rw [← hget]
      have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
      by_cases hne : (S.childSlice d).idxOf ((S.childSlice d)[idx]'hidxLt) = idx
      · exact hne
      · rcases Nat.lt_or_gt_of_ne hne with h1 | h3
        · exact False.elim (hPw _ _ hltIdx hidxLt h1 hEqGet)
        · exact False.elim (hPw _ _ hidxLt hltIdx h3 hEqGet.symm)
    refine ⟨cStar, hcStarMem, hcDom, ?_⟩
    unfold StaticTreeSlice.srcLocalOf
    simp only [hud_val, ↓reduceIte]
    change (if hi - lo = 0 then 0 else pos - lo + 1) = (S.childSlice d).idxOf cStar + 1
    simp only [hneZero, ↓reduceIte, hposEq, hIdx]

structure EmittedArc (Q : Nat) where
  owner : Fin Q
  srcLocal : Nat
  headLocal : Nat
  tailEntry : Nat
  deriving DecidableEq

def StaticTreeSlice.emittedArc (S : StaticTreeSlice mem treeBase g r dense)
    (uDense vDense : Fin dense.length) : EmittedArc dense.length where
  owner := S.domParent vDense
  srcLocal := S.srcLocalOf (S.domParent vDense) uDense
  headLocal := S.selfSlotFn vDense
  tailEntry := S.entry uDense

def StaticTreeSlice.emitForU (S : StaticTreeSlice mem treeBase g r dense)
    (uDense : Fin dense.length) : List (EmittedArc dense.length) :=
  (g.outArcs (dense[uDense.val]'uDense.isLt)).filterMap fun vOrig =>
    if hv : dense.idxOf vOrig < dense.length then
      some (S.emittedArc uDense ⟨dense.idxOf vOrig, hv⟩)
    else none

def StaticTreeSlice.allEmittedArcs (S : StaticTreeSlice mem treeBase g r dense) :
    List (EmittedArc dense.length) :=
  (List.finRange dense.length).flatMap (S.emitForU)

def StaticTreeSlice.emittedArcs (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) : List (EmittedArc dense.length) :=
  S.allEmittedArcs.filter (fun e => e.owner == d)

theorem StaticTreeSlice.emitForU_length (S : StaticTreeSlice mem treeBase g r dense)
    (uDense : Fin dense.length) :
    (S.emitForU uDense).length = (g.outArcs (dense[uDense.val]'uDense.isLt)).length := by
  unfold StaticTreeSlice.emitForU
  have hAll : ∀ vOrig ∈ g.outArcs (dense[uDense.val]'uDense.isLt),
      dense.idxOf vOrig < dense.length := fun vOrig hv =>
    List.idxOf_lt_length_of_mem
      (S.mem_reach vOrig (initiallyReachable_extend (S.reach_mem uDense.val uDense.isLt) hv))
  suffices ∀ l : List (Fin g.vertexCount),
      (∀ vOrig ∈ l, dense.idxOf vOrig < dense.length) →
      (l.filterMap fun vOrig =>
        if hv : dense.idxOf vOrig < dense.length then
          some (S.emittedArc uDense ⟨dense.idxOf vOrig, hv⟩)
        else none).length = l.length from
    this _ hAll
  intro l
  induction l with
  | nil => intro _; simp
  | cons v vs ih =>
    intro hvs
    have hv : dense.idxOf v < dense.length := hvs v List.mem_cons_self
    have hvs' : ∀ w ∈ vs, dense.idxOf w < dense.length := fun w hw =>
      hvs w (List.mem_cons_of_mem v hw)
    simp only [List.filterMap_cons, hv, ↓reduceDIte, List.length_cons]
    exact congrArg Nat.succ (ih hvs')

private theorem list_sum_filter_fin {Q : Nat} {α : Type _} (f : α → Fin Q) (xs : List α) :
    ((List.finRange Q).map (fun d => (xs.filter (fun a => f a == d)).length)).sum = xs.length := by
  induction xs with
  | nil =>
    simp only [List.filter_nil, List.length_nil]
    clear f
    induction (List.finRange Q) with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  | cons a xs ih =>
    have hSplit : ∀ d : Fin Q,
        ((a :: xs).filter (fun b => f b == d)).length =
          (if f a = d then 1 else 0) + (xs.filter (fun b => f b == d)).length := by
      intro d
      by_cases he : f a = d
      · simp [he, Nat.add_comm]
      · have hb : (f a == d) = false := beq_false_of_ne he
        simp [hb, he]
    have hMap : ((List.finRange Q).map (fun d => ((a :: xs).filter (fun b => f b == d)).length)).sum =
        ((List.finRange Q).map (fun d => if f a = d then 1 else 0)).sum +
        ((List.finRange Q).map (fun d => (xs.filter (fun b => f b == d)).length)).sum := by
      clear ih
      suffices ∀ ds : List (Fin Q),
          (ds.map (fun d => ((a :: xs).filter (fun b => f b == d)).length)).sum =
            (ds.map (fun d => if f a = d then 1 else 0)).sum +
            (ds.map (fun d => (xs.filter (fun b => f b == d)).length)).sum from
        this (List.finRange Q)
      intro ds
      induction ds with
      | nil => simp
      | cons d ds ihd =>
        simp only [List.map_cons, List.sum_cons, hSplit d, ihd]
        omega
    have hOne : ((List.finRange Q).map (fun d => if f a = d then 1 else 0)).sum = 1 := by
      clear ih hSplit hMap
      suffices ∀ ds : List (Fin Q), ds.Nodup → f a ∈ ds →
          (ds.map (fun d => if f a = d then 1 else 0)).sum = 1 from
        this (List.finRange Q) (List.nodup_finRange Q) (List.mem_finRange (f a))
      intro ds
      induction ds with
      | nil => intro _ hm; simp at hm
      | cons d ds ihd =>
        intro hnd hm
        have hnd' := List.nodup_cons.mp hnd
        simp only [List.map_cons, List.sum_cons]
        by_cases he : f a = d
        · have hZero : (ds.map (fun d' => if f a = d' then 1 else 0)).sum = 0 := by
            have hna : f a ∉ ds := fun e => hnd'.1 (he ▸ e)
            clear ihd hm hnd hnd' he d
            induction ds with
            | nil => rfl
            | cons d' ds' ihs =>
              have hne' : f a ≠ d' := fun e => hna (e ▸ List.mem_cons_self)
              have hna' : f a ∉ ds' := fun e => hna (List.mem_cons_of_mem d' e)
              simp only [List.map_cons, List.sum_cons, hne', ↓reduceIte, Nat.zero_add]
              exact ihs hna'
          have hHead : (if f a = d then 1 else 0) = 1 := by simp [he]
          rw [hHead, hZero]
        · have hMem' : f a ∈ ds := (List.mem_cons.mp hm).resolve_left he
          simp only [he, ↓reduceIte, Nat.zero_add]
          exact ihd hnd'.2 hMem'
    rw [hMap, hOne, ih]
    simp [Nat.add_comm]

theorem StaticTreeSlice.sum_emittedArcs_eq (S : StaticTreeSlice mem treeBase g r dense) :
    ((List.finRange dense.length).map (fun d => (S.emittedArcs d).length)).sum =
      S.allEmittedArcs.length := by
  unfold StaticTreeSlice.emittedArcs
  exact list_sum_filter_fin EmittedArc.owner S.allEmittedArcs

theorem StaticTreeSlice.allEmittedArcs_length_le (S : StaticTreeSlice mem treeBase g r dense) :
    S.allEmittedArcs.length ≤ g.arcCount := by
  unfold StaticTreeSlice.allEmittedArcs
  rw [List.length_flatMap]
  have hMap : (List.finRange dense.length).map (fun u => (S.emitForU u).length) =
      (List.finRange dense.length).map (fun u => (g.outArcs (dense[u.val]'u.isLt)).length) := by
    congr 1; funext u; exact S.emitForU_length u
  rw [hMap]
  have hMem : ∀ u ∈ List.finRange dense.length, u ∈ List.finRange dense.length := fun _ h => h
  have hInj : ∀ u₁ u₂ : Fin dense.length,
      dense[u₁.val]'u₁.isLt = dense[u₂.val]'u₂.isLt → u₁ = u₂ := fun _ _ h => S.dense_injective h
  have hArcSum : g.arcCount =
      ((List.finRange g.vertexCount).map (fun v => (g.outArcs v).length)).sum := by
    unfold Digraph.arcCount
    suffices ∀ (xs : List (List (Fin g.vertexCount))),
        listLengthSum xs = (xs.map List.length).sum by
      rw [this g.adj.toList]
      have hFin : (List.finRange g.vertexCount).map (fun v => (g.outArcs v).length) =
          g.adj.toList.map List.length := by
        apply List.ext_getElem
        · simp [g.adj_size]
        · intro i hi1 hi2
          simp only [List.getElem_map, List.getElem_finRange, Digraph.outArcs]
          rfl
      rw [hFin]
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [listLengthSum, ih]
  rw [hArcSum]
  have hMapDense : (List.finRange dense.length).map (fun u => (g.outArcs (dense[u.val]'u.isLt)).length) =
      dense.map (fun v => (g.outArcs v).length) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2; simp
  rw [hMapDense]
  have hSub : ∀ v ∈ dense, v ∈ List.finRange g.vertexCount := fun v _ => List.mem_finRange v
  clear hMem hInj hArcSum hMapDense hMap
  have hNodup := S.nodup
  suffices ∀ (xs ys : List (Fin g.vertexCount)), xs.Nodup → (∀ a ∈ xs, a ∈ ys) →
      (xs.map (fun v => (g.outArcs v).length)).sum ≤
        (ys.map (fun v => (g.outArcs v).length)).sum from
    this dense (List.finRange g.vertexCount) hNodup hSub
  intro xs
  induction xs with
  | nil => intro ys _ _; simp
  | cons x xs ih =>
    intro ys hnd hsub
    have hxys : x ∈ ys := hsub x List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ a ∈ xs, a ∈ ys.erase x := fun a ha =>
      (List.mem_erase_of_ne (fun e => hnd'.1 (by subst e; exact ha))).mpr
        (hsub a (List.mem_cons_of_mem x ha))
    have hIH := ih (ys.erase x) hnd'.2 hsub'
    have hEraseSum : (ys.map (fun v => (g.outArcs v).length)).sum =
        (g.outArcs x).length + ((ys.erase x).map (fun v => (g.outArcs v).length)).sum := by
      clear hnd hnd' hsub hsub' hIH ih
      induction ys with
      | nil => simp at hxys
      | cons y ys ihy =>
        by_cases he : x = y
        · subst he
          simp [List.erase_cons_head]
        · have hb : (y == x) = false := beq_false_of_ne (fun e => he e.symm)
          have hy_mem : x ∈ ys := (List.mem_cons.mp hxys).resolve_left he
          simp only [List.erase_cons, hb, Bool.false_eq_true, ↓reduceIte,
            List.map_cons, List.sum_cons, ihy hy_mem]
          omega
    rw [List.map_cons, List.sum_cons, hEraseSum]
    omega

theorem StaticTreeSlice.emittedArc_bounds (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) {e : EmittedArc dense.length}
    (he : e ∈ S.emittedArcs d) :
    e.owner = d ∧
    e.srcLocal < 1 + (S.childSlice d).length ∧
    e.headLocal < 1 + (S.childSlice d).length ∧
    e.tailEntry < dense.length := by
  unfold StaticTreeSlice.emittedArcs StaticTreeSlice.allEmittedArcs at he
  obtain ⟨hmAll, hOwnerB⟩ := List.mem_filter.mp he
  have hOwner : e.owner = d := beq_iff_eq.mp hOwnerB
  obtain ⟨uDense, _, heU⟩ := List.mem_flatMap.mp hmAll
  unfold StaticTreeSlice.emitForU at heU
  obtain ⟨vOrig, _, hvEq⟩ := List.mem_filterMap.mp heU
  by_cases hv : dense.idxOf vOrig < dense.length
  · simp only [hv, ↓reduceDIte, Option.some.injEq] at hvEq
    subst e
    refine ⟨hOwner, ?_, ?_, ?_⟩
    · rw [← hOwner]; exact S.srcLocalOf_lt (S.domParent ⟨dense.idxOf vOrig, hv⟩) uDense
    · rw [← hOwner]; exact Nat.lt_of_lt_of_eq (S.selfSlotFn_lt ⟨dense.idxOf vOrig, hv⟩) (Nat.add_comm _ 1)
    · exact Nat.lt_of_lt_of_le (S.entry_lt_stop uDense).1 (S.entry_lt_stop uDense).2
  · simp [hv] at hvEq

/-- The concrete `LabelledQuotient` induced at owner `d` by `S.emittedArcs d`. -/
@[reducible] def StaticTreeSlice.ramQuotient (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) : LabelledQuotient where
  origVertexCount := g.vertexCount
  vertexCount := 1 + (S.childSlice d).length
  root := ⟨0, by omega⟩
  adj := Array.ofFn fun uLocal : Fin (1 + (S.childSlice d).length) =>
    (S.emittedArcs d).filterMap fun e =>
      if e.srcLocal == uLocal.val then
        if hHead : e.headLocal < 1 + (S.childSlice d).length then
          if hEnt : e.tailEntry < dense.length then
            let uD := S.denseOfEntry ⟨e.tailEntry, hEnt⟩
            some ⟨⟨e.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩
          else none
        else none
      else none
  adj_size := by simp

private theorem idxOf_getElem_of_nodup' {α : Type _} [BEq α] [LawfulBEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf (l[i]'hi) = i := by
  have hmem : l[i]'hi ∈ l := List.getElem_mem hi
  have hlt : l.idxOf (l[i]'hi) < l.length := List.idxOf_lt_length_of_mem hmem
  have hEq : l[l.idxOf (l[i]'hi)]'hlt = l[i]'hi := List.getElem_idxOf hlt
  have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
  by_cases hne : l.idxOf (l[i]'hi) = i
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with h1 | h3
    · exact False.elim (hPw _ _ hlt hi h1 hEq)
    · exact False.elim (hPw _ _ hi hlt h3 hEq.symm)

theorem StaticTreeSlice.mem_outArcs_ramQuotient_iff (S : StaticTreeSlice mem treeBase g r dense)
    (d : Fin dense.length) (uLocal : Fin (S.ramQuotient d).vertexCount)
    (e : QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount) :
    e ∈ (S.ramQuotient d).outArcs uLocal ↔
      ∃ uDense vDense : Fin dense.length,
        g.HasArc (dense[uDense.val]'uDense.isLt) (dense[vDense.val]'vDense.isLt) ∧
        S.domParent vDense = d ∧
        S.srcLocalOf d uDense = uLocal.val ∧
        S.selfSlotFn vDense = e.head.val ∧
        dense[uDense.val]'uDense.isLt = e.origTail := by
  have hAdj : (S.ramQuotient d).outArcs uLocal =
      (S.emittedArcs d).filterMap (fun ea =>
        if ea.srcLocal == uLocal.val then
          if hHead : ea.headLocal < 1 + (S.childSlice d).length then
            if hEnt : ea.tailEntry < dense.length then
              let uD := S.denseOfEntry ⟨ea.tailEntry, hEnt⟩
              some (⟨⟨ea.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩ :
                QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount)
            else none
          else none
        else none) := by
    simp [LabelledQuotient.outArcs, StaticTreeSlice.ramQuotient]
  rw [hAdj, List.mem_filterMap]
  constructor
  · rintro ⟨ea, hea, hsome⟩
    by_cases hsrc : (ea.srcLocal == uLocal.val) = true
    · simp only [hsrc, ↓reduceIte] at hsome
      have hsrcEq : ea.srcLocal = uLocal.val := beq_iff_eq.mp hsrc
      have hBnd := S.emittedArc_bounds d hea
      simp only [hBnd.2.2.1, hBnd.2.2.2, ↓reduceDIte, Option.some.injEq] at hsome
      unfold StaticTreeSlice.emittedArcs StaticTreeSlice.allEmittedArcs at hea
      obtain ⟨hmAll, _⟩ := List.mem_filter.mp hea
      obtain ⟨uDense, _, heU⟩ := List.mem_flatMap.mp hmAll
      unfold StaticTreeSlice.emitForU at heU
      obtain ⟨vOrig, hvArc, hvEq⟩ := List.mem_filterMap.mp heU
      by_cases hv : dense.idxOf vOrig < dense.length
      · simp only [hv, ↓reduceDIte, Option.some.injEq] at hvEq
        let vDense : Fin dense.length := ⟨dense.idxOf vOrig, hv⟩
        have hvOrigEq : dense[vDense.val]'vDense.isLt = vOrig := List.getElem_idxOf hv
        have heaEq : ea = S.emittedArc uDense vDense := hvEq.symm
        have huD : S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩ = uDense := by
          have hEntEq : ea.tailEntry = S.entry uDense := by rw [heaEq]; rfl
          apply Fin.ext
          have hsub : (⟨ea.tailEntry, hBnd.2.2.2⟩ : Fin dense.length) =
              ⟨S.entry uDense, Nat.lt_of_lt_of_le (S.entry_lt_stop uDense).1 (S.entry_lt_stop uDense).2⟩ :=
            Fin.ext hEntEq
          rw [hsub, S.denseOfEntry_entry uDense]
        have hOwnV : S.domParent vDense = d :=
          (heaEq ▸ rfl : ea.owner = S.domParent vDense).symm.trans hBnd.1
        refine ⟨uDense, vDense, ?_, hOwnV, ?_, ?_, ?_⟩
        · change vOrig ∈ g.outArcs (dense[uDense.val]'uDense.isLt) at hvArc
          rwa [hvOrigEq]
        · have hSrcEq : (S.emittedArc uDense vDense).srcLocal = S.srcLocalOf (S.domParent vDense) uDense := rfl
          rw [← hsrcEq, heaEq, hSrcEq, hOwnV]
        · have hh : ea.headLocal = e.head.val := by rw [← hsome]
          rw [← hh, heaEq]; rfl
        · have ht : dense[(S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩).val]'
              (S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩).isLt = e.origTail := by
            rw [← hsome]
          simpa [huD] using ht
      · simp [hv] at hvEq
    · simp [hsrc] at hsome
  · rintro ⟨uDense, vDense, harc, hown, hsrc, hhead, htail⟩
    have hvArc : dense[vDense.val]'vDense.isLt ∈ g.outArcs (dense[uDense.val]'uDense.isLt) := harc
    have hidxV : dense.idxOf (dense[vDense.val]'vDense.isLt) = vDense.val :=
      idxOf_getElem_of_nodup' S.nodup vDense.isLt
    have hltV : dense.idxOf (dense[vDense.val]'vDense.isLt) < dense.length := by
      rw [hidxV]; exact vDense.isLt
    have hfinV : (⟨dense.idxOf (dense[vDense.val]'vDense.isLt), hltV⟩ : Fin dense.length) = vDense :=
      Fin.ext hidxV
    let ea := S.emittedArc uDense vDense
    have hea : ea ∈ S.emittedArcs d := by
      unfold StaticTreeSlice.emittedArcs StaticTreeSlice.allEmittedArcs
      apply List.mem_filter.mpr
      refine ⟨List.mem_flatMap.mpr ⟨uDense, List.mem_finRange uDense, ?_⟩, ?_⟩
      · unfold StaticTreeSlice.emitForU
        refine List.mem_filterMap.mpr ⟨dense[vDense.val]'vDense.isLt, hvArc, ?_⟩
        simp only [hltV, ↓reduceDIte, hfinV]
        rfl
      · exact beq_iff_eq.mpr hown
    refine ⟨ea, hea, ?_⟩
    have hsrcB : (ea.srcLocal == uLocal.val) = true := beq_iff_eq.mpr (by
      change S.srcLocalOf (S.domParent vDense) uDense = uLocal.val
      rw [hown]; exact hsrc)
    have hBnd := S.emittedArc_bounds d hea
    have huD : S.denseOfEntry ⟨ea.tailEntry, hBnd.2.2.2⟩ = uDense := by
      have hEntEq : ea.tailEntry = S.entry uDense := rfl
      apply Fin.ext
      have hsub : (⟨ea.tailEntry, hBnd.2.2.2⟩ : Fin dense.length) =
          ⟨S.entry uDense, Nat.lt_of_lt_of_le (S.entry_lt_stop uDense).1 (S.entry_lt_stop uDense).2⟩ :=
        Fin.ext hEntEq
      rw [hsub, S.denseOfEntry_entry uDense]
    simp only [hsrcB, hBnd.2.2.1, hBnd.2.2.2, ↓reduceIte, ↓reduceDIte, Option.some.injEq]
    cases e with
    | mk eh et =>
      congr 1
      · apply Fin.ext
        change S.selfSlotFn vDense = eh.val
        exact hhead
      · simp only [huD]
        exact htail

private theorem initiallyReachable_rank_le {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat} (progress : ∀ x y, g.HasArc x y → rank x < rank y) :
    ∀ x, g.InitiallyReachable r x → rank r ≤ rank x := by
  intro x hx
  induction hx with
  | refl => exact Nat.le_refl _
  | @step w _ _ _ harc' _ ih => exact Nat.le_trans (Nat.le_of_lt (progress _ _ harc')) ih

private theorem list_getElem_of_eq {α : Type _} {l₁ l₂ : List α} (h : l₁ = l₂)
    {j : Nat} (h₁ : j < l₁.length) (h₂ : j < l₂.length) : l₁[j]'h₁ = l₂[j]'h₂ := by
  subst h; rfl

private theorem reader_childPosOK {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) {buckets : ChildLists q.count}
    (childOK : ∀ d c : Fin q.count, c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count) :
    c ∈ buckets.get d ↔ q.input.parent.read c = d ∧ c ≠ d := by
  constructor
  · intro hc
    obtain ⟨hnonroot, hparent⟩ := (childOK d c).mp hc
    refine ⟨hparent, ?_⟩
    intro hcd
    have hself : q.input.parent.read c = c := hparent.trans hcd.symm
    have hdepth := q.reader.input_ok.depth_step c hnonroot
    rw [hself] at hdepth
    omega
  · rintro ⟨hparent, hne⟩
    refine (childOK d c).mpr ⟨?_, hparent⟩
    intro hc
    apply hne
    subst c
    exact q.reader.input_ok.parent_root.symm.trans hparent

theorem StaticTreeSlice.MatchesReader.mem_outArcs_denseQuotient_iff
    {S : StaticTreeSlice mem treeBase g r dense}
    {q : OriginalReader g r} (hMatch : S.MatchesReader q)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injRank : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count, c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hBuckets : ∀ d : Fin dense.length,
      buckets.get (Fin.cast hMatch.count_eq.symm d) =
        (S.childSlice d).map (Fin.cast hMatch.count_eq.symm))
    (d : Fin dense.length) :
    let d' := Fin.cast hMatch.count_eq.symm d
    have hLen : rows.length d' = (S.ramQuotient d).vertexCount := by
      rw [rows.length_exact, hBuckets d, List.length_map]
      change (S.childSlice d).length + 1 = 1 + (S.childSlice d).length
      omega
    ∀ (uLocal : Fin (S.ramQuotient d).vertexCount)
      (e : QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount),
      e ∈ (S.ramQuotient d).outArcs uLocal ↔
        (⟨Fin.cast hLen.symm e.head, e.origTail⟩ : QuotientArc g.vertexCount (rows.length d')) ∈
          (denseQuotient progress injRank q originalRows hRows rows childOK d').outArcs
            (Fin.cast hLen.symm uLocal) := by
  intro d' hLen uLocal e
  have acyc : g.IsAcyclic := ⟨rank, progress⟩
  let childPos := reader_childPosOK q childOK d'
  have hQorig : q.ids.originals.read d' = dense[d.val]'d.isLt := hMatch.originals_eq d
  have hdReach : g.InitiallyReachable r (q.ids.originals.read d') := by
    rw [hQorig]; exact S.reach_mem d.val d.isLt
  have hFindD : q.ids.find (q.ids.originals.read d') = some d' := q.ids.slot_of_original d'
  have hParentOrig : ∀ v : Fin dense.length,
      q.parent (dense[v.val]'v.isLt) = dense[(S.domParent v).val]'(S.domParent v).isLt := by
    intro v
    have hv' := hMatch.originals_eq v
    rw [← hv', q.parent_at_original]
    have hp := hMatch.parent_eq v
    have hpFin : q.input.parent.read (Fin.cast hMatch.count_eq.symm v) =
        Fin.cast hMatch.count_eq.symm (S.domParent v) := Fin.ext hp
    rw [hpFin]
    exact hMatch.originals_eq (S.domParent v)
  have hRowPos : 0 < rows.length d' := by rw [rows.length_exact]; omega
  have hPosOrigZero : ∀ (hChildPos : ∀ c : Fin q.count, c ∈ buckets.get d' ↔ q.input.parent.read c = d' ∧ c ≠ d')
      (i : Fin (rows.length d')), i.val = 0 →
      (positionToOriginal q d' hChildPos rows i).val = dense[d.val]'d.isLt := by
    intro hChildPos i hi
    have hiEq : i = ⟨0, hRowPos⟩ := Fin.ext hi
    rw [hiEq]
    unfold positionToOriginal
    have hk : rows.decode d' ⟨0, hRowPos⟩ = ⟨.inl d', rfl⟩ := by
      apply Subtype.ext
      exact rows.key_zero d'
    rw [hk]
    change q.ids.originals.read d' = dense[d.val]'d.isLt
    exact hQorig
  have hPosOrigSucc : ∀ (hChildPos : ∀ c : Fin q.count, c ∈ buckets.get d' ↔ q.input.parent.read c = d' ∧ c ≠ d')
      (i : Fin (rows.length d')) (j : Nat) (hj : j < (S.childSlice d).length),
      i.val = j + 1 →
      (positionToOriginal q d' hChildPos rows i).val =
        dense[((S.childSlice d)[j]'hj).val]'((S.childSlice d)[j]'hj).isLt := by
    intro hChildPos i j hj hi
    have hjB : j < (buckets.get d').length := by rw [hBuckets d, List.length_map]; exact hj
    have hjRow : j + 1 < rows.length d' := by rw [rows.length_exact]; omega
    have hiEq : i = ⟨j + 1, hjRow⟩ := Fin.ext hi
    rw [hiEq]
    unfold positionToOriginal
    have hk : (rows.decode d' ⟨j + 1, hjRow⟩).val = .inr (buckets.get d')[j] :=
      rows.key_succ d' j hjB
    have hDecEq : rows.decode d' ⟨j + 1, hjRow⟩ =
        ⟨.inr (buckets.get d')[j], by change (buckets.get d')[j] ∈ buckets.get d'; exact List.getElem_mem hjB⟩ :=
      Subtype.ext hk
    rw [hDecEq]
    change q.ids.originals.read (buckets.get d')[j] = _
    have hjMap : j < ((S.childSlice d).map (Fin.cast hMatch.count_eq.symm)).length := by
      rw [List.length_map]; exact hj
    have hGet : (buckets.get d')[j]'hjB =
        ((S.childSlice d).map (Fin.cast hMatch.count_eq.symm))[j]'hjMap :=
      list_getElem_of_eq (hBuckets d) hjB hjMap
    rw [hGet, List.getElem_map]
    exact hMatch.originals_eq ((S.childSlice d)[j]'hj)
  rw [S.mem_outArcs_ramQuotient_iff d uLocal e]
  unfold denseQuotient
  have hMemBuild := mem_outArcs_build_iff progress injRank q d' rows childOK originalRows hRows
    (q.ids.original_reachable d') (q.ids.slot_of_original d') hRowPos
    (Fin.cast hLen.symm uLocal) ⟨Fin.cast hLen.symm e.head, e.origTail⟩ q.parentSpec
  refine Iff.trans ?_ hMemBuild.symm
  constructor
  · rintro ⟨uDense, vDense, harc, hown, hsrc, hhead, htail⟩
    have huReach : g.InitiallyReachable r (dense[uDense.val]'uDense.isLt) :=
      S.reach_mem uDense.val uDense.isLt
    have hvPos : 0 < vDense.val := by
      by_cases hv0 : vDense.val = 0
      · exfalso
        have hvR : dense[vDense.val]'vDense.isLt = r := by
          have : vDense = ⟨0, S.qPos⟩ := Fin.ext hv0
          rw [this, S.head_eq]
        rw [hvR] at harc
        have hPath := initiallyReachable_rank_le (r := r) progress _ huReach
        have hArcLt := progress _ _ harc
        omega
      · exact Nat.pos_of_ne_zero hv0
    have hvNeD : dense[vDense.val]'vDense.isLt ≠ dense[d.val]'d.isLt := by
      have hvNe : vDense ≠ d := by rw [← hown]; exact (S.domParent_ne_self vDense hvPos).symm
      intro heq; exact hvNe (S.dense_injective heq)
    have hQparV : q.parent (dense[vDense.val]'vDense.isLt) = dense[d.val]'d.isLt := by
      rw [hParentOrig vDense, hown]
    have hExist : ∃ s, siblingEmission? (d := q.ids.originals.read d') progress injRank q.parentSpec
        (dense[uDense.val]'uDense.isLt, dense[vDense.val]'vDense.isLt) = some s :=
      (siblingEmission_exists_iff_headParent progress injRank q.parentSpec harc).mpr
        ⟨huReach, hQparV.trans hQorig.symm⟩
    obtain ⟨s, hs⟩ := hExist
    · refine ⟨(dense[uDense.val]'uDense.isLt, dense[vDense.val]'vDense.isLt),
        (mem_originalArcOccurrences_iff g _ _).mpr harc, s, hs, ?_, ?_, ?_⟩
      · obtain ⟨huSpec, hvSpec, _, hsEq⟩ := (siblingEmission?_eq_some_iff progress injRank q.parentSpec _ s).mp hs
        dsimp only at huSpec hvSpec hsEq
        have hsVal : s.source = siblingBlockOf progress injRank q.parentSpec ⟨dense[uDense.val]'uDense.isLt, huSpec⟩ := by
          rw [← hsEq]
        rw [hsVal]
        have hdomDU : g.Dominates r (dense[d.val]'d.isLt) (dense[uDense.val]'uDense.isLt) := by
          rw [← hQorig]
          exact huSpec.2
        rcases S.srcLocalOf_spec acyc d uDense hdomDU with ⟨hud, huZero⟩ | ⟨c, hcMem, hcDom, hcIdx⟩
        · have huZero' : uLocal.val = 0 := by rw [← hsrc, huZero]
          have hpos0 := hPosOrigZero childPos (Fin.cast hLen.symm uLocal) huZero'
          apply Subtype.ext
          have huOrigD : dense[uDense.val]'uDense.isLt = q.ids.originals.read d' := by
            rw [hud, hQorig]
          have hSub : (siblingBlockOf progress injRank q.parentSpec
              (⟨dense[uDense.val]'uDense.isLt, huSpec⟩ : Digraph.SiblingVertex g r (q.ids.originals.read d')) :
              SiblingBlockKey g r (q.ids.originals.read d') q.parent) =
              SiblingBlockKey.root g r (q.ids.originals.read d') q.parent :=
            (siblingBlockOf_eq_root_iff progress injRank q.parentSpec _).mpr huOrigD
          have hSubVal : (siblingBlockOf progress injRank q.parentSpec
              (⟨dense[uDense.val]'uDense.isLt, huSpec⟩ : Digraph.SiblingVertex g r (q.ids.originals.read d'))).val =
              q.ids.originals.read d' := congrArg Subtype.val hSub
          exact hSubVal.trans (hQorig.trans hpos0.symm)
        · have hIdxLt : (S.childSlice d).idxOf c < (S.childSlice d).length :=
            List.idxOf_lt_length_of_mem hcMem
          have huSucc : (Fin.cast hLen.symm uLocal).val = (S.childSlice d).idxOf c + 1 := by
            change uLocal.val = _; rw [← hsrc, hcIdx]
          have hposC := hPosOrigSucc childPos (Fin.cast hLen.symm uLocal) ((S.childSlice d).idxOf c) hIdxLt huSucc
          rw [List.getElem_idxOf hIdxLt] at hposC
          have hCneD : (positionToOriginal q d' childPos rows (Fin.cast hLen.symm uLocal)).val ≠
              q.ids.originals.read d' := by
            rw [hposC, hQorig]
            have hcProp := (S.mem_childSlice_iff d c).mp hcMem
            have hcNe : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c (Nat.pos_of_ne_zero hcProp.1)).symm
            intro heq; exact hcNe (S.dense_injective heq)
          have hSub : siblingBlockOf progress injRank q.parentSpec ⟨dense[uDense.val]'uDense.isLt, huSpec⟩ =
              positionToOriginal q d' childPos rows (Fin.cast hLen.symm uLocal) := by
            apply (siblingBlockOf_eq_child_iff progress injRank q.parentSpec _ _ hCneD).mpr
            rw [hposC]; exact hcDom
          exact hSub
      · obtain ⟨_, hvSpec, _, hsEq⟩ := (siblingEmission?_eq_some_iff progress injRank q.parentSpec _ s).mp hs
        dsimp only at hvSpec hsEq
        have hsVal : s.destination = siblingBlockOf progress injRank q.parentSpec ⟨dense[vDense.val]'vDense.isLt, hvSpec⟩ := by
          rw [← hsEq]
        rw [hsVal]
        have hvMem : vDense ∈ S.childSlice d := (S.mem_childSlice_iff d vDense).mpr ⟨Nat.ne_of_gt hvPos, hown⟩
        have hIdxLt : (S.childSlice d).idxOf vDense < (S.childSlice d).length :=
          List.idxOf_lt_length_of_mem hvMem
        have hSelfEq : S.selfSlotFn vDense = (S.childSlice d).idxOf vDense + 1 := by
          unfold StaticTreeSlice.selfSlotFn
          rw [dite_eq_right (Nat.ne_of_gt hvPos)]
          dsimp only
          rw [hown]
        have heHead : (Fin.cast hLen.symm e.head).val = (S.childSlice d).idxOf vDense + 1 := by
          change e.head.val = _; rw [← hhead, hSelfEq]
        have hposV := hPosOrigSucc childPos (Fin.cast hLen.symm e.head) ((S.childSlice d).idxOf vDense) hIdxLt heHead
        rw [List.getElem_idxOf hIdxLt] at hposV
        have hVneD : (positionToOriginal q d' childPos rows (Fin.cast hLen.symm e.head)).val ≠
            q.ids.originals.read d' := by
          rw [hposV, hQorig]; exact hvNeD
        apply (siblingBlockOf_eq_child_iff progress injRank q.parentSpec _ _ hVneD).mpr
        rw [hposV]; exact dominates_refl
      · change s.tail = e.origTail
        have hTail := siblingEmission_physicalTail progress injRank q.parentSpec harc hs
        change s.tail = dense[uDense.val]'uDense.isLt at hTail
        exact hTail.trans htail
  · rintro ⟨⟨a₁, a₂⟩, haMem, s, hs, hSrc, hDst, hTail⟩
    have harc : g.HasArc a₁ a₂ := (mem_originalArcOccurrences_iff g a₁ a₂).mp haMem
    obtain ⟨huReach, hQpar⟩ := (siblingEmission_exists_iff_headParent progress injRank q.parentSpec harc).mp ⟨s, hs⟩
    dsimp only at huReach hQpar
    have hQpar' : q.parent a₂ = q.ids.originals.read d' := hQpar
    have hvReach : g.InitiallyReachable r a₂ := initiallyReachable_extend huReach harc
    have ha₁Dense : a₁ ∈ dense := S.mem_reach a₁ huReach
    have ha₂Dense : a₂ ∈ dense := S.mem_reach a₂ hvReach
    let uDense : Fin dense.length := ⟨dense.idxOf a₁, List.idxOf_lt_length_of_mem ha₁Dense⟩
    let vDense : Fin dense.length := ⟨dense.idxOf a₂, List.idxOf_lt_length_of_mem ha₂Dense⟩
    have huOrig : dense[uDense.val]'uDense.isLt = a₁ :=
      List.getElem_idxOf (List.idxOf_lt_length_of_mem ha₁Dense)
    have hvOrig : dense[vDense.val]'vDense.isLt = a₂ :=
      List.getElem_idxOf (List.idxOf_lt_length_of_mem ha₂Dense)
    have harcDense : g.HasArc (dense[uDense.val]'uDense.isLt) (dense[vDense.val]'vDense.isLt) := by
      rw [huOrig, hvOrig]; exact harc
    have hown : S.domParent vDense = d := by
      apply S.dense_injective
      rw [← hParentOrig vDense, hvOrig]
      exact hQpar'.trans hQorig
    have hTailEq : dense[uDense.val]'uDense.isLt = e.origTail := by
      have ht := siblingEmission_physicalTail progress injRank q.parentSpec harc hs
      change s.tail = a₁ at ht
      rw [huOrig, ← ht]; exact hTail
    obtain ⟨huSpec, hvSpec, _, hsEq⟩ := (siblingEmission?_eq_some_iff progress injRank q.parentSpec _ s).mp hs
    dsimp only at huSpec hvSpec hsEq
    have hsrcSpec : siblingBlockOf progress injRank q.parentSpec ⟨a₁, huSpec⟩ =
        positionToOriginal q d' childPos rows (Fin.cast hLen.symm uLocal) := by
      rw [← hSrc, ← hsEq]
    have hdstSpec : siblingBlockOf progress injRank q.parentSpec ⟨a₂, hvSpec⟩ =
        positionToOriginal q d' childPos rows (Fin.cast hLen.symm e.head) := by
      rw [← hDst, ← hsEq]
    have hdomDU : g.Dominates r (dense[d.val]'d.isLt) (dense[uDense.val]'uDense.isLt) := by
      rw [huOrig, ← hQorig]; exact huSpec.2
    have hSrcEq : S.srcLocalOf d uDense = uLocal.val := by
      by_cases hu0 : uLocal.val = 0
      · have hpos0 := hPosOrigZero childPos (Fin.cast hLen.symm uLocal) hu0
        have hSub : siblingBlockOf progress injRank q.parentSpec ⟨a₁, huSpec⟩ =
            SiblingBlockKey.root g r (q.ids.originals.read d') q.parent := by
          apply Subtype.ext
          rw [hsrcSpec, hpos0, hQorig]
          rfl
        have ha₁D := (siblingBlockOf_eq_root_iff progress injRank q.parentSpec ⟨a₁, huSpec⟩).mp hSub
        dsimp only at ha₁D
        have hud : uDense = d := by apply S.dense_injective; rw [huOrig, ha₁D, hQorig]
        rw [hud, hu0]
        unfold StaticTreeSlice.srcLocalOf; simp
      · obtain ⟨j, hjEq⟩ : ∃ j, uLocal.val = j + 1 := Nat.exists_eq_succ_of_ne_zero hu0
        have hjLt : j < (S.childSlice d).length := by
          have : uLocal.val < 1 + (S.childSlice d).length := uLocal.isLt
          omega
        have hposC := hPosOrigSucc childPos (Fin.cast hLen.symm uLocal) j hjLt hjEq
        let c := (S.childSlice d)[j]'hjLt
        have hcMem : c ∈ S.childSlice d := List.getElem_mem hjLt
        have hCneD : (positionToOriginal q d' childPos rows (Fin.cast hLen.symm uLocal)).val ≠
            q.ids.originals.read d' := by
          rw [hposC, hQorig]
          have hcProp := (S.mem_childSlice_iff d c).mp hcMem
          have hcNe : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c (Nat.pos_of_ne_zero hcProp.1)).symm
          intro heq; exact hcNe (S.dense_injective heq)
        have hcDom : g.Dominates r (dense[c.val]'c.isLt) (dense[uDense.val]'uDense.isLt) := by
          have hCD := (siblingBlockOf_eq_child_iff progress injRank q.parentSpec ⟨a₁, huSpec⟩ _ hCneD).mp hsrcSpec
          dsimp only at hCD
          rwa [hposC, ← huOrig] at hCD
        rcases S.srcLocalOf_spec acyc d uDense hdomDU with ⟨hud, _⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
        · exfalso
          have hcProp := (S.mem_childSlice_iff d c).mp hcMem
          have hcPos : 0 < c.val := Nat.pos_of_ne_zero hcProp.1
          have hcDomD : g.Dominates r (dense[c.val]'c.isLt) (dense[d.val]'d.isLt) := by
            simpa only [hud] using hcDom
          have himm := S.domParent_spec c hcPos
          rw [hcProp.2] at himm
          have hcd_ne : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := by
            have : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c hcPos).symm
            intro e'; exact this (S.dense_injective e')
          have hr1 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hcDomD hcd_ne
          have hr2 := rank_lt_of_strict_dominator progress (S.reach_mem c.val c.isLt) himm.2.1 hcd_ne.symm
          exact Nat.lt_irrefl _ (Nat.lt_trans hr1 hr2)
        · have hcEq : c = c' := by
            have hcProp := (S.mem_childSlice_iff d c).mp hcMem
            have hc'Prop := (S.mem_childSlice_iff d c').mp hc'Mem
            have hQ1 : q.parent (dense[c.val]'c.isLt) = dense[d.val]'d.isLt := by rw [hParentOrig c, hcProp.2]
            have hQ2 : q.parent (dense[c'.val]'c'.isLt) = dense[d.val]'d.isLt := by rw [hParentOrig c', hc'Prop.2]
            have hcNe : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := by
              have : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c (Nat.pos_of_ne_zero hcProp.1)).symm
              intro e'; exact this (S.dense_injective e')
            have hc'Ne : dense[c'.val]'c'.isLt ≠ dense[d.val]'d.isLt := by
              have : c' ≠ d := by rw [← hc'Prop.2]; exact (S.domParent_ne_self c' (Nat.pos_of_ne_zero hc'Prop.1)).symm
              intro e'; exact this (S.dense_injective e')
            obtain ⟨c0, _, hUniq⟩ := existsUnique_dominator_child progress injRank q.parentSpec
              huReach huSpec.2 (by
                intro hEq
                rw [← huOrig, hQorig] at hEq
                have hud' : uDense = d := S.dense_injective hEq
                have hcDomD : g.Dominates r (dense[c.val]'c.isLt) (dense[d.val]'d.isLt) := by
                  simpa only [hud'] using hcDom
                have himm := S.domParent_spec c (Nat.pos_of_ne_zero hcProp.1)
                rw [hcProp.2] at himm
                have hr1 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hcDomD hcNe
                have hr2 := rank_lt_of_strict_dominator progress (S.reach_mem c.val c.isLt) himm.2.1 hcNe.symm
                exact Nat.lt_irrefl _ (Nat.lt_trans hr1 hr2))
            have h1 := hUniq (dense[c.val]'c.isLt) ⟨hQ1.trans hQorig.symm, fun e => hcNe (e.trans hQorig), S.reach_mem c.val c.isLt, by rw [← huOrig]; exact hcDom⟩
            have h2 := hUniq (dense[c'.val]'c'.isLt) ⟨hQ2.trans hQorig.symm, fun e => hc'Ne (e.trans hQorig), S.reach_mem c'.val c'.isLt, by rw [← huOrig]; exact hc'Dom⟩
            exact S.dense_injective (h1.trans h2.symm)
          subst hcEq
          rw [hc'Idx, hjEq]
          exact congrArg Nat.succ (idxOf_getElem_of_nodup' (S.childSlice_nodup d) hjLt)
    have hHeadEq : S.selfSlotFn vDense = e.head.val := by
      have hvPos : 0 < vDense.val := by
        by_cases hv0 : vDense.val = 0
        · exfalso
          have hvR : a₂ = r := by
            rw [← hvOrig]; have : vDense = ⟨0, S.qPos⟩ := Fin.ext hv0; rw [this, S.head_eq]
          rw [hvR] at harc
          have hPath := initiallyReachable_rank_le (r := r) progress _ huReach
          have hArcLt := progress _ _ harc
          omega
        · exact Nat.pos_of_ne_zero hv0
      have hvMem : vDense ∈ S.childSlice d := (S.mem_childSlice_iff d vDense).mpr ⟨Nat.ne_of_gt hvPos, hown⟩
      have hSelfEq : S.selfSlotFn vDense = (S.childSlice d).idxOf vDense + 1 := by
        unfold StaticTreeSlice.selfSlotFn
        rw [dite_eq_right (Nat.ne_of_gt hvPos)]
        dsimp only; rw [hown]
      by_cases he0 : e.head.val = 0
      · exfalso
        have hpos0 := hPosOrigZero childPos (Fin.cast hLen.symm e.head) he0
        have hSub : siblingBlockOf progress injRank q.parentSpec ⟨a₂, hvSpec⟩ =
            SiblingBlockKey.root g r (q.ids.originals.read d') q.parent := by
          apply Subtype.ext; rw [hdstSpec, hpos0, hQorig]; rfl
        have ha₂D := (siblingBlockOf_eq_root_iff progress injRank q.parentSpec ⟨a₂, hvSpec⟩).mp hSub
        dsimp only at ha₂D
        have hvd : vDense = d := by apply S.dense_injective; rw [hvOrig, ha₂D, hQorig]
        exact (S.domParent_ne_self vDense hvPos) (hown.trans hvd.symm)
      · obtain ⟨j, hjEq⟩ : ∃ j, e.head.val = j + 1 := Nat.exists_eq_succ_of_ne_zero he0
        have hjLt : j < (S.childSlice d).length := by
          have : e.head.val < 1 + (S.childSlice d).length := e.head.isLt
          omega
        have hposC := hPosOrigSucc childPos (Fin.cast hLen.symm e.head) j hjLt hjEq
        let c := (S.childSlice d)[j]'hjLt
        have hcMem : c ∈ S.childSlice d := List.getElem_mem hjLt
        have hCneD : (positionToOriginal q d' childPos rows (Fin.cast hLen.symm e.head)).val ≠
            q.ids.originals.read d' := by
          rw [hposC, hQorig]
          have hcProp := (S.mem_childSlice_iff d c).mp hcMem
          have hcNe : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c (Nat.pos_of_ne_zero hcProp.1)).symm
          intro heq; exact hcNe (S.dense_injective heq)
        have hcDomV : g.Dominates r (dense[c.val]'c.isLt) a₂ := by
          have hCV := (siblingBlockOf_eq_child_iff progress injRank q.parentSpec ⟨a₂, hvSpec⟩ _ hCneD).mp hdstSpec
          dsimp only at hCV
          rwa [hposC] at hCV
        have hcEqV : c = vDense := by
          have himm := S.domParent_spec vDense hvPos
          rw [hown] at himm
          have hcProp := (S.mem_childSlice_iff d c).mp hcMem
          have hcNe : c ≠ d := by rw [← hcProp.2]; exact (S.domParent_ne_self c (Nat.pos_of_ne_zero hcProp.1)).symm
          by_cases hcv : c = vDense
          · exact hcv
          · exfalso
            have hcv_orig : dense[c.val]'c.isLt ≠ a₂ := by
              rw [← hvOrig]; intro e'; exact hcv (S.dense_injective e')
            have hcDomD : g.Dominates r (dense[c.val]'c.isLt) (dense[d.val]'d.isLt) := by
              rw [← hvOrig] at hcDomV
              exact himm.2.2 (dense[c.val]'c.isLt) (by rw [hvOrig]; exact hcv_orig) hcDomV
            have himmC := S.domParent_spec c (Nat.pos_of_ne_zero hcProp.1)
            rw [hcProp.2] at himmC
            have hcd_orig : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt :=
              fun e' => hcNe (S.dense_injective e')
            have hr1 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hcDomD hcd_orig
            have hr2 := rank_lt_of_strict_dominator progress (S.reach_mem c.val c.isLt) himmC.2.1 hcd_orig.symm
            exact Nat.lt_irrefl _ (Nat.lt_trans hr1 hr2)
        rw [hSelfEq, ← hcEqV, hjEq]
        exact congrArg Nat.succ (idxOf_getElem_of_nodup' (S.childSlice_nodup d) hjLt)
    exact ⟨uDense, vDense, harcDense, hown, hSrcEq, hHeadEq, hTailEq⟩

theorem StaticTreeSlice.MatchesReader.ramQuotient_isFlat
    {S : StaticTreeSlice mem treeBase g r dense}
    {q : OriginalReader g r} (hMatch : S.MatchesReader q)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injRank : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count, c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hBuckets : ∀ d : Fin dense.length,
      buckets.get (Fin.cast hMatch.count_eq.symm d) =
        (S.childSlice d).map (Fin.cast hMatch.count_eq.symm))
    (d : Fin dense.length) :
    (S.ramQuotient d).IsFlat := by
  let d' := Fin.cast hMatch.count_eq.symm d
  have hQorig : q.ids.originals.read d' = dense[d.val]'d.isLt := hMatch.originals_eq d
  have hdReach : g.InitiallyReachable r (q.ids.originals.read d') := by
    rw [hQorig]; exact S.reach_mem d.val d.isLt
  have hFindD : q.ids.find (q.ids.originals.read d') = some d' := q.ids.slot_of_original d'
  have hRowPos : 0 < rows.length d' := by rw [rows.length_exact]; omega
  have hLen : rows.length d' = (S.ramQuotient d).vertexCount := by
    rw [rows.length_exact, hBuckets d, List.length_map]
    change (S.childSlice d).length + 1 = 1 + (S.childSlice d).length
    omega
  have hFlat := DenseOriginalQuotient.Transport.build_isFlat progress injRank q originalRows hRows
    d' hdReach hFindD rows childOK hRowPos q.parentSpec
  have hMemIff := hMatch.mem_outArcs_denseQuotient_iff progress injRank originalRows hRows
    rows childOK hBuckets d
  let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d'
  have hDqV : Dq.vertexCount = rows.length d' := rfl
  have hLenDq : Dq.vertexCount = (S.ramQuotient d).vertexCount := hDqV.trans hLen
  have hRootVal : Dq.root.val = 0 := rfl
  have hRootEq : Dq.root = Fin.cast hLenDq.symm (S.ramQuotient d).root := by
    apply Fin.ext; exact hRootVal
  have hCastInv : ∀ x : Fin Dq.vertexCount, Fin.cast hLenDq.symm (Fin.cast hLenDq x) = x :=
    fun x => Fin.ext rfl
  have hCastInv2 : ∀ a : Fin (S.ramQuotient d).vertexCount, Fin.cast hLenDq (Fin.cast hLenDq.symm a) = a :=
    fun a => Fin.ext rfl
  have hSurvLift : ∀ (F : Fin Dq.vertexCount → Prop) (a b : Fin (S.ramQuotient d).vertexCount),
      Dq.SurvivingPath F (Fin.cast hLenDq.symm a) (Fin.cast hLenDq.symm b) →
      (S.ramQuotient d).SurvivingPath (fun z => F (Fin.cast hLenDq.symm z)) a b := by
    intro F a b hp
    suffices ∀ x y : Fin Dq.vertexCount, Dq.SurvivingPath F x y →
        (S.ramQuotient d).SurvivingPath (fun z => F (Fin.cast hLenDq.symm z))
          (Fin.cast hLenDq x) (Fin.cast hLenDq y) by
      simpa only [hCastInv2] using this (Fin.cast hLenDq.symm a) (Fin.cast hLenDq.symm b) hp
    intro x y p
    induction p with
    | refl x hal => exact AvoidPath.refl (Fin.cast hLenDq x) (by simpa only [hCastInv] using hal)
    | step x w y hal harc _ ih =>
      obtain ⟨e', he', hwEq⟩ := harc
      let e : QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount :=
        ⟨Fin.cast hLenDq e'.head, e'.origTail⟩
      have heMem : e ∈ (S.ramQuotient d).outArcs (Fin.cast hLenDq x) := by
        rw [hMemIff (Fin.cast hLenDq x) e]
        have he'Cast : (⟨Fin.cast hLen.symm e.head, e.origTail⟩ : QuotientArc g.vertexCount (rows.length d')) ∈
            Dq.outArcs (Fin.cast hLen.symm (Fin.cast hLenDq x)) := by
          have hDqCast : ∀ {u1 u2 : Fin Dq.vertexCount} {a1 a2 : QuotientArc Dq.origVertexCount Dq.vertexCount},
              u1 = u2 → a1 = a2 → a1 ∈ Dq.outArcs u1 → a2 ∈ Dq.outArcs u2 := by
            intro u1 u2 a1 a2 hu ha hm; subst hu ha; exact hm
          have hU : x = Fin.cast hDqV (Fin.cast hLen.symm (Fin.cast hLenDq x)) := Fin.ext rfl
          have hA : e' = ⟨Fin.cast hDqV (Fin.cast hLen.symm e.head), e'.origTail⟩ := by
            cases e'; congr 1
          exact hDqCast hU hA he'
        exact he'Cast
      have harcS : (S.ramQuotient d).HasQuotientArc (Fin.cast hLenDq x) (Fin.cast hLenDq w) :=
        ⟨e, heMem, by simp [e, hwEq]⟩
      exact AvoidPath.step _ _ _ (by simpa only [hCastInv] using hal) harcS ih
  constructor
  · intro v
    have hp := hFlat.1 (Fin.cast hLenDq.symm v)
    rw [hRootEq] at hp
    exact hSurvLift (fun _ => False) (S.ramQuotient d).root v hp
  · intro u v hu hvu
    have hu' : Fin.cast hLenDq.symm u ≠ Dq.root := by
      rw [hRootEq]
      intro hEq
      exact hu (by simpa using congrArg (Fin.cast hLenDq) hEq)
    have hvu' : Fin.cast hLenDq.symm v ≠ Fin.cast hLenDq.symm u := by
      intro hEq
      exact hvu (by simpa using congrArg (Fin.cast hLenDq) hEq)
    have hp := hFlat.2 (Fin.cast hLenDq.symm u) (Fin.cast hLenDq.symm v) hu' hvu'
    rw [hRootEq] at hp
    have hEqF : (fun z : Fin (S.ramQuotient d).vertexCount => Fin.cast hLenDq.symm z = Fin.cast hLenDq.symm u) =
        (fun z => z = u) := by
      funext z
      exact propext ⟨fun h => by simpa [Fin.ext_iff] using h, fun h => h ▸ rfl⟩
    have hlifted := hSurvLift (fun z => z = Fin.cast hLenDq.symm u) (S.ramQuotient d).root v hp
    simpa only [hEqF] using hlifted

theorem StaticTreeSlice.ramQuotient_isAcyclic (S : StaticTreeSlice mem treeBase g r dense)
    (acyc : g.IsAcyclic) (d : Fin dense.length) :
    (S.ramQuotient d).IsAcyclic := by
  have ⟨rank, progress⟩ := acyc
  let qRank : Fin (S.ramQuotient d).vertexCount → Nat := fun uLocal =>
    if hu : uLocal.val = 0 then rank (dense[d.val]'d.isLt)
    else
      let j := uLocal.val - 1
      if hj : j < (S.childSlice d).length then
        let c := (S.childSlice d)[j]'hj
        rank (dense[c.val]'c.isLt)
      else 0
  refine ⟨qRank, ?_⟩
  intro uLocal vLocal harc
  obtain ⟨e, he, hvEq⟩ := harc
  rw [S.mem_outArcs_ramQuotient_iff d uLocal e] at he
  obtain ⟨uDense, vDense, harcOrig, hown, hsrc, hhead, _⟩ := he
  have hReachPath := initiallyReachable_rank_le (r := r) progress
  have hvPos : 0 < vDense.val := by
    by_cases hv0 : vDense.val = 0
    · exfalso
      have hvR : dense[vDense.val]'vDense.isLt = r := by
        have : vDense = ⟨0, S.qPos⟩ := Fin.ext hv0
        rw [this, S.head_eq]
      rw [hvR] at harcOrig
      have hPath := hReachPath (dense[uDense.val]'uDense.isLt) (S.reach_mem uDense.val uDense.isLt)
      have hArcLt := progress _ _ harcOrig
      omega
    · exact Nat.pos_of_ne_zero hv0
  have hvMem : vDense ∈ S.childSlice d := (S.mem_childSlice_iff d vDense).mpr ⟨Nat.ne_of_gt hvPos, hown⟩
  have hSelfEq : S.selfSlotFn vDense = (S.childSlice d).idxOf vDense + 1 := by
    unfold StaticTreeSlice.selfSlotFn
    rw [dite_eq_right (Nat.ne_of_gt hvPos)]
    dsimp only; rw [hown]
  have hVVal : vLocal.val = (S.childSlice d).idxOf vDense + 1 := by
    rw [← hvEq, ← hhead, hSelfEq]
  have hVIdxLt : (S.childSlice d).idxOf vDense < (S.childSlice d).length :=
    List.idxOf_lt_length_of_mem hvMem
  have hQRankV : qRank vLocal = rank (dense[vDense.val]'vDense.isLt) := by
    dsimp only [qRank]
    have hVNe0 : vLocal.val ≠ 0 := by omega
    have hVLt : vLocal.val - 1 < (S.childSlice d).length := by omega
    have hElemV : (S.childSlice d)[vLocal.val - 1]'hVLt = vDense := by
      have hSub : vLocal.val - 1 = (S.childSlice d).idxOf vDense := by omega
      simp only [hSub]
      exact List.getElem_idxOf hVIdxLt
    simp only [hVNe0, ↓reduceDIte, hVLt, hElemV]
  have huReach : g.InitiallyReachable r (dense[uDense.val]'uDense.isLt) := S.reach_mem uDense.val uDense.isLt
  have himmV := S.domParent_spec vDense hvPos
  rw [hown] at himmV
  have hdomDU : g.Dominates r (dense[d.val]'d.isLt) (dense[uDense.val]'uDense.isLt) :=
    dominates_reachable_predecessor_of_ne harcOrig huReach
      (fun e' => (S.domParent_ne_self vDense hvPos).symm (hown ▸ S.dense_injective e'))
      himmV.2.1
  have hQRankU : qRank uLocal ≤ rank (dense[uDense.val]'uDense.isLt) := by
    rcases S.srcLocalOf_spec acyc d uDense hdomDU with ⟨hud, hu0⟩ | ⟨c, hcMem, hcDom, hcIdx⟩
    · have huVal0 : uLocal.val = 0 := by rw [← hsrc, hu0]
      dsimp only [qRank]
      simp only [huVal0, ↓reduceDIte, hud, Nat.le_refl]
    · have hcIdxLt : (S.childSlice d).idxOf c < (S.childSlice d).length :=
        List.idxOf_lt_length_of_mem hcMem
      have huVal : uLocal.val = (S.childSlice d).idxOf c + 1 := by rw [← hsrc, hcIdx]
      have huNe0 : uLocal.val ≠ 0 := by omega
      have hULt : uLocal.val - 1 < (S.childSlice d).length := by omega
      have hElemU : (S.childSlice d)[uLocal.val - 1]'hULt = c := by
        have hSub : uLocal.val - 1 = (S.childSlice d).idxOf c := by omega
        simp only [hSub]
        exact List.getElem_idxOf hcIdxLt
      dsimp only [qRank]
      simp only [huNe0, ↓reduceDIte, hULt, hElemU]
      by_cases hcu : c = uDense
      · subst hcu; exact Nat.le_refl _
      · have hcuOrig : dense[c.val]'c.isLt ≠ dense[uDense.val]'uDense.isLt :=
          fun e' => hcu (S.dense_injective e')
        exact Nat.le_of_lt (rank_lt_of_strict_dominator progress huReach hcDom hcuOrig)
  have hArcLt := progress _ _ harcOrig
  omega

end QuotientModel

/-! ### 3. 16-Register RAM Quotient Emitter Phases -/

section RamEmitter

open PaperB.Machine PaperB.WordOps PaperB.RamProgram PaperB.RamProgram.FixedROM PaperB.RamDagReach

/-- Fixed register invariants preserved across all phases of `quotientEmitProgram`:
`r0..r4` hold `ConstRegs n m r.val`, `r5 = Q`, `r6 = treeBase`, `r7 = emitBase`. -/
structure EmitterRegs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (n m root Q treeBase emitBase : Nat)
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  consts : ConstRegs n m root s
  qVal : (reg s r5).val = Q
  treeBaseVal : (reg s r6).val = treeBase
  emitBaseVal : (reg s r7).val = emitBase

private theorem data_mem_val_of_eq {bits : Nat} {a b : Array (Word bits)} {k v : Nat}
    (heq : a[k]? = b[k]?) (hb : (b[k]?).map Fin.val = some v) :
    (a[k]?).map Fin.val = some v := by
  rw [heq]; exact hb

private theorem data_val_at {bits : Nat} {a : Array (Word bits)} {k v : Nat}
    (h : (a[k]?).map Fin.val = some v) :
    ∃ w : Word bits, a[k]? = some w ∧ w.val = v := by
  cases hk : a[k]? with
  | none => simp [hk] at h
  | some w =>
    simp only [hk, Option.map_some, Option.some.injEq] at h
    exact ⟨w, rfl, h⟩

private theorem array_set_getElem?_same {α : Type _} (a : Array α) (i : Nat) (hi : i < a.size) (v : α) :
    (a.set i v hi)[i]? = some v := by
  rw [Array.getElem?_set_self]

private theorem array_set_getElem?_ne {α : Type _} (a : Array α) (i j : Nat) (hi : i < a.size)
    (v : α) (hne : j ≠ i) : (a.set i v hi)[j]? = a[j]? := by
  exact Array.getElem?_set_ne hi hne.symm

private theorem array_set_congr {α : Type _} {a b : Array α} {i j : Nat} {v w : α}
    {hi : i < a.size} {hj : j < b.size} (ha : a = b) (hiEq : i = j) (hv : v = w) :
    a.set i v hi = b.set j w hj := by
  subst ha; subst hiEq; subst hv; rfl

private theorem filter_singleton_true {α : Type _} (p : α → Bool) (x : α) (hx : p x = true) :
    [x].filter p = [x] := by simp [hx]

private theorem filter_singleton_false {α : Type _} (p : α → Bool) (x : α) (hx : p x = false) :
    [x].filter p = [] := by simp [hx]

theorem step16_mov {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {dst src : Fin 16}
    (hAt : code[k]? = some (.mov dst src)) (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t dst = reg s src ∧ (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_mov16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_add {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {dst lhs rhs : Fin 16}
    (hAt : code[k]? = some (.add dst lhs rhs)) (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t dst = add (reg s lhs) (reg s rhs) ∧ (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_add16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_sub {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {dst lhs rhs : Fin 16}
    (hAt : code[k]? = some (.sub dst lhs rhs)) (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t dst = sub (reg s lhs) (reg s rhs) ∧ (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_sub16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_shr1 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {dst src : Fin 16}
    (hAt : code[k]? = some (.shr1 dst src)) (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      (reg t dst).val = (reg s src).val / 2 ∧ (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_shr1_at (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_loadData {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {d a : Fin 16} {w : Word bits}
    (hAt : code[k]? = some (.loadData d a)) (hMem : s.data[(reg s a).val]? = some w)
    (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t d = w ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_loadData16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) hMem (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_loadInput {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {d a : Fin 16} {w : Word bits}
    (hAt : code[k]? = some (.loadInput d a)) (hMem : input.words[(reg s a).val]? = some w)
    (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t d = w ∧ (∀ r : Fin 16, r ≠ d → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_loadInput16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit) hMem
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem step16_storeData {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {addr src : Fin 16}
    (hAt : code[k]? = some (.storeData addr src)) (hFit : k + 1 < code.size)
    (hBnd : (reg s addr).val < s.data.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      t.regs = s.regs ∧ t.data = s.data.set (reg s addr).val (reg s src) hBnd := by
  obtain ⟨t, ht, hpc', hr, hd⟩ :=
    step_storeData16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit) hBnd
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hr, hd⟩

theorem step16_goto {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k target : Nat}
    (hpc : s.pc = k) (hAt : code[k]? = some (.goto target)) (hTgt : target < code.size) :
    let t : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s.regs, data := s.data, pc := target, regs_size := s.regs_size, data_size := s.data_size }
    step code input s = some (.next t) :=
  step_goto_at (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) hTgt

theorem step16_branchLt_true {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k yesPC noPC : Nat}
    {x y : Fin 16}
    (hpc : s.pc = k) (hAt : code[k]? = some (.branchLt x y yesPC noPC))
    (hYes : yesPC < code.size) (hlt : (reg s x).val < (reg s y).val) :
    let t : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s.regs, data := s.data, pc := yesPC, regs_size := s.regs_size, data_size := s.data_size }
    step code input s = some (.next t) := by
  have hbr := branchLt_true hlt
  have hs := step_branchLt_at (code := code) (input := input) (s := s)
    (by rw [hpc]; exact hAt) (by rw [hbr]; exact hYes)
  rw [hbr] at hs
  exact hs

theorem step16_branchLt_false {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k yesPC noPC : Nat}
    {x y : Fin 16}
    (hpc : s.pc = k) (hAt : code[k]? = some (.branchLt x y yesPC noPC))
    (hNo : noPC < code.size) (hle : (reg s y).val ≤ (reg s x).val) :
    let t : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s.regs, data := s.data, pc := noPC, regs_size := s.regs_size, data_size := s.data_size }
    step code input s = some (.next t) := by
  have hbr := branchLt_false hle
  have hs := step_branchLt_at (code := code) (input := input) (s := s)
    (by rw [hpc]; exact hAt) (by rw [hbr]; exact hNo)
  rw [hbr] at hs
  exact hs

def initSelfSlotCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    .storeData r7 rZero,     -- 0: selfSlot[0] := 0
    .mov r8 rZero,           -- 1: d := 0
    .branchLt r8 r5 3 30,    -- 2: while d < Q
    .add r9 r5 r5,           -- 3: 2Q
    .add r10 r9 r9,          -- 4: 4Q
    .add r9 r9 r10,          -- 5: 6Q
    .add r9 r9 r5,           -- 6: 7Q
    .add r9 r9 r6,           -- 7: treeBase + 7Q
    .add r9 r9 r8,           -- 8: treeBase + 7Q + d
    .loadData r10 r9,        -- 9: lo = childStart[d]
    .add r9 r9 rOne,         -- 10: treeBase + 7Q + d + 1
    .loadData r11 r9,        -- 11: hi = childStart[d + 1]
    .mov r12 r10,            -- 12: pos := lo
    .branchLt r12 r11 14 28, -- 13: while pos < hi
    .add r13 r5 r5,          -- 14: 2Q
    .add r14 r13 r13,        -- 15: 4Q
    .add r14 r14 r14,        -- 16: 8Q
    .add r13 r14 r13,        -- 17: 10Q
    .add r13 r13 rOne,       -- 18: 10Q + 1
    .add r13 r13 r6,         -- 19: treeBase + 10Q + 1
    .add r13 r13 r12,        -- 20: treeBase + 10Q + 1 + pos
    .loadData r13 r13,       -- 21: c = childIds[pos]
    .sub r14 r12 r10,        -- 22: pos - lo
    .add r14 r14 rOne,       -- 23: pos - lo + 1
    .add r15 r7 r13,         -- 24: emitBase + c
    .storeData r15 r14,      -- 25: selfSlot[c] := pos - lo + 1
    .add r12 r12 rOne,       -- 26: pos++
    .goto 13,                -- 27
    .add r8 r8 rOne,         -- 28: d++
    .goto 2,                 -- 29
    .halt                    -- 30
  ]

def initSelfSlotPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast initSelfSlotCode 30 rfl rfl rfl

private theorem initSelfSlotCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (initSelfSlotCode (hi := hi) (hw := hw)).size = 31 := rfl

private structure InitSelfOuterInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (d : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 2
  dEq : (reg s r8).val = d
  dLe : d ≤ dense.length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase ∨ emitBase + dense.length ≤ k) → s.data[k]? = origData[k]?
  slotZero : (s.data[emitBase]?).map Fin.val = some 0
  slotsDone : ∀ d' : Fin dense.length, d'.val < d → ∀ c ∈ S.childSlice d',
    (s.data[emitBase + c.val]?).map Fin.val = some (S.selfSlotFn c)

private structure InitSelfInnerInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (d : Fin dense.length) (pos : Nat)
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 13
  dEq : (reg s r8).val = d.val
  loEq : (reg s r10).val = S.childStart d.val
  hiEq : (reg s r11).val = S.childStart (d.val + 1)
  posEq : (reg s r12).val = pos
  posGe : S.childStart d.val ≤ pos
  posLe : pos ≤ S.childStart (d.val + 1)
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase ∨ emitBase + dense.length ≤ k) → s.data[k]? = origData[k]?
  slotZero : (s.data[emitBase]?).map Fin.val = some 0
  slotsPrev : ∀ d' : Fin dense.length, d'.val < d.val → ∀ c ∈ S.childSlice d',
    (s.data[emitBase + c.val]?).map Fin.val = some (S.selfSlotFn c)
  slotsCur : ∀ j : Nat, S.childStart d.val ≤ j → j < pos →
    ∀ hj : j < dense.length - 1,
      (s.data[emitBase + (S.childIds ⟨j, hj⟩).val]?).map Fin.val =
        some (S.selfSlotFn (S.childIds ⟨j, hj⟩))

private theorem initSelfSlot_inner_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (hDenseLe : dense.length ≤ g.vertexCount)
    (d : Fin dense.length) (pos : Nat)
    (hposLt : pos < S.childStart (d.val + 1))
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : InitSelfInnerInv g r dense treeBase emitBase origData S d pos s) :
    ∃ s', Steps (initSelfSlotCode (hi := hi) (hw := hw)) input 15 s s' ∧
      InitSelfInnerInv g r dense treeBase emitBase origData S d (pos + 1) s' := by
  have hTreeFit := S.fit
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size
    rw [inv.dataSize] at h1
    change origData.size = workCap at h1
    omega
  have hQpow : dense.length < 2 ^ bits := by
    have hPos := S.qPos
    unfold staticTreeWords at hTreeFit
    omega
  have hPow : s.data.size ≤ 2 ^ bits := by rw [inv.dataSize]; exact hOrigSz
  have hEnd : S.childStart (d.val + 1) ≤ dense.length - 1 := by
    have hm := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
    rwa [S.childStart_end] at hm
  have hposLtD : pos < dense.length - 1 := by omega
  let c := S.childIds ⟨pos, hposLtD⟩
  have hcMem : c ∈ S.childSlice d :=
    (S.mem_childSlice_iff d c).mpr ((S.childIds_mem_iff d c).mp ⟨pos, inv.posGe, hposLt, hposLtD, rfl⟩)
  have hlt13 : (reg s r12).val < (reg s r11).val := by rw [inv.posEq, inv.hiEq]; exact hposLt
  let code := initSelfSlotCode (hi := hi) (hw := hw)
  have hstep13 := step16_branchLt_true code input inv.pcEq rfl (by rw [initSelfSlotCode_size]; decide) hlt13
  let s14 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 14, regs_size := s.regs_size, data_size := s.data_size }
  have hpc14 : s14.pc = 14 := rfl
  obtain ⟨s15, h14, hpc15, h15d, h15o, h15m⟩ := step16_add code input hpc14 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s16, h15, hpc16, h16d, h16o, h16m⟩ := step16_add code input hpc15 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s17, h16, hpc17, h17d, h17o, h17m⟩ := step16_add code input hpc16 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s18, h17, hpc18, h18d, h18o, h18m⟩ := step16_add code input hpc17 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s19, h18, hpc19, h19d, h19o, h19m⟩ := step16_add code input hpc18 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s20, h19, hpc20, h20d, h20o, h20m⟩ := step16_add code input hpc19 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s21, h20, hpc21, h21d, h21o, h21m⟩ := step16_add code input hpc20 rfl (by rw [initSelfSlotCode_size]; decide)
  have hQ : (reg s r5).val = dense.length := inv.regs.qVal
  have h1 : (reg s rOne).val = 1 := inv.regs.consts.one
  have h6 : (reg s r6).val = treeBase := inv.regs.treeBaseVal
  have hr15 : (reg s15 r13).val = 2 * dense.length := by
    rw [h15d, add_no_wrap _ _ (by change (reg s r5).val + (reg s r5).val < _; rw [hQ]; unfold staticTreeWords at hTreeFit; omega)]
    change (reg s r5).val + (reg s r5).val = _; rw [hQ]; omega
  have hr16 : (reg s16 r14).val = 4 * dense.length := by
    rw [h16d, add_no_wrap _ _ (by rw [hr15]; unfold staticTreeWords at hTreeFit; omega), hr15]; omega
  have hr17 : (reg s17 r14).val = 8 * dense.length := by
    rw [h17d, add_no_wrap _ _ (by rw [hr16]; unfold staticTreeWords at hTreeFit; omega), hr16]; omega
  have hr18 : (reg s18 r13).val = 10 * dense.length := by
    have h17_13 : (reg s17 r13).val = 2 * dense.length := by
      rw [h17o _ (by decide), h16o _ (by decide)]; exact hr15
    rw [h18d, add_no_wrap _ _ (by rw [hr17, h17_13]; unfold staticTreeWords at hTreeFit; omega), hr17, h17_13]; omega
  have hr19 : (reg s19 r13).val = 10 * dense.length + 1 := by
    have h18_1 : (reg s18 rOne).val = 1 := by
      rw [h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact h1
    rw [h19d, add_no_wrap _ _ (by rw [hr18, h18_1]; unfold staticTreeWords at hTreeFit; omega), hr18, h18_1]
  have hr20 : (reg s20 r13).val = treeBase + (10 * dense.length + 1) := by
    have h19_6 : (reg s19 r6).val = treeBase := by
      rw [h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact h6
    rw [h20d, add_no_wrap _ _ (by rw [hr19, h19_6]; unfold staticTreeWords at hTreeFit; omega), hr19, h19_6]; omega
  have hr21 : (reg s21 r13).val = treeBase + (10 * dense.length + 1) + pos := by
    have h20_12 : (reg s20 r12).val = pos := by
      rw [h20o _ (by decide), h19o _ (by decide), h18o _ (by decide), h17o _ (by decide),
        h16o _ (by decide), h15o _ (by decide)]
      exact inv.posEq
    rw [h21d, add_no_wrap _ _ (by rw [hr20, h20_12]; unfold staticTreeWords at hTreeFit; omega), hr20, h20_12]
  have hChildMem : (s21.data[(reg s21 r13).val]?).map Fin.val = some c.val := by
    rw [hr21, h21m, h20m, h19m, h18m, h17m, h16m, h15m]
    have hDisj : treeBase + (10 * dense.length + 1) + pos < emitBase ∨
        emitBase + dense.length ≤ treeBase + (10 * dense.length + 1) + pos := by
      unfold staticTreeWords emitterWorkWords at *
      rcases hDisjTreeEmit with hl | hr
      · left; omega
      · right; omega
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (S.childIds_mem ⟨pos, hposLtD⟩)
  obtain ⟨wc, hwc, hwcVal⟩ := data_val_at hChildMem
  obtain ⟨s22, h21, hpc22, h22d, h22o, h22m⟩ := step16_loadData code input hpc21 rfl hwc (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s23, h22, hpc23, h23d, h23o, h23m⟩ := step16_sub code input hpc22 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s24, h23, hpc24, h24d, h24o, h24m⟩ := step16_add code input hpc23 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s25, h24, hpc25, h25d, h25o, h25m⟩ := step16_add code input hpc24 rfl (by rw [initSelfSlotCode_size]; decide)
  have hr23 : (reg s23 r14).val = pos - S.childStart d.val := by
    have h22_12 : (reg s22 r12).val = pos := by
      rw [h22o _ (by decide), h21o _ (by decide), h20o _ (by decide), h19o _ (by decide),
        h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact inv.posEq
    have h22_10 : (reg s22 r10).val = S.childStart d.val := by
      rw [h22o _ (by decide), h21o _ (by decide), h20o _ (by decide), h19o _ (by decide),
        h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact inv.loEq
    rw [h23d, sub_exact _ _ (by rw [h22_12, h22_10]; exact inv.posGe), h22_12, h22_10]
  have hr24 : (reg s24 r14).val = (pos - S.childStart d.val) + 1 := by
    have h23_1 : (reg s23 rOne).val = 1 := by
      rw [h23o _ (by decide), h22o _ (by decide), h21o _ (by decide), h20o _ (by decide),
        h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact h1
    rw [h24d, add_no_wrap _ _ (by rw [hr23, h23_1]; omega), hr23, h23_1]
  have hr25 : (reg s25 r15).val = emitBase + c.val := by
    have h24_7 : (reg s24 r7).val = emitBase := by
      rw [h24o _ (by decide), h23o _ (by decide), h22o _ (by decide), h21o _ (by decide),
        h20o _ (by decide), h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
      exact inv.regs.emitBaseVal
    have h24_13 : (reg s24 r13).val = c.val := by
      rw [h24o _ (by decide), h23o _ (by decide), h22d, hwcVal]
    rw [h25d, add_no_wrap _ _ (by
      rw [h24_7, h24_13]
      unfold emitterWorkWords at hFitEmit
      have : c.val < dense.length := c.isLt
      omega), h24_7, h24_13]
  have hBound25 : (reg s25 r15).val < s25.data.size := by
    rw [hr25, h25m, h24m, h23m, h22m, h21m, h20m, h19m, h18m, h17m, h16m, h15m]
    change emitBase + c.val < s14.data.size
    have hSz : s14.data.size = origData.size := inv.dataSize
    rw [hSz]
    unfold emitterWorkWords at hFitEmit
    have := c.isLt
    omega
  obtain ⟨s26, h25, hpc26, h26regs, h26data⟩ := step16_storeData code input hpc25 rfl (by rw [initSelfSlotCode_size]; decide) hBound25
  obtain ⟨s27, h26, hpc27, h27d, h27o, h27m⟩ := step16_add code input hpc26 rfl (by rw [initSelfSlotCode_size]; decide)
  have h27 := step16_goto code input hpc27 rfl (by rw [initSelfSlotCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s27.regs, data := s27.data, pc := 13, regs_size := s27.regs_size, data_size := s27.data_size }
  have hSteps : Steps (initSelfSlotCode (hi := hi) (hw := hw)) input 15 s s' :=
    Steps.cons hstep13 <| Steps.cons h14 <| Steps.cons h15 <| Steps.cons h16 <|
    Steps.cons h17 <| Steps.cons h18 <| Steps.cons h19 <| Steps.cons h20 <|
    Steps.cons h21 <| Steps.cons h22 <| Steps.cons h23 <| Steps.cons h24 <|
    Steps.cons h25 <| Steps.cons h26 <| Steps.cons h27 (Steps.zero s')
  have hDataEq : s'.data = s25.data.set (emitBase + c.val) (reg s25 r14) (by rw [← hr25]; exact hBound25) := by
    change s27.data = _
    rw [h27m, h26data]
    simp only [hr25]
  have hS25Data : s25.data = s.data := by
    rw [h25m, h24m, h23m, h22m, h21m, h20m, h19m, h18m, h17m, h16m, h15m]
  have hDataSz : s'.data.size = origData.size := by
    rw [hDataEq, Array.size_set, hS25Data]
    exact inv.dataSize
  have hS25_14 : (reg s25 r14).val = (pos - S.childStart d.val) + 1 := by
    rw [h25o _ (by decide), hr24]
  have hRegPres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 →
      reg s' r' = reg s r' := by
    intro r' h12' h13' h14' h15'
    change reg s27 r' = reg s r'
    rw [h27o _ h12', reg_eq_of_regs_eq h26regs r', h25o _ h15', h24o _ h14', h23o _ h14',
      h22o _ h13', h21o _ h13', h20o _ h13', h19o _ h13', h18o _ h13', h17o _ h14',
      h16o _ h14', h15o _ h13']
    rfl
  refine ⟨s', hSteps, ?_⟩
  refine
    { pcEq := rfl
      dEq := by rw [hRegPres r8 (by decide) (by decide) (by decide) (by decide)]; exact inv.dEq
      loEq := by rw [hRegPres r10 (by decide) (by decide) (by decide) (by decide)]; exact inv.loEq
      hiEq := by rw [hRegPres r11 (by decide) (by decide) (by decide) (by decide)]; exact inv.hiEq
      posEq := by
        change (reg s27 r12).val = pos + 1
        have h26_12 : (reg s26 r12).val = pos := by
          rw [reg_eq_of_regs_eq h26regs r12, h25o _ (by decide), h24o _ (by decide),
            h23o _ (by decide), h22o _ (by decide), h21o _ (by decide), h20o _ (by decide),
            h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
          exact inv.posEq
        have h26_1 : (reg s26 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h26regs rOne, h25o _ (by decide), h24o _ (by decide),
            h23o _ (by decide), h22o _ (by decide), h21o _ (by decide), h20o _ (by decide),
            h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide)]
          exact h1
        rw [h27d, add_no_wrap _ _ (by rw [h26_12, h26_1]; omega), h26_12, h26_1]
      posGe := Nat.le_trans inv.posGe (Nat.le_succ pos)
      posLe := hposLt
      regs :=
        { consts :=
            { zero := by rw [hRegPres rZero (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPres rOne (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPres rN (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPres rM (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPres rRoot (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPres r5 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPres r6 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPres r7 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := hDataSz
      outsidePres := by
        intro k hk
        have hne : k ≠ emitBase + c.val := by
          have := c.isLt; rcases hk with hl | hr <;> omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne, hS25Data]
        exact inv.outsidePres k hk
      slotZero := by
        have hcNonZero : c.val ≠ 0 := ((S.mem_childSlice_iff d c).mp hcMem).1
        have hne : emitBase ≠ emitBase + c.val := by omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne, hS25Data]
        exact inv.slotZero
      slotsPrev := by
        intro d' hd' c' hc'
        by_cases heq : emitBase + c'.val = emitBase + c.val
        · exfalso
          have hc'Eq : c' = c := Fin.ext (by omega)
          subst hc'Eq
          have hp1 := ((S.mem_childSlice_iff d' c).mp hc').2
          have hp2 := ((S.mem_childSlice_iff d c).mp hcMem).2
          have hdd' : d' = d := hp1.symm.trans hp2
          omega
        · rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ heq, hS25Data]
          exact inv.slotsPrev d' hd' c' hc'
      slotsCur := by
        intro j hlo hhi hj
        by_cases hjEq : j = pos
        · subst hjEq
          have hSelf : S.selfSlotFn (S.childIds ⟨j, hj⟩) = (j - S.childStart d.val) + 1 :=
            S.selfSlotFn_pos (d := d) (c := S.childIds ⟨j, hj⟩) (pos := j) inv.posGe hposLt hj rfl
          have hIdEq : (S.childIds ⟨j, hj⟩).val = c.val := rfl
          simp only [hDataEq, hIdEq, array_set_getElem?_same, Option.map_some, hS25_14, hSelf]
        · have hjLt : j < pos := by omega
          have hne : emitBase + (S.childIds ⟨j, hj⟩).val ≠ emitBase + c.val := by
            intro hEq
            have hIdEq : S.childIds ⟨j, hj⟩ = c := Fin.ext (by omega)
            have hj1 : j - S.childStart d.val < (S.childSlice d).length := by
              simp [StaticTreeSlice.childSlice]; omega
            have hj2 : pos - S.childStart d.val < (S.childSlice d).length := by
              simp [StaticTreeSlice.childSlice]; omega
            have hGet : (S.childSlice d)[j - S.childStart d.val]'hj1 =
                (S.childSlice d)[pos - S.childStart d.val]'hj2 := by
              simp only [StaticTreeSlice.childSlice, List.getElem_ofFn]
              have h1 : S.childStart d.val + (j - S.childStart d.val) = j := by omega
              have h2 : S.childStart d.val + (pos - S.childStart d.val) = pos := by omega
              rw [show (⟨S.childStart d.val + (j - S.childStart d.val), _⟩ : Fin (dense.length - 1)) = ⟨j, hj⟩ from Fin.ext h1]
              rw [show (⟨S.childStart d.val + (pos - S.childStart d.val), _⟩ : Fin (dense.length - 1)) = ⟨pos, hposLtD⟩ from Fin.ext h2]
              exact hIdEq
            have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp (S.childSlice_nodup d))
            have hneSub : j - S.childStart d.val ≠ pos - S.childStart d.val := by omega
            rcases Nat.lt_or_gt_of_ne hneSub with hl | hr
            · exact hPw _ _ hj1 hj2 hl hGet
            · exact hPw _ _ hj2 hj1 hr hGet.symm
          rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne, hS25Data]
          exact inv.slotsCur j hlo hjLt hj }

private theorem initSelfSlot_outer_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (hDenseLe : dense.length ≤ g.vertexCount)
    (d : Nat) (hd : d < dense.length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : InitSelfOuterInv g r dense treeBase emitBase origData S d s) :
    ∃ s', Steps (initSelfSlotCode (hi := hi) (hw := hw)) input
        (14 + 15 * (S.childStart (d + 1) - S.childStart d)) s s' ∧
      InitSelfOuterInv g r dense treeBase emitBase origData S (d + 1) s' := by
  let dFin : Fin dense.length := ⟨d, hd⟩
  have hTreeFit := S.fit
  have hlt2 : (reg s r8).val < (reg s r5).val := by
    rw [inv.dEq, inv.regs.qVal]; exact hd
  let code := initSelfSlotCode (hi := hi) (hw := hw)
  have h2 := step16_branchLt_true code input inv.pcEq rfl (by rw [initSelfSlotCode_size]; decide) hlt2
  let s3 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 3, regs_size := s.regs_size, data_size := s.data_size }
  have hpc3 : s3.pc = 3 := rfl
  obtain ⟨s4, h3, hpc4, h4d, h4o, h4m⟩ := step16_add code input hpc3 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s5, h4, hpc5, h5d, h5o, h5m⟩ := step16_add code input hpc4 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s6, h5, hpc6, h6d, h6o, h6m⟩ := step16_add code input hpc5 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s7, h6, hpc7, h7d, h7o, h7m⟩ := step16_add code input hpc6 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s8, h7, hpc8, h8d, h8o, h8m⟩ := step16_add code input hpc7 rfl (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s9, h8, hpc9, h9d, h9o, h9m⟩ := step16_add code input hpc8 rfl (by rw [initSelfSlotCode_size]; decide)
  have hPow : origData.size ≤ 2 ^ bits := by rw [← inv.dataSize, s.data_size]; exact hw
  have hQ : (reg s r5).val = dense.length := inv.regs.qVal
  have h6v : (reg s r6).val = treeBase := inv.regs.treeBaseVal
  have h1 : (reg s rOne).val = 1 := inv.regs.consts.one
  have hr4 : (reg s4 r9).val = 2 * dense.length := by
    rw [h4d, add_no_wrap _ _ (by change (reg s r5).val + (reg s r5).val < _; rw [hQ]; unfold staticTreeWords at hTreeFit; omega)]
    change (reg s r5).val + (reg s r5).val = _; rw [hQ]; omega
  have hr5 : (reg s5 r10).val = 4 * dense.length := by
    rw [h5d, add_no_wrap _ _ (by rw [hr4]; unfold staticTreeWords at hTreeFit; omega), hr4]; omega
  have hr6 : (reg s6 r9).val = 6 * dense.length := by
    have h5_9 : (reg s5 r9).val = 2 * dense.length := by rw [h5o _ (by decide)]; exact hr4
    rw [h6d, add_no_wrap _ _ (by rw [h5_9, hr5]; unfold staticTreeWords at hTreeFit; omega), h5_9, hr5]; omega
  have hr7 : (reg s7 r9).val = 7 * dense.length := by
    have h6_5 : (reg s6 r5).val = dense.length := by
      rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact hQ
    rw [h7d, add_no_wrap _ _ (by rw [hr6, h6_5]; unfold staticTreeWords at hTreeFit; omega), hr6, h6_5]; omega
  have hr8 : (reg s8 r9).val = treeBase + 7 * dense.length := by
    have h7_6 : (reg s7 r6).val = treeBase := by
      rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact h6v
    rw [h8d, add_no_wrap _ _ (by rw [hr7, h7_6]; unfold staticTreeWords at hTreeFit; omega), hr7, h7_6]; omega
  have hr9 : (reg s9 r9).val = treeBase + 7 * dense.length + d := by
    have h8_8 : (reg s8 r8).val = d := by
      rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]
      exact inv.dEq
    rw [h9d, add_no_wrap _ _ (by rw [hr8, h8_8]; unfold staticTreeWords at hTreeFit; omega), hr8, h8_8]
  have hDisjLo : treeBase + 7 * dense.length + d < emitBase ∨
      emitBase + dense.length ≤ treeBase + 7 * dense.length + d := by
    unfold staticTreeWords emitterWorkWords at *
    rcases hDisjTreeEmit with hl | hr
    · left; omega
    · right; omega
  have hDisjHi : treeBase + 7 * dense.length + (d + 1) < emitBase ∨
      emitBase + dense.length ≤ treeBase + 7 * dense.length + (d + 1) := by
    unfold staticTreeWords emitterWorkWords at *
    rcases hDisjTreeEmit with hl | hr
    · left; omega
    · right; omega
  have hS9Data : s9.data = s.data := by rw [h9m, h8m, h7m, h6m, h5m, h4m]
  have hLoMem : (s9.data[(reg s9 r9).val]?).map Fin.val = some (S.childStart d) := by
    rw [hr9, hS9Data]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisjLo) (S.childStart_mem d (Nat.le_of_lt hd))
  obtain ⟨wlo, hwlo, hwloVal⟩ := data_val_at hLoMem
  obtain ⟨s10, h9, hpc10, h10d, h10o, h10m⟩ := step16_loadData code input hpc9 rfl hwlo (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s11, h10, hpc11, h11d, h11o, h11m⟩ := step16_add code input hpc10 rfl (by rw [initSelfSlotCode_size]; decide)
  have hr11_9 : (reg s11 r9).val = treeBase + 7 * dense.length + (d + 1) := by
    have h10_9 : (reg s10 r9).val = treeBase + 7 * dense.length + d := by
      rw [h10o _ (by decide)]; exact hr9
    have h10_1 : (reg s10 rOne).val = 1 := by
      rw [h10o _ (by decide), h9o _ (by decide), h8o _ (by decide), h7o _ (by decide),
        h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact h1
    rw [h11d, add_no_wrap _ _ (by rw [h10_9, h10_1]; unfold staticTreeWords at hTreeFit; omega), h10_9, h10_1]
    omega
  have hHiMem : (s11.data[(reg s11 r9).val]?).map Fin.val = some (S.childStart (d + 1)) := by
    rw [hr11_9, h11m, h10m, hS9Data]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisjHi) (S.childStart_mem (d + 1) hd)
  obtain ⟨whi, hwhi, hwhiVal⟩ := data_val_at hHiMem
  obtain ⟨s12, h11, hpc12, h12d, h12o, h12m⟩ := step16_loadData code input hpc11 rfl hwhi (by rw [initSelfSlotCode_size]; decide)
  obtain ⟨s13, h12, hpc13, h13d, h13o, h13m⟩ := step16_mov code input hpc12 rfl (by rw [initSelfSlotCode_size]; decide)
  have hPre : Steps (initSelfSlotCode (hi := hi) (hw := hw)) input 11 s s13 :=
    Steps.cons h2 <| Steps.cons h3 <| Steps.cons h4 <| Steps.cons h5 <|
    Steps.cons h6 <| Steps.cons h7 <| Steps.cons h8 <| Steps.cons h9 <|
    Steps.cons h10 <| Steps.cons h11 <| Steps.cons h12 (Steps.zero s13)
  have hS13Data : s13.data = s.data := by rw [h13m, h12m, h11m, h10m, hS9Data]
  have hRegPresPre : ∀ r' : Fin 16, r' ≠ r9 → r' ≠ r10 → r' ≠ r11 → r' ≠ r12 →
      reg s13 r' = reg s r' := by
    intro r' h9' h10' h11' h12'
    rw [h13o _ h12', h12o _ h11', h11o _ h9', h10o _ h10', h9o _ h9', h8o _ h9',
      h7o _ h9', h6o _ h9', h5o _ h10', h4o _ h9']
    rfl
  have hInner0 : InitSelfInnerInv g r dense treeBase emitBase origData S dFin (S.childStart d) s13 :=
    { pcEq := hpc13
      dEq := by rw [hRegPresPre r8 (by decide) (by decide) (by decide) (by decide)]; exact inv.dEq
      loEq := by
        rw [h13o _ (by decide), h12o _ (by decide), h11o _ (by decide), h10d, hwloVal]
      hiEq := by
        rw [h13o _ (by decide), h12d, hwhiVal]
      posEq := by
        rw [h13d, h12o _ (by decide), h11o _ (by decide), h10d, hwloVal]
      posGe := Nat.le_refl _
      posLe := S.childStart_mono d (d + 1) (Nat.le_succ d) hd
      regs :=
        { consts :=
            { zero := by rw [hRegPresPre rZero (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPresPre rOne (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPresPre rN (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPresPre rM (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPresPre rRoot (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPresPre r5 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPresPre r6 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPresPre r7 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [hS13Data]; exact inv.dataSize
      outsidePres := by intro k hk; rw [hS13Data]; exact inv.outsidePres k hk
      slotZero := by rw [hS13Data]; exact inv.slotZero
      slotsPrev := by intro d' hd' c hc; rw [hS13Data]; exact inv.slotsDone d' hd' c hc
      slotsCur := fun j hlo hhi _ => False.elim (by change S.childStart d ≤ j at hlo; omega) }
  have hRunInner : ∀ rem pos st,
      S.childStart (d + 1) - pos = rem →
      InitSelfInnerInv g r dense treeBase emitBase origData S dFin pos st →
      ∃ stEnd, Steps (initSelfSlotCode (hi := hi) (hw := hw)) input (15 * rem) st stEnd ∧
        InitSelfInnerInv g r dense treeBase emitBase origData S dFin (S.childStart (d + 1)) stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro pos st hrem hinv
      have hpeq : pos = S.childStart (d + 1) := by
        have := hinv.posLe; change pos ≤ S.childStart (d + 1) at this; omega
      subst hpeq
      exact ⟨st, by simp only [Nat.mul_zero]; exact Steps.zero st, hinv⟩
    | succ rem ih =>
      intro pos st hrem hinv
      have hplt : pos < S.childStart (d + 1) := by
        have := hinv.posLe; change pos ≤ S.childStart (d + 1) at this; omega
      obtain ⟨st1, hstep1, hinv1⟩ :=
        initSelfSlot_inner_step input S hFitEmit hDisjTreeEmit hDenseLe dFin pos hplt hinv
      obtain ⟨stEnd, hstepRest, hinvEnd⟩ := ih (pos + 1) st1 (by omega) hinv1
      have hMul : 15 * (rem + 1) = 15 + 15 * rem := by omega
      rw [hMul]
      exact ⟨stEnd, hstep1.append hstepRest, hinvEnd⟩
  obtain ⟨sEndIn, hStepsIn, hInvIn⟩ := hRunInner (S.childStart (d + 1) - S.childStart d) (S.childStart d) s13 rfl hInner0
  have hFalse : (reg sEndIn r11).val ≤ (reg sEndIn r12).val := by
    rw [hInvIn.posEq, hInvIn.hiEq]
    exact Nat.le_refl _
  have h13f := step16_branchLt_false code input hInvIn.pcEq rfl (by rw [initSelfSlotCode_size]; decide) hFalse
  let s28 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEndIn.regs, data := sEndIn.data, pc := 28, regs_size := sEndIn.regs_size, data_size := sEndIn.data_size }
  have hpc28 : s28.pc = 28 := rfl
  obtain ⟨s29, h28, hpc29, h29d, h29o, h29m⟩ := step16_add code input hpc28 rfl (by rw [initSelfSlotCode_size]; decide)
  have h29 := step16_goto code input hpc29 rfl (by rw [initSelfSlotCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s29.regs, data := s29.data, pc := 2, regs_size := s29.regs_size, data_size := s29.data_size }
  have hExit : Steps (initSelfSlotCode (hi := hi) (hw := hw)) input 3 sEndIn s' :=
    Steps.cons h13f <| Steps.cons h28 <| Steps.cons h29 (Steps.zero s')
  have hTotal : 14 + 15 * (S.childStart (d + 1) - S.childStart d) =
      11 + 15 * (S.childStart (d + 1) - S.childStart d) + 3 := by omega
  have hS'Data : s'.data = sEndIn.data := by change s29.data = _; rw [h29m]
  have hRegPresOut : ∀ r' : Fin 16, r' ≠ r8 → reg s' r' = reg sEndIn r' := by
    intro r' h8'
    change reg s29 r' = reg sEndIn r'
    rw [h29o _ h8']; rfl
  refine ⟨s', by rw [hTotal]; exact (hPre.append hStepsIn).append hExit, ?_⟩
  refine
    { pcEq := rfl
      dEq := by
        change (reg s29 r8).val = d + 1
        have h28_8 : (reg s28 r8).val = d := hInvIn.dEq
        have h28_1 : (reg s28 rOne).val = 1 := hInvIn.regs.consts.one
        rw [h29d, add_no_wrap _ _ (by rw [h28_8, h28_1]; omega), h28_8, h28_1]
      dLe := hd
      regs :=
        { consts :=
            { zero := by rw [hRegPresOut rZero (by decide)]; exact hInvIn.regs.consts.zero
              one := by rw [hRegPresOut rOne (by decide)]; exact hInvIn.regs.consts.one
              nVal := by rw [hRegPresOut rN (by decide)]; exact hInvIn.regs.consts.nVal
              mVal := by rw [hRegPresOut rM (by decide)]; exact hInvIn.regs.consts.mVal
              rootVal := by rw [hRegPresOut rRoot (by decide)]; exact hInvIn.regs.consts.rootVal }
          qVal := by rw [hRegPresOut r5 (by decide)]; exact hInvIn.regs.qVal
          treeBaseVal := by rw [hRegPresOut r6 (by decide)]; exact hInvIn.regs.treeBaseVal
          emitBaseVal := by rw [hRegPresOut r7 (by decide)]; exact hInvIn.regs.emitBaseVal }
      dataSize := by rw [hS'Data]; exact hInvIn.dataSize
      outsidePres := by intro k hk; rw [hS'Data]; exact hInvIn.outsidePres k hk
      slotZero := by rw [hS'Data]; exact hInvIn.slotZero
      slotsDone := by
        intro d' hd' c hc
        rw [hS'Data]
        by_cases hdLt : d'.val < d
        · exact hInvIn.slotsPrev d' hdLt c hc
        · have hdEq : d'.val = d := by omega
          have hdFinEq : d' = dFin := Fin.ext hdEq
          subst hdFinEq
          obtain ⟨j, hjLt, hcGet⟩ := List.mem_iff_getElem.mp hc
          simp only [StaticTreeSlice.childSlice, List.length_ofFn, List.getElem_ofFn] at hjLt hcGet
          have hjPosLt : S.childStart dFin.val + j < S.childStart (dFin.val + 1) := by omega
          have hEnd : S.childStart (dFin.val + 1) ≤ dense.length - 1 := by
            have hm := S.childStart_mono (dFin.val + 1) dense.length dFin.isLt (Nat.le_refl _)
            rwa [S.childStart_end] at hm
          have hjDense : S.childStart dFin.val + j < dense.length - 1 := by omega
          rw [← hcGet]
          exact hInvIn.slotsCur (S.childStart dFin.val + j) (Nat.le_add_right _ _) hjPosLt hjDense }

theorem run_initSelfSlotPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s₀)
    (S : StaticTreeSlice s₀.data treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ s₀.data.size)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 29 * g.vertexCount + 4 ∧
      PaperB.RamProgram.run (initSelfSlotPhase (hi := hi) (hw := hw)).code input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase t ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase ∨ emitBase + dense.length ≤ k) → t.data[k]? = s₀.data[k]?) ∧
      (∀ v : Fin dense.length, (t.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v)) := by
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  let code := initSelfSlotCode (hi := hi) (hw := hw)
  let sInit := Phase.initial s₀
  have hpc0 : sInit.pc = 0 := rfl
  have hPow : s₀.data.size ≤ 2 ^ bits := by rw [s₀.data_size]; exact hw
  have hBnd0 : (reg sInit r7).val < sInit.data.size := by
    change (reg s₀ r7).val < s₀.data.size
    rw [hRegs.emitBaseVal]
    unfold emitterWorkWords at hFitEmit
    omega
  obtain ⟨s1, h0, hpc1, h1regs, h1data⟩ := step16_storeData code input hpc0 rfl (by rw [initSelfSlotCode_size]; decide) hBnd0
  obtain ⟨s2, h1, hpc2, h2d, h2o, h2m⟩ := step16_mov code input hpc1 rfl (by rw [initSelfSlotCode_size]; decide)
  have hRegInit : ∀ r' : Fin 16, r' ≠ r8 → reg s2 r' = reg s₀ r' := by
    intro r' hr8'
    rw [h2o _ hr8', reg_eq_of_regs_eq h1regs r']; rfl
  have hS2Data : s2.data = s₀.data.set emitBase (reg s₀ rZero) (by rw [← hRegs.emitBaseVal]; exact hBnd0) := by
    rw [h2m, h1data]; change s₀.data.set _ _ _ = _; congr 1; exact hRegs.emitBaseVal
  have hOuter0 : InitSelfOuterInv g r dense treeBase emitBase s₀.data S 0 s2 :=
    { pcEq := hpc2
      dEq := by
        rw [h2d, reg_eq_of_regs_eq h1regs rZero]
        exact hRegs.consts.zero
      dLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [hRegInit rZero (by decide)]; exact hRegs.consts.zero
              one := by rw [hRegInit rOne (by decide)]; exact hRegs.consts.one
              nVal := by rw [hRegInit rN (by decide)]; exact hRegs.consts.nVal
              mVal := by rw [hRegInit rM (by decide)]; exact hRegs.consts.mVal
              rootVal := by rw [hRegInit rRoot (by decide)]; exact hRegs.consts.rootVal }
          qVal := by rw [hRegInit r5 (by decide)]; exact hRegs.qVal
          treeBaseVal := by rw [hRegInit r6 (by decide)]; exact hRegs.treeBaseVal
          emitBaseVal := by rw [hRegInit r7 (by decide)]; exact hRegs.emitBaseVal }
      dataSize := by rw [hS2Data, Array.size_set]
      outsidePres := by
        intro k hk
        have hne : k ≠ emitBase := by
          have := S.qPos
          rcases hk with hl | hr <;> omega
        rw [hS2Data, array_set_getElem?_ne _ _ _ _ _ hne]
      slotZero := by
        rw [hS2Data, array_set_getElem?_same, Option.map_some, hRegs.consts.zero]
      slotsDone := fun _ hd' => False.elim (Nat.not_lt_zero _ hd') }
  have hRunOuter : ∀ d st,
      d ≤ dense.length →
      InitSelfOuterInv g r dense treeBase emitBase s₀.data S d st →
      ∃ stEnd stepsOuter,
        stepsOuter ≤ 14 * (dense.length - d) + 15 * (dense.length - 1 - S.childStart d) ∧
        Steps (initSelfSlotCode (hi := hi) (hw := hw)) input stepsOuter st stEnd ∧
        InitSelfOuterInv g r dense treeBase emitBase s₀.data S dense.length stEnd := by
    intro d
    suffices ∀ rem st, d + rem = dense.length →
        InitSelfOuterInv g r dense treeBase emitBase s₀.data S d st →
        ∃ stEnd stepsOuter,
          stepsOuter ≤ 14 * rem + 15 * (S.childStart dense.length - S.childStart d) ∧
          Steps (initSelfSlotCode (hi := hi) (hw := hw)) input stepsOuter st stEnd ∧
          InitSelfOuterInv g r dense treeBase emitBase s₀.data S dense.length stEnd by
      intro st hd hinv
      obtain ⟨stEnd, stepsOuter, hBnd, hSt, hInvEnd⟩ :=
        this (dense.length - d) st (by omega) hinv
      rw [S.childStart_end] at hBnd
      exact ⟨stEnd, stepsOuter, by simpa [Nat.sub_add_cancel hd] using hBnd, hSt, hInvEnd⟩
    intro rem
    induction rem generalizing d with
    | zero =>
      intro st hrem hinv
      have hdeq : d = dense.length := by omega
      subst hdeq
      exact ⟨st, 0, Nat.zero_le _, Steps.zero st, hinv⟩
    | succ rem ih =>
      intro st hrem hinv
      have hdlt : d < dense.length := by omega
      obtain ⟨st1, hstep1, hinv1⟩ :=
        initSelfSlot_outer_step input S hFitEmit hDisjTreeEmit hDenseLe d hdlt hinv
      obtain ⟨stEnd, stepsRest, hBndRest, hStepRest, hInvEnd⟩ := ih (d + 1) st1 (by omega) hinv1
      have hMono1 := S.childStart_mono d (d + 1) (Nat.le_succ d) hdlt
      have hMono2 := S.childStart_mono (d + 1) dense.length hdlt (Nat.le_refl _)
      refine ⟨stEnd, (14 + 15 * (S.childStart (d + 1) - S.childStart d)) + stepsRest, ?_, hstep1.append hStepRest, hInvEnd⟩
      omega
  obtain ⟨sEnd, stepsOuter, hBndOuter, hStepsOuter, hInvEnd⟩ := hRunOuter 0 s2 (Nat.zero_le _) hOuter0
  have hFalseEnd : (reg sEnd r5).val ≤ (reg sEnd r8).val := by
    rw [hInvEnd.dEq, hInvEnd.regs.qVal]
    exact Nat.le_refl _
  have h2f := step16_branchLt_false code input hInvEnd.pcEq rfl (by rw [initSelfSlotCode_size]; decide) hFalseEnd
  let sHalt : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEnd.regs, data := sEnd.data, pc := 30, regs_size := sEnd.regs_size, data_size := sEnd.data_size }
  have hHalt : step code input sHalt = some (.halted sHalt) :=
    step_halt_at (by rfl)
  have hFullSteps : Steps code input (2 + stepsOuter + 1) sInit sHalt :=
    ((Steps.cons h0 <| Steps.cons h1 (Steps.zero s2)).append hStepsOuter).append
      (Steps.cons h2f (Steps.zero sHalt))
  have hExec := hFullSteps.halts hHalt
  refine ⟨sHalt, 2 + stepsOuter + 1 + 1, ?_, hExec, ?_, hInvEnd.dataSize, hInvEnd.outsidePres, ?_⟩
  · have hcs0 := S.childStart_zero
    have hPos := S.qPos
    rw [hcs0, Nat.sub_zero] at hBndOuter
    omega
  · exact
      { consts :=
          { zero := hInvEnd.regs.consts.zero
            one := hInvEnd.regs.consts.one
            nVal := hInvEnd.regs.consts.nVal
            mVal := hInvEnd.regs.consts.mVal
            rootVal := hInvEnd.regs.consts.rootVal }
        qVal := hInvEnd.regs.qVal
        treeBaseVal := hInvEnd.regs.treeBaseVal
        emitBaseVal := hInvEnd.regs.emitBaseVal }
  · intro v
    by_cases hv0 : v.val = 0
    · rw [S.selfSlotFn_root v hv0, hv0, Nat.add_zero]
      exact hInvEnd.slotZero
    · have hvMem : v ∈ S.childSlice (S.domParent v) :=
        (S.mem_childSlice_iff (S.domParent v) v).mpr ⟨hv0, rfl⟩
      exact hInvEnd.slotsDone (S.domParent v) (S.domParent v).isLt v hvMem

/-! #### Phase 2: `zeroQDegPhase` (`qDeg[0..Q) := 0`) -/

def zeroQDegCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    .mov r8 rZero,          -- 0: d := 0
    .branchLt r8 r5 2 7,    -- 1: while d < Q
    .add r9 r7 rN,          -- 2: emitBase + n
    .add r9 r9 r8,          -- 3: emitBase + n + d
    .storeData r9 rZero,    -- 4: qDeg[d] := 0
    .add r8 r8 rOne,        -- 5: d++
    .goto 1,                -- 6
    .halt                   -- 7
  ]

def zeroQDegPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast zeroQDegCode 7 rfl rfl rfl

private theorem zeroQDegCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (zeroQDegCode (hi := hi) (hw := hw)).size = 8 := rfl

private structure ZeroQDegInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (n m root Q treeBase emitBase : Nat) (origData : Array (Word bits))
    (d : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 1
  dEq : (reg s r8).val = d
  dLe : d ≤ Q
  regs : EmitterRegs n m root Q treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + n ∨ emitBase + n + Q ≤ k) → s.data[k]? = origData[k]?
  zeroDone : ∀ j : Nat, j < d → (s.data[emitBase + n + j]?).map Fin.val = some 0

private theorem zeroQDeg_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase : Nat} {origData : Array (Word bits)}
    (hQLe : Q ≤ n) (hFitEmit : emitBase + emitterWorkWords n m ≤ origData.size)
    (d : Nat) (hd : d < Q)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : ZeroQDegInv n m root Q treeBase emitBase origData d s) :
    ∃ s', Steps (zeroQDegCode (hi := hi) (hw := hw)) input 6 s s' ∧
      ZeroQDegInv n m root Q treeBase emitBase origData (d + 1) s' := by
  let code := zeroQDegCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hlt1 : (reg s r8).val < (reg s r5).val := by rw [inv.dEq, inv.regs.qVal]; exact hd
  have h1 := step16_branchLt_true code input inv.pcEq rfl (by rw [zeroQDegCode_size]; decide) hlt1
  let s2 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 2, regs_size := s.regs_size, data_size := s.data_size }
  have hpc2 : s2.pc = 2 := rfl
  obtain ⟨s3, h2, hpc3, h3d, h3o, h3m⟩ := step16_add code input hpc2 rfl (by rw [zeroQDegCode_size]; decide)
  obtain ⟨s4, h3, hpc4, h4d, h4o, h4m⟩ := step16_add code input hpc3 rfl (by rw [zeroQDegCode_size]; decide)
  have hr3 : (reg s3 r9).val = emitBase + n := by
    have h2_7 : (reg s2 r7).val = emitBase := inv.regs.emitBaseVal
    have h2_n : (reg s2 rN).val = n := inv.regs.consts.nVal
    rw [h3d, add_no_wrap _ _ (by rw [h2_7, h2_n]; unfold emitterWorkWords at hFitEmit; omega), h2_7, h2_n]
  have hr4 : (reg s4 r9).val = emitBase + n + d := by
    have h3_8 : (reg s3 r8).val = d := by rw [h3o _ (by decide)]; exact inv.dEq
    rw [h4d, add_no_wrap _ _ (by rw [hr3, h3_8]; unfold emitterWorkWords at hFitEmit; omega), hr3, h3_8]
  have hBnd4 : (reg s4 r9).val < s4.data.size := by
    rw [hr4, h4m, h3m]; change emitBase + n + d < s.data.size
    rw [inv.dataSize]; unfold emitterWorkWords at hFitEmit; omega
  obtain ⟨s5, h4, hpc5, h5regs, h5data⟩ := step16_storeData code input hpc4 rfl (by rw [zeroQDegCode_size]; decide) hBnd4
  obtain ⟨s6, h5, hpc6, h6d, h6o, h6m⟩ := step16_add code input hpc5 rfl (by rw [zeroQDegCode_size]; decide)
  have h6 := step16_goto code input hpc6 rfl (by rw [zeroQDegCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s6.regs, data := s6.data, pc := 1, regs_size := s6.regs_size, data_size := s6.data_size }
  have hSteps : Steps code input 6 s s' :=
    Steps.cons h1 <| Steps.cons h2 <| Steps.cons h3 <| Steps.cons h4 <| Steps.cons h5 <| Steps.cons h6 (Steps.zero s')
  have hDataEq : s'.data = s.data.set (emitBase + n + d) (reg s4 rZero)
      (by have hSz : s4.data.size = s.data.size := by rw [h4m, h3m]
          rw [← hr4, ← hSz]; exact hBnd4) := by
    change s6.data = _
    rw [h6m, h5data]
    exact array_set_congr (by rw [h4m, h3m]) hr4 rfl
  have hZeroVal : (reg s4 rZero).val = 0 := by
    rw [h4o _ (by decide), h3o _ (by decide)]; exact inv.regs.consts.zero
  have hRegPres : ∀ r' : Fin 16, r' ≠ r8 → r' ≠ r9 → reg s' r' = reg s r' := by
    intro r' h8' h9'
    change reg s6 r' = reg s r'
    rw [h6o _ h8', reg_eq_of_regs_eq h5regs r', h4o _ h9', h3o _ h9']; rfl
  refine ⟨s', hSteps, ?_⟩
  refine
    { pcEq := rfl
      dEq := by
        change (reg s6 r8).val = d + 1
        have h5_8 : (reg s5 r8).val = d := by
          rw [reg_eq_of_regs_eq h5regs r8, h4o _ (by decide), h3o _ (by decide)]; exact inv.dEq
        have h5_1 : (reg s5 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h5regs rOne, h4o _ (by decide), h3o _ (by decide)]; exact inv.regs.consts.one
        rw [h6d, add_no_wrap _ _ (by rw [h5_8, h5_1]; omega), h5_8, h5_1]
      dLe := hd
      regs :=
        { consts :=
            { zero := by rw [hRegPres rZero (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPres rOne (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPres rN (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPres rM (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPres rRoot (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPres r5 (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPres r6 (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPres r7 (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [hDataEq, Array.size_set]; exact inv.dataSize
      outsidePres := by
        intro k hk
        have hne : k ≠ emitBase + n + d := by rcases hk with hl | hr <;> omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
        exact inv.outsidePres k hk
      zeroDone := by
        intro j hj
        by_cases hjEq : j = d
        · subst hjEq
          rw [hDataEq, array_set_getElem?_same, Option.map_some, hZeroVal]
        · have hjLt : j < d := by omega
          have hne : emitBase + n + j ≠ emitBase + n + d := by omega
          rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
          exact inv.zeroDone j hjLt }

theorem run_zeroQDegPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : EmitterRegs n m root Q treeBase emitBase s₀)
    (hQLe : Q ≤ n)
    (hFitEmit : emitBase + emitterWorkWords n m ≤ s₀.data.size) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 6 * n + 3 ∧
      PaperB.RamProgram.run (zeroQDegPhase (hi := hi) (hw := hw)).code input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      EmitterRegs n m root Q treeBase emitBase t ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase + n ∨ emitBase + n + Q ≤ k) → t.data[k]? = s₀.data[k]?) ∧
      (∀ j : Nat, j < Q → (t.data[emitBase + n + j]?).map Fin.val = some 0) := by
  let code := zeroQDegCode (hi := hi) (hw := hw)
  let sInit := Phase.initial s₀
  have hpc0 : sInit.pc = 0 := rfl
  obtain ⟨s1, h0, hpc1, h1d, h1o, h1m⟩ := step16_mov code input hpc0 rfl (by rw [zeroQDegCode_size]; decide)
  have hInv0 : ZeroQDegInv n m root Q treeBase emitBase s₀.data 0 s1 :=
    { pcEq := hpc1
      dEq := by rw [h1d]; exact hRegs.consts.zero
      dLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [h1o _ (by decide)]; exact hRegs.consts.zero
              one := by rw [h1o _ (by decide)]; exact hRegs.consts.one
              nVal := by rw [h1o _ (by decide)]; exact hRegs.consts.nVal
              mVal := by rw [h1o _ (by decide)]; exact hRegs.consts.mVal
              rootVal := by rw [h1o _ (by decide)]; exact hRegs.consts.rootVal }
          qVal := by rw [h1o _ (by decide)]; exact hRegs.qVal
          treeBaseVal := by rw [h1o _ (by decide)]; exact hRegs.treeBaseVal
          emitBaseVal := by rw [h1o _ (by decide)]; exact hRegs.emitBaseVal }
      dataSize := by rw [h1m]; rfl
      outsidePres := by intro k _; rw [h1m]; rfl
      zeroDone := fun _ hj => False.elim (Nat.not_lt_zero _ hj) }
  have hRun : ∀ rem d st, d + rem = Q →
      ZeroQDegInv n m root Q treeBase emitBase s₀.data d st →
      ∃ stEnd, Steps code input (6 * rem) st stEnd ∧
        ZeroQDegInv n m root Q treeBase emitBase s₀.data Q stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro d st hrem hinv
      have hdEq : d = Q := by omega
      subst hdEq
      exact ⟨st, by simp only [Nat.mul_zero]; exact Steps.zero st, hinv⟩
    | succ rem ih =>
      intro d st hrem hinv
      have hdLt : d < Q := by omega
      obtain ⟨st1, hstep1, hinv1⟩ := zeroQDeg_step input hQLe hFitEmit d hdLt hinv
      obtain ⟨stEnd, hstepRest, hinvEnd⟩ := ih (d + 1) st1 (by omega) hinv1
      have hMul : 6 * (rem + 1) = 6 + 6 * rem := by omega
      rw [hMul]
      exact ⟨stEnd, hstep1.append hstepRest, hinvEnd⟩
  obtain ⟨sEnd, hStepsLoop, hInvEnd⟩ := hRun Q 0 s1 (Nat.zero_add Q) hInv0
  have hFalse : (reg sEnd r5).val ≤ (reg sEnd r8).val := by
    rw [hInvEnd.dEq, hInvEnd.regs.qVal]; exact Nat.le_refl _
  have h1f := step16_branchLt_false code input hInvEnd.pcEq rfl (by rw [zeroQDegCode_size]; decide) hFalse
  let sHalt : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEnd.regs, data := sEnd.data, pc := 7, regs_size := sEnd.regs_size, data_size := sEnd.data_size }
  have hHalt : step code input sHalt = some (.halted sHalt) := step_halt_at (by rfl)
  have hFull := ((Steps.cons h0 (Steps.zero s1)).append hStepsLoop).append (Steps.cons h1f (Steps.zero sHalt))
  have hExec := hFull.halts hHalt
  refine ⟨sHalt, 1 + 6 * Q + 1 + 1, by omega, hExec, ?_, hInvEnd.dataSize, hInvEnd.outsidePres, hInvEnd.zeroDone⟩
  exact
    { consts :=
        { zero := hInvEnd.regs.consts.zero
          one := hInvEnd.regs.consts.one
          nVal := hInvEnd.regs.consts.nVal
          mVal := hInvEnd.regs.consts.mVal
          rootVal := hInvEnd.regs.consts.rootVal }
      qVal := hInvEnd.regs.qVal
      treeBaseVal := hInvEnd.regs.treeBaseVal
      emitBaseVal := hInvEnd.regs.emitBaseVal }

/-! #### Phase 3: `countQDegPhase` (`qDeg[0..Q) := emittedArcs.length`) -/

def countQDegCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    .mov r8 rZero,            -- 0: uDense := 0
    .branchLt r8 r5 2 35,     -- 1: while uDense < Q
    .add r9 rN rN,            -- 2: 2n
    .add r9 r9 r9,            -- 3: 4n
    .add r9 r9 r8,            -- 4: 4n + uDense
    .loadData r9 r9,          -- 5: uOrig = denseToOrig[uDense]
    .add r10 r9 rOne,         -- 6: uOrig + 1
    .add r10 r10 rOne,        -- 7: uOrig + 2
    .add r10 r10 rOne,        -- 8: uOrig + 3
    .add r11 r10 rOne,        -- 9: uOrig + 4
    .loadInput r10 r10,       -- 10: eIdx = outPrefix[uOrig]
    .loadInput r11 r11,       -- 11: eEnd = outPrefix[uOrig + 1]
    .branchLt r10 r11 13 33,  -- 12: while eIdx < eEnd
    .add r12 rN r10,          -- 13: n + eIdx
    .add r12 r12 rOne,        -- 14: n + 1 + eIdx
    .add r12 r12 rOne,        -- 15: n + 2 + eIdx
    .add r12 r12 rOne,        -- 16: n + 3 + eIdx
    .add r12 r12 rOne,        -- 17: 4 + n + eIdx
    .loadInput r12 r12,       -- 18: vOrig
    .add r13 rN rN,           -- 19: 2n
    .add r13 r13 rN,          -- 20: 3n
    .add r13 r13 r12,         -- 21: 3n + vOrig
    .loadData r13 r13,        -- 22: vDense + 1
    .sub r13 r13 rOne,        -- 23: vDense
    .add r13 r6 r13,          -- 24: treeBase + vDense
    .loadData r13 r13,        -- 25: d = domParent[vDense]
    .add r14 r7 rN,           -- 26: emitBase + n
    .add r14 r14 r13,         -- 27: emitBase + n + d
    .loadData r15 r14,        -- 28: cnt = qDeg[d]
    .add r15 r15 rOne,        -- 29: cnt + 1
    .storeData r14 r15,       -- 30: qDeg[d] := cnt + 1
    .add r10 r10 rOne,        -- 31: eIdx++
    .goto 12,                 -- 32
    .add r8 r8 rOne,          -- 33: uDense++
    .goto 1,                  -- 34
    .halt                     -- 35
  ]

def countQDegPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast countQDegCode 35 rfl rfl rfl

private theorem countQDegCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (countQDegCode (hi := hi) (hw := hw)).size = 36 := rfl

def emittedPrefixList {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (u j : Nat) : List (EmittedArc dense.length) :=
  ((List.finRange dense.length).take u).flatMap S.emitForU ++
    if hu : u < dense.length then (S.emitForU ⟨u, hu⟩).take j else []

theorem emittedPrefixList_zero {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) :
    emittedPrefixList S 0 0 = [] := by
  simp [emittedPrefixList]

theorem emittedPrefixList_end {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) :
    emittedPrefixList S dense.length 0 = S.allEmittedArcs := by
  unfold emittedPrefixList StaticTreeSlice.allEmittedArcs
  simp only [Nat.lt_irrefl, ↓reduceDIte, List.append_nil]
  rw [List.take_of_length_le (by simp)]

private theorem list_take_succ_finRange (n u : Nat) (hu : u < n) :
    (List.finRange n).take (u + 1) = (List.finRange n).take u ++ [⟨u, hu⟩] := by
  have h1 : u < (List.finRange n).length := by simp [hu]
  rw [List.take_succ_eq_append_getElem h1]
  simp

theorem emittedPrefixList_step_u {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense)
    {u : Nat} (hu : u < dense.length) :
    emittedPrefixList S u (g.outArcs (dense[u]'hu)).length = emittedPrefixList S (u + 1) 0 := by
  unfold emittedPrefixList
  have hLen : (S.emitForU ⟨u, hu⟩).length = (g.outArcs (dense[u]'hu)).length := S.emitForU_length ⟨u, hu⟩
  simp only [hu, ↓reduceDIte]
  rw [← hLen, List.take_length, list_take_succ_finRange dense.length u hu, List.flatMap_append]
  by_cases hu1 : u + 1 < dense.length
  · simp [hu1]
  · simp [hu1]

private theorem emitForU_getElem {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (uDense : Fin dense.length) (j : Nat) (hj : j < (g.outArcs (dense[uDense.val]'uDense.isLt)).length) :
    let vOrig := (g.outArcs (dense[uDense.val]'uDense.isLt))[j]'hj
    let hv : dense.idxOf vOrig < dense.length :=
      List.idxOf_lt_length_of_mem
        (S.mem_reach vOrig (initiallyReachable_extend (S.reach_mem uDense.val uDense.isLt) (List.getElem_mem hj)))
    let hjEmit : j < (S.emitForU uDense).length := by rw [S.emitForU_length]; exact hj
    (S.emitForU uDense)[j]'hjEmit = S.emittedArc uDense ⟨dense.idxOf vOrig, hv⟩ := by
  intro vOrig hv hjEmit
  have hAll : ∀ w ∈ g.outArcs (dense[uDense.val]'uDense.isLt), dense.idxOf w < dense.length := fun w hw =>
    List.idxOf_lt_length_of_mem (S.mem_reach w (initiallyReachable_extend (S.reach_mem uDense.val uDense.isLt) hw))
  suffices ∀ (l : List (Fin g.vertexCount)) (k : Nat) (hk : k < l.length)
      (hl : ∀ w ∈ l, dense.idxOf w < dense.length)
      (hkF : k < (l.filterMap (fun w => if hw : dense.idxOf w < dense.length then
        some (S.emittedArc uDense ⟨dense.idxOf w, hw⟩) else none)).length),
      (l.filterMap (fun w => if hw : dense.idxOf w < dense.length then
        some (S.emittedArc uDense ⟨dense.idxOf w, hw⟩) else none))[k]'hkF =
        S.emittedArc uDense ⟨dense.idxOf (l[k]'hk), hl (l[k]'hk) (List.getElem_mem hk)⟩ from
    this (g.outArcs (dense[uDense.val]'uDense.isLt)) j hj hAll hjEmit
  intro l
  induction l with
  | nil => intro k hk; cases hk
  | cons w ws ih =>
    intro k hk hl hkF
    have hw : dense.idxOf w < dense.length := hl w List.mem_cons_self
    have hws : ∀ z ∈ ws, dense.idxOf z < dense.length := fun z hz => hl z (List.mem_cons_of_mem w hz)
    cases k with
    | zero =>
      simp only [List.filterMap_cons, hw, ↓reduceDIte, List.getElem_cons_zero]
    | succ k' =>
      simp only [List.filterMap_cons, hw, ↓reduceDIte, List.getElem_cons_succ] at hkF ⊢
      exact ih k' (Nat.lt_of_succ_lt_succ hk) hws (Nat.lt_of_succ_lt_succ hkF)

theorem emittedPrefixList_step_j {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense)
    {u j : Nat} (hu : u < dense.length) (hj : j < (g.outArcs (dense[u]'hu)).length) :
    let vOrig := (g.outArcs (dense[u]'hu))[j]'hj
    let hv : dense.idxOf vOrig < dense.length :=
      List.idxOf_lt_length_of_mem
        (S.mem_reach vOrig (initiallyReachable_extend (S.reach_mem u hu) (List.getElem_mem hj)))
    emittedPrefixList S u (j + 1) =
      emittedPrefixList S u j ++ [S.emittedArc ⟨u, hu⟩ ⟨dense.idxOf vOrig, hv⟩] := by
  intro vOrig hv
  unfold emittedPrefixList
  simp only [hu, ↓reduceDIte]
  have hjEmit : j < (S.emitForU ⟨u, hu⟩).length := by rw [S.emitForU_length]; exact hj
  rw [List.take_succ_eq_append_getElem hjEmit, List.append_assoc, emitForU_getElem S ⟨u, hu⟩ j hj]

private theorem list_flatMap_take_length_le {α β : Type _} (f : α → List β) :
    ∀ (xs : List α) (k : Nat), ((xs.take k).flatMap f).length ≤ (xs.flatMap f).length
  | [], _ => by simp
  | x :: xs, 0 => by simp
  | x :: xs, k + 1 => by
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
    exact Nat.add_le_add_left (list_flatMap_take_length_le f xs k) _

theorem emittedPrefixList_length_le {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (u j : Nat) :
    (emittedPrefixList S u j).length ≤ g.arcCount := by
  unfold emittedPrefixList
  rw [List.length_append]
  by_cases hu : u < dense.length
  · simp only [hu, ↓reduceDIte]
    have h1 : ((S.emitForU ⟨u, hu⟩).take j).length ≤ (S.emitForU ⟨u, hu⟩).length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    have h2 : (((List.finRange dense.length).take u).flatMap S.emitForU).length +
        (S.emitForU ⟨u, hu⟩).length =
        (((List.finRange dense.length).take (u + 1)).flatMap S.emitForU).length := by
      rw [list_take_succ_finRange dense.length u hu, List.flatMap_append, List.length_append]
      simp
    have h3 := list_flatMap_take_length_le S.emitForU (List.finRange dense.length) (u + 1)
    have h4 : ((List.finRange dense.length).flatMap S.emitForU).length = S.allEmittedArcs.length := rfl
    have h5 := S.allEmittedArcs_length_le
    omega
  · simp only [hu, ↓reduceDIte, List.length_nil, Nat.add_zero]
    have h3 := list_flatMap_take_length_le S.emitForU (List.finRange dense.length) u
    have h4 : ((List.finRange dense.length).flatMap S.emitForU).length = S.allEmittedArcs.length := rfl
    have h5 := S.allEmittedArcs_length_le
    omega

private structure CountQDegOuterInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (u : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 1
  uEq : (reg s r8).val = u
  uLe : u ≤ dense.length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + g.vertexCount ∨ emitBase + g.vertexCount + dense.length ≤ k) →
    s.data[k]? = origData[k]?
  counts : ∀ d : Fin dense.length,
    (s.data[emitBase + g.vertexCount + d.val]?).map Fin.val =
      some (((emittedPrefixList S u 0).filter (fun e => e.owner == d)).length)

private structure CountQDegInnerInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (u : Fin dense.length) (j : Nat)
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 12
  uEq : (reg s r8).val = u.val
  eIdxEq : (reg s r10).val = outPrefix g (dense[u.val]'u.isLt).val + j
  eEndEq : (reg s r11).val = outPrefix g (dense[u.val]'u.isLt).val + (g.outArcs (dense[u.val]'u.isLt)).length
  jLe : j ≤ (g.outArcs (dense[u.val]'u.isLt)).length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + g.vertexCount ∨ emitBase + g.vertexCount + dense.length ≤ k) →
    s.data[k]? = origData[k]?
  counts : ∀ d : Fin dense.length,
    (s.data[emitBase + g.vertexCount + d.val]?).map Fin.val =
      some (((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length)

private theorem countQDeg_inner_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (raw : RawDagInput input g r)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (origData[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Fin dense.length) (j : Nat)
    (hjLt : j < (g.outArcs (dense[u.val]'u.isLt)).length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : CountQDegInnerInv g r dense treeBase emitBase origData S u j s) :
    ∃ s', Steps (countQDegCode (hi := hi) (hw := hw)) input 21 s s' ∧
      CountQDegInnerInv g r dense treeBase emitBase origData S u (j + 1) s' := by
  let code := countQDegCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hInCap : rawDagInputCap g.vertexCount g.arcCount ≤ 2 ^ bits :=
    Nat.le_trans raw.cap_ge hi
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  have hTreeFit := S.fit
  let n := g.vertexCount
  let m := g.arcCount
  have hInCap' : 4 + n + m ≤ 2 ^ bits := by simpa [rawDagInputCap, n, m] using hInCap
  have hFitEmit' : emitBase + (3 * n + 3 * m + 3) ≤ origData.size := by
    simpa [emitterWorkWords, n, m] using hFitEmit
  let uOrig := dense[u.val]'u.isLt
  let vOrig := (g.outArcs uOrig)[j]'hjLt
  have hjLt' : j < (g.outArcs uOrig).length := hjLt
  have hvReach : g.InitiallyReachable r vOrig :=
    initiallyReachable_extend (S.reach_mem u.val u.isLt) (List.getElem_mem hjLt)
  have hvDenseMem : vOrig ∈ dense := S.mem_reach vOrig hvReach
  let vDense : Fin dense.length := ⟨dense.idxOf vOrig, List.idxOf_lt_length_of_mem hvDenseMem⟩
  let d := S.domParent vDense
  have hlt12 : (reg s r10).val < (reg s r11).val := by
    rw [inv.eIdxEq, inv.eEndEq]; omega
  have h12 := step16_branchLt_true code input inv.pcEq rfl (by rw [countQDegCode_size]; decide) hlt12
  let s13 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 13, regs_size := s.regs_size, data_size := s.data_size }
  have hpc13 : s13.pc = 13 := rfl
  obtain ⟨s14, h13, hpc14, h14d, h14o, h14m⟩ := step16_add code input hpc13 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s15, h14, hpc15, h15d, h15o, h15m⟩ := step16_add code input hpc14 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s16, h15, hpc16, h16d, h16o, h16m⟩ := step16_add code input hpc15 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s17, h16, hpc17, h17d, h17o, h17m⟩ := step16_add code input hpc16 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s18, h17, hpc18, h18d, h18o, h18m⟩ := step16_add code input hpc17 rfl (by rw [countQDegCode_size]; decide)
  have hOutBnd : outPrefix g uOrig.val + j < m := by
    have h1 : outPrefix g (uOrig.val + 1) ≤ outPrefix g g.vertexCount := outPrefix_mono g uOrig.isLt
    rw [outPrefix_succ_lt g uOrig, outPrefix_vertexCount] at h1
    change outPrefix g uOrig.val + j < g.arcCount; omega
  have hN : (reg s rN).val = n := inv.regs.consts.nVal
  have hOne : (reg s rOne).val = 1 := inv.regs.consts.one
  have hEidx : (reg s r10).val = outPrefix g uOrig.val + j := inv.eIdxEq
  have hInUnfold : rawDagInputCap n m = 4 + n + m := rfl
  have hr14 : (reg s14 r12).val = n + (outPrefix g uOrig.val + j) := by
    change (reg s rN).val = n at hN
    rw [h14d, add_no_wrap _ _ (by change (reg s rN).val + (reg s r10).val < 2 ^ bits; rw [hN, hEidx]; omega)]
    change (reg s rN).val + (reg s r10).val = _; rw [hN, hEidx]
  have hr15 : (reg s15 r12).val = n + (outPrefix g uOrig.val + j) + 1 := by
    have h14_1 : (reg s14 rOne).val = 1 := by rw [h14o _ (by decide)]; exact hOne
    rw [h15d, add_no_wrap _ _ (by rw [hr14, h14_1]; omega), hr14, h14_1]
  have hr16 : (reg s16 r12).val = n + (outPrefix g uOrig.val + j) + 2 := by
    have h15_1 : (reg s15 rOne).val = 1 := by rw [h15o _ (by decide), h14o _ (by decide)]; exact hOne
    rw [h16d, add_no_wrap _ _ (by rw [hr15, h15_1]; omega), hr15, h15_1]
  have hr17 : (reg s17 r12).val = n + (outPrefix g uOrig.val + j) + 3 := by
    have h16_1 : (reg s16 rOne).val = 1 := by
      rw [h16o _ (by decide), h15o _ (by decide), h14o _ (by decide)]; exact hOne
    rw [h17d, add_no_wrap _ _ (by rw [hr16, h16_1]; omega), hr16, h16_1]
  have hr18 : (reg s18 r12).val = 4 + n + outPrefix g uOrig.val + j := by
    have h17_1 : (reg s17 rOne).val = 1 := by
      rw [h17o _ (by decide), h16o _ (by decide), h15o _ (by decide), h14o _ (by decide)]; exact hOne
    rw [h18d, add_no_wrap _ _ (by rw [hr17, h17_1]; omega), hr17, h17_1]; omega
  have hTargetMem : (input.words[(reg s18 r12).val]?).map Fin.val = some vOrig.val := by
    rw [hr18]; exact raw.out_targets uOrig j hjLt
  obtain ⟨wv, hwv, hwvVal⟩ := data_val_at hTargetMem
  obtain ⟨s19, h18, hpc19, h19d, h19o, h19m⟩ :=
    step16_loadInput code input hpc18 rfl hwv (by rw [countQDegCode_size]; decide)
  obtain ⟨s20, h19, hpc20, h20d, h20o, h20m⟩ := step16_add code input hpc19 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s21, h20, hpc21, h21d, h21o, h21m⟩ := step16_add code input hpc20 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s22, h21, hpc22, h22d, h22o, h22m⟩ := step16_add code input hpc21 rfl (by rw [countQDegCode_size]; decide)
  have h19_n : (reg s19 rN).val = n := by
    rw [h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide),
      h15o _ (by decide), h14o _ (by decide)]; exact hN
  have h20_n : (reg s20 rN).val = n := by rw [h20o _ (by decide)]; exact h19_n
  have h21_12 : (reg s21 r12).val = vOrig.val := by
    rw [h21o _ (by decide), h20o _ (by decide), h19d, hwvVal]
  have hr20 : (reg s20 r13).val = 2 * n := by
    rw [h20d, add_no_wrap _ _ (by rw [h19_n]; unfold emitterWorkWords at hFitEmit; omega), h19_n]; omega
  have hr21 : (reg s21 r13).val = 3 * n := by
    rw [h21d, add_no_wrap _ _ (by rw [hr20, h20_n]; unfold emitterWorkWords at hFitEmit; omega), hr20, h20_n]; omega
  have hr22 : (reg s22 r13).val = 3 * n + vOrig.val := by
    rw [h22d, add_no_wrap _ _ (by
      rw [hr21, h21_12]; unfold emitterWorkWords at hFitEmit; have := vOrig.isLt; omega), hr21, h21_12]
  have hS22Data : s22.data = s.data := by
    rw [h22m, h21m, h20m, h19m, h18m, h17m, h16m, h15m, h14m]
  have hVDensePlusMem : (s22.data[(reg s22 r13).val]?).map Fin.val = some (vDense.val + 1) := by
    rw [hr22, hS22Data]
    have hDisj : 3 * n + vOrig.val < emitBase + n ∨ emitBase + n + dense.length ≤ 3 * n + vOrig.val := by
      left; have := vOrig.isLt; omega
    have hOrigEq : origToDensePlusOneBase g.vertexCount g.arcCount + vOrig.val = 3 * n + vOrig.val := by
      unfold origToDensePlusOneBase; simp [n]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (by rw [← hOrigEq]; exact hOrigToDense vOrig hvReach)
  obtain ⟨wvp, hwvp, hwvpVal⟩ := data_val_at hVDensePlusMem
  obtain ⟨s23, h22, hpc23, h23d, h23o, h23m⟩ :=
    step16_loadData code input hpc22 rfl hwvp (by rw [countQDegCode_size]; decide)
  obtain ⟨s24, h23, hpc24, h24d, h24o, h24m⟩ := step16_sub code input hpc23 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s25, h24, hpc25, h25d, h25o, h25m⟩ := step16_add code input hpc24 rfl (by rw [countQDegCode_size]; decide)
  have h23_1 : (reg s23 rOne).val = 1 := by
    rw [h23o _ (by decide), h22o _ (by decide), h21o _ (by decide), h20o _ (by decide),
      h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide),
      h15o _ (by decide), h14o _ (by decide)]
    exact hOne
  have hr24 : (reg s24 r13).val = vDense.val := by
    have h23_13 : (reg s23 r13).val = vDense.val + 1 := by rw [h23d, hwvpVal]
    rw [h24d, sub_exact _ _ (by rw [h23_13, h23_1]; omega), h23_13, h23_1]; omega
  have hr25 : (reg s25 r13).val = treeBase + vDense.val := by
    have h24_6 : (reg s24 r6).val = treeBase := by
      rw [h24o _ (by decide), h23o _ (by decide), h22o _ (by decide), h21o _ (by decide),
        h20o _ (by decide), h19o _ (by decide), h18o _ (by decide), h17o _ (by decide),
        h16o _ (by decide), h15o _ (by decide), h14o _ (by decide)]
      exact inv.regs.treeBaseVal
    rw [h25d, add_no_wrap _ _ (by rw [hr24, h24_6]; unfold staticTreeWords at hTreeFit; have := vDense.isLt; omega), h24_6, hr24]
  have hS25Data : s25.data = s.data := by rw [h25m, h24m, h23m, hS22Data]
  have hDomMem : (s25.data[(reg s25 r13).val]?).map Fin.val = some d.val := by
    rw [hr25, hS25Data]
    have hDisj : treeBase + vDense.val < emitBase + n ∨ emitBase + n + dense.length ≤ treeBase + vDense.val := by
      unfold staticTreeWords emitterWorkWords at *
      have := vDense.isLt
      rcases hDisjTreeEmit with hl | hr
      · left; omega
      · right; omega
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (S.domParent_mem vDense)
  obtain ⟨wd, hwd, hwdVal⟩ := data_val_at hDomMem
  obtain ⟨s26, h25, hpc26, h26d, h26o, h26m⟩ :=
    step16_loadData code input hpc25 rfl hwd (by rw [countQDegCode_size]; decide)
  obtain ⟨s27, h26, hpc27, h27d, h27o, h27m⟩ := step16_add code input hpc26 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s28, h27, hpc28, h28d, h28o, h28m⟩ := step16_add code input hpc27 rfl (by rw [countQDegCode_size]; decide)
  have hr27 : (reg s27 r14).val = emitBase + n := by
    have h26_7 : (reg s26 r7).val = emitBase := by
      rw [h26o _ (by decide), h25o _ (by decide), h24o _ (by decide), h23o _ (by decide),
        h22o _ (by decide), h21o _ (by decide), h20o _ (by decide), h19o _ (by decide),
        h18o _ (by decide), h17o _ (by decide), h16o _ (by decide), h15o _ (by decide), h14o _ (by decide)]
      exact inv.regs.emitBaseVal
    have h26_n : (reg s26 rN).val = n := by
      rw [h26o _ (by decide), h25o _ (by decide), h24o _ (by decide), h23o _ (by decide),
        h22o _ (by decide), h21o _ (by decide)]
      exact h20_n
    rw [h27d, add_no_wrap _ _ (by rw [h26_7, h26_n]; unfold emitterWorkWords at hFitEmit; omega), h26_7, h26_n]
  have hr28 : (reg s28 r14).val = emitBase + n + d.val := by
    have h27_13 : (reg s27 r13).val = d.val := by rw [h27o _ (by decide), h26d, hwdVal]
    rw [h28d, add_no_wrap _ _ (by rw [hr27, h27_13]; unfold emitterWorkWords at hFitEmit; have := d.isLt; omega), hr27, h27_13]
  have hS28Data : s28.data = s.data := by rw [h28m, h27m, h26m, hS25Data]
  have hCntMem : (s28.data[(reg s28 r14).val]?).map Fin.val =
      some (((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length) := by
    rw [hr28, hS28Data]; exact inv.counts d
  obtain ⟨wcnt, hwcnt, hwcntVal⟩ := data_val_at hCntMem
  obtain ⟨s29, h28, hpc29, h29d, h29o, h29m⟩ :=
    step16_loadData code input hpc28 rfl hwcnt (by rw [countQDegCode_size]; decide)
  obtain ⟨s30, h29, hpc30, h30d, h30o, h30m⟩ := step16_add code input hpc29 rfl (by rw [countQDegCode_size]; decide)
  have hCntLe : ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length + 1 ≤ m := by
    have h1 := emittedPrefixList_step_j S u.isLt hjLt
    have hLen : ((emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d)).length =
        ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length + 1 := by
      rw [h1, List.filter_append, List.length_append]
      have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d) = true :=
        beq_iff_eq.mpr rfl
      change ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length +
          ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter (fun e => e.owner == d)).length =
        ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length + 1
      have hFilt : [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter
          (fun e : EmittedArc dense.length => e.owner == d) =
          [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] :=
        filter_singleton_true _ _ hOwn
      rw [hFilt, List.length_singleton]
    have hLe := Nat.le_trans (List.length_filter_le (fun e => e.owner == d) (emittedPrefixList S u.val (j + 1)))
      (emittedPrefixList_length_le S u.val (j + 1))
    change _ ≤ g.arcCount at hLe
    change _ + 1 ≤ g.arcCount
    omega
  have hr30 : (reg s30 r15).val = ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length + 1 := by
    have h29_1 : (reg s29 rOne).val = 1 := by
      rw [h29o _ (by decide), h28o _ (by decide), h27o _ (by decide), h26o _ (by decide),
        h25o _ (by decide), h24o _ (by decide)]
      exact h23_1
    have h29_15 : (reg s29 r15).val = ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length := by
      rw [h29d, hwcntVal]
    rw [h30d, add_no_wrap _ _ (by rw [h29_15, h29_1]; omega), h29_15, h29_1]
  have hBnd30 : (reg s30 r14).val < s30.data.size := by
    have h30_14 : (reg s30 r14).val = emitBase + n + d.val := by rw [h30o _ (by decide), h29o _ (by decide)]; exact hr28
    rw [h30_14, h30m, h29m, hS28Data]
    have hSz : s.data.size = origData.size := inv.dataSize
    rw [hSz]; unfold emitterWorkWords at hFitEmit; have := d.isLt; omega
  obtain ⟨s31, h30, hpc31, h31regs, h31data⟩ := step16_storeData code input hpc30 rfl (by rw [countQDegCode_size]; decide) hBnd30
  obtain ⟨s32, h31, hpc32, h32d, h32o, h32m⟩ := step16_add code input hpc31 rfl (by rw [countQDegCode_size]; decide)
  have h32 := step16_goto code input hpc32 rfl (by rw [countQDegCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s32.regs, data := s32.data, pc := 12, regs_size := s32.regs_size, data_size := s32.data_size }
  have hSteps : Steps code input 21 s s' :=
    Steps.cons h12 <| Steps.cons h13 <| Steps.cons h14 <| Steps.cons h15 <|
    Steps.cons h16 <| Steps.cons h17 <| Steps.cons h18 <| Steps.cons h19 <|
    Steps.cons h20 <| Steps.cons h21 <| Steps.cons h22 <| Steps.cons h23 <|
    Steps.cons h24 <| Steps.cons h25 <| Steps.cons h26 <| Steps.cons h27 <|
    Steps.cons h28 <| Steps.cons h29 <| Steps.cons h30 <| Steps.cons h31 <| Steps.cons h32 (Steps.zero s')
  have h30_14 : (reg s30 r14).val = emitBase + n + d.val := by rw [h30o _ (by decide), h29o _ (by decide)]; exact hr28
  have hDataEq : s'.data = s.data.set (emitBase + n + d.val) (reg s30 r15)
      (by have hSz : s30.data.size = s.data.size := by rw [h30m, h29m, hS28Data]
          rw [← h30_14, ← hSz]; exact hBnd30) := by
    change s32.data = _
    rw [h32m, h31data]
    exact array_set_congr (by rw [h30m, h29m, hS28Data]) h30_14 rfl
  have hRegPres : ∀ r' : Fin 16, r' ≠ r10 → r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 →
      reg s' r' = reg s r' := by
    intro r' h10' h12' h13' h14' h15'
    change reg s32 r' = reg s r'
    rw [h32o _ h10', reg_eq_of_regs_eq h31regs r', h30o _ h15', h29o _ h15', h28o _ h14',
      h27o _ h14', h26o _ h13', h25o _ h13', h24o _ h13', h23o _ h13', h22o _ h13',
      h21o _ h13', h20o _ h13', h19o _ h12', h18o _ h12', h17o _ h12', h16o _ h12',
      h15o _ h12', h14o _ h12']
    rfl
  refine ⟨s', hSteps, ?_⟩
  refine
    { pcEq := rfl
      uEq := by rw [hRegPres r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.uEq
      eIdxEq := by
        change (reg s32 r10).val = _
        have h31_10 : (reg s31 r10).val = outPrefix g uOrig.val + j := by
          rw [reg_eq_of_regs_eq h31regs r10, h30o _ (by decide), h29o _ (by decide), h28o _ (by decide),
            h27o _ (by decide), h26o _ (by decide), h25o _ (by decide), h24o _ (by decide),
            h23o _ (by decide), h22o _ (by decide), h21o _ (by decide), h20o _ (by decide),
            h19o _ (by decide), h18o _ (by decide), h17o _ (by decide), h16o _ (by decide),
            h15o _ (by decide), h14o _ (by decide)]
          exact inv.eIdxEq
        have h31_1 : (reg s31 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h31regs rOne, h30o _ (by decide), h29o _ (by decide), h28o _ (by decide),
            h27o _ (by decide), h26o _ (by decide), h25o _ (by decide), h24o _ (by decide)]
          exact h23_1
        rw [h32d, add_no_wrap _ _ (by rw [h31_10, h31_1]; omega), h31_10, h31_1]; rfl
      eEndEq := by rw [hRegPres r11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.eEndEq
      jLe := hjLt
      regs :=
        { consts :=
            { zero := by rw [hRegPres rZero (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPres rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPres rN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPres rM (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPres rRoot (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPres r5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPres r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPres r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [hDataEq, Array.size_set]; exact inv.dataSize
      outsidePres := by
        intro k hk
        have hne : k ≠ emitBase + n + d.val := by
          have := d.isLt; rcases hk with hl | hr <;> omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
        exact inv.outsidePres k hk
      counts := by
        intro d'
        have hStepJ := emittedPrefixList_step_j S u.isLt hjLt
        rw [hStepJ, List.filter_append, List.length_append]
        by_cases hdEq : d' = d
        · have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d') = true :=
            beq_iff_eq.mpr hdEq.symm
          change (s'.data[emitBase + n + d'.val]?).map Fin.val =
            some (((emittedPrefixList S u.val j).filter (fun e => e.owner == d')).length +
              ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter (fun e => e.owner == d')).length)
          have hFilt : [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter
              (fun e : EmittedArc dense.length => e.owner == d') =
              [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] :=
            filter_singleton_true _ _ hOwn
          rw [hFilt, List.length_singleton, hdEq, hDataEq,
            array_set_getElem?_same, Option.map_some, hr30]
        · have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d') = false :=
            beq_false_of_ne (fun e => hdEq e.symm)
          have hne : emitBase + n + d'.val ≠ emitBase + n + d.val := by
            intro hEq; exact hdEq (Fin.ext (by omega))
          change (s'.data[emitBase + n + d'.val]?).map Fin.val =
            some (((emittedPrefixList S u.val j).filter (fun e => e.owner == d')).length +
              ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter (fun e => e.owner == d')).length)
          have hFilt : [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter
              (fun e : EmittedArc dense.length => e.owner == d') = [] :=
            filter_singleton_false _ _ hOwn
          rw [hFilt, List.length_nil, Nat.add_zero, hDataEq,
            array_set_getElem?_ne _ _ _ _ _ hne]
          change (s.data[emitBase + g.vertexCount + d'.val]?).map Fin.val = _
          exact inv.counts d' }

private theorem countQDeg_outer_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (raw : RawDagInput input g r)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hDenseToOrig : ∀ u' : Fin dense.length,
      (origData[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (origData[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Nat) (hu : u < dense.length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : CountQDegOuterInv g r dense treeBase emitBase origData S u s) :
    ∃ s', Steps (countQDegCode (hi := hi) (hw := hw)) input
        (14 + 21 * (g.outArcs (dense[u]'hu)).length) s s' ∧
      CountQDegOuterInv g r dense treeBase emitBase origData S (u + 1) s' := by
  let code := countQDegCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  let n := g.vertexCount
  let uFin : Fin dense.length := ⟨u, hu⟩
  let uOrig := dense[u]'hu
  have hlt1 : (reg s r8).val < (reg s r5).val := by rw [inv.uEq, inv.regs.qVal]; exact hu
  have h1 := step16_branchLt_true code input inv.pcEq rfl (by rw [countQDegCode_size]; decide) hlt1
  let s2 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 2, regs_size := s.regs_size, data_size := s.data_size }
  have hpc2 : s2.pc = 2 := rfl
  obtain ⟨s3, h2, hpc3, h3d, h3o, h3m⟩ := step16_add code input hpc2 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s4, h3, hpc4, h4d, h4o, h4m⟩ := step16_add code input hpc3 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s5, h4, hpc5, h5d, h5o, h5m⟩ := step16_add code input hpc4 rfl (by rw [countQDegCode_size]; decide)
  have hN : (reg s rN).val = n := inv.regs.consts.nVal
  have hOne : (reg s rOne).val = 1 := inv.regs.consts.one
  have hr3 : (reg s3 r9).val = 2 * n := by
    rw [h3d, add_no_wrap _ _ (by change (reg s rN).val + (reg s rN).val < _; rw [hN]; unfold emitterWorkWords at hFitEmit; omega)]
    change (reg s rN).val + (reg s rN).val = _; rw [hN]; omega
  have hr4 : (reg s4 r9).val = 4 * n := by
    rw [h4d, add_no_wrap _ _ (by rw [hr3]; unfold emitterWorkWords at hFitEmit; omega), hr3]; omega
  have hr5 : (reg s5 r9).val = 4 * n + u := by
    have h4_8 : (reg s4 r8).val = u := by rw [h4o _ (by decide), h3o _ (by decide)]; exact inv.uEq
    rw [h5d, add_no_wrap _ _ (by rw [hr4, h4_8]; unfold emitterWorkWords at hFitEmit; omega), hr4, h4_8]
  have hS5Data : s5.data = s.data := by rw [h5m, h4m, h3m]
  have hDenseMem : (s5.data[(reg s5 r9).val]?).map Fin.val = some uOrig.val := by
    rw [hr5, hS5Data]
    have hDisj : 4 * n + u < emitBase + n ∨ emitBase + n + dense.length ≤ 4 * n + u := by left; omega
    have hDenseEq : denseToOrigBase g.vertexCount g.arcCount + uFin.val = 4 * n + u := by
      unfold denseToOrigBase; simp [n, uFin]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (by rw [← hDenseEq]; exact hDenseToOrig uFin)
  obtain ⟨wu, hwu, hwuVal⟩ := data_val_at hDenseMem
  obtain ⟨s6, h5, hpc6, h6d, h6o, h6m⟩ :=
    step16_loadData code input hpc5 rfl hwu (by rw [countQDegCode_size]; decide)
  obtain ⟨s7, h6, hpc7, h7d, h7o, h7m⟩ := step16_add code input hpc6 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s8, h7, hpc8, h8d, h8o, h8m⟩ := step16_add code input hpc7 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s9, h8, hpc9, h9d, h9o, h9m⟩ := step16_add code input hpc8 rfl (by rw [countQDegCode_size]; decide)
  obtain ⟨s10, h9, hpc10, h10d, h10o, h10m⟩ := step16_add code input hpc9 rfl (by rw [countQDegCode_size]; decide)
  have hInCap : rawDagInputCap n g.arcCount ≤ 2 ^ bits := Nat.le_trans raw.cap_ge hi
  have hInUnfold : rawDagInputCap n g.arcCount = 4 + n + g.arcCount := rfl
  have h6_1 : (reg s6 rOne).val = 1 := by
    rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide)]; exact hOne
  have hr7 : (reg s7 r10).val = uOrig.val + 1 := by
    have h6_9 : (reg s6 r9).val = uOrig.val := by rw [h6d, hwuVal]
    rw [h7d, add_no_wrap _ _ (by rw [h6_9, h6_1]; have := uOrig.isLt; omega), h6_9, h6_1]
  have hr8 : (reg s8 r10).val = uOrig.val + 2 := by
    have h7_1 : (reg s7 rOne).val = 1 := by rw [h7o _ (by decide)]; exact h6_1
    rw [h8d, add_no_wrap _ _ (by rw [hr7, h7_1]; have := uOrig.isLt; omega), hr7, h7_1]
  have hr9 : (reg s9 r10).val = uOrig.val + 3 := by
    have h8_1 : (reg s8 rOne).val = 1 := by rw [h8o _ (by decide), h7o _ (by decide)]; exact h6_1
    rw [h9d, add_no_wrap _ _ (by rw [hr8, h8_1]; have := uOrig.isLt; omega), hr8, h8_1]
  have hr10 : (reg s10 r11).val = uOrig.val + 4 := by
    have h9_1 : (reg s9 rOne).val = 1 := by
      rw [h9o _ (by decide), h8o _ (by decide), h7o _ (by decide)]; exact h6_1
    rw [h10d, add_no_wrap _ _ (by rw [hr9, h9_1]; have := uOrig.isLt; omega), hr9, h9_1]
  have hS9_10 : (reg s10 r10).val = 3 + uOrig.val := by rw [h10o _ (by decide), hr9]; omega
  have hPref0Mem : (input.words[(reg s10 r10).val]?).map Fin.val = some (outPrefix g uOrig.val) := by
    rw [hS9_10]; exact raw.out_off uOrig.val (Nat.le_of_lt uOrig.isLt)
  obtain ⟨wp0, hwp0, hwp0Val⟩ := data_val_at hPref0Mem
  obtain ⟨s11, h10, hpc11, h11d, h11o, h11m⟩ :=
    step16_loadInput code input hpc10 rfl hwp0 (by rw [countQDegCode_size]; decide)
  have hS11_11 : (reg s11 r11).val = 3 + (uOrig.val + 1) := by rw [h11o _ (by decide), hr10]; omega
  have hPref1Mem : (input.words[(reg s11 r11).val]?).map Fin.val = some (outPrefix g (uOrig.val + 1)) := by
    rw [hS11_11]; exact raw.out_off (uOrig.val + 1) uOrig.isLt
  obtain ⟨wp1, hwp1, hwp1Val⟩ := data_val_at hPref1Mem
  obtain ⟨s12, h11, hpc12, h12d, h12o, h12m⟩ :=
    step16_loadInput code input hpc11 rfl hwp1 (by rw [countQDegCode_size]; decide)
  have hPre : Steps code input 11 s s12 :=
    Steps.cons h1 <| Steps.cons h2 <| Steps.cons h3 <| Steps.cons h4 <| Steps.cons h5 <|
    Steps.cons h6 <| Steps.cons h7 <| Steps.cons h8 <| Steps.cons h9 <| Steps.cons h10 <|
    Steps.cons h11 (Steps.zero s12)
  have hS12Data : s12.data = s.data := by rw [h12m, h11m, h10m, h9m, h8m, h7m, h6m, hS5Data]
  have hRegPresPre : ∀ r' : Fin 16, r' ≠ r9 → r' ≠ r10 → r' ≠ r11 → reg s12 r' = reg s r' := by
    intro r' h9' h10' h11'
    rw [h12o _ h11', h11o _ h10', h10o _ h11', h9o _ h10', h8o _ h10', h7o _ h10',
      h6o _ h9', h5o _ h9', h4o _ h9', h3o _ h9']
    rfl
  have hInner0 : CountQDegInnerInv g r dense treeBase emitBase origData S uFin 0 s12 :=
    { pcEq := hpc12
      uEq := by rw [hRegPresPre r8 (by decide) (by decide) (by decide)]; exact inv.uEq
      eIdxEq := by rw [h12o _ (by decide), h11d, hwp0Val]; rfl
      eEndEq := by rw [h12d, hwp1Val, outPrefix_succ_lt g uOrig]
      jLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [hRegPresPre rZero (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPresPre rOne (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPresPre rN (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPresPre rM (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPresPre rRoot (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPresPre r5 (by decide) (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPresPre r6 (by decide) (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPresPre r7 (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [hS12Data]; exact inv.dataSize
      outsidePres := by intro k hk; rw [hS12Data]; exact inv.outsidePres k hk
      counts := by intro d'; rw [hS12Data]; exact inv.counts d' }
  have hRunInner : ∀ rem j st,
      (g.outArcs uOrig).length - j = rem →
      CountQDegInnerInv g r dense treeBase emitBase origData S uFin j st →
      ∃ stEnd, Steps code input (21 * rem) st stEnd ∧
        CountQDegInnerInv g r dense treeBase emitBase origData S uFin (g.outArcs uOrig).length stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro j st hrem hinv
      have hLeJ : j ≤ (g.outArcs uOrig).length := hinv.jLe
      have hjeq : j = (g.outArcs uOrig).length := by omega
      subst hjeq
      exact ⟨st, by simp only [Nat.mul_zero]; exact Steps.zero st, hinv⟩
    | succ rem ih =>
      intro j st hrem hinv
      have hLeJ : j ≤ (g.outArcs uOrig).length := hinv.jLe
      have hjlt : j < (g.outArcs uOrig).length := by omega
      obtain ⟨st1, hstep1, hinv1⟩ := countQDeg_inner_step input raw S hOrigToDense
        hFitEmit hDisjReachEmit hDisjTreeEmit uFin j hjlt hinv
      obtain ⟨stEnd, hstepRest, hinvEnd⟩ := ih (j + 1) st1 (by omega) hinv1
      have hMul : 21 * (rem + 1) = 21 + 21 * rem := by omega
      rw [hMul]
      exact ⟨stEnd, hstep1.append hstepRest, hinvEnd⟩
  obtain ⟨sEndIn, hStepsIn, hInvIn⟩ := hRunInner (g.outArcs uOrig).length 0 s12 (Nat.sub_zero _) hInner0
  have hFalse : (reg sEndIn r11).val ≤ (reg sEndIn r10).val := by
    rw [hInvIn.eIdxEq, hInvIn.eEndEq]; exact Nat.le_refl _
  have h12f := step16_branchLt_false code input hInvIn.pcEq rfl (by rw [countQDegCode_size]; decide) hFalse
  let s33 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEndIn.regs, data := sEndIn.data, pc := 33, regs_size := sEndIn.regs_size, data_size := sEndIn.data_size }
  have hpc33 : s33.pc = 33 := rfl
  obtain ⟨s34, h33, hpc34, h34d, h34o, h34m⟩ := step16_add code input hpc33 rfl (by rw [countQDegCode_size]; decide)
  have h34 := step16_goto code input hpc34 rfl (by rw [countQDegCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s34.regs, data := s34.data, pc := 1, regs_size := s34.regs_size, data_size := s34.data_size }
  have hExit : Steps code input 3 sEndIn s' := Steps.cons h12f <| Steps.cons h33 <| Steps.cons h34 (Steps.zero s')
  have hTotal : 14 + 21 * (g.outArcs uOrig).length = 11 + 21 * (g.outArcs uOrig).length + 3 := by omega
  have hS'Data : s'.data = sEndIn.data := by change s34.data = _; rw [h34m]
  have hRegPresOut : ∀ r' : Fin 16, r' ≠ r8 → reg s' r' = reg sEndIn r' := by
    intro r' h8'; change reg s34 r' = reg sEndIn r'; rw [h34o _ h8']; rfl
  refine ⟨s', by rw [hTotal]; exact (hPre.append hStepsIn).append hExit, ?_⟩
  refine
    { pcEq := rfl
      uEq := by
        change (reg s34 r8).val = u + 1
        have h33_8 : (reg s33 r8).val = u := hInvIn.uEq
        have h33_1 : (reg s33 rOne).val = 1 := hInvIn.regs.consts.one
        rw [h34d, add_no_wrap _ _ (by rw [h33_8, h33_1]; omega), h33_8, h33_1]
      uLe := hu
      regs :=
        { consts :=
            { zero := by rw [hRegPresOut rZero (by decide)]; exact hInvIn.regs.consts.zero
              one := by rw [hRegPresOut rOne (by decide)]; exact hInvIn.regs.consts.one
              nVal := by rw [hRegPresOut rN (by decide)]; exact hInvIn.regs.consts.nVal
              mVal := by rw [hRegPresOut rM (by decide)]; exact hInvIn.regs.consts.mVal
              rootVal := by rw [hRegPresOut rRoot (by decide)]; exact hInvIn.regs.consts.rootVal }
          qVal := by rw [hRegPresOut r5 (by decide)]; exact hInvIn.regs.qVal
          treeBaseVal := by rw [hRegPresOut r6 (by decide)]; exact hInvIn.regs.treeBaseVal
          emitBaseVal := by rw [hRegPresOut r7 (by decide)]; exact hInvIn.regs.emitBaseVal }
      dataSize := by rw [hS'Data]; exact hInvIn.dataSize
      outsidePres := by intro k hk; rw [hS'Data]; exact hInvIn.outsidePres k hk
      counts := by
        intro d'
        rw [hS'Data, ← emittedPrefixList_step_u S hu]
        exact hInvIn.counts d' }

theorem run_countQDegPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (raw : RawDagInput input g r)
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s₀)
    (S : StaticTreeSlice s₀.data treeBase g r dense)
    (hDenseToOrig : ∀ u' : Fin dense.length,
      (s₀.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (s₀.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ s₀.data.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (hZeroes : ∀ j : Nat, j < dense.length →
      (s₀.data[emitBase + g.vertexCount + j]?).map Fin.val = some 0) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 14 * g.vertexCount + 21 * g.arcCount + 3 ∧
      PaperB.RamProgram.run (countQDegPhase (hi := hi) (hw := hw)).code input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase t ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase + g.vertexCount ∨ emitBase + g.vertexCount + dense.length ≤ k) →
        t.data[k]? = s₀.data[k]?) ∧
      (∀ d : Fin dense.length,
        (t.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (S.emittedArcs d).length) := by
  let code := countQDegCode (hi := hi) (hw := hw)
  let sInit := Phase.initial s₀
  have hpc0 : sInit.pc = 0 := rfl
  obtain ⟨s1, h0, hpc1, h1d, h1o, h1m⟩ := step16_mov code input hpc0 rfl (by rw [countQDegCode_size]; decide)
  have hInv0 : CountQDegOuterInv g r dense treeBase emitBase s₀.data S 0 s1 :=
    { pcEq := hpc1
      uEq := by rw [h1d]; exact hRegs.consts.zero
      uLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [h1o _ (by decide)]; exact hRegs.consts.zero
              one := by rw [h1o _ (by decide)]; exact hRegs.consts.one
              nVal := by rw [h1o _ (by decide)]; exact hRegs.consts.nVal
              mVal := by rw [h1o _ (by decide)]; exact hRegs.consts.mVal
              rootVal := by rw [h1o _ (by decide)]; exact hRegs.consts.rootVal }
          qVal := by rw [h1o _ (by decide)]; exact hRegs.qVal
          treeBaseVal := by rw [h1o _ (by decide)]; exact hRegs.treeBaseVal
          emitBaseVal := by rw [h1o _ (by decide)]; exact hRegs.emitBaseVal }
      dataSize := by rw [h1m]; rfl
      outsidePres := by intro k _; rw [h1m]; rfl
      counts := by
        intro d
        rw [emittedPrefixList_zero S, List.filter_nil, List.length_nil, h1m]
        exact hZeroes d.val d.isLt }
  have hRunOuter : ∀ rem u st, u + rem = dense.length →
      CountQDegOuterInv g r dense treeBase emitBase s₀.data S u st →
      ∃ stEnd stepsOuter,
        stepsOuter ≤ 14 * rem + 21 * (((List.finRange dense.length).drop u).map
          (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum ∧
        Steps code input stepsOuter st stEnd ∧
        CountQDegOuterInv g r dense treeBase emitBase s₀.data S dense.length stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro u st hrem hinv
      have huEq : u = dense.length := by omega
      subst huEq
      exact ⟨st, 0, Nat.zero_le _, Steps.zero st, hinv⟩
    | succ rem ih =>
      intro u st hrem hinv
      have huLt : u < dense.length := by omega
      obtain ⟨st1, hstep1, hinv1⟩ := countQDeg_outer_step input raw S hDenseToOrig hOrigToDense
        hFitEmit hDisjReachEmit hDisjTreeEmit u huLt hinv
      obtain ⟨stEnd, stepsRest, hBndRest, hStepRest, hInvEnd⟩ := ih (u + 1) st1 (by omega) hinv1
      have hDrop : ((List.finRange dense.length).drop u).map
            (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length) =
          (g.outArcs (dense[u]'huLt)).length ::
            ((List.finRange dense.length).drop (u + 1)).map
              (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length) := by
        have hEq : (List.finRange dense.length).drop u =
            ⟨u, huLt⟩ :: (List.finRange dense.length).drop (u + 1) := by
          have h1 : u < (List.finRange dense.length).length := by simp [huLt]
          rw [List.drop_eq_getElem_cons h1]
          simp
        rw [hEq, List.map_cons]
      refine ⟨stEnd, (14 + 21 * (g.outArcs (dense[u]'huLt)).length) + stepsRest, ?_, hstep1.append hStepRest, hInvEnd⟩
      rw [hDrop, List.sum_cons]
      omega
  obtain ⟨sEnd, stepsOuter, hBndOuter, hStepsOuter, hInvEnd⟩ := hRunOuter dense.length 0 s1 (Nat.zero_add _) hInv0
  have hFalseEnd : (reg sEnd r5).val ≤ (reg sEnd r8).val := by
    rw [hInvEnd.uEq, hInvEnd.regs.qVal]; exact Nat.le_refl _
  have h1f := step16_branchLt_false code input hInvEnd.pcEq rfl (by rw [countQDegCode_size]; decide) hFalseEnd
  let sHalt : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEnd.regs, data := sEnd.data, pc := 35, regs_size := sEnd.regs_size, data_size := sEnd.data_size }
  have hHalt : step code input sHalt = some (.halted sHalt) := step_halt_at (by rfl)
  have hFull := ((Steps.cons h0 (Steps.zero s1)).append hStepsOuter).append (Steps.cons h1f (Steps.zero sHalt))
  have hExec := hFull.halts hHalt
  refine ⟨sHalt, 1 + stepsOuter + 1 + 1, ?_, hExec, ?_, hInvEnd.dataSize, hInvEnd.outsidePres, ?_⟩
  · have hSumLe : (((List.finRange dense.length).map
        (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum) ≤ g.arcCount := by
      have h1 : ((List.finRange dense.length).map
          (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum = S.allEmittedArcs.length := by
        unfold StaticTreeSlice.allEmittedArcs
        rw [List.length_flatMap, List.map_congr_left (fun u' _ => (S.emitForU_length u').symm)]
      rw [h1]; exact S.allEmittedArcs_length_le
    have hDenseLe := S.length_le
    simp only [List.drop_zero] at hBndOuter
    omega
  · exact
      { consts :=
          { zero := hInvEnd.regs.consts.zero
            one := hInvEnd.regs.consts.one
            nVal := hInvEnd.regs.consts.nVal
            mVal := hInvEnd.regs.consts.mVal
            rootVal := hInvEnd.regs.consts.rootVal }
        qVal := hInvEnd.regs.qVal
        treeBaseVal := hInvEnd.regs.treeBaseVal
        emitBaseVal := hInvEnd.regs.emitBaseVal }
  · intro d
    have hc := hInvEnd.counts d
    rw [emittedPrefixList_end S] at hc
    exact hc

/-! #### Phase 4: `qStartPrefixPhase` (`qStart[0..Q]` & `qCursor[0..Q)` in `emitQDeg`) -/

def qStartPrefixCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    .mov r8 rZero,          -- 0: acc := 0
    .mov r9 rZero,          -- 1: d := 0
    .branchLt r9 r5 3 12,   -- 2: while d < Q
    .add r10 r7 rN,         -- 3: emitBase + n
    .add r10 r10 r9,        -- 4: emitBase + n + d
    .loadData r11 r10,      -- 5: deg = qDeg[d]
    .storeData r10 r8,      -- 6: qCursor[d] := acc (in qDeg slot)
    .add r12 r10 rN,        -- 7: emitBase + 2*n + d
    .storeData r12 r8,      -- 8: qStart[d] := acc
    .add r8 r8 r11,         -- 9: acc += deg
    .add r9 r9 rOne,        -- 10: d++
    .goto 2,                -- 11
    .add r12 r7 rN,         -- 12: emitBase + n
    .add r12 r12 rN,        -- 13: emitBase + 2*n
    .add r12 r12 r5,        -- 14: emitBase + 2*n + Q
    .storeData r12 r8,      -- 15: qStart[Q] := mReach
    .halt                   -- 16
  ]

def qStartPrefixPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast qStartPrefixCode 16 rfl rfl rfl

private theorem qStartPrefixCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (qStartPrefixCode (hi := hi) (hw := hw)).size = 17 := rfl

def qStartFn {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (d : Nat) : Nat :=
  (((List.finRange dense.length).take d).map (fun d' => (S.emittedArcs d').length)).sum

theorem qStartFn_zero {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) :
    qStartFn S 0 = 0 := by simp [qStartFn]

theorem qStartFn_succ {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) {d : Nat} (hd : d < dense.length) :
    qStartFn S (d + 1) = qStartFn S d + (S.emittedArcs ⟨d, hd⟩).length := by
  unfold qStartFn
  rw [list_take_succ_finRange dense.length d hd, List.map_append, List.sum_append]
  simp

theorem qStartFn_end {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) :
    qStartFn S dense.length = S.allEmittedArcs.length := by
  unfold qStartFn
  rw [List.take_of_length_le (by simp)]
  exact S.sum_emittedArcs_eq

theorem qStartFn_le_arcCount {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (d : Nat) :
    qStartFn S d ≤ g.arcCount := by
  have hEnd := qStartFn_end S
  have hLe := S.allEmittedArcs_length_le
  have hMono : qStartFn S d ≤ qStartFn S dense.length := by
    by_cases hd : d ≤ dense.length
    · suffices ∀ rem k, k + rem = dense.length → qStartFn S k ≤ qStartFn S dense.length from
        this (dense.length - d) d (by omega)
      intro rem
      induction rem with
      | zero =>
        intro k hk
        have hkEq : k = dense.length := by omega
        rw [hkEq]
        exact Nat.le_refl _
      | succ rem ih =>
        intro k hk
        have hlt : k < dense.length := by omega
        exact Nat.le_trans (by rw [qStartFn_succ S hlt]; exact Nat.le_add_right _ _) (ih (k + 1) (by omega))
    · unfold qStartFn
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
      exact Nat.le_refl _
  omega

private structure QStartPrefixInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (d : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 2
  accEq : (reg s r8).val = qStartFn S d
  dEq : (reg s r9).val = d
  dLe : d ≤ dense.length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + g.vertexCount ∨
      (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 2 * g.vertexCount) ∨
      emitBase + 2 * g.vertexCount + dense.length + 1 ≤ k) →
    s.data[k]? = origData[k]?
  cursorsDone : ∀ j : Nat, j < d →
    (s.data[emitBase + g.vertexCount + j]?).map Fin.val = some (qStartFn S j)
  startsDone : ∀ j : Nat, j < d →
    (s.data[emitBase + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)
  degsRem : ∀ j : Fin dense.length, d ≤ j.val →
    (s.data[emitBase + g.vertexCount + j.val]?).map Fin.val = some (S.emittedArcs j).length

private theorem qStartPrefix_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (d : Nat) (hd : d < dense.length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : QStartPrefixInv g r dense treeBase emitBase origData S d s) :
    ∃ s', Steps (qStartPrefixCode (hi := hi) (hw := hw)) input 10 s s' ∧
      QStartPrefixInv g r dense treeBase emitBase origData S (d + 1) s' := by
  let code := qStartPrefixCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  let n := g.vertexCount
  let dFin : Fin dense.length := ⟨d, hd⟩
  have hlt2 : (reg s r9).val < (reg s r5).val := by rw [inv.dEq, inv.regs.qVal]; exact hd
  have h2 := step16_branchLt_true code input inv.pcEq rfl (by rw [qStartPrefixCode_size]; decide) hlt2
  let s3 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 3, regs_size := s.regs_size, data_size := s.data_size }
  have hpc3 : s3.pc = 3 := rfl
  obtain ⟨s4, h3, hpc4, h4d, h4o, h4m⟩ := step16_add code input hpc3 rfl (by rw [qStartPrefixCode_size]; decide)
  obtain ⟨s5, h4, hpc5, h5d, h5o, h5m⟩ := step16_add code input hpc4 rfl (by rw [qStartPrefixCode_size]; decide)
  have hN : (reg s rN).val = n := inv.regs.consts.nVal
  have h7v : (reg s r7).val = emitBase := inv.regs.emitBaseVal
  have hr4 : (reg s4 r10).val = emitBase + n := by
    rw [h4d, add_no_wrap _ _ (by change (reg s r7).val + (reg s rN).val < _; rw [h7v, hN]; unfold emitterWorkWords at hFitEmit; omega)]
    change (reg s r7).val + (reg s rN).val = _; rw [h7v, hN]
  have hr5 : (reg s5 r10).val = emitBase + n + d := by
    have h4_9 : (reg s4 r9).val = d := by rw [h4o _ (by decide)]; exact inv.dEq
    rw [h5d, add_no_wrap _ _ (by rw [hr4, h4_9]; unfold emitterWorkWords at hFitEmit; omega), hr4, h4_9]
  have hS5Data : s5.data = s.data := by rw [h5m, h4m]
  have hDegMem : (s5.data[(reg s5 r10).val]?).map Fin.val = some (S.emittedArcs dFin).length := by
    rw [hr5, hS5Data]; exact inv.degsRem dFin (Nat.le_refl _)
  obtain ⟨wdeg, hwdeg, hwdegVal⟩ := data_val_at hDegMem
  obtain ⟨s6, h5, hpc6, h6d, h6o, h6m⟩ :=
    step16_loadData code input hpc5 rfl hwdeg (by rw [qStartPrefixCode_size]; decide)
  have hBnd6 : (reg s6 r10).val < s6.data.size := by
    have h6_10 : (reg s6 r10).val = emitBase + n + d := by rw [h6o _ (by decide)]; exact hr5
    rw [h6_10, h6m, hS5Data]
    have hSz : s.data.size = origData.size := inv.dataSize
    rw [hSz]; unfold emitterWorkWords at hFitEmit; omega
  obtain ⟨s7, h6, hpc7, h7regs, h7data⟩ := step16_storeData code input hpc6 rfl (by rw [qStartPrefixCode_size]; decide) hBnd6
  obtain ⟨s8, h7, hpc8, h8d, h8o, h8m⟩ := step16_add code input hpc7 rfl (by rw [qStartPrefixCode_size]; decide)
  have hr8 : (reg s8 r12).val = emitBase + 2 * n + d := by
    have h7_10 : (reg s7 r10).val = emitBase + n + d := by
      rw [reg_eq_of_regs_eq h7regs r10, h6o _ (by decide)]; exact hr5
    have h7_n : (reg s7 rN).val = n := by
      rw [reg_eq_of_regs_eq h7regs rN, h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact hN
    rw [h8d, add_no_wrap _ _ (by rw [h7_10, h7_n]; unfold emitterWorkWords at hFitEmit; omega), h7_10, h7_n]; omega
  have hBnd8 : (reg s8 r12).val < s8.data.size := by
    rw [hr8, h8m, h7data, Array.size_set, h6m, hS5Data]
    have hSz : s.data.size = origData.size := inv.dataSize
    rw [hSz]; unfold emitterWorkWords at hFitEmit; omega
  obtain ⟨s9, h8, hpc9, h9regs, h9data⟩ := step16_storeData code input hpc8 rfl (by rw [qStartPrefixCode_size]; decide) hBnd8
  obtain ⟨s10, h9, hpc10, h10d, h10o, h10m⟩ := step16_add code input hpc9 rfl (by rw [qStartPrefixCode_size]; decide)
  obtain ⟨s11, h10, hpc11, h11d, h11o, h11m⟩ := step16_add code input hpc10 rfl (by rw [qStartPrefixCode_size]; decide)
  have h11 := step16_goto code input hpc11 rfl (by rw [qStartPrefixCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s11.regs, data := s11.data, pc := 2, regs_size := s11.regs_size, data_size := s11.data_size }
  have hSteps : Steps code input 10 s s' :=
    Steps.cons h2 <| Steps.cons h3 <| Steps.cons h4 <| Steps.cons h5 <|
    Steps.cons h6 <| Steps.cons h7 <| Steps.cons h8 <| Steps.cons h9 <|
    Steps.cons h10 <| Steps.cons h11 (Steps.zero s')
  have hAccSucc : qStartFn S (d + 1) = qStartFn S d + (S.emittedArcs dFin).length := qStartFn_succ S hd
  have hAccLe : qStartFn S (d + 1) ≤ g.arcCount := qStartFn_le_arcCount S (d + 1)
  have hArcPow : g.arcCount < 2 ^ bits := by
    have := Nat.le_trans (qStartFn_le_arcCount S (d + 1)) (Nat.le_refl _)
    unfold emitterWorkWords at hFitEmit; omega
  have hAccVal : (reg s6 r8).val = qStartFn S d := by
    rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact inv.accEq
  have hS8_8 : (reg s8 r8).val = qStartFn S d := by
    rw [h8o _ (by decide), reg_eq_of_regs_eq h7regs r8]; exact hAccVal
  have h6_10 : (reg s6 r10).val = emitBase + n + d := by rw [h6o _ (by decide)]; exact hr5
  have hDataEq : s'.data = (s.data.set (emitBase + n + d) (reg s6 r8)
        (by have hSz : s6.data.size = s.data.size := by rw [h6m, hS5Data]
            rw [← h6_10, ← hSz]; exact hBnd6)).set
      (emitBase + 2 * n + d) (reg s8 r8)
      (by
        rw [Array.size_set]
        have hSz : s8.data.size = s.data.size := by rw [h8m, h7data, Array.size_set, h6m, hS5Data]
        rw [← hr8, ← hSz]
        exact hBnd8) := by
    change s11.data = _
    rw [h11m, h10m, h9data]
    exact array_set_congr
      (by rw [h8m, h7data]; exact array_set_congr (by rw [h6m, hS5Data]) h6_10 rfl) hr8 rfl
  have hRegPres : ∀ r' : Fin 16, r' ≠ r8 → r' ≠ r9 → r' ≠ r10 → r' ≠ r11 → r' ≠ r12 →
      reg s' r' = reg s r' := by
    intro r' h8' h9' h10' h11' h12'
    change reg s11 r' = reg s r'
    rw [h11o _ h9', h10o _ h8', reg_eq_of_regs_eq h9regs r', h8o _ h12',
      reg_eq_of_regs_eq h7regs r', h6o _ h11', h5o _ h10', h4o _ h10']
    rfl
  refine ⟨s', hSteps, ?_⟩
  refine
    { pcEq := rfl
      accEq := by
        change (reg s11 r8).val = qStartFn S (d + 1)
        have h9_8 : (reg s9 r8).val = qStartFn S d := by rw [reg_eq_of_regs_eq h9regs r8]; exact hS8_8
        have h9_11 : (reg s9 r11).val = (S.emittedArcs dFin).length := by
          rw [reg_eq_of_regs_eq h9regs r11, h8o _ (by decide), reg_eq_of_regs_eq h7regs r11, h6d, hwdegVal]
        rw [h11o _ (by decide), h10d, add_no_wrap _ _ (by rw [h9_8, h9_11]; omega), h9_8, h9_11, hAccSucc]
      dEq := by
        change (reg s11 r9).val = d + 1
        have h10_9 : (reg s10 r9).val = d := by
          rw [h10o _ (by decide), reg_eq_of_regs_eq h9regs r9, h8o _ (by decide),
            reg_eq_of_regs_eq h7regs r9, h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]
          exact inv.dEq
        have h10_1 : (reg s10 rOne).val = 1 := by
          rw [h10o _ (by decide), reg_eq_of_regs_eq h9regs rOne, h8o _ (by decide),
            reg_eq_of_regs_eq h7regs rOne, h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]
          exact inv.regs.consts.one
        rw [h11d, add_no_wrap _ _ (by rw [h10_9, h10_1]; omega), h10_9, h10_1]
      dLe := hd
      regs :=
        { consts :=
            { zero := by rw [hRegPres rZero (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPres rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPres rN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPres rM (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPres rRoot (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPres r5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.qVal
          treeBaseVal := by rw [hRegPres r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.treeBaseVal
          emitBaseVal := by rw [hRegPres r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [hDataEq, Array.size_set, Array.size_set]; exact inv.dataSize
      outsidePres := by
        intro k hk
        have hne1 : k ≠ emitBase + n + d := by rcases hk with h1 | ⟨h2, h3⟩ | h4 <;> omega
        have hne2 : k ≠ emitBase + 2 * n + d := by rcases hk with h1 | ⟨h2, h3⟩ | h4 <;> omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne2, array_set_getElem?_ne _ _ _ _ _ hne1]
        exact inv.outsidePres k hk
      cursorsDone := by
        intro j hj
        by_cases hjEq : j = d
        · subst hjEq
          have hne2 : emitBase + n + j ≠ emitBase + 2 * n + j := by omega
          rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne2, array_set_getElem?_same, Option.map_some, hAccVal]
        · have hjLt : j < d := by omega
          have hne1 : emitBase + n + j ≠ emitBase + n + d := by omega
          have hne2 : emitBase + n + j ≠ emitBase + 2 * n + d := by omega
          rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne2, array_set_getElem?_ne _ _ _ _ _ hne1]
          exact inv.cursorsDone j hjLt
      startsDone := by
        intro j hj
        by_cases hjEq : j = d
        · subst hjEq
          rw [hDataEq, array_set_getElem?_same, Option.map_some, hS8_8]
        · have hjLt : j < d := by omega
          have hne1 : emitBase + 2 * n + j ≠ emitBase + n + d := by omega
          have hne2 : emitBase + 2 * n + j ≠ emitBase + 2 * n + d := by omega
          rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne2, array_set_getElem?_ne _ _ _ _ _ hne1]
          exact inv.startsDone j hjLt
      degsRem := by
        intro j hj
        have hne1 : emitBase + g.vertexCount + j.val ≠ emitBase + n + d := by
          change emitBase + n + j.val ≠ emitBase + n + d; omega
        have hne2 : emitBase + g.vertexCount + j.val ≠ emitBase + 2 * n + d := by
          have := j.isLt; change emitBase + n + j.val ≠ emitBase + 2 * n + d; omega
        rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne2, array_set_getElem?_ne _ _ _ _ _ hne1]
        exact inv.degsRem j (Nat.le_of_lt hj) }

theorem run_qStartPrefixPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s₀)
    (S : StaticTreeSlice s₀.data treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ s₀.data.size)
    (hDegs : ∀ d : Fin dense.length,
      (s₀.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (S.emittedArcs d).length) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 10 * g.vertexCount + 8 ∧
      PaperB.RamProgram.run (qStartPrefixPhase (hi := hi) (hw := hw)).code input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase t ∧
      (reg t r8).val = S.allEmittedArcs.length ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase + g.vertexCount ∨
          (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 2 * g.vertexCount) ∨
          emitBase + 2 * g.vertexCount + dense.length + 1 ≤ k) →
        t.data[k]? = s₀.data[k]?) ∧
      (∀ j : Nat, j < dense.length →
        (t.data[emitBase + g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) ∧
      (∀ j : Nat, j ≤ dense.length →
        (t.data[emitBase + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) := by
  let code := qStartPrefixCode (hi := hi) (hw := hw)
  have hOrigSz : s₀.data.size ≤ 2 ^ bits := by rw [s₀.data_size]; exact hw
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  let sInit := Phase.initial s₀
  have hpc0 : sInit.pc = 0 := rfl
  obtain ⟨s1, h0, hpc1, h1d, h1o, h1m⟩ := step16_mov code input hpc0 rfl (by rw [qStartPrefixCode_size]; decide)
  obtain ⟨s2, h1, hpc2, h2d, h2o, h2m⟩ := step16_mov code input hpc1 rfl (by rw [qStartPrefixCode_size]; decide)
  have hRegInit : ∀ r' : Fin 16, r' ≠ r8 → r' ≠ r9 → reg s2 r' = reg s₀ r' := by
    intro r' h8' h9'; rw [h2o _ h9', h1o _ h8']; rfl
  have hS2Data : s2.data = s₀.data := by rw [h2m, h1m]; rfl
  have hInv0 : QStartPrefixInv g r dense treeBase emitBase s₀.data S 0 s2 :=
    { pcEq := hpc2
      accEq := by rw [h2o _ (by decide), h1d]; exact (qStartFn_zero S).symm ▸ hRegs.consts.zero
      dEq := by rw [h2d, h1o _ (by decide)]; exact hRegs.consts.zero
      dLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [hRegInit rZero (by decide) (by decide)]; exact hRegs.consts.zero
              one := by rw [hRegInit rOne (by decide) (by decide)]; exact hRegs.consts.one
              nVal := by rw [hRegInit rN (by decide) (by decide)]; exact hRegs.consts.nVal
              mVal := by rw [hRegInit rM (by decide) (by decide)]; exact hRegs.consts.mVal
              rootVal := by rw [hRegInit rRoot (by decide) (by decide)]; exact hRegs.consts.rootVal }
          qVal := by rw [hRegInit r5 (by decide) (by decide)]; exact hRegs.qVal
          treeBaseVal := by rw [hRegInit r6 (by decide) (by decide)]; exact hRegs.treeBaseVal
          emitBaseVal := by rw [hRegInit r7 (by decide) (by decide)]; exact hRegs.emitBaseVal }
      dataSize := by rw [hS2Data]
      outsidePres := by intro k _; rw [hS2Data]
      cursorsDone := fun _ hj => False.elim (Nat.not_lt_zero _ hj)
      startsDone := fun _ hj => False.elim (Nat.not_lt_zero _ hj)
      degsRem := by intro j _; rw [hS2Data]; exact hDegs j }
  have hRun : ∀ rem d st, d + rem = dense.length →
      QStartPrefixInv g r dense treeBase emitBase s₀.data S d st →
      ∃ stEnd, Steps code input (10 * rem) st stEnd ∧
        QStartPrefixInv g r dense treeBase emitBase s₀.data S dense.length stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro d st hrem hinv
      have hdEq : d = dense.length := by omega
      subst hdEq
      exact ⟨st, by simp only [Nat.mul_zero]; exact Steps.zero st, hinv⟩
    | succ rem ih =>
      intro d st hrem hinv
      have hdLt : d < dense.length := by omega
      obtain ⟨st1, hstep1, hinv1⟩ := qStartPrefix_step input S hFitEmit d hdLt hinv
      obtain ⟨stEnd, hstepRest, hinvEnd⟩ := ih (d + 1) st1 (by omega) hinv1
      have hMul : 10 * (rem + 1) = 10 + 10 * rem := by omega
      rw [hMul]
      exact ⟨stEnd, hstep1.append hstepRest, hinvEnd⟩
  obtain ⟨sEnd, hStepsLoop, hInvEnd⟩ := hRun dense.length 0 s2 (Nat.zero_add _) hInv0
  have hFalse : (reg sEnd r5).val ≤ (reg sEnd r9).val := by
    rw [hInvEnd.dEq, hInvEnd.regs.qVal]; exact Nat.le_refl _
  have h2f := step16_branchLt_false code input hInvEnd.pcEq rfl (by rw [qStartPrefixCode_size]; decide) hFalse
  let s12 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEnd.regs, data := sEnd.data, pc := 12, regs_size := sEnd.regs_size, data_size := sEnd.data_size }
  have hpc12 : s12.pc = 12 := rfl
  obtain ⟨s13, h12, hpc13, h13d, h13o, h13m⟩ := step16_add code input hpc12 rfl (by rw [qStartPrefixCode_size]; decide)
  obtain ⟨s14, h13, hpc14, h14d, h14o, h14m⟩ := step16_add code input hpc13 rfl (by rw [qStartPrefixCode_size]; decide)
  obtain ⟨s15, h14, hpc15, h15d, h15o, h15m⟩ := step16_add code input hpc14 rfl (by rw [qStartPrefixCode_size]; decide)
  have hr13 : (reg s13 r12).val = emitBase + g.vertexCount := by
    have h7v : (reg s12 r7).val = emitBase := hInvEnd.regs.emitBaseVal
    have hn : (reg s12 rN).val = g.vertexCount := hInvEnd.regs.consts.nVal
    rw [h13d, add_no_wrap _ _ (by rw [h7v, hn]; unfold emitterWorkWords at hFitEmit; omega), h7v, hn]
  have hr14 : (reg s14 r12).val = emitBase + 2 * g.vertexCount := by
    have hn : (reg s13 rN).val = g.vertexCount := by rw [h13o _ (by decide)]; exact hInvEnd.regs.consts.nVal
    rw [h14d, add_no_wrap _ _ (by rw [hr13, hn]; unfold emitterWorkWords at hFitEmit; omega), hr13, hn]; omega
  have hr15 : (reg s15 r12).val = emitBase + 2 * g.vertexCount + dense.length := by
    have hq : (reg s14 r5).val = dense.length := by rw [h14o _ (by decide), h13o _ (by decide)]; exact hInvEnd.regs.qVal
    rw [h15d, add_no_wrap _ _ (by rw [hr14, hq]; unfold emitterWorkWords at hFitEmit; omega), hr14, hq]
  have hBnd15 : (reg s15 r12).val < s15.data.size := by
    rw [hr15, h15m, h14m, h13m]; change emitBase + 2 * g.vertexCount + dense.length < sEnd.data.size
    rw [hInvEnd.dataSize]; unfold emitterWorkWords at hFitEmit; omega
  obtain ⟨s16, h15, hpc16, h16regs, h16data⟩ := step16_storeData code input hpc15 rfl (by rw [qStartPrefixCode_size]; decide) hBnd15
  have hHalt : step code input s16 = some (.halted s16) := step_halt_at (by rw [hpc16]; rfl)
  have hTailSteps : Steps code input 5 sEnd s16 :=
    Steps.cons h2f <| Steps.cons h12 <| Steps.cons h13 <| Steps.cons h14 <| Steps.cons h15 (Steps.zero s16)
  have hFull := ((Steps.cons h0 <| Steps.cons h1 (Steps.zero s2)).append hStepsLoop).append hTailSteps
  have hExec := hFull.halts hHalt
  have hDataEq : s16.data = sEnd.data.set (emitBase + 2 * g.vertexCount + dense.length) (reg s15 r8)
      (by have hSz : s15.data.size = sEnd.data.size := by rw [h15m, h14m, h13m]
          rw [← hr15, ← hSz]; exact hBnd15) := by
    rw [h16data]
    exact array_set_congr (by rw [h15m, h14m, h13m]) hr15 rfl
  have hRegEnd : ∀ r' : Fin 16, r' ≠ r12 → reg s16 r' = reg sEnd r' := by
    intro r' h12'; rw [reg_eq_of_regs_eq h16regs r', h15o _ h12', h14o _ h12', h13o _ h12']; rfl
  refine ⟨s16, 2 + 10 * dense.length + 5 + 1, by omega, hExec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { consts :=
          { zero := by rw [hRegEnd rZero (by decide)]; exact hInvEnd.regs.consts.zero
            one := by rw [hRegEnd rOne (by decide)]; exact hInvEnd.regs.consts.one
            nVal := by rw [hRegEnd rN (by decide)]; exact hInvEnd.regs.consts.nVal
            mVal := by rw [hRegEnd rM (by decide)]; exact hInvEnd.regs.consts.mVal
            rootVal := by rw [hRegEnd rRoot (by decide)]; exact hInvEnd.regs.consts.rootVal }
        qVal := by rw [hRegEnd r5 (by decide)]; exact hInvEnd.regs.qVal
        treeBaseVal := by rw [hRegEnd r6 (by decide)]; exact hInvEnd.regs.treeBaseVal
        emitBaseVal := by rw [hRegEnd r7 (by decide)]; exact hInvEnd.regs.emitBaseVal }
  · rw [hRegEnd r8 (by decide), hInvEnd.accEq, qStartFn_end S]
  · rw [hDataEq, Array.size_set]; exact hInvEnd.dataSize
  · intro k hk
    have hne : k ≠ emitBase + 2 * g.vertexCount + dense.length := by
      rcases hk with h1 | ⟨h2, h3⟩ | h4 <;> omega
    rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
    exact hInvEnd.outsidePres k hk
  · intro j hj
    have hne : emitBase + g.vertexCount + j ≠ emitBase + 2 * g.vertexCount + dense.length := by omega
    rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
    exact hInvEnd.cursorsDone j hj
  · intro j hj
    by_cases hjEq : j = dense.length
    · subst hjEq
      rw [hDataEq, array_set_getElem?_same, Option.map_some,
        (by rw [h15o _ (by decide), h14o _ (by decide), h13o _ (by decide)]; exact hInvEnd.accEq :
          (reg s15 r8).val = qStartFn S dense.length)]
    · have hjLt : j < dense.length := by omega
      have hne : emitBase + 2 * g.vertexCount + j ≠ emitBase + 2 * g.vertexCount + dense.length := by omega
      rw [hDataEq, array_set_getElem?_ne _ _ _ _ _ hne]
      exact hInvEnd.startsDone j hjLt

/-! #### Phase 5: `scatterQuotientArcsPhase` (binary search + scatter `(qSrc, qHead, qEntry)`) -/

private theorem emittedPrefixList_isPrefix {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (u j : Nat) :
    ∃ suf, emittedPrefixList S u j ++ suf = S.allEmittedArcs := by
  unfold emittedPrefixList StaticTreeSlice.allEmittedArcs
  by_cases hu : u < dense.length
  · simp only [hu, ↓reduceDIte]
    have hSplit : List.finRange dense.length =
        (List.finRange dense.length).take u ++ ⟨u, hu⟩ :: (List.finRange dense.length).drop (u + 1) := by
      have h1 := (List.take_append_drop u (List.finRange dense.length)).symm
      have hDrop : (List.finRange dense.length).drop u = ⟨u, hu⟩ :: (List.finRange dense.length).drop (u + 1) := by
        have hlt : u < (List.finRange dense.length).length := by simp [hu]
        rw [List.drop_eq_getElem_cons hlt]; simp
      rw [hDrop] at h1
      exact h1
    have hTake : S.emitForU ⟨u, hu⟩ = (S.emitForU ⟨u, hu⟩).take j ++ (S.emitForU ⟨u, hu⟩).drop j :=
      (List.take_append_drop j _).symm
    refine ⟨(S.emitForU ⟨u, hu⟩).drop j ++ ((List.finRange dense.length).drop (u + 1)).flatMap S.emitForU, ?_⟩
    have hFM := congrArg (List.flatMap S.emitForU) hSplit
    rw [List.flatMap_append, List.flatMap_cons] at hFM
    have hEq : (List.finRange dense.length).flatMap S.emitForU =
        ((List.finRange dense.length).take u).flatMap S.emitForU ++
          (((S.emitForU ⟨u, hu⟩).take j ++ (S.emitForU ⟨u, hu⟩).drop j) ++
            ((List.finRange dense.length).drop (u + 1)).flatMap S.emitForU) := by
      rw [hFM, ← hTake]
    rw [hEq]
    simp only [List.append_assoc]
  · simp only [hu, ↓reduceDIte]
    have hTakeAll : (List.finRange dense.length).take u = List.finRange dense.length :=
      List.take_of_length_le (by simp; omega)
    rw [hTakeAll, List.append_nil]
    exact ⟨[], List.append_nil _⟩

private theorem emittedPrefixList_filter_le {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (u j : Nat) (d : Fin dense.length) :
    ((emittedPrefixList S u j).filter (fun e => e.owner == d)).length ≤ (S.emittedArcs d).length := by
  obtain ⟨suf, hsuf⟩ := emittedPrefixList_isPrefix S u j
  have h1 : S.emittedArcs d =
      (emittedPrefixList S u j).filter (fun e => e.owner == d) ++
      suf.filter (fun e => e.owner == d) := by
    unfold StaticTreeSlice.emittedArcs
    rw [← hsuf, List.filter_append]
  rw [h1, List.length_append]
  exact Nat.le_add_right _ _

private theorem emittedPrefixList_filter_getElem {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) (u j : Nat) (d : Fin dense.length)
    (p : Nat) (hp : p < ((emittedPrefixList S u j).filter (fun e => e.owner == d)).length) :
    ((emittedPrefixList S u j).filter (fun e => e.owner == d))[p]'hp =
      (S.emittedArcs d)[p]'(Nat.lt_of_lt_of_le hp (emittedPrefixList_filter_le S u j d)) := by
  obtain ⟨suf, hsuf⟩ := emittedPrefixList_isPrefix S u j
  have h1 : S.emittedArcs d =
      (emittedPrefixList S u j).filter (fun e => e.owner == d) ++
      suf.filter (fun e => e.owner == d) := by
    unfold StaticTreeSlice.emittedArcs
    rw [← hsuf, List.filter_append]
  have hp' : p < (S.emittedArcs d).length := Nat.lt_of_lt_of_le hp (emittedPrefixList_filter_le S u j d)
  have he : (S.emittedArcs d)[p]'hp' =
      ((emittedPrefixList S u j).filter (fun e => e.owner == d) ++ suf.filter (fun e => e.owner == d))[p]'(by rw [← h1]; exact hp') := by
    congr 1
  rw [he, List.getElem_append_left hp]

private theorem qStartFn_mono {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ dense.length) :
    qStartFn S a ≤ qStartFn S b := by
  suffices ∀ rem k, k + rem = b → qStartFn S k ≤ qStartFn S b from this (b - a) a (by omega)
  intro rem
  induction rem with
  | zero =>
    intro k hk
    have hkEq : k = b := by omega
    rw [hkEq]
    exact Nat.le_refl _
  | succ rem ih =>
    intro k hk
    have hkLt : k < dense.length := by omega
    exact Nat.le_trans (by rw [qStartFn_succ S hkLt]; exact Nat.le_add_right _ _) (ih (k + 1) (by omega))

def scatterHeadCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    -- Outer loop (uDense in r8, tailEntry in r9), PC 0..42 (size = 43)
    .mov r8 rZero,            -- 0: uDense := 0
    .branchLt r8 r5 2 128,    -- 1: while uDense < Q
    .add r12 rN rN,           -- 2: 2n
    .add r12 r12 r12,         -- 3: 4n
    .add r12 r12 r8,          -- 4: 4n + uDense
    .loadData r12 r12,        -- 5: uOrig
    .add r10 r12 rOne,        -- 6: uOrig + 1
    .add r10 r10 rOne,        -- 7: uOrig + 2
    .add r10 r10 rOne,        -- 8: uOrig + 3
    .add r11 r10 rOne,        -- 9: uOrig + 4
    .loadInput r10 r10,       -- 10: eIdx = outPrefix[uOrig]
    .loadInput r11 r11,       -- 11: eEnd = outPrefix[uOrig + 1]
    .add r9 r5 r5,            -- 12: 2Q
    .add r9 r9 r9,            -- 13: 4Q
    .add r9 r6 r9,            -- 14: treeBase + 4Q
    .add r9 r9 r8,            -- 15: treeBase + 4Q + uDense
    .loadData r9 r9,          -- 16: tailEntry = entry[uDense]
    -- Inner loop (eIdx in r10, eEnd in r11)
    .branchLt r10 r11 18 126, -- 17: while eIdx < eEnd
    .add r12 rN r10,          -- 18: n + eIdx
    .add r12 r12 rOne,        -- 19: n + 1 + eIdx
    .add r12 r12 rOne,        -- 20: n + 2 + eIdx
    .add r12 r12 rOne,        -- 21: n + 3 + eIdx
    .add r12 r12 rOne,        -- 22: 4 + n + eIdx
    .loadInput r12 r12,       -- 23: vOrig
    .add r13 rN rN,           -- 24: 2n
    .add r13 r13 rN,          -- 25: 3n
    .add r13 r13 r12,         -- 26: 3n + vOrig
    .loadData r13 r13,        -- 27: vDense + 1
    .sub r13 r13 rOne,        -- 28: vDense
    .add r14 r6 r13,          -- 29: treeBase + vDense
    .loadData r14 r14,        -- 30: d = domParent[vDense]
    .add r15 rN rN,           -- 31: 2n
    .add r15 r15 rN,          -- 32: 3n
    .add r15 r15 rM,          -- 33: 3n + m
    .add r15 r15 rM,          -- 34: 3n + 2m
    .add r15 r15 rM,          -- 35: 3n + 3m
    .add r15 r15 r7,          -- 36: emitBase + 3n + 3m
    .add r15 r15 rOne,        -- 37: emitBase + 3n + 3m + 1 (scratch0)
    .storeData r15 r14,       -- 38: scratch0 := d
    .add r13 r7 r13,          -- 39: emitBase + vDense
    .loadData r13 r13,        -- 40: headLocal = selfSlot[vDense]
    .add r15 r15 rOne,        -- 41: scratch1
    .storeData r15 r13        -- 42: scratch1 := headLocal
  ]

def scatterMidCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    -- PC 43..91 (size = 49)
    .branchLt r8 r14 47 44,   -- 43: if uDense < d then bsearch
    .branchLt r14 r8 47 45,   -- 44: if d < uDense then bsearch
    .mov r12 rZero,           -- 45: uDense = d => srcLocal := 0
    .goto 92,                 -- 46: jump to scatter write
    .add r15 r5 r5,           -- 47: 2Q
    .add r15 r15 r15,         -- 48: 4Q
    .add r15 r15 r5,          -- 49: 5Q
    .add r15 r15 r5,          -- 50: 6Q
    .add r15 r15 r5,          -- 51: 7Q
    .add r15 r15 r6,          -- 52: treeBase + 7Q
    .add r15 r15 r14,         -- 53: treeBase + 7Q + d
    .loadData r12 r15,        -- 54: L = childStart[d]
    .add r15 r15 rOne,        -- 55: treeBase + 7Q + d + 1
    .loadData r13 r15,        -- 56: R = childStart[d + 1]
    .add r14 r12 rOne,        -- 57: bsearch header: L + 1
    .branchLt r14 r13 59 74,  -- 58: while L + 1 < R
    .sub r14 r13 r12,         -- 59: R - L
    .shr1 r14 r14,            -- 60: (R - L) / 2
    .add r14 r12 r14,         -- 61: mid = L + (R - L) / 2
    .add r15 r5 r5,           -- 62: 2Q
    .add r15 r15 r15,         -- 63: 4Q
    .add r15 r15 r15,         -- 64: 8Q
    .add r15 r15 rOne,        -- 65: 8Q + 1
    .add r15 r15 r6,          -- 66: treeBase + 8Q + 1
    .add r15 r15 r14,         -- 67: treeBase + 8Q + 1 + mid
    .loadData r15 r15,        -- 68: childEntries[mid]
    .branchLt r9 r15 70 72,   -- 69: if target < childEntries[mid] then R := mid else L := mid
    .mov r13 r14,             -- 70: R := mid
    .goto 57,                 -- 71
    .mov r12 r14,             -- 72: L := mid
    .goto 57,                 -- 73
    .add r15 rN rN,           -- 74: 2n
    .add r15 r15 rN,          -- 75: 3n
    .add r15 r15 rM,          -- 76: 3n + m
    .add r15 r15 rM,          -- 77: 3n + 2m
    .add r15 r15 rM,          -- 78: 3n + 3m
    .add r15 r15 r7,          -- 79: emitBase + 3n + 3m
    .add r15 r15 rOne,        -- 80: scratch0
    .loadData r14 r15,        -- 81: d
    .add r15 r5 r5,           -- 82: 2Q
    .add r15 r15 r15,         -- 83: 4Q
    .add r15 r15 r5,          -- 84: 5Q
    .add r15 r15 r5,          -- 85: 6Q
    .add r15 r15 r5,          -- 86: 7Q
    .add r15 r15 r6,          -- 87: treeBase + 7Q
    .add r15 r15 r14,         -- 88: treeBase + 7Q + d
    .loadData r14 r15,        -- 89: childStart[d]
    .sub r12 r12 r14,         -- 90: pos - childStart[d]
    .add r12 r12 rOne         -- 91: srcLocal = (pos - childStart[d]) + 1
  ]

def scatterTailCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[
    -- PC 92..132 (size = 41)
    .add r15 rN rN,           -- 92: 2n
    .add r15 r15 rN,          -- 93: 3n
    .add r15 r15 rM,          -- 94: 3n + m
    .add r15 r15 rM,          -- 95: 3n + 2m
    .add r15 r15 rM,          -- 96: 3n + 3m
    .add r15 r15 r7,          -- 97: emitBase + 3n + 3m
    .add r15 r15 rOne,        -- 98: scratch0
    .loadData r14 r15,        -- 99: d
    .add r14 r14 rN,          -- 100: n + d
    .add r14 r14 r7,          -- 101: emitBase + n + d (addr of qCursor[d])
    .loadData r13 r14,        -- 102: cur = qCursor[d]
    .add r15 rN rN,           -- 103: 2n
    .add r15 r15 rN,          -- 104: 3n
    .add r15 r15 rOne,        -- 105: 3n + 1
    .add r15 r15 r7,          -- 106: emitBase + 3n + 1
    .add r15 r15 r13,         -- 107: emitBase + 3n + 1 + cur
    .storeData r15 r12,       -- 108: qSrc[cur] := srcLocal
    .add r12 rN rN,           -- 109: 2n
    .add r12 r12 rN,          -- 110: 3n
    .add r12 r12 rM,          -- 111: 3n + m
    .add r12 r12 rM,          -- 112: 3n + 2m
    .add r12 r12 rM,          -- 113: 3n + 3m
    .add r12 r12 r7,          -- 114: emitBase + 3n + 3m
    .add r12 r12 rOne,        -- 115: scratch0
    .add r12 r12 rOne,        -- 116: scratch1
    .loadData r12 r12,        -- 117: headLocal
    .add r15 r15 rM,          -- 118: emitBase + 3n + m + 1 + cur
    .storeData r15 r12,       -- 119: qHead[cur] := headLocal
    .add r15 r15 rM,          -- 120: emitBase + 3n + 2m + 1 + cur
    .storeData r15 r9,        -- 121: qEntry[cur] := tailEntry
    .add r13 r13 rOne,        -- 122: cur + 1
    .storeData r14 r13,       -- 123: qCursor[d] := cur + 1
    .add r10 r10 rOne,        -- 124: eIdx++
    .goto 17,                 -- 125
    -- Inner loop exit
    .add r8 r8 rOne,          -- 126: uDense++
    .goto 1,                  -- 127
    -- Outer loop exit: r8 := qStart[Q] = mReach
    .add r8 rN rN,            -- 128: 2n
    .add r8 r8 r7,            -- 129: emitBase + 2n
    .add r8 r8 r5,            -- 130: emitBase + 2n + Q
    .loadData r8 r8,          -- 131: r8 := mReach
    .halt                     -- 132
  ]

def scatterQuotientArcsCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  scatterHeadCode ++ (scatterMidCode ++ scatterTailCode)

private theorem scatterHeadCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (scatterHeadCode (hi := hi) (hw := hw)).size = 43 := rfl

private theorem scatterMidCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (scatterMidCode (hi := hi) (hw := hw)).size = 49 := rfl

private theorem scatterTailCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (scatterTailCode (hi := hi) (hw := hw)).size = 41 := rfl

private theorem scatterQuotientArcsCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    (scatterQuotientArcsCode (hi := hi) (hw := hw)).size = 133 := by
  unfold scatterQuotientArcsCode
  rw [Array.size_append, Array.size_append,
    scatterHeadCode_size, scatterMidCode_size, scatterTailCode_size]

private theorem scatterCode_head {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {k : Nat} (hk : k < 43) :
    (scatterQuotientArcsCode (hi := hi) (hw := hw))[k]? =
      (scatterHeadCode (hi := hi) (hw := hw))[k]? := by
  unfold scatterQuotientArcsCode
  exact Array.getElem?_append_left (by rw [scatterHeadCode_size]; exact hk)

private theorem scatterCode_mid {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {k : Nat} (hk1 : 43 ≤ k) (hk2 : k < 92) :
    (scatterQuotientArcsCode (hi := hi) (hw := hw))[k]? =
      (scatterMidCode (hi := hi) (hw := hw))[k - 43]? := by
  unfold scatterQuotientArcsCode
  rw [Array.getElem?_append_right (by rw [scatterHeadCode_size]; exact hk1), scatterHeadCode_size]
  exact Array.getElem?_append_left (by rw [scatterMidCode_size]; omega)

private theorem scatterCode_tail {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {k : Nat} (hk1 : 92 ≤ k) :
    (scatterQuotientArcsCode (hi := hi) (hw := hw))[k]? =
      (scatterTailCode (hi := hi) (hw := hw))[k - 92]? := by
  unfold scatterQuotientArcsCode
  rw [Array.getElem?_append_right (by rw [scatterHeadCode_size]; omega), scatterHeadCode_size]
  rw [Array.getElem?_append_right (by rw [scatterMidCode_size]; omega), scatterMidCode_size]
  congr 1

def scatterQuotientArcsPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast scatterQuotientArcsCode 132
    scatterQuotientArcsCode_size
    (by rw [scatterCode_tail (by decide)]; rfl)
    (by
      have hHead : (scatterHeadCode (hi := hi) (hw := hw)).toList.all nonHalt = true := rfl
      have hMid : (scatterMidCode (hi := hi) (hw := hw)).toList.all nonHalt = true := rfl
      have hTail : ((scatterTailCode (hi := hi) (hw := hw)).toList.take 40).all nonHalt = true := rfl
      have hLenH : (scatterHeadCode (hi := hi) (hw := hw)).toList.length = 43 := rfl
      have hLenM : (scatterMidCode (hi := hi) (hw := hw)).toList.length = 49 := rfl
      have hTakeM : ((scatterMidCode (hi := hi) (hw := hw)).toList ++
          (scatterTailCode (hi := hi) (hw := hw)).toList).take 89 =
          (scatterMidCode (hi := hi) (hw := hw)).toList ++
            ((scatterTailCode (hi := hi) (hw := hw)).toList.take 40) := by
        rw [List.take_append, List.take_of_length_le (by rw [hLenM]; decide), hLenM]
      have hSplit1 : ((scatterHeadCode (hi := hi) (hw := hw)).toList ++
          ((scatterMidCode (hi := hi) (hw := hw)).toList ++
            (scatterTailCode (hi := hi) (hw := hw)).toList)).take 132 =
          (scatterHeadCode (hi := hi) (hw := hw)).toList ++
          ((scatterMidCode (hi := hi) (hw := hw)).toList ++
            ((scatterTailCode (hi := hi) (hw := hw)).toList.take 40)) := by
        rw [List.take_append, List.take_of_length_le (by rw [hLenH]; decide), hLenH]
        exact congrArg ((scatterHeadCode (hi := hi) (hw := hw)).toList ++ ·) hTakeM
      change ((scatterHeadCode (hi := hi) (hw := hw) ++
        (scatterMidCode (hi := hi) (hw := hw) ++ scatterTailCode (hi := hi) (hw := hw))).toList.take 132).all nonHalt = true
      rw [Array.toList_append, Array.toList_append, hSplit1, List.all_append, List.all_append,
        hHead, hMid, hTail]
      rfl)

private def ScatterWritten {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} {treeBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (emitBase : Nat) (pref : List (EmittedArc dense.length))
    (data : Array (Word bits)) : Prop :=
  ∀ (d : Fin dense.length) (p : Nat) (hp : p < (pref.filter (fun e => e.owner == d)).length),
    let pos := qStartFn S d.val + p
    let e := (pref.filter (fun e => e.owner == d))[p]'hp
    (data[emitBase + 3 * g.vertexCount + 1 + pos]?).map Fin.val = some e.srcLocal ∧
    (data[emitBase + 3 * g.vertexCount + g.arcCount + 1 + pos]?).map Fin.val = some e.headLocal ∧
    (data[emitBase + 3 * g.vertexCount + 2 * g.arcCount + 1 + pos]?).map Fin.val = some e.tailEntry

private structure ScatterOuterInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (u : Nat) (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 1
  uEq : (reg s r8).val = u
  uLe : u ≤ dense.length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + g.vertexCount ∨
      (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 3 * g.vertexCount + 1) ∨
      emitBase + 3 * g.vertexCount + 3 * g.arcCount + 3 ≤ k) →
    s.data[k]? = origData[k]?
  cursors : ∀ d : Fin dense.length,
    (s.data[emitBase + g.vertexCount + d.val]?).map Fin.val =
      some (qStartFn S d.val + ((emittedPrefixList S u 0).filter (fun e => e.owner == d)).length)
  written : ScatterWritten S emitBase (emittedPrefixList S u 0) s.data

private structure ScatterInnerInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (g : Digraph) (r : Fin g.vertexCount) (dense : List (Fin g.vertexCount))
    (treeBase emitBase : Nat) (origData : Array (Word bits))
    (S : StaticTreeSlice origData treeBase g r dense)
    (u : Fin dense.length) (j : Nat)
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  pcEq : s.pc = 17
  uEq : (reg s r8).val = u.val
  tailEq : (reg s r9).val = S.entry u
  eIdxEq : (reg s r10).val = outPrefix g (dense[u.val]'u.isLt).val + j
  eEndEq : (reg s r11).val = outPrefix g (dense[u.val]'u.isLt).val + (g.outArcs (dense[u.val]'u.isLt)).length
  jLe : j ≤ (g.outArcs (dense[u.val]'u.isLt)).length
  regs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s
  dataSize : s.data.size = origData.size
  outsidePres : ∀ k, (k < emitBase + g.vertexCount ∨
      (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 3 * g.vertexCount + 1) ∨
      emitBase + 3 * g.vertexCount + 3 * g.arcCount + 3 ≤ k) →
    s.data[k]? = origData[k]?
  cursors : ∀ d : Fin dense.length,
    (s.data[emitBase + g.vertexCount + d.val]?).map Fin.val =
      some (qStartFn S d.val + ((emittedPrefixList S u.val j).filter (fun e => e.owner == d)).length)
  written : ScatterWritten S emitBase (emittedPrefixList S u.val j) s.data

private theorem scatter_bsearch_run {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (_hDenseLe : dense.length ≤ g.vertexCount)
    (hOrigSz : origData.size ≤ 2 ^ bits)
    (u : Fin dense.length) :
    ∀ (fuel l rhs : Nat) (s : State (layout16 bits inputCap workCap hi hw)),
      l < rhs → rhs ≤ dense.length - 1 → rhs - l ≤ 2 ^ fuel →
      s.pc = 57 →
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s →
      (reg s r8).val = u.val →
      (reg s r9).val = S.entry u →
      (reg s r12).val = l →
      (reg s r13).val = rhs →
      (∀ i (_hi : i < dense.length - 1),
        (s.data[treeBase + 8 * dense.length + 1 + i]?).map Fin.val = some (S.childEntryAt i)) →
      s.data.size ≤ 2 ^ bits →
      ∃ s' stepsB, stepsB ≤ 15 * fuel + 2 ∧
        Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input stepsB s s' ∧
        s'.pc = 74 ∧
        (reg s' r12).val = bsearchRun S.childEntryAt fuel l rhs (S.entry u) ∧
        (∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s' r' = reg s r') ∧
        s'.data = s.data := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  have hQPos := S.qPos
  intro fuel
  induction fuel with
  | zero =>
    intro l rhs s hlR hRLe hPow hpc hRegs hu hTgt hl hR hEntries hDataSz
    have hrl : rhs = l + 1 := by simp only [Nat.pow_zero] at hPow; omega
    obtain ⟨s58, h57, hpc58, h58d, h58o, h58m⟩ :=
      step16_add code input hpc (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have h58_14 : (reg s58 r14).val = l + 1 := by
      have h1 : (reg s rOne).val = 1 := hRegs.consts.one
      rw [h58d, add_no_wrap _ _ (by rw [hl, h1]; omega), hl, h1]
    have h58_13 : (reg s58 r13).val = rhs := by rw [h58o _ (by decide)]; exact hR
    have hFalse : (reg s58 r13).val ≤ (reg s58 r14).val := by rw [h58_14, h58_13, hrl]; exact Nat.le_refl _
    have h58f := step16_branchLt_false code input hpc58
      (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hFalse
    let s' : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s58.regs, data := s58.data, pc := 74, regs_size := s58.regs_size, data_size := s58.data_size }
    have hb0 : bsearchRun S.childEntryAt 0 l rhs (S.entry u) = l := rfl
    refine ⟨s', 2, by omega, Steps.cons h57 <| Steps.cons h58f (Steps.zero s'), rfl, ?_, ?_, ?_⟩
    · rw [hb0]; change (reg s58 r12).val = l; rw [h58o _ (by decide)]; exact hl
    · intro r' _ _ h14' _; change reg s58 r' = reg s r'; rw [h58o _ h14']
    · change s58.data = _; rw [h58m]
  | succ fuel ih =>
    intro l rhs s hlR hRLe hPow hpc hRegs hu hTgt hl hR hEntries hDataSz
    have hQpow : dense.length < 2 ^ bits := by
      have hEntryBnd := S.fit
      unfold staticTreeWords at hEntryBnd
      omega
    obtain ⟨s58, h57, hpc58, h58d, h58o, h58m⟩ :=
      step16_add code input hpc (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have h58_14 : (reg s58 r14).val = l + 1 := by
      have h1 : (reg s rOne).val = 1 := hRegs.consts.one
      rw [h58d, add_no_wrap _ _ (by rw [hl, h1]; omega), hl, h1]
    have h58_13 : (reg s58 r13).val = rhs := by rw [h58o _ (by decide)]; exact hR
    by_cases hcond : l + 1 < rhs
    · have hTrue : (reg s58 r14).val < (reg s58 r13).val := by rw [h58_14, h58_13]; exact hcond
      have h58t := step16_branchLt_true code input hpc58
        (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hTrue
      let s59 : State (layout16 bits inputCap workCap hi hw) :=
        { regs := s58.regs, data := s58.data, pc := 59, regs_size := s58.regs_size, data_size := s58.data_size }
      have hpc59 : s59.pc = 59 := rfl
      obtain ⟨s60, h59, hpc60, h60d, h60o, h60m⟩ := step16_sub code input hpc59 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s61, h60, hpc61, h61d, h61o, h61m⟩ := step16_shr1 code input hpc60 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s62, h61, hpc62, h62d, h62o, h62m⟩ := step16_add code input hpc61 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s63, h62, hpc63, h63d, h63o, h63m⟩ := step16_add code input hpc62 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s64, h63, hpc64, h64d, h64o, h64m⟩ := step16_add code input hpc63 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s65, h64, hpc65, h65d, h65o, h65m⟩ := step16_add code input hpc64 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s66, h65, hpc66, h66d, h66o, h66m⟩ := step16_add code input hpc65 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s67, h66, hpc67, h67d, h67o, h67m⟩ := step16_add code input hpc66 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      obtain ⟨s68, h67, hpc68, h68d, h68o, h68m⟩ := step16_add code input hpc67 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
      have hS59_12 : (reg s59 r12).val = l := by change (reg s58 r12).val = l; rw [h58o _ (by decide)]; exact hl
      have hS59_13 : (reg s59 r13).val = rhs := h58_13
      have h60_14 : (reg s60 r14).val = rhs - l := by
        rw [h60d, sub_exact _ _ (by rw [hS59_13, hS59_12]; exact Nat.le_of_lt hlR), hS59_13, hS59_12]
      have h61_14 : (reg s61 r14).val = (rhs - l) / 2 := by rw [h61d, h60_14]
      let mid := l + (rhs - l) / 2
      have hMidLt : mid < rhs := by omega
      have hMidGt : l < mid := by omega
      have hMidDense : mid < dense.length - 1 := by omega
      have h62_14 : (reg s62 r14).val = mid := by
        have h61_12 : (reg s61 r12).val = l := by rw [h61o _ (by decide), h60o _ (by decide)]; exact hS59_12
        rw [h62d, add_no_wrap _ _ (by rw [h61_12, h61_14]; omega), h61_12, h61_14]
      have hS62Pres : ∀ r' : Fin 16, r' ≠ r14 → reg s62 r' = reg s r' := by
        intro r' h14'
        rw [h62o _ h14', h61o _ h14', h60o _ h14']
        change reg s58 r' = reg s r'
        rw [h58o _ h14']
      have hTreeFit := S.fit
      have hQVal62 : (reg s62 r5).val = dense.length := by rw [hS62Pres r5 (by decide)]; exact hRegs.qVal
      have hOne62 : (reg s62 rOne).val = 1 := by rw [hS62Pres rOne (by decide)]; exact hRegs.consts.one
      have hTreeBase62 : (reg s62 r6).val = treeBase := by rw [hS62Pres r6 (by decide)]; exact hRegs.treeBaseVal
      have h63_15 : (reg s63 r15).val = 2 * dense.length := by
        rw [h63d, add_no_wrap _ _ (by rw [hQVal62]; unfold staticTreeWords at hTreeFit; omega), hQVal62]; omega
      have h64_15 : (reg s64 r15).val = 4 * dense.length := by
        rw [h64d, add_no_wrap _ _ (by rw [h63_15]; unfold staticTreeWords at hTreeFit; omega), h63_15]; omega
      have h65_15 : (reg s65 r15).val = 8 * dense.length := by
        rw [h65d, add_no_wrap _ _ (by rw [h64_15]; unfold staticTreeWords at hTreeFit; omega), h64_15]; omega
      have h66_15 : (reg s66 r15).val = 8 * dense.length + 1 := by
        have h65_1 : (reg s65 rOne).val = 1 := by rw [h65o _ (by decide), h64o _ (by decide), h63o _ (by decide)]; exact hOne62
        rw [h66d, add_no_wrap _ _ (by rw [h65_15, h65_1]; unfold staticTreeWords at hTreeFit; omega), h65_15, h65_1]
      have h67_15 : (reg s67 r15).val = treeBase + (8 * dense.length + 1) := by
        have h66_6 : (reg s66 r6).val = treeBase := by
          rw [h66o _ (by decide), h65o _ (by decide), h64o _ (by decide), h63o _ (by decide)]; exact hTreeBase62
        rw [h67d, add_no_wrap _ _ (by rw [h66_6, h66_15]; unfold staticTreeWords at hTreeFit; omega), h66_6, h66_15]; omega
      have h68_15 : (reg s68 r15).val = treeBase + 8 * dense.length + 1 + mid := by
        have h67_14 : (reg s67 r14).val = mid := by
          rw [h67o _ (by decide), h66o _ (by decide), h65o _ (by decide), h64o _ (by decide), h63o _ (by decide)]; exact h62_14
        rw [h68d, add_no_wrap _ _ (by rw [h67_15, h67_14]; unfold staticTreeWords at hTreeFit; omega), h67_15, h67_14]; omega
      have hS68Data : s68.data = s.data := by
        rw [h68m, h67m, h66m, h65m, h64m, h63m, h62m, h61m, h60m]; exact h58m
      have hEntryMem : (s68.data[(reg s68 r15).val]?).map Fin.val = some (S.childEntryAt mid) := by
        rw [h68_15, hS68Data]; exact hEntries mid hMidDense
      obtain ⟨wmid, hwmid, hwmidVal⟩ := data_val_at hEntryMem
      obtain ⟨s69, h68, hpc69, h69d, h69o, h69m⟩ :=
        step16_loadData code input hpc68 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) hwmid (by rw [scatterQuotientArcsCode_size]; decide)
      have h69_9 : (reg s69 r9).val = S.entry u := by
        rw [h69o _ (by decide), h68o _ (by decide), h67o _ (by decide), h66o _ (by decide),
          h65o _ (by decide), h64o _ (by decide), h63o _ (by decide), hS62Pres r9 (by decide)]; exact hTgt
      have h69_15 : (reg s69 r15).val = S.childEntryAt mid := by rw [h69d, hwmidVal]
      have h69_14 : (reg s69 r14).val = mid := by
        rw [h69o _ (by decide), h68o _ (by decide), h67o _ (by decide), h66o _ (by decide),
          h65o _ (by decide), h64o _ (by decide), h63o _ (by decide)]; exact h62_14
      have hS69Pres : ∀ r' : Fin 16, r' ≠ r14 → r' ≠ r15 → reg s69 r' = reg s r' := by
        intro r' h14' h15'
        rw [h69o _ h15', h68o _ h15', h67o _ h15', h66o _ h15', h65o _ h15', h64o _ h15', h63o _ h15', hS62Pres r' h14']
      have hPow2 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hcmp : S.entry u < S.childEntryAt mid
      · have hlt69 : (reg s69 r9).val < (reg s69 r15).val := by rw [h69_9, h69_15]; exact hcmp
        have h69 := step16_branchLt_true code input hpc69
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hlt69
        let s70 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s69.regs, data := s69.data, pc := 70, regs_size := s69.regs_size, data_size := s69.data_size }
        have hpc70 : s70.pc = 70 := rfl
        obtain ⟨s71, h70, hpc71, h71d, h71o, h71m⟩ := step16_mov code input hpc70
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
        have h71 := step16_goto code input hpc71
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
        let sNext : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s71.regs, data := s71.data, pc := 57, regs_size := s71.regs_size, data_size := s71.data_size }
        have hSteps15 : Steps code input 15 s sNext :=
          Steps.cons h57 <| Steps.cons h58t <| Steps.cons h59 <| Steps.cons h60 <| Steps.cons h61 <|
          Steps.cons h62 <| Steps.cons h63 <| Steps.cons h64 <| Steps.cons h65 <| Steps.cons h66 <|
          Steps.cons h67 <| Steps.cons h68 <| Steps.cons h69 <| Steps.cons h70 <| Steps.cons h71 (Steps.zero sNext)
        have hPresNext : ∀ r' : Fin 16, r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg sNext r' = reg s r' := by
          intro r' h13' h14' h15'
          change reg s71 r' = reg s r'
          rw [h71o _ h13']; exact hS69Pres r' h14' h15'
        have hDataNext : sNext.data = s.data := by change s71.data = _; rw [h71m, h69m, hS68Data]
        have hRegsNext : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase sNext :=
          { consts :=
              { zero := by rw [hPresNext rZero (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
                one := by rw [hPresNext rOne (by decide) (by decide) (by decide)]; exact hRegs.consts.one
                nVal := by rw [hPresNext rN (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
                mVal := by rw [hPresNext rM (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
                rootVal := by rw [hPresNext rRoot (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
            qVal := by rw [hPresNext r5 (by decide) (by decide) (by decide)]; exact hRegs.qVal
            treeBaseVal := by rw [hPresNext r6 (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
            emitBaseVal := by rw [hPresNext r7 (by decide) (by decide) (by decide)]; exact hRegs.emitBaseVal }
        obtain ⟨sEnd, stepsB, hBndB, hStepsB, hpcEnd, hrEnd, hPresEnd, hDataEnd⟩ :=
          ih l mid sNext hMidGt (by omega) (by omega) rfl hRegsNext
            (by rw [hPresNext r8 (by decide) (by decide) (by decide)]; exact hu)
            (by rw [hPresNext r9 (by decide) (by decide) (by decide)]; exact hTgt)
            (by rw [hPresNext r12 (by decide) (by decide) (by decide)]; exact hl)
            (by change (reg s71 r13).val = mid; rw [h71d]; exact h69_14)
            (by intro i hi; rw [hDataNext]; exact hEntries i hi)
            (by rw [hDataNext]; exact hDataSz)
        have hBRun : bsearchRun S.childEntryAt (fuel + 1) l rhs (S.entry u) =
            bsearchRun S.childEntryAt fuel l mid (S.entry u) := by
          have hcmp' : S.entry u < S.childEntryAt (l + (rhs - l) / 2) := hcmp
          have hEq1 : bsearchRun S.childEntryAt (fuel + 1) l rhs (S.entry u) =
              if l + 1 < rhs then
                let p := bsearchStep S.childEntryAt l rhs (S.entry u)
                bsearchRun S.childEntryAt fuel p.1 p.2 (S.entry u)
              else l := rfl
          rw [hEq1, ite_eq_left hcond]; dsimp only [bsearchStep]; rw [ite_eq_left hcmp']
        refine ⟨sEnd, 15 + stepsB, by omega, hSteps15.append hStepsB, hpcEnd, by rw [hBRun]; exact hrEnd, ?_, ?_⟩
        · intro r' h12' h13' h14' h15'
          rw [hPresEnd r' h12' h13' h14' h15', hPresNext r' h13' h14' h15']
        · rw [hDataEnd, hDataNext]
      · have hle69 : (reg s69 r15).val ≤ (reg s69 r9).val := by
          rw [h69_9, h69_15]; exact Nat.le_of_not_lt hcmp
        have h69 := step16_branchLt_false code input hpc69
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hle69
        let s72 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s69.regs, data := s69.data, pc := 72, regs_size := s69.regs_size, data_size := s69.data_size }
        have hpc72 : s72.pc = 72 := rfl
        obtain ⟨s73, h72, hpc73, h73d, h73o, h73m⟩ := step16_mov code input hpc72
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
        have h73 := step16_goto code input hpc73
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
        let sNext : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s73.regs, data := s73.data, pc := 57, regs_size := s73.regs_size, data_size := s73.data_size }
        have hSteps15 : Steps code input 15 s sNext :=
          Steps.cons h57 <| Steps.cons h58t <| Steps.cons h59 <| Steps.cons h60 <| Steps.cons h61 <|
          Steps.cons h62 <| Steps.cons h63 <| Steps.cons h64 <| Steps.cons h65 <| Steps.cons h66 <|
          Steps.cons h67 <| Steps.cons h68 <| Steps.cons h69 <| Steps.cons h72 <| Steps.cons h73 (Steps.zero sNext)
        have hPresNext : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r14 → r' ≠ r15 → reg sNext r' = reg s r' := by
          intro r' h12' h14' h15'
          change reg s73 r' = reg s r'
          rw [h73o _ h12']; exact hS69Pres r' h14' h15'
        have hDataNext : sNext.data = s.data := by change s73.data = _; rw [h73m, h69m, hS68Data]
        have hRegsNext : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase sNext :=
          { consts :=
              { zero := by rw [hPresNext rZero (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
                one := by rw [hPresNext rOne (by decide) (by decide) (by decide)]; exact hRegs.consts.one
                nVal := by rw [hPresNext rN (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
                mVal := by rw [hPresNext rM (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
                rootVal := by rw [hPresNext rRoot (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
            qVal := by rw [hPresNext r5 (by decide) (by decide) (by decide)]; exact hRegs.qVal
            treeBaseVal := by rw [hPresNext r6 (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
            emitBaseVal := by rw [hPresNext r7 (by decide) (by decide) (by decide)]; exact hRegs.emitBaseVal }
        obtain ⟨sEnd, stepsB, hBndB, hStepsB, hpcEnd, hrEnd, hPresEnd, hDataEnd⟩ :=
          ih mid rhs sNext hMidLt hRLe (by omega) rfl hRegsNext
            (by rw [hPresNext r8 (by decide) (by decide) (by decide)]; exact hu)
            (by rw [hPresNext r9 (by decide) (by decide) (by decide)]; exact hTgt)
            (by change (reg s73 r12).val = mid; rw [h73d]; exact h69_14)
            (by rw [hPresNext r13 (by decide) (by decide) (by decide)]; exact hR)
            (by intro i hi; rw [hDataNext]; exact hEntries i hi)
            (by rw [hDataNext]; exact hDataSz)
        have hBRun : bsearchRun S.childEntryAt (fuel + 1) l rhs (S.entry u) =
            bsearchRun S.childEntryAt fuel mid rhs (S.entry u) := by
          have hcmp' : ¬ (S.entry u < S.childEntryAt (l + (rhs - l) / 2)) := hcmp
          have hEq1 : bsearchRun S.childEntryAt (fuel + 1) l rhs (S.entry u) =
              if l + 1 < rhs then
                let p := bsearchStep S.childEntryAt l rhs (S.entry u)
                bsearchRun S.childEntryAt fuel p.1 p.2 (S.entry u)
              else l := rfl
          rw [hEq1, ite_eq_left hcond]; dsimp only [bsearchStep]; rw [ite_eq_right hcmp']
        refine ⟨sEnd, 15 + stepsB, by omega, hSteps15.append hStepsB, hpcEnd, by rw [hBRun]; exact hrEnd, ?_, ?_⟩
        · intro r' h12' h13' h14' h15'
          rw [hPresEnd r' h12' h13' h14' h15', hPresNext r' h12' h14' h15']
        · rw [hDataEnd, hDataNext]
    · have hFalse : (reg s58 r13).val ≤ (reg s58 r14).val := by rw [h58_14, h58_13]; omega
      have h58f := step16_branchLt_false code input hpc58
        (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hFalse
      let s' : State (layout16 bits inputCap workCap hi hw) :=
        { regs := s58.regs, data := s58.data, pc := 74, regs_size := s58.regs_size, data_size := s58.data_size }
      have hb : bsearchRun S.childEntryAt (fuel + 1) l rhs (S.entry u) = l := by
        unfold bsearchRun; simp only [hcond, ↓reduceIte]
      refine ⟨s', 2, by omega, Steps.cons h57 <| Steps.cons h58f (Steps.zero s'), rfl, ?_, ?_, ?_⟩
      · rw [hb]; change (reg s58 r12).val = l; rw [h58o _ (by decide)]; exact hl
      · intro r' _ _ h14' _; change reg s58 r' = reg s r'; rw [h58o _ h14']
      · change s58.data = _; rw [h58m]

private theorem scatter_inner_head {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (raw : RawDagInput input g r)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (origData[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hSelfSlots : ∀ v : Fin dense.length,
      (origData[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Fin dense.length) (j : Nat)
    (hjLt : j < (g.outArcs (dense[u.val]'u.isLt)).length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : ScatterInnerInv g r dense treeBase emitBase origData S u j s) :
    let uOrig := dense[u.val]'u.isLt
    let vOrig := (g.outArcs uOrig)[j]'hjLt
    have harcOrig : g.HasArc uOrig vOrig := List.getElem_mem hjLt
    have hvReach : g.InitiallyReachable r vOrig := initiallyReachable_extend (S.reach_mem u.val u.isLt) harcOrig
    let vDense : Fin dense.length := ⟨dense.idxOf vOrig, List.idxOf_lt_length_of_mem (S.mem_reach vOrig hvReach)⟩
    let d := S.domParent vDense
    let headLocal := S.selfSlotFn vDense
    ∃ s43, Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input 26 s s43 ∧
      s43.pc = 43 ∧
      (reg s43 r14).val = d.val ∧
      (∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s43 r' = reg s r') ∧
      (∀ k, k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1 →
        k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2 →
        s43.data[k]? = s.data[k]?) ∧
      (s43.data[emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1]?).map Fin.val = some d.val ∧
      (s43.data[emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2]?).map Fin.val = some headLocal ∧
      s43.data.size = origData.size := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hInCap : rawDagInputCap g.vertexCount g.arcCount ≤ 2 ^ bits := Nat.le_trans raw.cap_ge hi
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  have hTreeFit := S.fit
  let n := g.vertexCount
  let m := g.arcCount
  have hInCap' : 4 + n + m ≤ 2 ^ bits := by simpa [rawDagInputCap, n, m] using hInCap
  have hFitEmit' : emitBase + (3 * n + 3 * m + 3) ≤ origData.size := by
    simpa [emitterWorkWords, n, m] using hFitEmit
  have hTreeFit' : treeBase + 11 * dense.length ≤ origData.size := by
    simpa [staticTreeWords] using hTreeFit
  let uOrig := dense[u.val]'u.isLt
  let vOrig := (g.outArcs uOrig)[j]'hjLt
  have hjLt' : j < (g.outArcs uOrig).length := hjLt
  have huReach : g.InitiallyReachable r uOrig := S.reach_mem u.val u.isLt
  have harcOrig : g.HasArc uOrig vOrig := List.getElem_mem hjLt
  have hvReach : g.InitiallyReachable r vOrig := initiallyReachable_extend huReach harcOrig
  have hvDenseMem : vOrig ∈ dense := S.mem_reach vOrig hvReach
  let vDense : Fin dense.length := ⟨dense.idxOf vOrig, List.idxOf_lt_length_of_mem hvDenseMem⟩
  let d := S.domParent vDense
  let headLocal := S.selfSlotFn vDense
  have h3N_lt : 3 * n + vOrig.val < 2 ^ bits := by have := vOrig.isLt; omega
  have h3N_disj : 3 * n + vOrig.val < emitBase + n := by have := vOrig.isLt; omega
  have hFit38 : emitBase + 3 * n + 3 * m + 1 < origData.size := by omega
  have hFit42 : emitBase + 3 * n + 3 * m + 2 < origData.size := by omega
  have hBits42 : emitBase + 3 * n + 3 * m + 2 < 2 ^ bits := by omega
  have hEmitV_lt : emitBase + vDense.val < 2 ^ bits := by have := vDense.isLt; omega
  have hEmitV_disj : emitBase + vDense.val < emitBase + n := by have := vDense.isLt; omega
  have hEmitV_ne : emitBase + vDense.val ≠ emitBase + 3 * n + 3 * m + 1 := by have := vDense.isLt; omega
  have h3N3M1_lt : 3 * n + 3 * m < 2 ^ bits := by omega
  have hEmit3N3M1_lt : emitBase + 3 * n + 3 * m + 1 < 2 ^ bits := by omega
  have hTreeBeforeOrAfter : ∀ idx, idx < 11 * dense.length →
      treeBase + idx < emitBase + n ∨ emitBase + 3 * n + 3 * m + 3 ≤ treeBase + idx := by
    intro idx hidx
    unfold staticTreeWords emitterWorkWords at hDisjTreeEmit
    rcases hDisjTreeEmit with hl | hr
    · left; omega
    · right; omega
  have hOutBnd : outPrefix g uOrig.val + j < m := by
    have h1 : outPrefix g (uOrig.val + 1) ≤ outPrefix g g.vertexCount := outPrefix_mono g uOrig.isLt
    rw [outPrefix_succ_lt g uOrig, outPrefix_vertexCount] at h1
    change outPrefix g uOrig.val + j < g.arcCount; omega
  have hN : (reg s rN).val = n := inv.regs.consts.nVal
  have hM : (reg s rM).val = m := inv.regs.consts.mVal
  have hOne : (reg s rOne).val = 1 := inv.regs.consts.one
  have hTreeBase : (reg s r6).val = treeBase := inv.regs.treeBaseVal
  have hEmitBase : (reg s r7).val = emitBase := inv.regs.emitBaseVal
  have hEidx : (reg s r10).val = outPrefix g uOrig.val + j := inv.eIdxEq
  have hlt17 : (reg s r10).val < (reg s r11).val := by rw [inv.eIdxEq, inv.eEndEq]; omega
  have h17 := step16_branchLt_true code input inv.pcEq
    (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hlt17
  let s18 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 18, regs_size := s.regs_size, data_size := s.data_size }
  have hpc18 : s18.pc = 18 := rfl
  obtain ⟨s19, h18, hpc19, h19d, h19o, h19m⟩ := step16_add code input hpc18 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s20, h19, hpc20, h20d, h20o, h20m⟩ := step16_add code input hpc19 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s21, h20, hpc21, h21d, h21o, h21m⟩ := step16_add code input hpc20 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s22, h21, hpc22, h22d, h22o, h22m⟩ := step16_add code input hpc21 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s23, h22, hpc23, h23d, h23o, h23m⟩ := step16_add code input hpc22 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hr19 : (reg s19 r12).val = n + (outPrefix g uOrig.val + j) := by
    change (reg s rN).val = n at hN
    rw [h19d, add_no_wrap _ _ (by change (reg s rN).val + (reg s r10).val < 2 ^ bits; rw [hN, hEidx]; omega)]
    change (reg s rN).val + (reg s r10).val = _; rw [hN, hEidx]
  have hr20 : (reg s20 r12).val = n + (outPrefix g uOrig.val + j) + 1 := by
    have h19_1 : (reg s19 rOne).val = 1 := by rw [h19o _ (by decide)]; exact hOne
    rw [h20d, add_no_wrap _ _ (by rw [hr19, h19_1]; omega), hr19, h19_1]
  have hr21 : (reg s21 r12).val = n + (outPrefix g uOrig.val + j) + 2 := by
    have h20_1 : (reg s20 rOne).val = 1 := by rw [h20o _ (by decide), h19o _ (by decide)]; exact hOne
    rw [h21d, add_no_wrap _ _ (by rw [hr20, h20_1]; omega), hr20, h20_1]
  have hr22 : (reg s22 r12).val = n + (outPrefix g uOrig.val + j) + 3 := by
    have h21_1 : (reg s21 rOne).val = 1 := by rw [h21o _ (by decide), h20o _ (by decide), h19o _ (by decide)]; exact hOne
    rw [h22d, add_no_wrap _ _ (by rw [hr21, h21_1]; omega), hr21, h21_1]
  have hr23 : (reg s23 r12).val = 4 + n + outPrefix g uOrig.val + j := by
    have h22_1 : (reg s22 rOne).val = 1 := by
      rw [h22o _ (by decide), h21o _ (by decide), h20o _ (by decide), h19o _ (by decide)]; exact hOne
    rw [h23d, add_no_wrap _ _ (by rw [hr22, h22_1]; omega), hr22, h22_1]; omega
  have hTargetMem : (input.words[(reg s23 r12).val]?).map Fin.val = some vOrig.val := by
    rw [hr23]; exact raw.out_targets uOrig j hjLt
  obtain ⟨wv, hwv, hwvVal⟩ := data_val_at hTargetMem
  obtain ⟨s24, h23, hpc24, h24d, h24o, h24m⟩ :=
    step16_loadInput code input hpc23 (by rw [scatterCode_head (by decide)]; rfl) hwv (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s25, h24, hpc25, h25d, h25o, h25m⟩ := step16_add code input hpc24 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s26, h25, hpc26, h26d, h26o, h26m⟩ := step16_add code input hpc25 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s27, h26, hpc27, h27d, h27o, h27m⟩ := step16_add code input hpc26 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hS24Pres : ∀ r' : Fin 16, r' ≠ r12 → reg s24 r' = reg s r' := by
    intro r' h12'
    rw [h24o _ h12', h23o _ h12', h22o _ h12', h21o _ h12', h20o _ h12', h19o _ h12']; rfl
  have h24_12 : (reg s24 r12).val = vOrig.val := by rw [h24d, hwvVal]
  have h24_n : (reg s24 rN).val = n := by rw [hS24Pres rN (by decide)]; exact hN
  have hr25 : (reg s25 r13).val = 2 * n := by
    rw [h25d, add_no_wrap _ _ (by rw [h24_n]; omega), h24_n]; omega
  have hr26 : (reg s26 r13).val = 3 * n := by
    have h25_n : (reg s25 rN).val = n := by rw [h25o _ (by decide)]; exact h24_n
    rw [h26d, add_no_wrap _ _ (by rw [hr25, h25_n]; omega), hr25, h25_n]; omega
  have hr27 : (reg s27 r13).val = 3 * n + vOrig.val := by
    have h26_12 : (reg s26 r12).val = vOrig.val := by rw [h26o _ (by decide), h25o _ (by decide)]; exact h24_12
    rw [h27d, add_no_wrap _ _ (by rw [hr26, h26_12]; exact h3N_lt), hr26, h26_12]
  have hS27Data : s27.data = s.data := by
    rw [h27m, h26m, h25m, h24m, h23m, h22m, h21m, h20m, h19m]
  have hVDenseMem : (s27.data[(reg s27 r13).val]?).map Fin.val = some (vDense.val + 1) := by
    rw [hr27, hS27Data]
    have hDisj : 3 * n + vOrig.val < emitBase + n ∨
        (emitBase + n + dense.length ≤ 3 * n + vOrig.val ∧ 3 * n + vOrig.val < emitBase + 3 * n + 1) ∨
        emitBase + 3 * n + 3 * m + 3 ≤ 3 * n + vOrig.val := Or.inl h3N_disj
    have hOrigEq : origToDensePlusOneBase g.vertexCount g.arcCount + vOrig.val = 3 * n + vOrig.val := by
      unfold origToDensePlusOneBase; simp [n]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (by rw [← hOrigEq]; exact hOrigToDense vOrig hvReach)
  obtain ⟨wvp, hwvp, hwvpVal⟩ := data_val_at hVDenseMem
  obtain ⟨s28, h27, hpc28, h28d, h28o, h28m⟩ :=
    step16_loadData code input hpc27 (by rw [scatterCode_head (by decide)]; rfl) hwvp (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s29, h28, hpc29, h29d, h29o, h29m⟩ := step16_sub code input hpc28 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s30, h29, hpc30, h30d, h30o, h30m⟩ := step16_add code input hpc29 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hS27Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → reg s27 r' = reg s r' := by
    intro r' h12' h13'
    rw [h27o _ h13', h26o _ h13', h25o _ h13', hS24Pres r' h12']
  have h28_13 : (reg s28 r13).val = vDense.val + 1 := by rw [h28d, hwvpVal]
  have h28_1 : (reg s28 rOne).val = 1 := by rw [h28o _ (by decide), hS27Pres rOne (by decide) (by decide)]; exact hOne
  have hr29 : (reg s29 r13).val = vDense.val := by
    rw [h29d, sub_exact _ _ (by rw [h28_13, h28_1]; omega), h28_13, h28_1]; omega
  have hr30 : (reg s30 r14).val = treeBase + vDense.val := by
    have h29_6 : (reg s29 r6).val = treeBase := by
      rw [h29o _ (by decide), h28o _ (by decide), hS27Pres r6 (by decide) (by decide)]; exact hTreeBase
    rw [h30d, add_no_wrap _ _ (by rw [h29_6, hr29]; have := vDense.isLt; omega), h29_6, hr29]
  have hS30Data : s30.data = s.data := by rw [h30m, h29m, h28m, hS27Data]
  have hDomMem : (s30.data[(reg s30 r14).val]?).map Fin.val = some d.val := by
    rw [hr30, hS30Data]
    have hDisj : treeBase + vDense.val < emitBase + n ∨
        (emitBase + n + dense.length ≤ treeBase + vDense.val ∧ treeBase + vDense.val < emitBase + 3 * n + 1) ∨
        emitBase + 3 * n + 3 * m + 3 ≤ treeBase + vDense.val := by
      rcases hTreeBeforeOrAfter vDense.val (by have := vDense.isLt; omega) with hl | hr
      · exact Or.inl hl
      · exact Or.inr (Or.inr hr)
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (S.domParent_mem vDense)
  obtain ⟨wd, hwd, hwdVal⟩ := data_val_at hDomMem
  obtain ⟨s31, h30, hpc31, h31d, h31o, h31m⟩ :=
    step16_loadData code input hpc30 (by rw [scatterCode_head (by decide)]; rfl) hwd (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s32, h31, hpc32, h32d, h32o, h32m⟩ := step16_add code input hpc31 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s33, h32, hpc33, h33d, h33o, h33m⟩ := step16_add code input hpc32 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s34, h33, hpc34, h34d, h34o, h34m⟩ := step16_add code input hpc33 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s35, h34, hpc35, h35d, h35o, h35m⟩ := step16_add code input hpc34 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s36, h35, hpc36, h36d, h36o, h36m⟩ := step16_add code input hpc35 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s37, h36, hpc37, h37d, h37o, h37m⟩ := step16_add code input hpc36 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s38, h37, hpc38, h38d, h38o, h38m⟩ := step16_add code input hpc37 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hS31Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → reg s31 r' = reg s r' := by
    intro r' h12' h13' h14'
    rw [h31o _ h14', h30o _ h14', h29o _ h13', h28o _ h13', hS27Pres r' h12' h13']
  have hr32 : (reg s32 r15).val = 2 * n := by
    have h31_n : (reg s31 rN).val = n := by rw [hS31Pres rN (by decide) (by decide) (by decide)]; exact hN
    rw [h32d, add_no_wrap _ _ (by rw [h31_n]; omega), h31_n]; omega
  have hr33 : (reg s33 r15).val = 3 * n := by
    have h32_n : (reg s32 rN).val = n := by rw [h32o _ (by decide), hS31Pres rN (by decide) (by decide) (by decide)]; exact hN
    rw [h33d, add_no_wrap _ _ (by rw [hr32, h32_n]; omega), hr32, h32_n]; omega
  have hr34 : (reg s34 r15).val = 3 * n + m := by
    have h33_m : (reg s33 rM).val = m := by
      rw [h33o _ (by decide), h32o _ (by decide), hS31Pres rM (by decide) (by decide) (by decide)]; exact hM
    rw [h34d, add_no_wrap _ _ (by rw [hr33, h33_m]; omega), hr33, h33_m]
  have hr35 : (reg s35 r15).val = 3 * n + 2 * m := by
    have h34_m : (reg s34 rM).val = m := by
      rw [h34o _ (by decide), h33o _ (by decide), h32o _ (by decide), hS31Pres rM (by decide) (by decide) (by decide)]; exact hM
    rw [h35d, add_no_wrap _ _ (by rw [hr34, h34_m]; omega), hr34, h34_m]; omega
  have hr36 : (reg s36 r15).val = 3 * n + 3 * m := by
    have h35_m : (reg s35 rM).val = m := by
      rw [h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide), hS31Pres rM (by decide) (by decide) (by decide)]; exact hM
    rw [h36d, add_no_wrap _ _ (by rw [hr35, h35_m]; omega), hr35, h35_m]; omega
  have hr37 : (reg s37 r15).val = emitBase + 3 * n + 3 * m := by
    have h36_7 : (reg s36 r7).val = emitBase := by
      rw [h36o _ (by decide), h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide), hS31Pres r7 (by decide) (by decide) (by decide)]; exact hEmitBase
    rw [h37d, add_no_wrap _ _ (by rw [hr36, h36_7]; omega), hr36, h36_7]; omega
  have hr38 : (reg s38 r15).val = emitBase + 3 * n + 3 * m + 1 := by
    have h37_1 : (reg s37 rOne).val = 1 := by
      rw [h37o _ (by decide), h36o _ (by decide), h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide), hS31Pres rOne (by decide) (by decide) (by decide)]; exact hOne
    rw [h38d, add_no_wrap _ _ (by rw [hr37, h37_1]; omega), hr37, h37_1]
  have hS38Data : s38.data = s.data := by rw [h38m, h37m, h36m, h35m, h34m, h33m, h32m, h31m, hS30Data]
  have hBnd38 : (reg s38 r15).val < s38.data.size := by
    rw [hr38, hS38Data, inv.dataSize]; exact hFit38
  obtain ⟨s39, h38, hpc39, h39regs, h39data⟩ :=
    step16_storeData code input hpc38 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd38
  obtain ⟨s40, h39, hpc40, h40d, h40o, h40m⟩ := step16_add code input hpc39 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hr40 : (reg s40 r13).val = emitBase + vDense.val := by
    have h39_7 : (reg s39 r7).val = emitBase := by
      rw [reg_eq_of_regs_eq h39regs r7, h38o _ (by decide), h37o _ (by decide), h36o _ (by decide),
        h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide),
        hS31Pres r7 (by decide) (by decide) (by decide)]; exact hEmitBase
    have h39_13 : (reg s39 r13).val = vDense.val := by
      rw [reg_eq_of_regs_eq h39regs r13, h38o _ (by decide), h37o _ (by decide), h36o _ (by decide),
        h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide),
        h31o _ (by decide), h30o _ (by decide)]; exact hr29
    rw [h40d, add_no_wrap _ _ (by rw [h39_7, h39_13]; exact hEmitV_lt), h39_7, h39_13]
  have hS40Data : s40.data = s.data.set (emitBase + 3 * n + 3 * m + 1) (reg s38 r14)
      (by have hSz : s38.data.size = s.data.size := by rw [hS38Data]
          rw [← hr38, ← hSz]; exact hBnd38) := by
    rw [h40m, h39data]
    exact array_set_congr hS38Data hr38 rfl
  have hSelfMem : (s40.data[(reg s40 r13).val]?).map Fin.val = some headLocal := by
    rw [hr40, hS40Data]
    rw [array_set_getElem?_ne _ _ _ _ _ hEmitV_ne]
    have hDisj : emitBase + vDense.val < emitBase + n ∨
        (emitBase + n + dense.length ≤ emitBase + vDense.val ∧ emitBase + vDense.val < emitBase + 3 * n + 1) ∨
        emitBase + 3 * n + 3 * m + 3 ≤ emitBase + vDense.val := Or.inl hEmitV_disj
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (hSelfSlots vDense)
  obtain ⟨whd, hwhd, hwhdVal⟩ := data_val_at hSelfMem
  obtain ⟨s41, h40, hpc41, h41d, h41o, h41m⟩ :=
    step16_loadData code input hpc40 (by rw [scatterCode_head (by decide)]; rfl) hwhd (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s42, h41, hpc42, h42d, h42o, h42m⟩ := step16_add code input hpc41 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hr42 : (reg s42 r15).val = emitBase + 3 * n + 3 * m + 2 := by
    have h41_15 : (reg s41 r15).val = emitBase + 3 * n + 3 * m + 1 := by
      rw [h41o _ (by decide), h40o _ (by decide), reg_eq_of_regs_eq h39regs r15]; exact hr38
    have h41_1 : (reg s41 rOne).val = 1 := by
      rw [h41o _ (by decide), h40o _ (by decide), reg_eq_of_regs_eq h39regs rOne,
        h38o _ (by decide), h37o _ (by decide), h36o _ (by decide), h35o _ (by decide),
        h34o _ (by decide), h33o _ (by decide), h32o _ (by decide),
        hS31Pres rOne (by decide) (by decide) (by decide)]; exact hOne
    rw [h42d, add_no_wrap _ _ (by rw [h41_15, h41_1]; exact hBits42), h41_15, h41_1]
  have hBnd42 : (reg s42 r15).val < s42.data.size := by
    rw [hr42, h42m, h41m, hS40Data, Array.size_set, inv.dataSize]; exact hFit42
  obtain ⟨s43, h42, hpc43, h43regs, h43data⟩ :=
    step16_storeData code input hpc42 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd42
  have hPre43 : Steps code input 26 s s43 :=
    Steps.cons h17 <| Steps.cons h18 <| Steps.cons h19 <| Steps.cons h20 <| Steps.cons h21 <|
    Steps.cons h22 <| Steps.cons h23 <| Steps.cons h24 <| Steps.cons h25 <| Steps.cons h26 <|
    Steps.cons h27 <| Steps.cons h28 <| Steps.cons h29 <| Steps.cons h30 <| Steps.cons h31 <|
    Steps.cons h32 <| Steps.cons h33 <| Steps.cons h34 <| Steps.cons h35 <| Steps.cons h36 <|
    Steps.cons h37 <| Steps.cons h38 <| Steps.cons h39 <| Steps.cons h40 <| Steps.cons h41 <|
    Steps.cons h42 (Steps.zero s43)
  have h43_d : (reg s43 r14).val = d.val := by
    rw [reg_eq_of_regs_eq h43regs r14, h42o _ (by decide), h41o _ (by decide), h40o _ (by decide),
      reg_eq_of_regs_eq h39regs r14, h38o _ (by decide), h37o _ (by decide), h36o _ (by decide),
      h35o _ (by decide), h34o _ (by decide), h33o _ (by decide), h32o _ (by decide),
      h31d, hwdVal]
  have h43_38r14 : (reg s38 r14).val = d.val := by
    rw [h38o _ (by decide), h37o _ (by decide), h36o _ (by decide), h35o _ (by decide),
      h34o _ (by decide), h33o _ (by decide), h32o _ (by decide), h31d, hwdVal]
  have h43Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s43 r' = reg s r' := by
    intro r' h12' h13' h14' h15'
    rw [reg_eq_of_regs_eq h43regs r', h42o _ h15', h41o _ h13', h40o _ h13',
      reg_eq_of_regs_eq h39regs r', h38o _ h15', h37o _ h15', h36o _ h15',
      h35o _ h15', h34o _ h15', h33o _ h15', h32o _ h15', hS31Pres r' h12' h13' h14']
  have hS43ScratchPres : ∀ k, k ≠ emitBase + 3 * n + 3 * m + 1 → k ≠ emitBase + 3 * n + 3 * m + 2 →
      s43.data[k]? = s.data[k]? := by
    intro k hk1 hk2
    rw [h43data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr42]; exact hk2),
      h42m, h41m, hS40Data, array_set_getElem?_ne _ _ _ _ _ hk1]
  have hS43Scr0 : (s43.data[emitBase + 3 * n + 3 * m + 1]?).map Fin.val = some d.val := by
    rw [h43data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr42]; omega),
      h42m, h41m, hS40Data, array_set_getElem?_same, Option.map_some, h43_38r14]
  have hS43Scr1 : (s43.data[emitBase + 3 * n + 3 * m + 2]?).map Fin.val = some headLocal := by
    rw [h43data]
    have hget : (s42.data.set (reg s42 r15).val (reg s42 r13) hBnd42)[emitBase + 3 * n + 3 * m + 2]? =
        some (reg s42 r13) := by
      rw [← hr42]; exact array_set_getElem?_same _ _ _ _
    rw [hget, Option.map_some, h42o _ (by decide), h41d, hwhdVal]
  have hS43Sz : s43.data.size = origData.size := by
    rw [h43data, Array.size_set, h42m, h41m, hS40Data, Array.size_set, inv.dataSize]
  exact ⟨s43, hPre43, hpc43, h43_d, h43Pres, hS43ScratchPres, hS43Scr0, hS43Scr1, hS43Sz⟩

private theorem scatter_inner_mid {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (acyc : g.IsAcyclic)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Fin dense.length) (vDense : Fin dense.length)
    (harcOrig : g.HasArc (dense[u.val]'u.isLt) (dense[vDense.val]'vDense.isLt))
    (s : State (layout16 bits inputCap workCap hi hw))
    (s43 : State (layout16 bits inputCap workCap hi hw))
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s)
    (hS_8 : (reg s r8).val = u.val)
    (hS_9 : (reg s r9).val = S.entry u)
    (hOrigPres : ∀ k, (k < emitBase + g.vertexCount ∨
        (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 3 * g.vertexCount + 1) ∨
        emitBase + 3 * g.vertexCount + 3 * g.arcCount + 3 ≤ k) →
      s.data[k]? = origData[k]?)
    (hpc43 : s43.pc = 43)
    (h43_d : (reg s43 r14).val = (S.domParent vDense).val)
    (h43Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s43 r' = reg s r')
    (hS43ScratchPres : ∀ k, k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1 →
      k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2 →
      s43.data[k]? = s.data[k]?)
    (hS43Scr0 : (s43.data[emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1]?).map Fin.val =
      some (S.domParent vDense).val)
    (hS43Sz : s43.data.size = origData.size) :
    ∃ s92 stepsMid, stepsMid ≤ 32 + 15 * OracleContract.L g.vertexCount ∧
      Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input stepsMid s43 s92 ∧
      s92.pc = 92 ∧
      (reg s92 r12).val = S.srcLocalOf (S.domParent vDense) u ∧
      (∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s92 r' = reg s r') ∧
      s92.data = s43.data := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  let n := g.vertexCount
  let m := g.arcCount
  let d := S.domParent vDense
  let srcLocal := S.srcLocalOf d u
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s43.data_size; rw [hS43Sz] at h1; change origData.size = workCap at h1; omega
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  have hTreeFit := S.fit
  have hFitEmit' : emitBase + (3 * n + 3 * m + 3) ≤ origData.size := by
    simpa [emitterWorkWords, n, m] using hFitEmit
  have hTreeFit' : treeBase + 11 * dense.length ≤ origData.size := by
    simpa [staticTreeWords] using hTreeFit
  have hTreeBeforeOrAfter : ∀ idx, idx < 11 * dense.length →
      treeBase + idx < emitBase + n ∨ emitBase + 3 * n + 3 * m + 3 ≤ treeBase + idx := by
    intro idx hidx
    unfold staticTreeWords emitterWorkWords at hDisjTreeEmit
    rcases hDisjTreeEmit with hl | hr
    · left; omega
    · right; omega
  have hN : (reg s rN).val = n := hRegs.consts.nVal
  have hM : (reg s rM).val = m := hRegs.consts.mVal
  have hOne : (reg s rOne).val = 1 := hRegs.consts.one
  have hQ : (reg s r5).val = dense.length := hRegs.qVal
  have hTreeBase : (reg s r6).val = treeBase := hRegs.treeBaseVal
  have hEmitBase : (reg s r7).val = emitBase := hRegs.emitBaseVal
  by_cases hud : u.val = d.val
  · have h43_8 : (reg s43 r8).val = u.val := by
      rw [h43Pres r8 (by decide) (by decide) (by decide) (by decide)]; exact hS_8
    have hf1 : (reg s43 r14).val ≤ (reg s43 r8).val := by rw [h43_8, h43_d, hud]; exact Nat.le_refl _
    have h43f := step16_branchLt_false code input hpc43
      (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hf1
    let s44 : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s43.regs, data := s43.data, pc := 44, regs_size := s43.regs_size, data_size := s43.data_size }
    have hpc44 : s44.pc = 44 := rfl
    have hf2 : (reg s44 r8).val ≤ (reg s44 r14).val := by
      change (reg s43 r8).val ≤ (reg s43 r14).val; rw [h43_8, h43_d, hud]; exact Nat.le_refl _
    have h44f := step16_branchLt_false code input hpc44
      (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hf2
    let s45 : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s44.regs, data := s44.data, pc := 45, regs_size := s44.regs_size, data_size := s44.data_size }
    have hpc45 : s45.pc = 45 := rfl
    obtain ⟨s46, h45, hpc46, h46d, h46o, h46m⟩ :=
      step16_mov code input hpc45 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have h46 := step16_goto code input hpc46
      (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    let s92 : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s46.regs, data := s46.data, pc := 92, regs_size := s46.regs_size, data_size := s46.data_size }
    have hSrc0 : srcLocal = 0 := by unfold srcLocal StaticTreeSlice.srcLocalOf; simp [hud]
    refine ⟨s92, 4, Nat.le_trans (by decide : 4 ≤ 32) (Nat.le_add_right _ _),
      Steps.cons h43f <| Steps.cons h44f <| Steps.cons h45 <| Steps.cons h46 (Steps.zero s92),
      rfl, ?_, ?_, ?_⟩
    · change (reg s46 r12).val = srcLocal
      rw [hSrc0, h46d]
      change (reg s43 rZero).val = 0
      rw [h43Pres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
    · intro r' h12' h13' h14' h15'
      change reg s46 r' = reg s r'
      rw [h46o _ h12']; exact h43Pres r' h12' h13' h14' h15'
    · change s46.data = s43.data; exact h46m
  · have h43_8 : (reg s43 r8).val = u.val := by
      rw [h43Pres r8 (by decide) (by decide) (by decide) (by decide)]; exact hS_8
    have hEnter47 : ∃ s47 stepsBr, stepsBr ≤ 2 ∧ Steps code input stepsBr s43 s47 ∧
        s47.pc = 47 ∧ s47.regs = s43.regs ∧ s47.data = s43.data := by
      rcases Nat.lt_or_gt_of_ne hud with hlt | hgt
      · have h1 := step16_branchLt_true code input hpc43
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
          (by rw [h43_8, h43_d]; exact hlt)
        exact ⟨_, 1, by omega, Steps.cons h1 (Steps.zero _), rfl, rfl, rfl⟩
      · have hf1 := step16_branchLt_false code input hpc43
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
          (by rw [h43_8, h43_d]; exact Nat.le_of_lt hgt)
        let s44 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s43.regs, data := s43.data, pc := 44, regs_size := s43.regs_size, data_size := s43.data_size }
        have hpc44 : s44.pc = 44 := rfl
        have ht2 := step16_branchLt_true code input hpc44
          (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
          (by change (reg s43 r14).val < (reg s43 r8).val; rw [h43_8, h43_d]; exact hgt)
        exact ⟨_, 2, Nat.le_refl 2,
          Steps.cons hf1 <| Steps.cons ht2 (Steps.zero _), rfl, rfl, rfl⟩
    obtain ⟨s47, stepsBr, hBrBnd, hStepsBr, hpc47, h47regs, h47data⟩ := hEnter47
    have huReach : g.InitiallyReachable r (dense[u.val]'u.isLt) := S.reach_mem u.val u.isLt
    have hDomDU : g.Dominates r (dense[d.val]'d.isLt) (dense[u.val]'u.isLt) := by
      have hvPos : 0 < vDense.val := by
        by_cases hv0 : vDense.val = 0
        · exfalso
          have hvR : dense[vDense.val]'vDense.isLt = r := by
            have hv0' : vDense = ⟨0, S.qPos⟩ := Fin.ext hv0
            rw [hv0', S.head_eq]
          have ⟨rank, progress⟩ := acyc
          have hPath := initiallyReachable_rank_le (r := r) progress (dense[u.val]'u.isLt) huReach
          rw [hvR] at harcOrig
          have hArcLt := progress _ _ harcOrig
          omega
        · exact Nat.pos_of_ne_zero hv0
      have himmV := S.domParent_spec vDense hvPos
      exact dominates_reachable_predecessor_of_ne harcOrig huReach
        (fun e' => (S.domParent_ne_self vDense hvPos).symm (S.dense_injective e')) himmV.2.1
    have hChildEx : S.childStart d.val < S.childStart (d.val + 1) := by
      rcases S.srcLocalOf_spec acyc d u hDomDU with ⟨hudEq, _⟩ | ⟨c, hcMem, _, _⟩
      · exact False.elim (hud (congrArg Fin.val hudEq))
      · obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp hcMem
        simp only [StaticTreeSlice.childSlice, List.length_ofFn] at hk
        omega
    have hREnd : S.childStart (d.val + 1) ≤ dense.length - 1 := by
      have hm := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
      rwa [S.childStart_end] at hm
    obtain ⟨s48, h47, hpc48, h48d, h48o, h48m⟩ := step16_add code input hpc47 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s49, h48, hpc49, h49d, h49o, h49m⟩ := step16_add code input hpc48 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s50, h49, hpc50, h50d, h50o, h50m⟩ := step16_add code input hpc49 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s51, h50, hpc51, h51d, h51o, h51m⟩ := step16_add code input hpc50 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s52, h51, hpc52, h52d, h52o, h52m⟩ := step16_add code input hpc51 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s53, h52, hpc53, h53d, h53o, h53m⟩ := step16_add code input hpc52 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s54, h53, hpc54, h54d, h54o, h54m⟩ := step16_add code input hpc53 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have hS47Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s47 r' = reg s r' := by
      intro r' h12' h13' h14' h15'; rw [reg_eq_of_regs_eq h47regs r']; exact h43Pres r' h12' h13' h14' h15'
    have h47_Q : (reg s47 r5).val = dense.length := by rw [hS47Pres r5 (by decide) (by decide) (by decide) (by decide)]; exact hQ
    have h47_TB : (reg s47 r6).val = treeBase := by rw [hS47Pres r6 (by decide) (by decide) (by decide) (by decide)]; exact hTreeBase
    have h47_d : (reg s47 r14).val = d.val := by rw [reg_eq_of_regs_eq h47regs r14]; exact h43_d
    have hr48 : (reg s48 r15).val = 2 * dense.length := by
      rw [h48d, add_no_wrap _ _ (by rw [h47_Q]; omega), h47_Q]; omega
    have hr49 : (reg s49 r15).val = 4 * dense.length := by
      rw [h49d, add_no_wrap _ _ (by rw [hr48]; omega), hr48]; omega
    have hr50 : (reg s50 r15).val = 5 * dense.length := by
      have h49_5 : (reg s49 r5).val = dense.length := by rw [h49o _ (by decide), h48o _ (by decide)]; exact h47_Q
      rw [h50d, add_no_wrap _ _ (by rw [hr49, h49_5]; omega), hr49, h49_5]; omega
    have hr51 : (reg s51 r15).val = 6 * dense.length := by
      have h50_5 : (reg s50 r5).val = dense.length := by rw [h50o _ (by decide), h49o _ (by decide), h48o _ (by decide)]; exact h47_Q
      rw [h51d, add_no_wrap _ _ (by rw [hr50, h50_5]; omega), hr50, h50_5]; omega
    have hr52 : (reg s52 r15).val = 7 * dense.length := by
      have h51_5 : (reg s51 r5).val = dense.length := by rw [h51o _ (by decide), h50o _ (by decide), h49o _ (by decide), h48o _ (by decide)]; exact h47_Q
      rw [h52d, add_no_wrap _ _ (by rw [hr51, h51_5]; omega), hr51, h51_5]; omega
    have hr53 : (reg s53 r15).val = treeBase + 7 * dense.length := by
      have h52_6 : (reg s52 r6).val = treeBase := by rw [h52o _ (by decide), h51o _ (by decide), h50o _ (by decide), h49o _ (by decide), h48o _ (by decide)]; exact h47_TB
      rw [h53d, add_no_wrap _ _ (by rw [hr52, h52_6]; omega), hr52, h52_6]; omega
    have hr54 : (reg s54 r15).val = treeBase + 7 * dense.length + d.val := by
      have h53_14 : (reg s53 r14).val = d.val := by
        rw [h53o _ (by decide), h52o _ (by decide), h51o _ (by decide), h50o _ (by decide),
          h49o _ (by decide), h48o _ (by decide)]; exact h47_d
      rw [h54d, add_no_wrap _ _ (by rw [hr53, h53_14]; have := d.isLt; omega), hr53, h53_14]
    have hS54Data : s54.data = s43.data := by
      rw [h54m, h53m, h52m, h51m, h50m, h49m, h48m, h47data]
    have hTreePresS43 : ∀ idx, idx < 11 * dense.length → s43.data[treeBase + idx]? = origData[treeBase + idx]? := by
      intro idx hidx
      have hScr := hS43ScratchPres (treeBase + idx)
        (by rcases hTreeBeforeOrAfter idx hidx with hl | hr <;> omega)
        (by rcases hTreeBeforeOrAfter idx hidx with hl | hr <;> omega)
      have hDisj : treeBase + idx < emitBase + n ∨
          (emitBase + n + dense.length ≤ treeBase + idx ∧ treeBase + idx < emitBase + 3 * n + 1) ∨
          emitBase + 3 * n + 3 * m + 3 ≤ treeBase + idx := by
        rcases hTreeBeforeOrAfter idx hidx with hl | hr
        · exact Or.inl hl
        · exact Or.inr (Or.inr hr)
      exact hScr.trans (hOrigPres _ hDisj)
    have hCS0Mem : (s54.data[(reg s54 r15).val]?).map Fin.val = some (S.childStart d.val) := by
      rw [hr54, hS54Data]
      have heq := hTreePresS43 (7 * dense.length + d.val) (by have := d.isLt; omega)
      rw [show treeBase + (7 * dense.length + d.val) = treeBase + 7 * dense.length + d.val by omega] at heq
      exact data_mem_val_of_eq heq (S.childStart_mem d.val (Nat.le_of_lt d.isLt))
    obtain ⟨wcs0, hwcs0, hwcs0Val⟩ := data_val_at hCS0Mem
    obtain ⟨s55, h54, hpc55, h55d, h55o, h55m⟩ :=
      step16_loadData code input hpc54 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) hwcs0 (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s56, h55, hpc56, h56d, h56o, h56m⟩ := step16_add code input hpc55 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have hr56 : (reg s56 r15).val = treeBase + 7 * dense.length + (d.val + 1) := by
      have h55_15 : (reg s55 r15).val = treeBase + 7 * dense.length + d.val := by rw [h55o _ (by decide)]; exact hr54
      have h55_1 : (reg s55 rOne).val = 1 := by
        rw [h55o _ (by decide), h54o _ (by decide), h53o _ (by decide), h52o _ (by decide),
          h51o _ (by decide), h50o _ (by decide), h49o _ (by decide), h48o _ (by decide),
          hS47Pres rOne (by decide) (by decide) (by decide) (by decide)]; exact hOne
      rw [h56d, add_no_wrap _ _ (by rw [h55_15, h55_1]; have := d.isLt; omega), h55_15, h55_1]; omega
    have hS56Data : s56.data = s43.data := by rw [h56m, h55m, hS54Data]
    have hCS1Mem : (s56.data[(reg s56 r15).val]?).map Fin.val = some (S.childStart (d.val + 1)) := by
      rw [hr56, hS56Data]
      have heq := hTreePresS43 (7 * dense.length + (d.val + 1)) (by have := d.isLt; omega)
      rw [show treeBase + (7 * dense.length + (d.val + 1)) = treeBase + 7 * dense.length + (d.val + 1) by omega] at heq
      exact data_mem_val_of_eq heq (S.childStart_mem (d.val + 1) d.isLt)
    obtain ⟨wcs1, hwcs1, hwcs1Val⟩ := data_val_at hCS1Mem
    obtain ⟨s57, h56, hpc57, h57d, h57o, h57m⟩ :=
      step16_loadData code input hpc56 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) hwcs1 (by rw [scatterQuotientArcsCode_size]; decide)
    have hPre57 : Steps code input 10 s47 s57 :=
      Steps.cons h47 <| Steps.cons h48 <| Steps.cons h49 <| Steps.cons h50 <| Steps.cons h51 <|
      Steps.cons h52 <| Steps.cons h53 <| Steps.cons h54 <| Steps.cons h55 <| Steps.cons h56 (Steps.zero s57)
    have h57Data : s57.data = s43.data := by rw [h57m, hS56Data]
    have h57Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s57 r' = reg s r' := by
      intro r' h12' h13' h14' h15'
      rw [h57o _ h13', h56o _ h15', h55o _ h12', h54o _ h15', h53o _ h15', h52o _ h15',
        h51o _ h15', h50o _ h15', h49o _ h15', h48o _ h15']
      exact hS47Pres r' h12' h13' h14' h15'
    have hRegs57 : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s57 :=
      { consts :=
          { zero := by rw [h57Pres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [h57Pres rOne (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [h57Pres rN (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [h57Pres rM (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [h57Pres rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [h57Pres r5 (by decide) (by decide) (by decide) (by decide)]; exact hQ
        treeBaseVal := by rw [h57Pres r6 (by decide) (by decide) (by decide) (by decide)]; exact hTreeBase
        emitBaseVal := by rw [h57Pres r7 (by decide) (by decide) (by decide) (by decide)]; exact hEmitBase }
    have hPowL : S.childStart (d.val + 1) - S.childStart d.val ≤ 2 ^ OracleContract.L g.vertexCount := by
      have h1 : S.childStart (d.val + 1) - S.childStart d.val ≤ dense.length := by omega
      have h3 : g.vertexCount + 1 < 2 ^ ((g.vertexCount + 1).log2 + 1) := Nat.lt_log2_self (n := g.vertexCount + 1)
      have h4 : 2 ^ ((g.vertexCount + 1).log2 + 1) = 2 ^ OracleContract.L g.vertexCount := rfl
      omega
    have hEntries57 : ∀ i (hi : i < dense.length - 1),
        (s57.data[treeBase + 8 * dense.length + 1 + i]?).map Fin.val = some (S.childEntryAt i) := by
      intro i hi
      rw [h57Data]
      have heq := hTreePresS43 (8 * dense.length + 1 + i) (by omega)
      rw [show treeBase + (8 * dense.length + 1 + i) = treeBase + 8 * dense.length + 1 + i by omega] at heq
      rw [heq]
      unfold StaticTreeSlice.childEntryAt
      simp only [hi, ↓reduceDIte]
      simpa only [show treeBase + (8 * dense.length + 1) + i = treeBase + 8 * dense.length + 1 + i by omega]
        using S.childEntries_mem ⟨i, hi⟩
    obtain ⟨s74, stepsB, hBndB, hStepsB, hpc74, h74_12, h74Pres, h74Data⟩ :=
      scatter_bsearch_run input S hDenseLe hOrigSz u (OracleContract.L g.vertexCount)
        (S.childStart d.val) (S.childStart (d.val + 1)) s57 hChildEx hREnd hPowL hpc57 hRegs57
        (by rw [h57Pres r8 (by decide) (by decide) (by decide) (by decide)]; exact hS_8)
        (by rw [h57Pres r9 (by decide) (by decide) (by decide) (by decide)]; exact hS_9)
        (by rw [h57o _ (by decide), h56o _ (by decide), h55d, hwcs0Val])
        (by rw [h57d, hwcs1Val])
        hEntries57 (by rw [h57Data, hS43Sz]; exact hOrigSz)
    obtain ⟨s75, h74, hpc75, h75d, h75o, h75m⟩ := step16_add code input hpc74 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s76, h75, hpc76, h76d, h76o, h76m⟩ := step16_add code input hpc75 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s77, h76, hpc77, h77d, h77o, h77m⟩ := step16_add code input hpc76 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s78, h77, hpc78, h78d, h78o, h78m⟩ := step16_add code input hpc77 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s79, h78, hpc79, h79d, h79o, h79m⟩ := step16_add code input hpc78 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s80, h79, hpc80, h80d, h80o, h80m⟩ := step16_add code input hpc79 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s81, h80, hpc81, h81d, h81o, h81m⟩ := step16_add code input hpc80 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have h74_N : (reg s74 rN).val = n := by
      rw [h74Pres rN (by decide) (by decide) (by decide) (by decide), h57Pres rN (by decide) (by decide) (by decide) (by decide)]; exact hN
    have h74_M : (reg s74 rM).val = m := by
      rw [h74Pres rM (by decide) (by decide) (by decide) (by decide), h57Pres rM (by decide) (by decide) (by decide) (by decide)]; exact hM
    have h74_7 : (reg s74 r7).val = emitBase := by
      rw [h74Pres r7 (by decide) (by decide) (by decide) (by decide), h57Pres r7 (by decide) (by decide) (by decide) (by decide)]; exact hEmitBase
    have h74_1 : (reg s74 rOne).val = 1 := by
      rw [h74Pres rOne (by decide) (by decide) (by decide) (by decide), h57Pres rOne (by decide) (by decide) (by decide) (by decide)]; exact hOne
    have hr75 : (reg s75 r15).val = 2 * n := by rw [h75d, add_no_wrap _ _ (by rw [h74_N]; omega), h74_N]; omega
    have hr76 : (reg s76 r15).val = 3 * n := by
      have hn' : (reg s75 rN).val = n := by rw [h75o _ (by decide)]; exact h74_N
      rw [h76d, add_no_wrap _ _ (by rw [hr75, hn']; omega), hr75, hn']; omega
    have hr77 : (reg s77 r15).val = 3 * n + m := by
      have hm' : (reg s76 rM).val = m := by rw [h76o _ (by decide), h75o _ (by decide)]; exact h74_M
      rw [h77d, add_no_wrap _ _ (by rw [hr76, hm']; omega), hr76, hm']
    have hr78 : (reg s78 r15).val = 3 * n + 2 * m := by
      have hm' : (reg s77 rM).val = m := by rw [h77o _ (by decide), h76o _ (by decide), h75o _ (by decide)]; exact h74_M
      rw [h78d, add_no_wrap _ _ (by rw [hr77, hm']; omega), hr77, hm']; omega
    have hr79 : (reg s79 r15).val = 3 * n + 3 * m := by
      have hm' : (reg s78 rM).val = m := by rw [h78o _ (by decide), h77o _ (by decide), h76o _ (by decide), h75o _ (by decide)]; exact h74_M
      rw [h79d, add_no_wrap _ _ (by rw [hr78, hm']; omega), hr78, hm']; omega
    have hr80 : (reg s80 r15).val = emitBase + 3 * n + 3 * m := by
      have h7' : (reg s79 r7).val = emitBase := by rw [h79o _ (by decide), h78o _ (by decide), h77o _ (by decide), h76o _ (by decide), h75o _ (by decide)]; exact h74_7
      rw [h80d, add_no_wrap _ _ (by rw [hr79, h7']; omega), hr79, h7']; omega
    have hr81 : (reg s81 r15).val = emitBase + 3 * n + 3 * m + 1 := by
      have h1' : (reg s80 rOne).val = 1 := by rw [h80o _ (by decide), h79o _ (by decide), h78o _ (by decide), h77o _ (by decide), h76o _ (by decide), h75o _ (by decide)]; exact h74_1
      rw [h81d, add_no_wrap _ _ (by rw [hr80, h1']; omega), hr80, h1']
    have hS81Data : s81.data = s43.data := by
      rw [h81m, h80m, h79m, h78m, h77m, h76m, h75m, h74Data, h57Data]
    have hScr0Mem81 : (s81.data[(reg s81 r15).val]?).map Fin.val = some d.val := by
      rw [hr81, hS81Data]; exact hS43Scr0
    obtain ⟨wd0, hwd0, hwd0Val⟩ := data_val_at hScr0Mem81
    obtain ⟨s82, h81, hpc82, h82d, h82o, h82m⟩ :=
      step16_loadData code input hpc81 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) hwd0 (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s83, h82, hpc83, h83d, h83o, h83m⟩ := step16_add code input hpc82 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s84, h83, hpc84, h84d, h84o, h84m⟩ := step16_add code input hpc83 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s85, h84, hpc85, h85d, h85o, h85m⟩ := step16_add code input hpc84 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s86, h85, hpc86, h86d, h86o, h86m⟩ := step16_add code input hpc85 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s87, h86, hpc87, h87d, h87o, h87m⟩ := step16_add code input hpc86 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s88, h87, hpc88, h88d, h88o, h88m⟩ := step16_add code input hpc87 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s89, h88, hpc89, h89d, h89o, h89m⟩ := step16_add code input hpc88 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have h82Pres : ∀ r' : Fin 16, r' ≠ r14 → r' ≠ r15 → reg s82 r' = reg s74 r' := by
      intro r' h14' h15'
      rw [h82o _ h14', h81o _ h15', h80o _ h15', h79o _ h15', h78o _ h15', h77o _ h15', h76o _ h15', h75o _ h15']
    have h82_Q : (reg s82 r5).val = dense.length := by
      rw [h82Pres r5 (by decide) (by decide), h74Pres r5 (by decide) (by decide) (by decide) (by decide), h57Pres r5 (by decide) (by decide) (by decide) (by decide)]; exact hQ
    have h82_TB : (reg s82 r6).val = treeBase := by
      rw [h82Pres r6 (by decide) (by decide), h74Pres r6 (by decide) (by decide) (by decide) (by decide), h57Pres r6 (by decide) (by decide) (by decide) (by decide)]; exact hTreeBase
    have h82_d : (reg s82 r14).val = d.val := by rw [h82d, hwd0Val]
    have hr83 : (reg s83 r15).val = 2 * dense.length := by rw [h83d, add_no_wrap _ _ (by rw [h82_Q]; omega), h82_Q]; omega
    have hr84 : (reg s84 r15).val = 4 * dense.length := by rw [h84d, add_no_wrap _ _ (by rw [hr83]; omega), hr83]; omega
    have hr85 : (reg s85 r15).val = 5 * dense.length := by
      have hq' : (reg s84 r5).val = dense.length := by rw [h84o _ (by decide), h83o _ (by decide)]; exact h82_Q
      rw [h85d, add_no_wrap _ _ (by rw [hr84, hq']; omega), hr84, hq']; omega
    have hr86 : (reg s86 r15).val = 6 * dense.length := by
      have hq' : (reg s85 r5).val = dense.length := by rw [h85o _ (by decide), h84o _ (by decide), h83o _ (by decide)]; exact h82_Q
      rw [h86d, add_no_wrap _ _ (by rw [hr85, hq']; omega), hr85, hq']; omega
    have hr87 : (reg s87 r15).val = 7 * dense.length := by
      have hq' : (reg s86 r5).val = dense.length := by rw [h86o _ (by decide), h85o _ (by decide), h84o _ (by decide), h83o _ (by decide)]; exact h82_Q
      rw [h87d, add_no_wrap _ _ (by rw [hr86, hq']; omega), hr86, hq']; omega
    have hr88 : (reg s88 r15).val = treeBase + 7 * dense.length := by
      have htb' : (reg s87 r6).val = treeBase := by rw [h87o _ (by decide), h86o _ (by decide), h85o _ (by decide), h84o _ (by decide), h83o _ (by decide)]; exact h82_TB
      rw [h88d, add_no_wrap _ _ (by rw [hr87, htb']; omega), hr87, htb']; omega
    have hr89 : (reg s89 r15).val = treeBase + 7 * dense.length + d.val := by
      have hd' : (reg s88 r14).val = d.val := by rw [h88o _ (by decide), h87o _ (by decide), h86o _ (by decide), h85o _ (by decide), h84o _ (by decide), h83o _ (by decide)]; exact h82_d
      rw [h89d, add_no_wrap _ _ (by rw [hr88, hd']; have := d.isLt; omega), hr88, hd']
    have hS89Data : s89.data = s43.data := by rw [h89m, h88m, h87m, h86m, h85m, h84m, h83m, h82m, hS81Data]
    have hCSMem89 : (s89.data[(reg s89 r15).val]?).map Fin.val = some (S.childStart d.val) := by
      rw [hr89, hS89Data]
      have heq := hTreePresS43 (7 * dense.length + d.val) (by have := d.isLt; omega)
      rw [show treeBase + (7 * dense.length + d.val) = treeBase + 7 * dense.length + d.val by omega] at heq
      exact data_mem_val_of_eq heq (S.childStart_mem d.val (Nat.le_of_lt d.isLt))
    obtain ⟨wcs2, hwcs2, hwcs2Val⟩ := data_val_at hCSMem89
    obtain ⟨s90, h89, hpc90, h90d, h90o, h90m⟩ :=
      step16_loadData code input hpc89 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) hwcs2 (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s91, h90, hpc91, h91d, h91o, h91m⟩ := step16_sub code input hpc90 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    obtain ⟨s92, h91, hpc92, h92d, h92o, h92m⟩ := step16_add code input hpc91 (by rw [scatterCode_mid (by decide) (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
    have hPosBnd : S.childStart d.val ≤ bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) ∧
        bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) < S.childStart (d.val + 1) :=
      bsearchRun_mem_range S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) hChildEx
    have h90_12 : (reg s90 r12).val = bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) := by
      rw [h90o _ (by decide), h89o _ (by decide), h88o _ (by decide), h87o _ (by decide),
        h86o _ (by decide), h85o _ (by decide), h84o _ (by decide), h83o _ (by decide),
        h82Pres r12 (by decide) (by decide)]
      exact h74_12
    have h90_14 : (reg s90 r14).val = S.childStart d.val := by rw [h90d, hwcs2Val]
    have h91_12 : (reg s91 r12).val = bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) - S.childStart d.val := by
      rw [h91d, sub_exact _ _ (by rw [h90_12, h90_14]; exact hPosBnd.1), h90_12, h90_14]
    have h91_1 : (reg s91 rOne).val = 1 := by
      rw [h91o _ (by decide), h90o _ (by decide), h89o _ (by decide), h88o _ (by decide),
        h87o _ (by decide), h86o _ (by decide), h85o _ (by decide), h84o _ (by decide),
        h83o _ (by decide), h82Pres rOne (by decide) (by decide)]; exact h74_1
    have hSrcEq : srcLocal = bsearchRun S.childEntryAt (OracleContract.L g.vertexCount) (S.childStart d.val) (S.childStart (d.val + 1)) (S.entry u) - S.childStart d.val + 1 := by
      unfold srcLocal StaticTreeSlice.srcLocalOf
      have hne : u.val ≠ d.val := hud
      have hnz : S.childStart (d.val + 1) - S.childStart d.val ≠ 0 := by omega
      simp only [hne, ↓reduceIte, hnz]
    have h92_12 : (reg s92 r12).val = srcLocal := by
      rw [hSrcEq, h92d, add_no_wrap _ _ (by rw [h91_12, h91_1]; omega), h91_12, h91_1]
    have hPost18 : Steps code input 18 s74 s92 :=
      Steps.cons h74 <| Steps.cons h75 <| Steps.cons h76 <| Steps.cons h77 <| Steps.cons h78 <|
      Steps.cons h79 <| Steps.cons h80 <| Steps.cons h81 <| Steps.cons h82 <| Steps.cons h83 <|
      Steps.cons h84 <| Steps.cons h85 <| Steps.cons h86 <| Steps.cons h87 <| Steps.cons h88 <|
      Steps.cons h89 <| Steps.cons h90 <| Steps.cons h91 (Steps.zero s92)
    have h92Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s92 r' = reg s r' := by
      intro r' h12' h13' h14' h15'
      rw [h92o _ h12', h91o _ h12', h90o _ h14', h89o _ h15', h88o _ h15', h87o _ h15', h86o _ h15',
        h85o _ h15', h84o _ h15', h83o _ h15', h82Pres r' h14' h15', h74Pres r' h12' h13' h14' h15',
        h57Pres r' h12' h13' h14' h15']
    have h92Data : s92.data = s43.data := by rw [h92m, h91m, h90m, hS89Data]
    exact ⟨s92, stepsBr + 10 + stepsB + 18, by omega,
      ((hStepsBr.append hPre57).append hStepsB).append hPost18, hpc92, h92_12, h92Pres, h92Data⟩

private theorem scatter_inner_tail {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (u : Fin dense.length) (j : Nat) (_hjLt : j < (g.outArcs (dense[u.val]'u.isLt)).length)
    (d : Fin dense.length) (srcLocal headLocal cur : Nat)
    (hCurLtM : cur < g.arcCount)
    (s s43 s92 : State (layout16 bits inputCap workCap hi hw))
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s)
    (hTailEq : (reg s r9).val = S.entry u)
    (hEidx : (reg s r10).val = outPrefix g (dense[u.val]'u.isLt).val + j)
    (hOutBnd : outPrefix g (dense[u.val]'u.isLt).val + j < g.arcCount)
    (hSDataSz : s.data.size = origData.size)
    (hS43ScratchPres : ∀ k, k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1 →
      k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2 →
      s43.data[k]? = s.data[k]?)
    (hS43Scr0 : (s43.data[emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1]?).map Fin.val = some d.val)
    (hS43Scr1 : (s43.data[emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2]?).map Fin.val = some headLocal)
    (hS43Sz : s43.data.size = origData.size)
    (hCurMem : (s.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some cur)
    (hpc92 : s92.pc = 92)
    (h92_12 : (reg s92 r12).val = srcLocal)
    (h92Pres : ∀ r' : Fin 16, r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s92 r' = reg s r')
    (h92Data : s92.data = s43.data) :
    ∃ s', Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input 34 s92 s' ∧
      s'.pc = 17 ∧
      (reg s' r10).val = outPrefix g (dense[u.val]'u.isLt).val + (j + 1) ∧
      (∀ r' : Fin 16, r' ≠ r10 → r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s' r' = reg s r') ∧
      s'.data.size = origData.size ∧
      (∀ k, k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 1 →
        k ≠ emitBase + 3 * g.vertexCount + 3 * g.arcCount + 2 →
        k ≠ emitBase + 3 * g.vertexCount + 1 + cur →
        k ≠ emitBase + 3 * g.vertexCount + g.arcCount + 1 + cur →
        k ≠ emitBase + 3 * g.vertexCount + 2 * g.arcCount + 1 + cur →
        k ≠ emitBase + g.vertexCount + d.val →
        s'.data[k]? = s.data[k]?) ∧
      (s'.data[emitBase + 3 * g.vertexCount + 1 + cur]?).map Fin.val = some srcLocal ∧
      (s'.data[emitBase + 3 * g.vertexCount + g.arcCount + 1 + cur]?).map Fin.val = some headLocal ∧
      (s'.data[emitBase + 3 * g.vertexCount + 2 * g.arcCount + 1 + cur]?).map Fin.val = some (S.entry u) ∧
      (s'.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (cur + 1) := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  let n := g.vertexCount
  let m := g.arcCount
  let tailEntry := S.entry u
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [hSDataSz] at h1; change origData.size = workCap at h1; omega
  have hDenseLe : dense.length ≤ n := S.length_le
  have hFitEmit' : emitBase + (3 * n + 3 * m + 3) ≤ origData.size := by
    simpa [emitterWorkWords, n, m] using hFitEmit
  have h2N_lt : n + n < 2 ^ bits := by omega
  have h3N_lt : 2 * n + n < 2 ^ bits := by omega
  have h3NM_lt : 3 * n + m < 2 ^ bits := by omega
  have h3N2M_lt : 3 * n + m + m < 2 ^ bits := by omega
  have h3N3M_lt : 3 * n + 2 * m + m < 2 ^ bits := by omega
  have hEmit3N3M_lt : 3 * n + 3 * m + emitBase < 2 ^ bits := by omega
  have hEmit3N3M1_lt : emitBase + 3 * n + 3 * m + 1 < 2 ^ bits := by omega
  have hEmit3N3M2_lt : emitBase + 3 * n + 3 * m + 1 + 1 < 2 ^ bits := by omega
  have hND_lt : n + d.val < 2 ^ bits := by have := d.isLt; omega
  have hEmitND_lt : n + d.val + emitBase < 2 ^ bits := by have := d.isLt; omega
  have hEmitND_ne1 : emitBase + n + d.val ≠ emitBase + 3 * n + 3 * m + 1 := by have := d.isLt; omega
  have hEmitND_ne2 : emitBase + n + d.val ≠ emitBase + 3 * n + 3 * m + 2 := by have := d.isLt; omega
  have hEmitND_sz : emitBase + n + d.val < origData.size := by have := d.isLt; omega
  have h3N1_lt : 3 * n + 1 < 2 ^ bits := by omega
  have hEmit3N1_lt : 3 * n + 1 + emitBase < 2 ^ bits := by omega
  have hEmit3N1C_lt : emitBase + 3 * n + 1 + cur < 2 ^ bits := by omega
  have hEmit3N1C_sz : emitBase + 3 * n + 1 + cur < origData.size := by omega
  have hEmit3NM1C_lt : emitBase + 3 * n + 1 + cur + m < 2 ^ bits := by omega
  have hEmit3NM1C_sz : emitBase + 3 * n + m + 1 + cur < origData.size := by omega
  have hEmit3N2M1C_lt : emitBase + 3 * n + m + 1 + cur + m < 2 ^ bits := by omega
  have hEmit3N2M1C_sz : emitBase + 3 * n + 2 * m + 1 + cur < origData.size := by omega
  have hCur1_lt : cur + 1 < 2 ^ bits := by omega
  have hEidx1_lt : outPrefix g (dense[u.val]'u.isLt).val + j + 1 < 2 ^ bits := by omega
  have hSrcNe6 : emitBase + 3 * n + 1 + cur ≠ emitBase + n + d.val := by have := d.isLt; omega
  have hSrcNe5 : emitBase + 3 * n + 1 + cur ≠ emitBase + 3 * n + 2 * m + 1 + cur := by omega
  have hSrcNe4 : emitBase + 3 * n + 1 + cur ≠ emitBase + 3 * n + m + 1 + cur := by omega
  have hHeadNe6 : emitBase + 3 * n + m + 1 + cur ≠ emitBase + n + d.val := by have := d.isLt; omega
  have hHeadNe5 : emitBase + 3 * n + m + 1 + cur ≠ emitBase + 3 * n + 2 * m + 1 + cur := by omega
  have hEntryNe6 : emitBase + 3 * n + 2 * m + 1 + cur ≠ emitBase + n + d.val := by have := d.isLt; omega
  have hHeadNeSrc : emitBase + 3 * n + 3 * m + 2 ≠ emitBase + 3 * n + 1 + cur := by omega
  have hN : (reg s rN).val = n := hRegs.consts.nVal
  have hM : (reg s rM).val = m := hRegs.consts.mVal
  have hOne : (reg s rOne).val = 1 := hRegs.consts.one
  have hEmitBase : (reg s r7).val = emitBase := hRegs.emitBaseVal
  have h92_N : (reg s92 rN).val = n := by rw [h92Pres rN (by decide) (by decide) (by decide) (by decide)]; exact hN
  have h92_M : (reg s92 rM).val = m := by rw [h92Pres rM (by decide) (by decide) (by decide) (by decide)]; exact hM
  have h92_7 : (reg s92 r7).val = emitBase := by rw [h92Pres r7 (by decide) (by decide) (by decide) (by decide)]; exact hEmitBase
  have h92_1 : (reg s92 rOne).val = 1 := by rw [h92Pres rOne (by decide) (by decide) (by decide) (by decide)]; exact hOne
  obtain ⟨s93, h92, hpc93, h93d, h93o, h93m⟩ := step16_add code input hpc92 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s94, h93, hpc94, h94d, h94o, h94m⟩ := step16_add code input hpc93 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s95, h94, hpc95, h95d, h95o, h95m⟩ := step16_add code input hpc94 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s96, h95, hpc96, h96d, h96o, h96m⟩ := step16_add code input hpc95 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s97, h96, hpc97, h97d, h97o, h97m⟩ := step16_add code input hpc96 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s98, h97, hpc98, h98d, h98o, h98m⟩ := step16_add code input hpc97 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s99, h98, hpc99, h99d, h99o, h99m⟩ := step16_add code input hpc98 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hr93 : (reg s93 r15).val = 2 * n := by
    rw [h93d, add_no_wrap _ _ (by rw [h92_N]; exact h2N_lt), h92_N, Nat.two_mul]
  have hr94 : (reg s94 r15).val = 3 * n := by
    have hn' : (reg s93 rN).val = n := by rw [h93o _ (by decide)]; exact h92_N
    rw [h94d, add_no_wrap _ _ (by rw [hr93, hn']; exact h3N_lt), hr93, hn']; exact (Nat.succ_mul 2 n).symm
  have hr95 : (reg s95 r15).val = 3 * n + m := by
    have hm' : (reg s94 rM).val = m := by rw [h94o _ (by decide), h93o _ (by decide)]; exact h92_M
    rw [h95d, add_no_wrap _ _ (by rw [hr94, hm']; exact h3NM_lt), hr94, hm']
  have hr96 : (reg s96 r15).val = 3 * n + 2 * m := by
    have hm' : (reg s95 rM).val = m := by rw [h95o _ (by decide), h94o _ (by decide), h93o _ (by decide)]; exact h92_M
    rw [h96d, add_no_wrap _ _ (by rw [hr95, hm']; exact h3N2M_lt), hr95, hm', Nat.add_assoc, Nat.two_mul]
  have hr97 : (reg s97 r15).val = 3 * n + 3 * m := by
    have hm' : (reg s96 rM).val = m := by rw [h96o _ (by decide), h95o _ (by decide), h94o _ (by decide), h93o _ (by decide)]; exact h92_M
    rw [h97d, add_no_wrap _ _ (by rw [hr96, hm']; exact h3N3M_lt), hr96, hm', Nat.add_assoc, (Nat.succ_mul 2 m).symm]
  have hr98 : (reg s98 r15).val = emitBase + 3 * n + 3 * m := by
    have h7' : (reg s97 r7).val = emitBase := by rw [h97o _ (by decide), h96o _ (by decide), h95o _ (by decide), h94o _ (by decide), h93o _ (by decide)]; exact h92_7
    rw [h98d, add_no_wrap _ _ (by rw [hr97, h7']; exact hEmit3N3M_lt), hr97, h7', Nat.add_comm _ emitBase, Nat.add_assoc]
  have hr99 : (reg s99 r15).val = emitBase + 3 * n + 3 * m + 1 := by
    have h1' : (reg s98 rOne).val = 1 := by rw [h98o _ (by decide), h97o _ (by decide), h96o _ (by decide), h95o _ (by decide), h94o _ (by decide), h93o _ (by decide)]; exact h92_1
    rw [h99d, add_no_wrap _ _ (by rw [hr98, h1']; exact hEmit3N3M1_lt), hr98, h1']
  have hS99Data : s99.data = s43.data := by rw [h99m, h98m, h97m, h96m, h95m, h94m, h93m, h92Data]
  have hScr0Mem99 : (s99.data[(reg s99 r15).val]?).map Fin.val = some d.val := by
    rw [hr99, hS99Data]; exact hS43Scr0
  obtain ⟨wds0, hwds0, hwds0Val⟩ := data_val_at hScr0Mem99
  obtain ⟨s100, h99, hpc100, h100d, h100o, h100m⟩ :=
    step16_loadData code input hpc99 (by rw [scatterCode_tail (by decide)]; rfl) hwds0 (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s101, h100, hpc101, h101d, h101o, h101m⟩ := step16_add code input hpc100 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s102, h101, hpc102, h102d, h102o, h102m⟩ := step16_add code input hpc101 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hS99Pres : ∀ r' : Fin 16, r' ≠ r15 → reg s99 r' = reg s92 r' := by
    intro r' h15'; rw [h99o _ h15', h98o _ h15', h97o _ h15', h96o _ h15', h95o _ h15', h94o _ h15', h93o _ h15']
  have hr101 : (reg s101 r14).val = n + d.val := by
    have hn' : (reg s100 rN).val = n := by rw [h100o _ (by decide), hS99Pres rN (by decide)]; exact h92_N
    have hd' : (reg s100 r14).val = d.val := by rw [h100d, hwds0Val]
    rw [h101d, add_no_wrap _ _ (by rw [hn', hd']; exact Nat.add_comm n d.val ▸ hND_lt), hn', hd', Nat.add_comm]
  have hr102 : (reg s102 r14).val = emitBase + n + d.val := by
    have h7' : (reg s101 r7).val = emitBase := by rw [h101o _ (by decide), h100o _ (by decide), hS99Pres r7 (by decide)]; exact h92_7
    rw [h102d, add_no_wrap _ _ (by rw [hr101, h7']; exact hEmitND_lt), hr101, h7', Nat.add_comm _ emitBase, Nat.add_assoc]
  have hS102Data : s102.data = s43.data := by rw [h102m, h101m, h100m, hS99Data]
  have hCurMem102 : (s102.data[(reg s102 r14).val]?).map Fin.val = some cur := by
    rw [hr102, hS102Data]
    exact data_mem_val_of_eq (hS43ScratchPres _ hEmitND_ne1 hEmitND_ne2) hCurMem
  obtain ⟨wcur, hwcur, hwcurVal⟩ := data_val_at hCurMem102
  obtain ⟨s103, h102, hpc103, h103d, h103o, h103m⟩ :=
    step16_loadData code input hpc102 (by rw [scatterCode_tail (by decide)]; rfl) hwcur (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s104, h103, hpc104, h104d, h104o, h104m⟩ := step16_add code input hpc103 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s105, h104, hpc105, h105d, h105o, h105m⟩ := step16_add code input hpc104 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s106, h105, hpc106, h106d, h106o, h106m⟩ := step16_add code input hpc105 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s107, h106, hpc107, h107d, h107o, h107m⟩ := step16_add code input hpc106 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s108, h107, hpc108, h108d, h108o, h108m⟩ := step16_add code input hpc107 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h103Pres : ∀ r' : Fin 16, r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s103 r' = reg s92 r' := by
    intro r' h13' h14' h15'
    rw [h103o _ h13', h102o _ h14', h101o _ h14', h100o _ h14', hS99Pres r' h15']
  have h103_N : (reg s103 rN).val = n := by rw [h103Pres rN (by decide) (by decide) (by decide)]; exact h92_N
  have h103_1 : (reg s103 rOne).val = 1 := by rw [h103Pres rOne (by decide) (by decide) (by decide)]; exact h92_1
  have h103_7 : (reg s103 r7).val = emitBase := by rw [h103Pres r7 (by decide) (by decide) (by decide)]; exact h92_7
  have h103_13 : (reg s103 r13).val = cur := by rw [h103d, hwcurVal]
  have hr104 : (reg s104 r15).val = 2 * n := by
    rw [h104d, add_no_wrap _ _ (by rw [h103_N]; exact h2N_lt), h103_N, Nat.two_mul]
  have hr105 : (reg s105 r15).val = 3 * n := by
    have hn' : (reg s104 rN).val = n := by rw [h104o _ (by decide)]; exact h103_N
    rw [h105d, add_no_wrap _ _ (by rw [hr104, hn']; exact h3N_lt), hr104, hn']; exact (Nat.succ_mul 2 n).symm
  have hr106 : (reg s106 r15).val = 3 * n + 1 := by
    have h1' : (reg s105 rOne).val = 1 := by rw [h105o _ (by decide), h104o _ (by decide)]; exact h103_1
    rw [h106d, add_no_wrap _ _ (by rw [hr105, h1']; exact h3N1_lt), hr105, h1']
  have hr107 : (reg s107 r15).val = emitBase + 3 * n + 1 := by
    have h7' : (reg s106 r7).val = emitBase := by rw [h106o _ (by decide), h105o _ (by decide), h104o _ (by decide)]; exact h103_7
    rw [h107d, add_no_wrap _ _ (by rw [hr106, h7']; exact hEmit3N1_lt), hr106, h7', Nat.add_comm _ emitBase, Nat.add_assoc]
  have hr108 : (reg s108 r15).val = emitBase + 3 * n + 1 + cur := by
    have hcur' : (reg s107 r13).val = cur := by rw [h107o _ (by decide), h106o _ (by decide), h105o _ (by decide), h104o _ (by decide)]; exact h103_13
    rw [h108d, add_no_wrap _ _ (by rw [hr107, hcur']; exact hEmit3N1C_lt), hr107, hcur']
  have hS108Data : s108.data = s43.data := by
    rw [h108m, h107m, h106m, h105m, h104m, h103m, hS102Data]
  have hBnd108 : (reg s108 r15).val < s108.data.size := by rw [hr108, hS108Data, hS43Sz]; exact hEmit3N1C_sz
  obtain ⟨s109, h108, hpc109, h109regs, h109data⟩ :=
    step16_storeData code input hpc108 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd108
  have h108_12 : (reg s108 r12).val = srcLocal := by
    rw [h108o _ (by decide), h107o _ (by decide), h106o _ (by decide), h105o _ (by decide),
      h104o _ (by decide), h103Pres r12 (by decide) (by decide) (by decide)]; exact h92_12
  obtain ⟨s110, h109, hpc110, h110d, h110o, h110m⟩ := step16_add code input hpc109 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s111, h110, hpc111, h111d, h111o, h111m⟩ := step16_add code input hpc110 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s112, h111, hpc112, h112d, h112o, h112m⟩ := step16_add code input hpc111 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s113, h112, hpc113, h113d, h113o, h113m⟩ := step16_add code input hpc112 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s114, h113, hpc114, h114d, h114o, h114m⟩ := step16_add code input hpc113 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s115, h114, hpc115, h115d, h115o, h115m⟩ := step16_add code input hpc114 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s116, h115, hpc116, h116d, h116o, h116m⟩ := step16_add code input hpc115 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s117, h116, hpc117, h117d, h117o, h117m⟩ := step16_add code input hpc116 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h109Pres : ∀ r' : Fin 16, r' ≠ r13 → r' ≠ r14 → r' ≠ r15 → reg s109 r' = reg s92 r' := by
    intro r' h13' h14' h15'
    rw [reg_eq_of_regs_eq h109regs r', h108o _ h15', h107o _ h15', h106o _ h15', h105o _ h15',
      h104o _ h15', h103Pres r' h13' h14' h15']
  have h109_N : (reg s109 rN).val = n := by rw [h109Pres rN (by decide) (by decide) (by decide)]; exact h92_N
  have h109_M : (reg s109 rM).val = m := by rw [h109Pres rM (by decide) (by decide) (by decide)]; exact h92_M
  have h109_7 : (reg s109 r7).val = emitBase := by rw [h109Pres r7 (by decide) (by decide) (by decide)]; exact h92_7
  have h109_1 : (reg s109 rOne).val = 1 := by rw [h109Pres rOne (by decide) (by decide) (by decide)]; exact h92_1
  have hr110 : (reg s110 r12).val = 2 * n := by
    rw [h110d, add_no_wrap _ _ (by rw [h109_N]; exact h2N_lt), h109_N, Nat.two_mul]
  have hr111 : (reg s111 r12).val = 3 * n := by
    have hn' : (reg s110 rN).val = n := by rw [h110o _ (by decide)]; exact h109_N
    rw [h111d, add_no_wrap _ _ (by rw [hr110, hn']; exact h3N_lt), hr110, hn']; exact (Nat.succ_mul 2 n).symm
  have hr112 : (reg s112 r12).val = 3 * n + m := by
    have hm' : (reg s111 rM).val = m := by rw [h111o _ (by decide), h110o _ (by decide)]; exact h109_M
    rw [h112d, add_no_wrap _ _ (by rw [hr111, hm']; exact h3NM_lt), hr111, hm']
  have hr113 : (reg s113 r12).val = 3 * n + 2 * m := by
    have hm' : (reg s112 rM).val = m := by rw [h112o _ (by decide), h111o _ (by decide), h110o _ (by decide)]; exact h109_M
    rw [h113d, add_no_wrap _ _ (by rw [hr112, hm']; exact h3N2M_lt), hr112, hm', Nat.add_assoc, Nat.two_mul]
  have hr114 : (reg s114 r12).val = 3 * n + 3 * m := by
    have hm' : (reg s113 rM).val = m := by rw [h113o _ (by decide), h112o _ (by decide), h111o _ (by decide), h110o _ (by decide)]; exact h109_M
    rw [h114d, add_no_wrap _ _ (by rw [hr113, hm']; exact h3N3M_lt), hr113, hm', Nat.add_assoc, (Nat.succ_mul 2 m).symm]
  have hr115 : (reg s115 r12).val = emitBase + 3 * n + 3 * m := by
    have h7' : (reg s114 r7).val = emitBase := by rw [h114o _ (by decide), h113o _ (by decide), h112o _ (by decide), h111o _ (by decide), h110o _ (by decide)]; exact h109_7
    rw [h115d, add_no_wrap _ _ (by rw [hr114, h7']; exact hEmit3N3M_lt), hr114, h7', Nat.add_comm _ emitBase, Nat.add_assoc]
  have hr116 : (reg s116 r12).val = emitBase + 3 * n + 3 * m + 1 := by
    have h1' : (reg s115 rOne).val = 1 := by rw [h115o _ (by decide), h114o _ (by decide), h113o _ (by decide), h112o _ (by decide), h111o _ (by decide), h110o _ (by decide)]; exact h109_1
    rw [h116d, add_no_wrap _ _ (by rw [hr115, h1']; exact hEmit3N3M1_lt), hr115, h1']
  have hr117 : (reg s117 r12).val = emitBase + 3 * n + 3 * m + 2 := by
    have h1' : (reg s116 rOne).val = 1 := by rw [h116o _ (by decide), h115o _ (by decide), h114o _ (by decide), h113o _ (by decide), h112o _ (by decide), h111o _ (by decide), h110o _ (by decide)]; exact h109_1
    rw [h117d, add_no_wrap _ _ (by rw [hr116, h1']; exact hEmit3N3M2_lt), hr116, h1']
  have hS117Data : s117.data = s109.data := by rw [h117m, h116m, h115m, h114m, h113m, h112m, h111m, h110m]
  have hScr1Mem117 : (s117.data[(reg s117 r12).val]?).map Fin.val = some headLocal := by
    rw [hr117, hS117Data, h109data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr108]; exact hHeadNeSrc), hS108Data]
    exact hS43Scr1
  obtain ⟨whd2, hwhd2, hwhd2Val⟩ := data_val_at hScr1Mem117
  obtain ⟨s118, h117, hpc118, h118d, h118o, h118m⟩ :=
    step16_loadData code input hpc117 (by rw [scatterCode_tail (by decide)]; rfl) hwhd2 (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s119, h118, hpc119, h119d, h119o, h119m⟩ := step16_add code input hpc118 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h117Pres : ∀ r' : Fin 16, r' ≠ r12 → reg s117 r' = reg s109 r' := by
    intro r' h12'
    rw [h117o _ h12', h116o _ h12', h115o _ h12', h114o _ h12', h113o _ h12', h112o _ h12', h111o _ h12', h110o _ h12']
  have h118_M : (reg s118 rM).val = m := by rw [h118o _ (by decide), h117Pres rM (by decide)]; exact h109_M
  have hr119 : (reg s119 r15).val = emitBase + 3 * n + m + 1 + cur := by
    have h15' : (reg s118 r15).val = emitBase + 3 * n + 1 + cur := by
      rw [h118o _ (by decide), h117Pres r15 (by decide), reg_eq_of_regs_eq h109regs r15]; exact hr108
    rw [h119d, add_no_wrap _ _ (by rw [h15', h118_M]; exact hEmit3NM1C_lt), h15', h118_M]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hBnd119 : (reg s119 r15).val < s119.data.size := by
    rw [hr119, h119m, h118m, hS117Data, h109data, Array.size_set, hS108Data, hS43Sz]; exact hEmit3NM1C_sz
  obtain ⟨s120, h119, hpc120, h120regs, h120data⟩ :=
    step16_storeData code input hpc119 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd119
  have h119_12 : (reg s119 r12).val = headLocal := by rw [h119o _ (by decide), h118d, hwhd2Val]
  obtain ⟨s121, h120, hpc121, h121d, h121o, h121m⟩ := step16_add code input hpc120 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hr121 : (reg s121 r15).val = emitBase + 3 * n + 2 * m + 1 + cur := by
    have h15' : (reg s120 r15).val = emitBase + 3 * n + m + 1 + cur := by
      rw [reg_eq_of_regs_eq h120regs r15]; exact hr119
    have hm' : (reg s120 rM).val = m := by
      rw [reg_eq_of_regs_eq h120regs rM, h119o _ (by decide)]; exact h118_M
    rw [h121d, add_no_wrap _ _ (by rw [h15', hm']; exact hEmit3N2M1C_lt), h15', hm']
    simp only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hBnd121 : (reg s121 r15).val < s121.data.size := by
    rw [hr121, h121m, h120data, Array.size_set, h119m, h118m, hS117Data, h109data, Array.size_set, hS108Data, hS43Sz]; exact hEmit3N2M1C_sz
  obtain ⟨s122, h121, hpc122, h122regs, h122data⟩ :=
    step16_storeData code input hpc121 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd121
  have h121_9 : (reg s121 r9).val = tailEntry := by
    rw [h121o _ (by decide), reg_eq_of_regs_eq h120regs r9, h119o _ (by decide), h118o _ (by decide),
      h117Pres r9 (by decide), h109Pres r9 (by decide) (by decide) (by decide),
      h92Pres r9 (by decide) (by decide) (by decide) (by decide)]
    exact hTailEq
  obtain ⟨s123, h122, hpc123, h123d, h123o, h123m⟩ := step16_add code input hpc122 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h122_13 : (reg s122 r13).val = cur := by
    rw [reg_eq_of_regs_eq h122regs r13, h121o _ (by decide), reg_eq_of_regs_eq h120regs r13,
      h119o _ (by decide), h118o _ (by decide), h117Pres r13 (by decide),
      reg_eq_of_regs_eq h109regs r13, h108o _ (by decide), h107o _ (by decide),
      h106o _ (by decide), h105o _ (by decide), h104o _ (by decide)]
    exact h103_13
  have h122_1 : (reg s122 rOne).val = 1 := by
    rw [reg_eq_of_regs_eq h122regs rOne, h121o _ (by decide), reg_eq_of_regs_eq h120regs rOne,
      h119o _ (by decide), h118o _ (by decide), h117Pres rOne (by decide)]; exact h109_1
  have hr123 : (reg s123 r13).val = cur + 1 := by
    rw [h123d, add_no_wrap _ _ (by rw [h122_13, h122_1]; exact hCur1_lt), h122_13, h122_1]
  have h123_14 : (reg s123 r14).val = emitBase + n + d.val := by
    rw [h123o _ (by decide), reg_eq_of_regs_eq h122regs r14, h121o _ (by decide),
      reg_eq_of_regs_eq h120regs r14, h119o _ (by decide), h118o _ (by decide),
      h117Pres r14 (by decide), reg_eq_of_regs_eq h109regs r14, h108o _ (by decide),
      h107o _ (by decide), h106o _ (by decide), h105o _ (by decide), h104o _ (by decide),
      h103o _ (by decide)]
    exact hr102
  have hBnd123 : (reg s123 r14).val < s123.data.size := by
    rw [h123_14, h123m, h122data, Array.size_set, h121m, h120data, Array.size_set,
      h119m, h118m, hS117Data, h109data, Array.size_set, hS108Data, hS43Sz]
    exact hEmitND_sz
  obtain ⟨s124, h123, hpc124, h124regs, h124data⟩ :=
    step16_storeData code input hpc123 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hBnd123
  obtain ⟨s125, h124, hpc125, h125d, h125o, h125m⟩ := step16_add code input hpc124 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h125 := step16_goto code input hpc125 (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s125.regs, data := s125.data, pc := 17, regs_size := s125.regs_size, data_size := s125.data_size }
  have hTail34 : Steps code input 34 s92 s' :=
    Steps.cons h92 <| Steps.cons h93 <| Steps.cons h94 <| Steps.cons h95 <| Steps.cons h96 <|
    Steps.cons h97 <| Steps.cons h98 <| Steps.cons h99 <| Steps.cons h100 <| Steps.cons h101 <|
    Steps.cons h102 <| Steps.cons h103 <| Steps.cons h104 <| Steps.cons h105 <| Steps.cons h106 <|
    Steps.cons h107 <| Steps.cons h108 <| Steps.cons h109 <| Steps.cons h110 <| Steps.cons h111 <|
    Steps.cons h112 <| Steps.cons h113 <| Steps.cons h114 <| Steps.cons h115 <| Steps.cons h116 <|
    Steps.cons h117 <| Steps.cons h118 <| Steps.cons h119 <| Steps.cons h120 <| Steps.cons h121 <|
    Steps.cons h122 <| Steps.cons h123 <| Steps.cons h124 <| Steps.cons h125 (Steps.zero s')
  have hS'DataSz : s'.data.size = origData.size := by
    change s125.data.size = _; rw [h125m, h124data, Array.size_set, h123m, h122data, Array.size_set,
      h121m, h120data, Array.size_set, h119m, h118m, hS117Data, h109data, Array.size_set, hS108Data, hS43Sz]
  have hRegPresTail : ∀ r' : Fin 16, r' ≠ r10 → r' ≠ r12 → r' ≠ r13 → r' ≠ r14 → r' ≠ r15 →
      reg s' r' = reg s r' := by
    intro r' h10' h12' h13' h14' h15'
    change reg s125 r' = reg s r'
    rw [h125o _ h10', reg_eq_of_regs_eq h124regs r', h123o _ h13', reg_eq_of_regs_eq h122regs r',
      h121o _ h15', reg_eq_of_regs_eq h120regs r', h119o _ h15', h118o _ h12', h117Pres r' h12',
      h109Pres r' h13' h14' h15']
    exact h92Pres r' h12' h13' h14' h15'
  have hEidx' : (reg s' r10).val = outPrefix g (dense[u.val]'u.isLt).val + (j + 1) := by
    change (reg s125 r10).val = _
    have h124_10 : (reg s124 r10).val = outPrefix g (dense[u.val]'u.isLt).val + j := by
      rw [reg_eq_of_regs_eq h124regs r10, h123o _ (by decide), reg_eq_of_regs_eq h122regs r10,
        h121o _ (by decide), reg_eq_of_regs_eq h120regs r10, h119o _ (by decide),
        h118o _ (by decide), h117Pres r10 (by decide), h109Pres r10 (by decide) (by decide) (by decide),
        h92Pres r10 (by decide) (by decide) (by decide) (by decide)]
      exact hEidx
    have h124_1 : (reg s124 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq h124regs rOne, h123o _ (by decide)]; exact h122_1
    rw [h125d, add_no_wrap _ _ (by rw [h124_10, h124_1]; exact hEidx1_lt), h124_10, h124_1, Nat.add_assoc]
  have hPres6 : ∀ k,
      k ≠ emitBase + 3 * n + 3 * m + 1 →
      k ≠ emitBase + 3 * n + 3 * m + 2 →
      k ≠ emitBase + 3 * n + 1 + cur →
      k ≠ emitBase + 3 * n + m + 1 + cur →
      k ≠ emitBase + 3 * n + 2 * m + 1 + cur →
      k ≠ emitBase + n + d.val →
      s'.data[k]? = s.data[k]? := by
    intro k hk1 hk2 hk3 hk4 hk5 hk6
    change s125.data[k]? = s.data[k]?
    rw [h125m, h124data, array_set_getElem?_ne _ _ _ _ _ (by rw [h123_14]; exact hk6),
      h123m, h122data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr121]; exact hk5),
      h121m, h120data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr119]; exact hk4),
      h119m, h118m, hS117Data, h109data,
      array_set_getElem?_ne _ _ _ _ _ (by rw [hr108]; exact hk3), hS108Data]
    exact hS43ScratchPres k hk1 hk2
  have hWriteSrc : (s'.data[emitBase + 3 * n + 1 + cur]?).map Fin.val = some srcLocal := by
    change (s125.data[emitBase + 3 * n + 1 + cur]?).map Fin.val = some srcLocal
    have hget : (s108.data.set (reg s108 r15).val (reg s108 r12) hBnd108)[emitBase + 3 * n + 1 + cur]? =
        some (reg s108 r12) := by
      rw [← hr108]; exact array_set_getElem?_same _ _ _ _
    rw [h125m, h124data, array_set_getElem?_ne _ _ _ _ _ (by rw [h123_14]; exact hSrcNe6),
      h123m, h122data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr121]; exact hSrcNe5),
      h121m, h120data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr119]; exact hSrcNe4),
      h119m, h118m, hS117Data, h109data, hget, Option.map_some, h108_12]
  have hWriteHead : (s'.data[emitBase + 3 * n + m + 1 + cur]?).map Fin.val = some headLocal := by
    change (s125.data[emitBase + 3 * n + m + 1 + cur]?).map Fin.val = some headLocal
    have hget : (s119.data.set (reg s119 r15).val (reg s119 r12) hBnd119)[emitBase + 3 * n + m + 1 + cur]? =
        some (reg s119 r12) := by
      rw [← hr119]; exact array_set_getElem?_same _ _ _ _
    rw [h125m, h124data, array_set_getElem?_ne _ _ _ _ _ (by rw [h123_14]; exact hHeadNe6),
      h123m, h122data, array_set_getElem?_ne _ _ _ _ _ (by rw [hr121]; exact hHeadNe5),
      h121m, h120data, hget, Option.map_some, h119_12]
  have hWriteEntry : (s'.data[emitBase + 3 * n + 2 * m + 1 + cur]?).map Fin.val = some tailEntry := by
    change (s125.data[emitBase + 3 * n + 2 * m + 1 + cur]?).map Fin.val = some tailEntry
    have hget : (s121.data.set (reg s121 r15).val (reg s121 r9) hBnd121)[emitBase + 3 * n + 2 * m + 1 + cur]? =
        some (reg s121 r9) := by
      rw [← hr121]; exact array_set_getElem?_same _ _ _ _
    rw [h125m, h124data, array_set_getElem?_ne _ _ _ _ _ (by rw [h123_14]; exact hEntryNe6),
      h123m, h122data, hget, Option.map_some, h121_9]
  have hWriteCur : (s'.data[emitBase + n + d.val]?).map Fin.val = some (cur + 1) := by
    change (s125.data[emitBase + n + d.val]?).map Fin.val = some (cur + 1)
    have hget : (s123.data.set (reg s123 r14).val (reg s123 r13) hBnd123)[emitBase + n + d.val]? =
        some (reg s123 r13) := by
      rw [← h123_14]; exact array_set_getElem?_same _ _ _ _
    rw [h125m, h124data, hget, Option.map_some, hr123]
  exact ⟨s', hTail34, rfl, hEidx', hRegPresTail, hS'DataSz, hPres6,
    hWriteSrc, hWriteHead, hWriteEntry, hWriteCur⟩

private theorem scatter_inner_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (raw : RawDagInput input g r)
    (acyc : g.IsAcyclic)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (origData[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hSelfSlots : ∀ v : Fin dense.length,
      (origData[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Fin dense.length) (j : Nat)
    (hjLt : j < (g.outArcs (dense[u.val]'u.isLt)).length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : ScatterInnerInv g r dense treeBase emitBase origData S u j s) :
    ∃ s' stepsInner, stepsInner ≤ 92 + 15 * OracleContract.L g.vertexCount ∧
      Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input stepsInner s s' ∧
      ScatterInnerInv g r dense treeBase emitBase origData S u (j + 1) s' := by
  let n := g.vertexCount
  let m := g.arcCount
  let uOrig := dense[u.val]'u.isLt
  let vOrig := (g.outArcs uOrig)[j]'hjLt
  have harcOrig : g.HasArc uOrig vOrig := List.getElem_mem hjLt
  have huReach : g.InitiallyReachable r uOrig := S.reach_mem u.val u.isLt
  have hvReach : g.InitiallyReachable r vOrig := initiallyReachable_extend huReach harcOrig
  have hvDenseMem : vOrig ∈ dense := S.mem_reach vOrig hvReach
  let vDense : Fin dense.length := ⟨dense.idxOf vOrig, List.idxOf_lt_length_of_mem hvDenseMem⟩
  let d := S.domParent vDense
  let srcLocal := S.srcLocalOf d u
  let headLocal := S.selfSlotFn vDense
  let pref := emittedPrefixList S u.val j
  let curOff := (pref.filter (fun e => e.owner == d)).length
  let cur := qStartFn S d.val + curOff
  have hDenseLe : dense.length ≤ n := S.length_le
  have hQ : (reg s r5).val = dense.length := inv.regs.qVal
  have hTreeBase : (reg s r6).val = treeBase := inv.regs.treeBaseVal
  have hEmitBase : (reg s r7).val = emitBase := inv.regs.emitBaseVal
  have hStepJ : emittedPrefixList S u.val (j + 1) =
      pref ++ [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] := by
    simpa [uOrig, vOrig, vDense, pref] using emittedPrefixList_step_j S u.isLt hjLt
  have hCurLtSucc : cur < qStartFn S (d.val + 1) := by
    rw [qStartFn_succ S d.isLt]
    have hSub : (pref.filter (fun e => e.owner == d)).length <
        ((emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d)).length := by
      have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d) = true :=
        beq_iff_eq.mpr rfl
      have hFilt1 : ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] : List (EmittedArc dense.length)).filter
          (fun e => e.owner == d) =
          [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] :=
        filter_singleton_true _ _ hOwn
      rw [hStepJ, List.filter_append, hFilt1, List.length_append, List.length_singleton]
      omega
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hSub (emittedPrefixList_filter_le S u.val (j + 1) d)) _
  have hCurLtM : cur < m := by
    have h2 := qStartFn_le_arcCount S (d.val + 1)
    change _ ≤ g.arcCount at h2
    omega
  have hOutBnd : outPrefix g uOrig.val + j < m := by
    have h1 : outPrefix g (uOrig.val + 1) ≤ outPrefix g g.vertexCount := outPrefix_mono g uOrig.isLt
    rw [outPrefix_succ_lt g uOrig, outPrefix_vertexCount] at h1
    change outPrefix g uOrig.val + (g.outArcs uOrig).length ≤ g.arcCount at h1
    have hjLt' : j < (g.outArcs uOrig).length := hjLt
    omega
  have harcOrig' : g.HasArc (dense[u.val]'u.isLt) (dense[vDense.val]'vDense.isLt) := by
    simpa [uOrig, vOrig, vDense, List.getElem_idxOf] using harcOrig
  obtain ⟨s43, hPre43, hpc43, h43_d, h43Pres, hS43ScratchPres, hS43Scr0, hS43Scr1, hS43Sz⟩ :=
    scatter_inner_head input raw S hOrigToDense hSelfSlots hFitEmit hDisjReachEmit hDisjTreeEmit u j hjLt inv
  obtain ⟨s92, stepsMid, hMidBnd, hStepsMid, hpc92, h92_12, h92Pres, h92Data⟩ :=
    scatter_inner_mid input acyc S hFitEmit hDisjTreeEmit u vDense harcOrig' s s43 inv.regs
      inv.uEq inv.tailEq inv.outsidePres hpc43 h43_d h43Pres hS43ScratchPres hS43Scr0 hS43Sz
  obtain ⟨s', hTail34, hpc', hEidx', hRegPresTail, hS'DataSz, hPres6,
      hWriteSrc, hWriteHead, hWriteEntry, hWriteCur⟩ :=
    scatter_inner_tail input S hFitEmit u j hjLt d srcLocal headLocal cur hCurLtM s s43 s92
      inv.regs inv.tailEq inv.eIdxEq hOutBnd inv.dataSize hS43ScratchPres hS43Scr0 hS43Scr1 hS43Sz
      (inv.cursors d) hpc92 h92_12 h92Pres h92Data
  refine ⟨s', 26 + stepsMid + 34, by omega, (hPre43.append hStepsMid).append hTail34, ?_⟩
  refine
    { pcEq := hpc'
      uEq := by rw [hRegPresTail r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.uEq
      tailEq := by rw [hRegPresTail r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.tailEq
      eIdxEq := hEidx'
      eEndEq := by rw [hRegPresTail r11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.eEndEq
      jLe := hjLt
      regs :=
        { consts :=
            { zero := by rw [hRegPresTail rZero (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [hRegPresTail rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [hRegPresTail rN (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.nVal
              mVal := by rw [hRegPresTail rM (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [hRegPresTail rRoot (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [hRegPresTail r5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hQ
          treeBaseVal := by rw [hRegPresTail r6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTreeBase
          emitBaseVal := by rw [hRegPresTail r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hEmitBase }
      dataSize := hS'DataSz
      outsidePres := by
        intro k hk
        have h1 : k ≠ emitBase + 3 * n + 3 * m + 1 := by rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        have h2 : k ≠ emitBase + 3 * n + 3 * m + 2 := by rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        have h3 : k ≠ emitBase + 3 * n + 1 + cur := by rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        have h4 : k ≠ emitBase + 3 * n + m + 1 + cur := by rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        have h5 : k ≠ emitBase + 3 * n + 2 * m + 1 + cur := by rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        have h6 : k ≠ emitBase + n + d.val := by
          have := d.isLt
          rcases hk with hl | ⟨hm1, hm2⟩ | hr <;> omega
        rw [hPres6 k h1 h2 h3 h4 h5 h6]
        exact inv.outsidePres k hk
      cursors := by
        intro d'
        rw [hStepJ, List.filter_append, List.length_append]
        by_cases hdEq : d' = d
        · have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d') = true :=
            beq_iff_eq.mpr hdEq.symm
          have hFilt1 : ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] : List (EmittedArc dense.length)).filter
              (fun e => e.owner == d') =
              [S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] :=
            filter_singleton_true _ _ hOwn
          change (s'.data[emitBase + n + d'.val]?).map Fin.val =
            some (qStartFn S d'.val + ((pref.filter (fun e => e.owner == d')).length +
              ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter
                (fun e : EmittedArc dense.length => e.owner == d')).length))
          rw [hFilt1, List.length_singleton, hdEq]
          exact hWriteCur
        · have hOwn : ((S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩).owner == d') = false :=
            beq_false_of_ne (fun e => hdEq e.symm)
          have hFilt1 : ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩] : List (EmittedArc dense.length)).filter
              (fun e => e.owner == d') = [] :=
            filter_singleton_false _ _ hOwn
          change (s'.data[emitBase + n + d'.val]?).map Fin.val =
            some (qStartFn S d'.val + ((pref.filter (fun e => e.owner == d')).length +
              ([S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩].filter
                (fun e : EmittedArc dense.length => e.owner == d')).length))
          rw [hFilt1, List.length_nil, Nat.add_zero]
          have hne1 : emitBase + n + d'.val ≠ emitBase + 3 * n + 3 * m + 1 := by have := d'.isLt; omega
          have hne2 : emitBase + n + d'.val ≠ emitBase + 3 * n + 3 * m + 2 := by have := d'.isLt; omega
          have hne3 : emitBase + n + d'.val ≠ emitBase + 3 * n + 1 + cur := by have := d'.isLt; omega
          have hne4 : emitBase + n + d'.val ≠ emitBase + 3 * n + m + 1 + cur := by have := d'.isLt; omega
          have hne5 : emitBase + n + d'.val ≠ emitBase + 3 * n + 2 * m + 1 + cur := by have := d'.isLt; omega
          have hne6 : emitBase + n + d'.val ≠ emitBase + n + d.val := by
            intro hEq; exact hdEq (Fin.ext (by omega))
          rw [hPres6 _ hne1 hne2 hne3 hne4 hne5 hne6]
          exact inv.cursors d'
      written := by
        intro d' p hp
        let newArc : EmittedArc dense.length :=
          S.emittedArc ⟨u.val, u.isLt⟩ ⟨dense.idxOf vOrig, vDense.isLt⟩
        have hNewOwner : newArc.owner = d := rfl
        have hFiltApp : (emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d') =
            pref.filter (fun e => e.owner == d') ++ [newArc].filter (fun e => e.owner == d') := by
          rw [hStepJ, List.filter_append]
        by_cases hdEq : d' = d
        · subst hdEq
          have hOwn : (newArc.owner == d) = true := beq_iff_eq.mpr rfl
          have hFilt1 : ([newArc] : List (EmittedArc dense.length)).filter (fun e => e.owner == d) = [newArc] :=
            filter_singleton_true _ _ hOwn
          have hFiltEq : (emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d) =
              pref.filter (fun e => e.owner == d) ++ [newArc] := by
            rw [hFiltApp, hFilt1]
          have hpLen : p < curOff + 1 := by
            rw [hFiltEq, List.length_append, List.length_singleton] at hp; exact hp
          by_cases hpEq : p = curOff
          · subst hpEq
            have hGet : ((emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d))[curOff]'hp = newArc := by
              have hIdx : ((pref.filter (fun e => e.owner == d)) ++ [newArc])[curOff]'(by rw [← hFiltEq]; exact hp) = newArc := by
                rw [List.getElem_append_right (Nat.le_refl _)]; simp
              rw [← hIdx]; congr 1
            change (s'.data[emitBase + 3 * n + 1 + (qStartFn S d.val + curOff)]?).map Fin.val = some _ ∧
              (s'.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + curOff)]?).map Fin.val = some _ ∧
              (s'.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + curOff)]?).map Fin.val = some _
            rw [hGet]
            exact ⟨hWriteSrc, hWriteHead, hWriteEntry⟩
          · have hpLt : p < curOff := by omega
            have hGet : ((emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d))[p]'hp =
                (pref.filter (fun e => e.owner == d))[p]'hpLt := by
              have hIdx : ((pref.filter (fun e => e.owner == d)) ++ [newArc])[p]'(by rw [← hFiltEq]; exact hp) =
                  (pref.filter (fun e => e.owner == d))[p]'hpLt := List.getElem_append_left hpLt
              rw [← hIdx]; congr 1
            let pos := qStartFn S d.val + p
            have hPosLtM : pos < m := by
              have h1 : pos < qStartFn S (d.val + 1) := by
                rw [qStartFn_succ S d.isLt]
                exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hpLt (emittedPrefixList_filter_le S u.val j d)) _
              have h2 := qStartFn_le_arcCount S (d.val + 1)
              change _ ≤ g.arcCount at h2; omega
            have hPosNe : pos ≠ cur := by change qStartFn S d.val + p ≠ qStartFn S d.val + curOff; omega
            rw [hGet]
            refine ⟨?_, ?_, ?_⟩
            · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
              exact (inv.written d p hpLt).1
            · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
              exact (inv.written d p hpLt).2.1
            · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
              exact (inv.written d p hpLt).2.2
        · have hOwn : (newArc.owner == d') = false := beq_false_of_ne (fun e => hdEq e.symm)
          have hFilt1 : ([newArc] : List (EmittedArc dense.length)).filter (fun e => e.owner == d') = [] :=
            filter_singleton_false _ _ hOwn
          have hFiltEq : (emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d') =
              pref.filter (fun e => e.owner == d') := by
            rw [hFiltApp, hFilt1, List.append_nil]
          have hpLt : p < (pref.filter (fun e => e.owner == d')).length := by rw [← hFiltEq]; exact hp
          have hGet : ((emittedPrefixList S u.val (j + 1)).filter (fun e => e.owner == d'))[p]'hp =
              (pref.filter (fun e => e.owner == d'))[p]'hpLt := by
            congr 1
          let pos := qStartFn S d'.val + p
          have hPosLtSucc : pos < qStartFn S (d'.val + 1) := by
            rw [qStartFn_succ S d'.isLt]
            exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hpLt (emittedPrefixList_filter_le S u.val j d')) _
          have hPosLtM : pos < m := by
            have h2 := qStartFn_le_arcCount S (d'.val + 1)
            change _ ≤ g.arcCount at h2; omega
          have hPosNe : pos ≠ cur := by
            rcases Nat.lt_or_gt_of_ne (fun e => hdEq (Fin.ext e)) with hlt | hgt
            · have hm := qStartFn_mono S (by omega : d'.val + 1 ≤ d.val) (Nat.le_of_lt d.isLt)
              omega
            · have hm := qStartFn_mono S (by omega : d.val + 1 ≤ d'.val) (Nat.le_of_lt d'.isLt)
              omega
          rw [hGet]
          refine ⟨?_, ?_, ?_⟩
          · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
            exact (inv.written d' p hpLt).1
          · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
            exact (inv.written d' p hpLt).2.1
          · rw [hPres6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by have := d.isLt; omega)]
            exact (inv.written d' p hpLt).2.2 }

private theorem scatter_outer_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat} {origData : Array (Word bits)}
    (raw : RawDagInput input g r)
    (acyc : g.IsAcyclic)
    (S : StaticTreeSlice origData treeBase g r dense)
    (hDenseToOrig : ∀ u' : Fin dense.length,
      (origData[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (origData[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hSelfSlots : ∀ v : Fin dense.length,
      (origData[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ origData.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase)
    (u : Nat) (hu : u < dense.length)
    {s : State (layout16 bits inputCap workCap hi hw)}
    (inv : ScatterOuterInv g r dense treeBase emitBase origData S u s) :
    ∃ s' stepsOuter,
      stepsOuter ≤ 19 + (92 + 15 * OracleContract.L g.vertexCount) * (g.outArcs (dense[u]'hu)).length ∧
      Steps (scatterQuotientArcsCode (hi := hi) (hw := hw)) input stepsOuter s s' ∧
      ScatterOuterInv g r dense treeBase emitBase origData S (u + 1) s' := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  have hOrigSz : origData.size ≤ 2 ^ bits := by
    have h1 := s.data_size; rw [inv.dataSize] at h1; change origData.size = workCap at h1; omega
  have hInCap : rawDagInputCap g.vertexCount g.arcCount ≤ 2 ^ bits := Nat.le_trans raw.cap_ge hi
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  have hTreeFit := S.fit
  let n := g.vertexCount
  let m := g.arcCount
  have hInCap' : 4 + n + m ≤ 2 ^ bits := by simpa [rawDagInputCap, n, m] using hInCap
  have hFitEmit' : emitBase + (3 * n + 3 * m + 3) ≤ origData.size := by
    simpa [emitterWorkWords, n, m] using hFitEmit
  have hTreeFit' : treeBase + 11 * dense.length ≤ origData.size := by
    simpa [staticTreeWords] using hTreeFit
  let uFin : Fin dense.length := ⟨u, hu⟩
  let uOrig := dense[u]'hu
  have h2N_lt : n + n < 2 ^ bits := by omega
  have h4N_lt : 2 * n + 2 * n < 2 ^ bits := by omega
  have h4NU_lt : 4 * n + u < 2 ^ bits := by omega
  have h4NU_disj : 4 * n + u < emitBase + n := by omega
  have hUOrig1 : uOrig.val + 1 < 2 ^ bits := by have := uOrig.isLt; omega
  have hUOrig2 : uOrig.val + 1 + 1 < 2 ^ bits := by have := uOrig.isLt; omega
  have hUOrig3 : uOrig.val + 2 + 1 < 2 ^ bits := by have := uOrig.isLt; omega
  have hUOrig4 : uOrig.val + 3 + 1 < 2 ^ bits := by have := uOrig.isLt; omega
  have h2Q_lt : dense.length + dense.length < 2 ^ bits := by omega
  have h4Q_lt : 2 * dense.length + 2 * dense.length < 2 ^ bits := by omega
  have hTB4Q_lt : 4 * dense.length + treeBase < 2 ^ bits := by omega
  have hTB4QU_lt : treeBase + 4 * dense.length + u < 2 ^ bits := by omega
  have hlt1 : (reg s r8).val < (reg s r5).val := by rw [inv.uEq, inv.regs.qVal]; exact hu
  have h1 := step16_branchLt_true code input inv.pcEq
    (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hlt1
  let s2 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 2, regs_size := s.regs_size, data_size := s.data_size }
  have hpc2 : s2.pc = 2 := rfl
  obtain ⟨s3, h2, hpc3, h3d, h3o, h3m⟩ := step16_add code input hpc2 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s4, h3, hpc4, h4d, h4o, h4m⟩ := step16_add code input hpc3 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s5, h4, hpc5, h5d, h5o, h5m⟩ := step16_add code input hpc4 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hN : (reg s rN).val = n := inv.regs.consts.nVal
  have hOne : (reg s rOne).val = 1 := inv.regs.consts.one
  have hQ : (reg s r5).val = dense.length := inv.regs.qVal
  have hTB : (reg s r6).val = treeBase := inv.regs.treeBaseVal
  have hr3 : (reg s3 r12).val = 2 * n := by
    rw [h3d, add_no_wrap _ _ (by change (reg s rN).val + (reg s rN).val < 2 ^ bits; rw [hN]; exact h2N_lt)]
    change (reg s rN).val + (reg s rN).val = _; rw [hN]; exact (Nat.two_mul n).symm
  have hr4 : (reg s4 r12).val = 4 * n := by
    rw [h4d, add_no_wrap _ _ (by rw [hr3]; exact h4N_lt), hr3]; omega
  have hr5 : (reg s5 r12).val = 4 * n + u := by
    have h4_8 : (reg s4 r8).val = u := by rw [h4o _ (by decide), h3o _ (by decide)]; exact inv.uEq
    rw [h5d, add_no_wrap _ _ (by rw [hr4, h4_8]; exact h4NU_lt), hr4, h4_8]
  have hS5Data : s5.data = s.data := by rw [h5m, h4m, h3m]
  have hDenseMem : (s5.data[(reg s5 r12).val]?).map Fin.val = some uOrig.val := by
    rw [hr5, hS5Data]
    have hDisj : 4 * n + u < emitBase + n ∨
        (emitBase + n + dense.length ≤ 4 * n + u ∧ 4 * n + u < emitBase + 3 * n + 1) ∨
        emitBase + 3 * n + 3 * m + 3 ≤ 4 * n + u := Or.inl h4NU_disj
    have hDenseEq : denseToOrigBase g.vertexCount g.arcCount + uFin.val = 4 * n + u := by
      unfold denseToOrigBase; simp [n, uFin]
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (by rw [← hDenseEq]; exact hDenseToOrig uFin)
  obtain ⟨wu, hwu, hwuVal⟩ := data_val_at hDenseMem
  obtain ⟨s6, h5, hpc6, h6d, h6o, h6m⟩ :=
    step16_loadData code input hpc5 (by rw [scatterCode_head (by decide)]; rfl) hwu (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s7, h6, hpc7, h7d, h7o, h7m⟩ := step16_add code input hpc6 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s8, h7, hpc8, h8d, h8o, h8m⟩ := step16_add code input hpc7 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s9, h8, hpc9, h9d, h9o, h9m⟩ := step16_add code input hpc8 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s10, h9, hpc10, h10d, h10o, h10m⟩ := step16_add code input hpc9 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h6_1 : (reg s6 rOne).val = 1 := by rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide)]; exact hOne
  have hr7 : (reg s7 r10).val = uOrig.val + 1 := by
    have h6_12 : (reg s6 r12).val = uOrig.val := by rw [h6d, hwuVal]
    rw [h7d, add_no_wrap _ _ (by rw [h6_12, h6_1]; exact hUOrig1), h6_12, h6_1]
  have hr8 : (reg s8 r10).val = uOrig.val + 2 := by
    have h1' : (reg s7 rOne).val = 1 := by rw [h7o _ (by decide)]; exact h6_1
    rw [h8d, add_no_wrap _ _ (by rw [hr7, h1']; exact hUOrig2), hr7, h1']
  have hr9 : (reg s9 r10).val = uOrig.val + 3 := by
    have h1' : (reg s8 rOne).val = 1 := by rw [h8o _ (by decide), h7o _ (by decide)]; exact h6_1
    rw [h9d, add_no_wrap _ _ (by rw [hr8, h1']; exact hUOrig3), hr8, h1']
  have hr10 : (reg s10 r11).val = uOrig.val + 4 := by
    have h1' : (reg s9 rOne).val = 1 := by rw [h9o _ (by decide), h8o _ (by decide), h7o _ (by decide)]; exact h6_1
    rw [h10d, add_no_wrap _ _ (by rw [hr9, h1']; exact hUOrig4), hr9, h1']
  have hS10_10 : (reg s10 r10).val = 3 + uOrig.val := by rw [h10o _ (by decide), hr9]; omega
  have hPref0Mem : (input.words[(reg s10 r10).val]?).map Fin.val = some (outPrefix g uOrig.val) := by
    rw [hS10_10]; exact raw.out_off uOrig.val (Nat.le_of_lt uOrig.isLt)
  obtain ⟨wp0, hwp0, hwp0Val⟩ := data_val_at hPref0Mem
  obtain ⟨s11, h10, hpc11, h11d, h11o, h11m⟩ :=
    step16_loadInput code input hpc10 (by rw [scatterCode_head (by decide)]; rfl) hwp0 (by rw [scatterQuotientArcsCode_size]; decide)
  have hS11_11 : (reg s11 r11).val = 3 + (uOrig.val + 1) := by rw [h11o _ (by decide), hr10]; omega
  have hPref1Mem : (input.words[(reg s11 r11).val]?).map Fin.val = some (outPrefix g (uOrig.val + 1)) := by
    rw [hS11_11]; exact raw.out_off (uOrig.val + 1) uOrig.isLt
  obtain ⟨wp1, hwp1, hwp1Val⟩ := data_val_at hPref1Mem
  obtain ⟨s12, h11, hpc12, h12d, h12o, h12m⟩ :=
    step16_loadInput code input hpc11 (by rw [scatterCode_head (by decide)]; rfl) hwp1 (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s13, h12, hpc13, h13d, h13o, h13m⟩ := step16_add code input hpc12 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s14, h13, hpc14, h14d, h14o, h14m⟩ := step16_add code input hpc13 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s15, h14, hpc15, h15d, h15o, h15m⟩ := step16_add code input hpc14 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s16, h15, hpc16, h16d, h16o, h16m⟩ := step16_add code input hpc15 (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h12Pres : ∀ r' : Fin 16, r' ≠ r10 → r' ≠ r11 → r' ≠ r12 → reg s12 r' = reg s r' := by
    intro r' h10' h11' h12'
    rw [h12o _ h11', h11o _ h10', h10o _ h11', h9o _ h10', h8o _ h10', h7o _ h10',
      h6o _ h12', h5o _ h12', h4o _ h12', h3o _ h12']; rfl
  have h12_Q : (reg s12 r5).val = dense.length := by rw [h12Pres r5 (by decide) (by decide) (by decide)]; exact hQ
  have h12_TB : (reg s12 r6).val = treeBase := by rw [h12Pres r6 (by decide) (by decide) (by decide)]; exact hTB
  have h12_8 : (reg s12 r8).val = u := by rw [h12Pres r8 (by decide) (by decide) (by decide)]; exact inv.uEq
  have hr13 : (reg s13 r9).val = 2 * dense.length := by
    rw [h13d, add_no_wrap _ _ (by rw [h12_Q]; exact h2Q_lt), h12_Q]; exact (Nat.two_mul _).symm
  have hr14 : (reg s14 r9).val = 4 * dense.length := by
    rw [h14d, add_no_wrap _ _ (by rw [hr13]; exact h4Q_lt), hr13]; omega
  have hr15 : (reg s15 r9).val = treeBase + 4 * dense.length := by
    have htb' : (reg s14 r6).val = treeBase := by rw [h14o _ (by decide), h13o _ (by decide)]; exact h12_TB
    rw [h15d, add_no_wrap _ _ (by rw [hr14, htb']; exact Nat.add_comm _ _ ▸ hTB4Q_lt), hr14, htb']
  have hr16 : (reg s16 r9).val = treeBase + 4 * dense.length + u := by
    have h8' : (reg s15 r8).val = u := by rw [h15o _ (by decide), h14o _ (by decide), h13o _ (by decide)]; exact h12_8
    rw [h16d, add_no_wrap _ _ (by rw [hr15, h8']; exact hTB4QU_lt), hr15, h8']
  have hS16Data : s16.data = s.data := by
    rw [h16m, h15m, h14m, h13m, h12m, h11m, h10m, h9m, h8m, h7m, h6m, hS5Data]
  have hEntryMem16 : (s16.data[(reg s16 r9).val]?).map Fin.val = some (S.entry uFin) := by
    rw [hr16, hS16Data]
    have hDisj : treeBase + 4 * dense.length + u < emitBase + n ∨
        (emitBase + n + dense.length ≤ treeBase + 4 * dense.length + u ∧
          treeBase + 4 * dense.length + u < emitBase + 3 * n + 1) ∨
        emitBase + 3 * n + 3 * m + 3 ≤ treeBase + 4 * dense.length + u := by
      unfold staticTreeWords emitterWorkWords at hDisjTreeEmit
      rcases hDisjTreeEmit with hl | hr
      · left; omega
      · right; right; omega
    exact data_mem_val_of_eq (inv.outsidePres _ hDisj) (S.entry_mem uFin)
  obtain ⟨went, hwent, hwentVal⟩ := data_val_at hEntryMem16
  obtain ⟨s17, h16, hpc17, h17d, h17o, h17m⟩ :=
    step16_loadData code input hpc16 (by rw [scatterCode_head (by decide)]; rfl) hwent (by rw [scatterQuotientArcsCode_size]; decide)
  have hPre : Steps code input 16 s s17 :=
    Steps.cons h1 <| Steps.cons h2 <| Steps.cons h3 <| Steps.cons h4 <| Steps.cons h5 <|
    Steps.cons h6 <| Steps.cons h7 <| Steps.cons h8 <| Steps.cons h9 <| Steps.cons h10 <|
    Steps.cons h11 <| Steps.cons h12 <| Steps.cons h13 <| Steps.cons h14 <| Steps.cons h15 <|
    Steps.cons h16 (Steps.zero s17)
  have h17Data : s17.data = s.data := by rw [h17m, hS16Data]
  have h17Pres : ∀ r' : Fin 16, r' ≠ r9 → r' ≠ r10 → r' ≠ r11 → r' ≠ r12 → reg s17 r' = reg s r' := by
    intro r' h9' h10' h11' h12'
    rw [h17o _ h9', h16o _ h9', h15o _ h9', h14o _ h9', h13o _ h9', h12Pres r' h10' h11' h12']
  have hInner0 : ScatterInnerInv g r dense treeBase emitBase origData S uFin 0 s17 :=
    { pcEq := hpc17
      uEq := by rw [h17Pres r8 (by decide) (by decide) (by decide) (by decide)]; exact inv.uEq
      tailEq := by rw [h17d, hwentVal]
      eIdxEq := by
        rw [h17o _ (by decide), h16o _ (by decide), h15o _ (by decide), h14o _ (by decide),
          h13o _ (by decide), h12o _ (by decide), h11d, hwp0Val]; rfl
      eEndEq := by
        rw [h17o _ (by decide), h16o _ (by decide), h15o _ (by decide), h14o _ (by decide),
          h13o _ (by decide), h12d, hwp1Val, outPrefix_succ_lt g uOrig]
      jLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [h17Pres rZero (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.zero
              one := by rw [h17Pres rOne (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.one
              nVal := by rw [h17Pres rN (by decide) (by decide) (by decide) (by decide)]; exact hN
              mVal := by rw [h17Pres rM (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.mVal
              rootVal := by rw [h17Pres rRoot (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.consts.rootVal }
          qVal := by rw [h17Pres r5 (by decide) (by decide) (by decide) (by decide)]; exact hQ
          treeBaseVal := by rw [h17Pres r6 (by decide) (by decide) (by decide) (by decide)]; exact hTB
          emitBaseVal := by rw [h17Pres r7 (by decide) (by decide) (by decide) (by decide)]; exact inv.regs.emitBaseVal }
      dataSize := by rw [h17Data]; exact inv.dataSize
      outsidePres := by intro k hk; rw [h17Data]; exact inv.outsidePres k hk
      cursors := by intro d'; rw [h17Data]; exact inv.cursors d'
      written := by intro d' p hp; rw [h17Data]; exact inv.written d' p hp }
  have hRunInner : ∀ rem j st, (g.outArcs uOrig).length - j = rem →
      ScatterInnerInv g r dense treeBase emitBase origData S uFin j st →
      ∃ stEnd stepsIn, stepsIn ≤ (92 + 15 * OracleContract.L g.vertexCount) * rem ∧
        Steps code input stepsIn st stEnd ∧
        ScatterInnerInv g r dense treeBase emitBase origData S uFin (g.outArcs uOrig).length stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro j st hrem hinv
      have hLeJ : j ≤ (g.outArcs uOrig).length := hinv.jLe
      have hjeq : j = (g.outArcs uOrig).length := by omega
      subst hjeq
      exact ⟨st, 0, Nat.zero_le _, Steps.zero st, hinv⟩
    | succ rem ih =>
      intro j st hrem hinv
      have hLeJ : j ≤ (g.outArcs uOrig).length := hinv.jLe
      have hjlt : j < (g.outArcs uOrig).length := by omega
      obtain ⟨st1, steps1, hBnd1, hstep1, hinv1⟩ := scatter_inner_step input raw acyc S hOrigToDense
        hSelfSlots hFitEmit hDisjReachEmit hDisjTreeEmit uFin j hjlt hinv
      obtain ⟨stEnd, stepsRest, hBndRest, hstepRest, hinvEnd⟩ := ih (j + 1) st1 (by omega) hinv1
      have hMul : (92 + 15 * OracleContract.L g.vertexCount) * (rem + 1) =
          (92 + 15 * OracleContract.L g.vertexCount) +
          (92 + 15 * OracleContract.L g.vertexCount) * rem := by
        rw [Nat.mul_succ]; omega
      refine ⟨stEnd, steps1 + stepsRest, by omega, hstep1.append hstepRest, hinvEnd⟩
  obtain ⟨sEndIn, stepsIn, hBndIn, hStepsIn, hInvIn⟩ :=
    hRunInner (g.outArcs uOrig).length 0 s17 (Nat.sub_zero _) hInner0
  have hFalse : (reg sEndIn r11).val ≤ (reg sEndIn r10).val := by
    rw [hInvIn.eIdxEq, hInvIn.eEndEq]; exact Nat.le_refl _
  have h17f := step16_branchLt_false code input hInvIn.pcEq
    (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hFalse
  let s126 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEndIn.regs, data := sEndIn.data, pc := 126, regs_size := sEndIn.regs_size, data_size := sEndIn.data_size }
  have hpc126 : s126.pc = 126 := rfl
  obtain ⟨s127, h126, hpc127, h127d, h127o, h127m⟩ := step16_add code input hpc126
    (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have h127 := step16_goto code input hpc127
    (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  let s' : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s127.regs, data := s127.data, pc := 1, regs_size := s127.regs_size, data_size := s127.data_size }
  have hExit : Steps code input 3 sEndIn s' := Steps.cons h17f <| Steps.cons h126 <| Steps.cons h127 (Steps.zero s')
  have hS'Data : s'.data = sEndIn.data := by change s127.data = _; rw [h127m]
  have hRegPresOut : ∀ r' : Fin 16, r' ≠ r8 → reg s' r' = reg sEndIn r' := by
    intro r' h8'; change reg s127 r' = reg sEndIn r'; rw [h127o _ h8']; rfl
  refine ⟨s', 16 + stepsIn + 3, by
      change stepsIn ≤ (92 + 15 * OracleContract.L g.vertexCount) * ((g.outArcs dense[u]).length - 0) at hBndIn
      rw [Nat.sub_zero] at hBndIn
      exact Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_right hBndIn 3) 16) (by rw [Nat.add_comm 16]; omega),
    (hPre.append hStepsIn).append hExit, ?_⟩
  refine
    { pcEq := rfl
      uEq := by
        change (reg s127 r8).val = u + 1
        have h126_8 : (reg s126 r8).val = u := hInvIn.uEq
        have h126_1 : (reg s126 rOne).val = 1 := hInvIn.regs.consts.one
        rw [h127d, add_no_wrap _ _ (by rw [h126_8, h126_1]; omega), h126_8, h126_1]
      uLe := hu
      regs :=
        { consts :=
            { zero := by rw [hRegPresOut rZero (by decide)]; exact hInvIn.regs.consts.zero
              one := by rw [hRegPresOut rOne (by decide)]; exact hInvIn.regs.consts.one
              nVal := by rw [hRegPresOut rN (by decide)]; exact hInvIn.regs.consts.nVal
              mVal := by rw [hRegPresOut rM (by decide)]; exact hInvIn.regs.consts.mVal
              rootVal := by rw [hRegPresOut rRoot (by decide)]; exact hInvIn.regs.consts.rootVal }
          qVal := by rw [hRegPresOut r5 (by decide)]; exact hInvIn.regs.qVal
          treeBaseVal := by rw [hRegPresOut r6 (by decide)]; exact hInvIn.regs.treeBaseVal
          emitBaseVal := by rw [hRegPresOut r7 (by decide)]; exact hInvIn.regs.emitBaseVal }
      dataSize := by rw [hS'Data]; exact hInvIn.dataSize
      outsidePres := by intro k hk; rw [hS'Data]; exact hInvIn.outsidePres k hk
      cursors := by
        intro d'
        rw [hS'Data, ← emittedPrefixList_step_u S hu]
        exact hInvIn.cursors d'
      written := by
        have hW : ScatterWritten S emitBase (emittedPrefixList S u (g.outArcs (dense[u]'hu)).length) sEndIn.data :=
          hInvIn.written
        have hW' : ScatterWritten S emitBase (emittedPrefixList S (u + 1) 0) s'.data := by
          rw [hS'Data, ← emittedPrefixList_step_u S hu]; exact hW
        exact hW' }

theorem run_scatterQuotientArcsPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (raw : RawDagInput input g r)
    (acyc : g.IsAcyclic)
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s₀)
    (S : StaticTreeSlice s₀.data treeBase g r dense)
    (hDenseToOrig : ∀ u' : Fin dense.length,
      (s₀.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (s₀.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hSelfSlots : ∀ v : Fin dense.length,
      (s₀.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v))
    (hCursors : ∀ d : Fin dense.length,
      (s₀.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (qStartFn S d.val))
    (hStarts : ∀ j : Nat, j ≤ dense.length →
      (s₀.data[emitBase + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ s₀.data.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 19 * g.vertexCount + (92 + 15 * OracleContract.L g.vertexCount) * g.arcCount + 7 ∧
      PaperB.RamProgram.run (scatterQuotientArcsPhase (hi := hi) (hw := hw)).code input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase t ∧
      (reg t r8).val = S.allEmittedArcs.length ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase + g.vertexCount ∨
          (emitBase + g.vertexCount + dense.length ≤ k ∧ k < emitBase + 3 * g.vertexCount + 1) ∨
          emitBase + 3 * g.vertexCount + 3 * g.arcCount + 3 ≤ k) →
        t.data[k]? = s₀.data[k]?) ∧
      (∀ d : Fin dense.length,
        (t.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (qStartFn S (d.val + 1))) ∧
      (∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
        let pos := qStartFn S d.val + p
        let e := (S.emittedArcs d)[p]'hp
        (t.data[emitBase + 3 * g.vertexCount + 1 + pos]?).map Fin.val = some e.srcLocal ∧
        (t.data[emitBase + 3 * g.vertexCount + g.arcCount + 1 + pos]?).map Fin.val = some e.headLocal ∧
        (t.data[emitBase + 3 * g.vertexCount + 2 * g.arcCount + 1 + pos]?).map Fin.val = some e.tailEntry) := by
  let code := scatterQuotientArcsCode (hi := hi) (hw := hw)
  have hOrigSz : s₀.data.size ≤ 2 ^ bits := by rw [s₀.data_size]; exact hw
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  let sInit := Phase.initial s₀
  have hpc0 : sInit.pc = 0 := rfl
  obtain ⟨s1, h0, hpc1, h1d, h1o, h1m⟩ := step16_mov code input hpc0
    (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hInv0 : ScatterOuterInv g r dense treeBase emitBase s₀.data S 0 s1 :=
    { pcEq := hpc1
      uEq := by rw [h1d]; exact hRegs.consts.zero
      uLe := Nat.zero_le _
      regs :=
        { consts :=
            { zero := by rw [h1o _ (by decide)]; exact hRegs.consts.zero
              one := by rw [h1o _ (by decide)]; exact hRegs.consts.one
              nVal := by rw [h1o _ (by decide)]; exact hRegs.consts.nVal
              mVal := by rw [h1o _ (by decide)]; exact hRegs.consts.mVal
              rootVal := by rw [h1o _ (by decide)]; exact hRegs.consts.rootVal }
          qVal := by rw [h1o _ (by decide)]; exact hRegs.qVal
          treeBaseVal := by rw [h1o _ (by decide)]; exact hRegs.treeBaseVal
          emitBaseVal := by rw [h1o _ (by decide)]; exact hRegs.emitBaseVal }
      dataSize := by rw [h1m]; rfl
      outsidePres := by intro k _; rw [h1m]; rfl
      cursors := by
        intro d
        rw [emittedPrefixList_zero S, List.filter_nil, List.length_nil, Nat.add_zero, h1m]
        exact hCursors d
      written := by
        intro d p hp
        rw [emittedPrefixList_zero S, List.filter_nil, List.length_nil] at hp
        exact False.elim (Nat.not_lt_zero _ hp) }
  have hRunOuter : ∀ rem u st, u + rem = dense.length →
      ScatterOuterInv g r dense treeBase emitBase s₀.data S u st →
      ∃ stEnd stepsOuter,
        stepsOuter ≤ 19 * rem + (92 + 15 * OracleContract.L g.vertexCount) *
          (((List.finRange dense.length).drop u).map
            (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum ∧
        Steps code input stepsOuter st stEnd ∧
        ScatterOuterInv g r dense treeBase emitBase s₀.data S dense.length stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro u st hrem hinv
      have huEq : u = dense.length := by omega
      subst huEq
      exact ⟨st, 0, Nat.zero_le _, Steps.zero st, hinv⟩
    | succ rem ih =>
      intro u st hrem hinv
      have huLt : u < dense.length := by omega
      obtain ⟨st1, steps1, hBnd1, hstep1, hinv1⟩ := scatter_outer_step input raw acyc S hDenseToOrig
        hOrigToDense hSelfSlots hFitEmit hDisjReachEmit hDisjTreeEmit u huLt hinv
      obtain ⟨stEnd, stepsRest, hBndRest, hStepRest, hInvEnd⟩ := ih (u + 1) st1 (by omega) hinv1
      have hDrop : ((List.finRange dense.length).drop u).map
            (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length) =
          (g.outArcs (dense[u]'huLt)).length ::
            ((List.finRange dense.length).drop (u + 1)).map
              (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length) := by
        have hEq : (List.finRange dense.length).drop u =
            ⟨u, huLt⟩ :: (List.finRange dense.length).drop (u + 1) := by
          have h1 : u < (List.finRange dense.length).length := by simp [huLt]
          rw [List.drop_eq_getElem_cons h1]; simp
        rw [hEq, List.map_cons]
      refine ⟨stEnd, steps1 + stepsRest, ?_, hstep1.append hStepRest, hInvEnd⟩
      have hDistrib := Nat.mul_add (92 + 15 * OracleContract.L g.vertexCount)
        (g.outArcs (dense[u]'huLt)).length
        (((List.finRange dense.length).drop (u + 1)).map
          (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum
      rw [hDrop, List.sum_cons, hDistrib]
      omega
  obtain ⟨sEnd, stepsOuter, hBndOuter, hStepsOuter, hInvEnd⟩ :=
    hRunOuter dense.length 0 s1 (Nat.zero_add _) hInv0
  have hFalseEnd : (reg sEnd r5).val ≤ (reg sEnd r8).val := by
    rw [hInvEnd.uEq, hInvEnd.regs.qVal]; exact Nat.le_refl _
  have h1f := step16_branchLt_false code input hInvEnd.pcEq
    (by rw [scatterCode_head (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide) hFalseEnd
  let s128 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := sEnd.regs, data := sEnd.data, pc := 128, regs_size := sEnd.regs_size, data_size := sEnd.data_size }
  have hpc128 : s128.pc = 128 := rfl
  obtain ⟨s129, h128, hpc129, h129d, h129o, h129m⟩ := step16_add code input hpc128
    (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s130, h129, hpc130, h130d, h130o, h130m⟩ := step16_add code input hpc129
    (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  obtain ⟨s131, h130, hpc131, h131d, h131o, h131m⟩ := step16_add code input hpc130
    (by rw [scatterCode_tail (by decide)]; rfl) (by rw [scatterQuotientArcsCode_size]; decide)
  have hN : (reg sEnd rN).val = g.vertexCount := hInvEnd.regs.consts.nVal
  have hEB : (reg sEnd r7).val = emitBase := hInvEnd.regs.emitBaseVal
  have hQ : (reg sEnd r5).val = dense.length := hInvEnd.regs.qVal
  have hr129 : (reg s129 r8).val = 2 * g.vertexCount := by
    rw [h129d, add_no_wrap _ _ (by change (reg sEnd rN).val + (reg sEnd rN).val < 2 ^ bits; rw [hN]; unfold emitterWorkWords at hFitEmit; omega)]
    change (reg sEnd rN).val + (reg sEnd rN).val = _; rw [hN]; omega
  have hr130 : (reg s130 r8).val = emitBase + 2 * g.vertexCount := by
    have h7' : (reg s129 r7).val = emitBase := by rw [h129o _ (by decide)]; exact hEB
    rw [h130d, add_no_wrap _ _ (by rw [hr129, h7']; unfold emitterWorkWords at hFitEmit; omega), hr129, h7']; omega
  have hr131 : (reg s131 r8).val = emitBase + 2 * g.vertexCount + dense.length := by
    have h5' : (reg s130 r5).val = dense.length := by rw [h130o _ (by decide), h129o _ (by decide)]; exact hQ
    rw [h131d, add_no_wrap _ _ (by rw [hr130, h5']; unfold emitterWorkWords at hFitEmit; omega), hr130, h5']
  have hS131Data : s131.data = sEnd.data := by rw [h131m, h130m, h129m]
  have hMReachMem : (s131.data[(reg s131 r8).val]?).map Fin.val = some S.allEmittedArcs.length := by
    rw [hr131, hS131Data]
    have hDisj : emitBase + 2 * g.vertexCount + dense.length < emitBase + g.vertexCount ∨
        (emitBase + g.vertexCount + dense.length ≤ emitBase + 2 * g.vertexCount + dense.length ∧
          emitBase + 2 * g.vertexCount + dense.length < emitBase + 3 * g.vertexCount + 1) ∨
        emitBase + 3 * g.vertexCount + 3 * g.arcCount + 3 ≤ emitBase + 2 * g.vertexCount + dense.length := by
      right; left; omega
    have hSt := data_mem_val_of_eq (hInvEnd.outsidePres _ hDisj) (hStarts dense.length (Nat.le_refl _))
    rwa [qStartFn_end S] at hSt
  obtain ⟨wmr, hwmr, hwmrVal⟩ := data_val_at hMReachMem
  obtain ⟨s132, h131, hpc132, h132d, h132o, h132m⟩ :=
    step16_loadData code input hpc131 (by rw [scatterCode_tail (by decide)]; rfl) hwmr (by rw [scatterQuotientArcsCode_size]; decide)
  have hHalt : step code input s132 = some (.halted s132) :=
    step_halt_at (by rw [hpc132, scatterCode_tail (by decide)]; rfl)
  have hTail : Steps code input 5 sEnd s132 :=
    Steps.cons h1f <| Steps.cons h128 <| Steps.cons h129 <| Steps.cons h130 <| Steps.cons h131 (Steps.zero s132)
  have hFull := ((Steps.cons h0 (Steps.zero s1)).append hStepsOuter).append hTail
  have hExec := hFull.halts hHalt
  have hS132Data : s132.data = sEnd.data := by rw [h132m, hS131Data]
  have hRegEnd : ∀ r' : Fin 16, r' ≠ r8 → reg s132 r' = reg sEnd r' := by
    intro r' h8'
    rw [h132o _ h8', h131o _ h8', h130o _ h8', h129o _ h8']; rfl
  refine ⟨s132, 1 + stepsOuter + 5 + 1, ?_, hExec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hSumLe : (((List.finRange dense.length).map
        (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum) ≤ g.arcCount := by
      have h1 : ((List.finRange dense.length).map
          (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum = S.allEmittedArcs.length := by
        unfold StaticTreeSlice.allEmittedArcs
        rw [List.length_flatMap, List.map_congr_left (fun u' _ => (S.emitForU_length u').symm)]
      rw [h1]; exact S.allEmittedArcs_length_le
    simp only [List.drop_zero] at hBndOuter
    have hMulLe : (92 + 15 * OracleContract.L g.vertexCount) *
        (((List.finRange dense.length).map (fun u' => (g.outArcs (dense[u'.val]'u'.isLt)).length)).sum) ≤
        (92 + 15 * OracleContract.L g.vertexCount) * g.arcCount := Nat.mul_le_mul_left _ hSumLe
    omega
  · exact
      { consts :=
          { zero := by rw [hRegEnd rZero (by decide)]; exact hInvEnd.regs.consts.zero
            one := by rw [hRegEnd rOne (by decide)]; exact hInvEnd.regs.consts.one
            nVal := by rw [hRegEnd rN (by decide)]; exact hN
            mVal := by rw [hRegEnd rM (by decide)]; exact hInvEnd.regs.consts.mVal
            rootVal := by rw [hRegEnd rRoot (by decide)]; exact hInvEnd.regs.consts.rootVal }
        qVal := by rw [hRegEnd r5 (by decide)]; exact hQ
        treeBaseVal := by rw [hRegEnd r6 (by decide)]; exact hInvEnd.regs.treeBaseVal
        emitBaseVal := by rw [hRegEnd r7 (by decide)]; exact hEB }
  · rw [h132d, hwmrVal]
  · rw [hS132Data]; exact hInvEnd.dataSize
  · intro k hk; rw [hS132Data]; exact hInvEnd.outsidePres k hk
  · intro d
    rw [hS132Data]
    have hc := hInvEnd.cursors d
    rw [emittedPrefixList_end S] at hc
    change (sEnd.data[emitBase + g.vertexCount + d.val]?).map Fin.val =
        some (qStartFn S d.val + (S.emittedArcs d).length) at hc
    rwa [← qStartFn_succ S d.isLt] at hc
  · have hW : ScatterWritten S emitBase S.allEmittedArcs sEnd.data := by
      rw [← emittedPrefixList_end S]; exact hInvEnd.written
    intro d p hp
    rw [hS132Data]
    exact hW d p hp

/-! ### 4. Linked 5-Phase Quotient Emitter Program & Exact Output Theorem -/

def quotientEmitPhases {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    List (Phase (layout16 bits inputCap workCap hi hw)) :=
  [ initSelfSlotPhase,
    zeroQDegPhase,
    countQDegPhase,
    qStartPrefixPhase,
    scatterQuotientArcsPhase ]

def quotientEmitProgram {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  pipeline (quotientEmitPhases (hi := hi) (hw := hw))

theorem run_quotient_emit {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {treeBase emitBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (raw : RawDagInput input g r)
    (acyc : g.IsAcyclic)
    (hRegs : EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase s₀)
    (S : StaticTreeSlice s₀.data treeBase g r dense)
    (hDenseToOrig : ∀ u' : Fin dense.length,
      (s₀.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val)
    (hOrigToDense : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (s₀.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1))
    (hFitEmit : emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ s₀.data.size)
    (hDisjReachEmit : 5 * g.vertexCount ≤ emitBase)
    (hDisjTreeEmit : treeBase + staticTreeWords dense.length ≤ emitBase ∨
      emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ treeBase) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (states : List (PaperB.RamProgram.State (layout16 bits inputCap workCap hi hw))) (steps : Nat),
      steps ≤ 128 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ∧
      run (quotientEmitProgram (hi := hi) (hw := hw)) input steps (Phase.initial s₀) =
        some ⟨t, steps⟩ ∧
      SuccessfulTrace (quotientEmitProgram (hi := hi) (hw := hw)) input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint (layout16 bits inputCap workCap hi hw) ∧
      EmitterRegs g.vertexCount g.arcCount r.val dense.length treeBase emitBase t ∧
      (reg t r8).val = S.allEmittedArcs.length ∧
      t.data.size = s₀.data.size ∧
      (∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
        t.data[k]? = s₀.data[k]?) ∧
      (∀ v : Fin dense.length,
        (t.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v)) ∧
      (∀ j : Nat, j ≤ dense.length →
        (t.data[emitBase + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) ∧
      (∀ d : Fin dense.length,
        (t.data[emitBase + g.vertexCount + d.val]?).map Fin.val = some (qStartFn S (d.val + 1))) ∧
      (∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
        let pos := qStartFn S d.val + p
        let e := (S.emittedArcs d)[p]'hp
        (t.data[emitBase + 3 * g.vertexCount + 1 + pos]?).map Fin.val = some e.srcLocal ∧
        (t.data[emitBase + 3 * g.vertexCount + g.arcCount + 1 + pos]?).map Fin.val = some e.headLocal ∧
        (t.data[emitBase + 3 * g.vertexCount + 2 * g.arcCount + 1 + pos]?).map Fin.val = some e.tailEntry) := by
  have hDenseLe : dense.length ≤ g.vertexCount := S.length_le
  -- Helper: preserve `treeBase .. treeBase + 11 * Q` across `[emitBase .. emitBase + emitterWorkWords)` writes
  have hTreeOfOut : ∀ {m₁ m₂ : Array (Word bits)}, m₁.size = m₂.size →
      (∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) → m₁[k]? = m₂[k]?) →
      ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords dense.length → m₁[k]? = m₂[k]? := by
    intro m₁ m₂ _ hOut k hk1 hk2
    apply hOut
    rcases hDisjTreeEmit with hl | hr
    · left; omega
    · right; omega
  -- Phase 1
  obtain ⟨t1, st1, hBnd1, hRun1, hRegs1, hSz1, hOut1, hSelf1⟩ :=
    run_initSelfSlotPhase input hRegs S hFitEmit hDisjTreeEmit
  have hOutEmit1 : ∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
      t1.data[k]? = s₀.data[k]? := by
    intro k hk; apply hOut1; rcases hk with hl | hr
    · left; exact hl
    · right; unfold emitterWorkWords at hr; omega
  -- Phase 2
  obtain ⟨t2, st2, hBnd2, hRun2, hRegs2, hSz2, hOut2, hZero2⟩ :=
    run_zeroQDegPhase input hRegs1 hDenseLe (hSz1 ▸ hFitEmit)
  have hOutEmit2 : ∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
      t2.data[k]? = s₀.data[k]? := by
    intro k hk
    have h1 := hOut2 k (by
      unfold emitterWorkWords at hk
      rcases hk with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    exact h1.trans (hOutEmit1 k hk)
  have hSelf2 : ∀ v : Fin dense.length, (t2.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v) := by
    intro v
    have h1 := hOut2 (emitBase + v.val) (by left; have := v.isLt; omega)
    rw [h1]; exact hSelf1 v
  have hSz20 : t2.data.size = s₀.data.size := hSz2.trans hSz1
  let S2 : StaticTreeSlice t2.data treeBase g r dense :=
    S.ofMemEq hSz20 (hTreeOfOut hSz20 hOutEmit2)
  have hDenseToOrig2 : ∀ u' : Fin dense.length,
      (t2.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val := by
    intro u'
    have hk : denseToOrigBase g.vertexCount g.arcCount + u'.val < emitBase := by
      unfold denseToOrigBase; have := u'.isLt; omega
    rw [hOutEmit2 _ (Or.inl hk)]; exact hDenseToOrig u'
  have hOrigToDense2 : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (t2.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1) := by
    intro v hv
    have hk : origToDensePlusOneBase g.vertexCount g.arcCount + v.val < emitBase := by
      unfold origToDensePlusOneBase; have := v.isLt; omega
    rw [hOutEmit2 _ (Or.inl hk)]; exact hOrigToDense v hv
  -- Phase 3
  obtain ⟨t3, st3, hBnd3, hRun3, hRegs3, hSz3, hOut3, hDegs3⟩ :=
    run_countQDegPhase input raw hRegs2 S2 hDenseToOrig2 hOrigToDense2
      (hSz2 ▸ hSz1 ▸ hFitEmit) hDisjReachEmit hDisjTreeEmit hZero2
  have hOutEmit3 : ∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
      t3.data[k]? = s₀.data[k]? := by
    intro k hk
    have h1 := hOut3 k (by
      unfold emitterWorkWords at hk
      rcases hk with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    exact h1.trans (hOutEmit2 k hk)
  have hSelf3 : ∀ v : Fin dense.length, (t3.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v) := by
    intro v
    have h1 := hOut3 (emitBase + v.val) (by left; have := v.isLt; omega)
    rw [h1]; exact hSelf2 v
  have hSz30 : t3.data.size = s₀.data.size := hSz3.trans hSz20
  let S3 : StaticTreeSlice t3.data treeBase g r dense :=
    S.ofMemEq hSz30 (hTreeOfOut hSz30 hOutEmit3)
  -- Phase 4
  obtain ⟨t4, st4, hBnd4, hRun4, hRegs4, _, hSz4, hOut4, hCursors4, hStarts4⟩ :=
    run_qStartPrefixPhase input hRegs3 S3 (hSz3 ▸ hSz2 ▸ hSz1 ▸ hFitEmit) hDegs3
  have hOutEmit4 : ∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
      t4.data[k]? = s₀.data[k]? := by
    intro k hk
    have h1 := hOut4 k (by
      unfold emitterWorkWords at hk
      rcases hk with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    exact h1.trans (hOutEmit3 k hk)
  have hSelf4 : ∀ v : Fin dense.length, (t4.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v) := by
    intro v
    have h1 := hOut4 (emitBase + v.val) (by left; have := v.isLt; omega)
    rw [h1]; exact hSelf3 v
  have hSz40 : t4.data.size = s₀.data.size := hSz4.trans hSz30
  let S4 : StaticTreeSlice t4.data treeBase g r dense :=
    S.ofMemEq hSz40 (hTreeOfOut hSz40 hOutEmit4)
  have hDenseToOrig4 : ∀ u' : Fin dense.length,
      (t4.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some (dense[u'.val]'u'.isLt).val := by
    intro u'
    have hk : denseToOrigBase g.vertexCount g.arcCount + u'.val < emitBase := by
      unfold denseToOrigBase; have := u'.isLt; omega
    rw [hOutEmit4 _ (Or.inl hk)]; exact hDenseToOrig u'
  have hOrigToDense4 : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (t4.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (dense.idxOf v + 1) := by
    intro v hv
    have hk : origToDensePlusOneBase g.vertexCount g.arcCount + v.val < emitBase := by
      unfold origToDensePlusOneBase; have := v.isLt; omega
    rw [hOutEmit4 _ (Or.inl hk)]; exact hOrigToDense v hv
  -- Phase 5
  obtain ⟨t5, st5, hBnd5, hRun5, hRegs5, hMReach5, hSz5, hOut5, hCursors5, hWritten5⟩ :=
    run_scatterQuotientArcsPhase input raw acyc hRegs4 S4 hDenseToOrig4 hOrigToDense4 hSelf4
      (fun d => hCursors4 d.val d.isLt) hStarts4 (hSz4 ▸ hSz3 ▸ hSz2 ▸ hSz1 ▸ hFitEmit)
      hDisjReachEmit hDisjTreeEmit
  -- Link all 5 phases via `run_pipeline`
  have hPhases : PhasesRun input (quotientEmitPhases (hi := hi) (hw := hw)) s₀ (Phase.initial t5)
      (st1 + (st2 + (st3 + (st4 + (st5 + 1))))) :=
    PhasesRun.cons hRun1 <|
    PhasesRun.cons hRun2 <|
    PhasesRun.cons hRun3 <|
    PhasesRun.cons hRun4 <|
    PhasesRun.cons hRun5 PhasesRun.nil
  obtain ⟨u, states, hURegs, hUData, hExec, hTrace, hPeak⟩ := run_pipeline hPhases
  have hRegU : ∀ r' : Fin 16, reg u r' = reg t5 r' := fun r' => reg_eq_of_regs_eq hURegs r'
  have hDataU : u.data = t5.data := hUData
  have hOutEmit5 : ∀ k, (k < emitBase ∨ emitBase + emitterWorkWords g.vertexCount g.arcCount ≤ k) →
      t5.data[k]? = s₀.data[k]? := by
    intro k hk
    have h1 := hOut5 k (by
      unfold emitterWorkWords at hk
      rcases hk with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    exact h1.trans (hOutEmit4 k hk)
  have hSelf5 : ∀ v : Fin dense.length, (t5.data[emitBase + v.val]?).map Fin.val = some (S.selfSlotFn v) := by
    intro v
    have h1 := hOut5 (emitBase + v.val) (by left; have := v.isLt; omega)
    rw [h1]; exact hSelf4 v
  have hStarts5 : ∀ j : Nat, j ≤ dense.length →
      (t5.data[emitBase + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j) := by
    intro j hj
    have h1 := hOut5 (emitBase + 2 * g.vertexCount + j) (by right; left; omega)
    rw [h1]; exact hStarts4 j hj
  have hStepBound : st1 + (st2 + (st3 + (st4 + (st5 + 1)))) ≤
      128 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount := by
    have hL : 1 ≤ OracleContract.L g.vertexCount := OracleContract.one_le_L g.vertexCount
    have h78 : 78 * g.vertexCount ≤ 78 * (g.vertexCount * OracleContract.L g.vertexCount) := by
      rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hL
    have h113 : 113 * g.arcCount ≤ 113 * (g.arcCount * OracleContract.L g.vertexCount) := by
      rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hL
    have h26 : 26 ≤ 128 * OracleContract.L g.vertexCount := by omega
    have hMul : 128 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount =
        128 * (g.vertexCount * OracleContract.L g.vertexCount) +
        128 * (g.arcCount * OracleContract.L g.vertexCount) +
        128 * OracleContract.L g.vertexCount := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]
    have hMul2 : (92 + 15 * OracleContract.L g.vertexCount) * g.arcCount =
        92 * g.arcCount + 15 * (g.arcCount * OracleContract.L g.vertexCount) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (OracleContract.L g.vertexCount) g.arcCount]
    omega
  refine ⟨u, states, st1 + (st2 + (st3 + (st4 + (st5 + 1)))), hStepBound, hExec, hTrace, hPeak, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { consts :=
          { zero := by rw [hRegU rZero]; exact hRegs5.consts.zero
            one := by rw [hRegU rOne]; exact hRegs5.consts.one
            nVal := by rw [hRegU rN]; exact hRegs5.consts.nVal
            mVal := by rw [hRegU rM]; exact hRegs5.consts.mVal
            rootVal := by rw [hRegU rRoot]; exact hRegs5.consts.rootVal }
        qVal := by rw [hRegU r5]; exact hRegs5.qVal
        treeBaseVal := by rw [hRegU r6]; exact hRegs5.treeBaseVal
        emitBaseVal := by rw [hRegU r7]; exact hRegs5.emitBaseVal }
  · rw [hRegU r8]; exact hMReach5
  · rw [hDataU, hSz5, hSz4, hSz3, hSz2, hSz1]
  · intro k hk; rw [hDataU]; exact hOutEmit5 k hk
  · intro v; rw [hDataU]; exact hSelf5 v
  · intro j hj; rw [hDataU]; exact hStarts5 j hj
  · intro d; rw [hDataU]; exact hCursors5 d
  · intro d p hp; rw [hDataU]; exact hWritten5 d p hp

end RamEmitter

end PaperB.RamQuotientEmitter
