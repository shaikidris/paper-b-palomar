module

public import PaperB.ExitSingleMap
public import PaperB.ExitStoredWrite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
Direct dependencies: `PaperB/ExitSingleMap.lean` supplies `buildOneSlot` and
`buildOneSlot_exact`; `exit-packed-record-write.lean` supplies `WriteResult`,
`writeStoredAt`, and its same-slot, other-slot, and write-count theorems.
The latter imports `PaperB.ExitStoredCodec`, which supplies the codec and
the physical reader. The schedule and incoming-arc traversal are upstream
of this step: the caller supplies the slot, packed IDs, and computed edge.
-/

namespace PaperB.ExitPhysicalOneSlot

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite

structure Layout {bits : Nat} (base : Word bits) (words slots : Nat) : Prop where
  address : base.val + 18 * slots ≤ 2 ^ bits
  capacity : base.val + 18 * slots ≤ words

theorem Layout.addrAt {bits words slots : Nat} {base : Word bits}
    (l : Layout base words slots) {u : Nat} (hu : u < slots) :
    base.val + 18 * u + 18 ≤ 2 ^ bits := by
  have h := l.address
  omega

theorem Layout.memAt {bits words slots : Nat} {base : Word bits}
    (l : Layout base words slots) {u : Nat} (hu : u < slots) :
    base.val + 18 * u + 18 ≤ words := by
  have h := l.capacity
  omega

structure Job where
  slot : Nat
  parent : Nat
  jump : Nat
  edge : Map

/-- Exactly the old slots that `buildOneSlot` can read. -/
def Job.Dependencies (j : Job) (occupied : Nat → Prop) (old : Store) : Prop :=
  j.jump ≠ j.parent → occupied j.parent ∧ occupied (old j.parent).jump

def Job.occupy (j : Job) (occupied : Nat → Prop) (u : Nat) : Prop :=
  occupied u ∨ u = j.slot

/-- This is the store update used by `buildOneSlot_exact` when `j.slot = F.size`.
It is a specification, not a runtime store. -/
def Job.overlay (j : Job) (old : Store) : Store :=
  fun u => if u = j.slot then buildOneSlot old j.parent j.jump j.edge else old u

/-- Snapshot only the selected block. Decoding closes over the scratch block,
not the bank, even if a decoded map contains a function. -/
private def detachedRead {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (ha : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hm : base.val + 18 * u + 18 ≤ mem.size) : Stored :=
  let cells := Array.ofFn (readStoredBlockAt mem base u ha hm)
  (storedCodec tags).decode (fun i : Fin 18 =>
    cells[i.val]'(by simpa [cells] using i.isLt))

private theorem detachedRead_eq {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (ha : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hm : base.val + 18 * u + 18 ≤ mem.size) :
    detachedRead tags mem base u ha hm = readStoredAt tags mem base u ha hm := by
  unfold detachedRead readStoredAt
  apply congrArg (storedCodec tags).decode
  funext i
  simp only [Array.getElem_ofFn]

variable {bits words slots : Nat}
variable (tags : TagsFit bits) (base : Word bits)
variable (layout : Layout base words slots)

/-- `words` is the size of the allocated array, by `bank.size_eq`. -/
def readSlot (bank : WriteResult bits words) (u : Nat) (hu : u < slots) : Stored :=
  readStoredAt tags bank.mem base u (layout.addrAt hu)
    (bank.le_size (layout.memAt hu))

def OccupiedExact (bank : WriteResult bits words)
    (occupied : Nat → Prop) (old : Store) : Prop :=
  ∀ u, occupied u →
    ∃ hu : u < slots, readSlot tags base layout bank u hu = old u

private def readForBuild (bank : WriteResult bits words) (j : Job) : Store :=
  fun u =>
    if hu : u < slots then
      detachedRead tags bank.mem base u (layout.addrAt hu)
        (bank.le_size (layout.memAt hu))
    else
      Stored.parentOnly j.parent j.edge

/-- No bank reads in the parent-only branch. The skew branch reads two
18-word snapshots, each with its own 18-word scratch array. The fallback
in the total reader is not reached on a certified skew branch. -/
def buildFromBank (bank : WriteResult bits words) (j : Job) : Stored :=
  buildOneSlot (readForBuild tags base layout bank j) j.parent j.jump j.edge

private theorem readForBuild_exact (bank : WriteResult bits words) (j : Job)
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old)
    {u : Nat} (hou : occupied u) :
    readForBuild tags base layout bank j u = old u := by
  obtain ⟨hu, he⟩ := hex u hou
  simp only [readForBuild, dif_pos hu, detachedRead_eq]
  exact he

theorem buildFromBank_eq (bank : WriteResult bits words) (j : Job)
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old)
    (deps : j.Dependencies occupied old) :
    buildFromBank tags base layout bank j =
      buildOneSlot old j.parent j.jump j.edge := by
  by_cases h : j.jump = j.parent
  · simp only [buildFromBank, buildOneSlot, if_pos h]
  · obtain ⟨hp, hq⟩ := deps h
    have ep := readForBuild_exact tags base layout bank j hex hp
    have eq := readForBuild_exact tags base layout bank j hex hq
    simp only [buildFromBank, buildOneSlot, if_neg h, ep, eq]

/-- Codec fit (e.g. from `stored_fits`) is separate from array capacity. -/
theorem buildFromBank_fit (bank : WriteResult bits words) (j : Job)
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old)
    (deps : j.Dependencies occupied old)
    (fit : (storedCodec tags).valid (buildOneSlot old j.parent j.jump j.edge)) :
    (storedCodec tags).valid (buildFromBank tags base layout bank j) := by
  rw [buildFromBank_eq tags base layout bank j hex deps]
  exact fit

private def writeBuilt (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) (r : Stored) (hr : (storedCodec tags).valid r) :
    WriteResult bits words :=
  match bank with
  | ⟨mem, hs, n⟩ =>
    let out := writeStoredAt tags mem base u (layout.addrAt hu)
      (by rw [hs]; exact layout.memAt hu) r hr
    ⟨out.mem, out.size_eq.trans hs, n + out.writes⟩

/-- Build before transferring the bank to the writer. Only the current
array is returned; the logical store and its certificates are not carried.
The writer performs 18 cell updates with no resize. As usual for Lean
arrays, in-place reuse requires that the caller not retain a live alias
to the input bank. The write count counts cell updates, not RC copies. -/
def step (bank : WriteResult bits words) (j : Job) (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j)) :
    WriteResult bits words :=
  let r := buildFromBank tags base layout bank j
  writeBuilt tags base layout bank j.slot hu r fit

private theorem writeBuilt_writes (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) (r : Stored) (hr : (storedCodec tags).valid r) :
    (writeBuilt tags base layout bank u hu r hr).writes = bank.writes + 18 := by
  cases bank with
  | mk mem hs n =>
    exact congrArg (fun k : Nat => n + k)
      (writeStoredAt_writes tags mem base u (layout.addrAt hu)
        (by rw [hs]; exact layout.memAt hu) r hr)

private theorem readSlot_writeBuilt_same (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) (r : Stored) (hr : (storedCodec tags).valid r) :
    readSlot tags base layout (writeBuilt tags base layout bank u hu r hr) u hu =
      r := by
  cases bank with
  | mk mem hs n =>
    exact readStoredAt_writeStoredAt tags mem base u (layout.addrAt hu)
      (by rw [hs]; exact layout.memAt hu) r hr

private theorem readSlot_writeBuilt_other (bank : WriteResult bits words)
    (u v : Nat) (hu : u < slots) (hv : v < slots) (hne : u ≠ v)
    (r : Stored) (hr : (storedCodec tags).valid r) :
    readSlot tags base layout (writeBuilt tags base layout bank u hu r hr) v hv =
      readSlot tags base layout bank v hv := by
  cases bank with
  | mk mem hs n =>
    exact readStoredAt_writeStoredAt_other tags mem base u v
      (layout.addrAt hu) (by rw [hs]; exact layout.memAt hu)
      (layout.addrAt hv) (by rw [hs]; exact layout.memAt hv) hne r hr

theorem step_writes (bank : WriteResult bits words) (j : Job) (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j)) :
    (step tags base layout bank j hu fit).writes = bank.writes + 18 :=
  writeBuilt_writes tags base layout bank j.slot hu
    (buildFromBank tags base layout bank j) fit

/-- Physical round-trip, independently of any logical invariant. -/
theorem step_roundTrip (bank : WriteResult bits words) (j : Job)
    (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j)) :
    readSlot tags base layout (step tags base layout bank j hu fit) j.slot hu =
      buildFromBank tags base layout bank j :=
  readSlot_writeBuilt_same tags base layout bank j.slot hu
    (buildFromBank tags base layout bank j) fit

theorem step_preserves (bank : WriteResult bits words) (j : Job)
    (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j))
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old)
    (fresh : ¬ occupied j.slot) :
    OccupiedExact tags base layout (step tags base layout bank j hu fit)
      occupied old := by
  intro v hov
  obtain ⟨hv, he⟩ := hex v hov
  have hne : j.slot ≠ v := fun e => fresh (e.symm ▸ hov)
  exact ⟨hv, (readSlot_writeBuilt_other tags base layout bank j.slot v hu hv hne
    (buildFromBank tags base layout bank j) fit).trans he⟩

/-- Induction interface: every old occupied slot stays exact, and the new
slot decodes to the record in the pure single-slot update. -/
theorem step_exact (bank : WriteResult bits words) (j : Job)
    (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j))
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old)
    (fresh : ¬ occupied j.slot) (deps : j.Dependencies occupied old) :
    OccupiedExact tags base layout (step tags base layout bank j hu fit)
      (j.occupy occupied) (j.overlay old) := by
  have kept := step_preserves tags base layout bank j hu fit hex fresh
  have added := (step_roundTrip tags base layout bank j hu fit).trans
    (buildFromBank_eq tags base layout bank j hex deps)
  intro v hov
  change occupied v ∨ v = j.slot at hov
  rcases hov with h | rfl
  · obtain ⟨hv, he⟩ := kept v h
    have hne : v ≠ j.slot := fun e => fresh (e ▸ h)
    exact ⟨hv, by simpa only [Job.overlay, if_neg hne] using he⟩
  · exact ⟨hu, by simpa only [Job.overlay, if_pos (Eq.refl j.slot), if_true] using added⟩



/-- Root and top-level slots have the same payload, at distinct addresses. -/
def seedRecord : Stored := Stored.parentOnly 0 Map.identity

theorem seedRecord_fields :
    seedRecord.parent = 0 ∧ seedRecord.jump = 0 ∧
      seedRecord.parentMap = Map.identity ∧ seedRecord.jumpMap = Map.identity :=
  ⟨rfl, rfl, rfl, rfl⟩

def SeedSlot (F : JumpForest) (u : Nat) : Prop :=
  u = 0 ∨ (0 < u ∧ u < F.size ∧ F.parentOf u = 0)

theorem rootSeed_ok {read : Store} {depth : Nat → Nat}
    (hd : depth 0 = 0) (hr : read 0 = seedRecord) :
    depth 0 = 0 ∧ (read 0).parent = 0 ∧ (read 0).jump = 0 ∧
      (read 0).jumpMap = Map.identity ∧ JumpOK read depth 0 := by
  refine ⟨hd, congrArg Stored.parent hr, congrArg Stored.jump hr,
    congrArg Stored.jumpMap hr, ?_⟩
  change ParentPath read depth 0 (read 0).jump (read 0).jumpMap
  have hp : ParentPath read depth 0 0 Map.identity := by constructor
  simpa only [hr, seedRecord, Stored.parentOnly] using hp

/-- Unlike the root loop, this certificate uses one strict parent edge. -/
theorem topSeed_jumpOK {read : Store} {depth : Nat → Nat} {u : Nat}
    (hd : depth 0 = 0) (live : 0 < depth u) (hr : read u = seedRecord) :
    JumpOK read depth u := by
  have down : depth (read u).parent < depth u := by
    simpa only [hr, seedRecord, Stored.parentOnly, hd] using live
  have hp : ParentPath read depth u (read u).parent (read u).parentMap :=
    parent_segment down
  change ParentPath read depth u (read u).jump (read u).jumpMap
  simpa only [hr, seedRecord, Stored.parentOnly] using hp

/-- A positive-depth query at a depth-one slot never takes the artificial edge. -/
theorem topSeed_trace_nil (F : JumpForest) (fuel u d : Nat)
    (hu : F.depthOf u = 1) (hd : 0 < d) :
    F.traceMovesAux fuel u d = [] := by
  have h : ¬ d < F.depthOf u := by omega
  cases fuel with
  | zero => simp only [JumpForest.traceMovesAux_zero]
  | succ fuel => simp only [JumpForest.traceMovesAux_succ, if_neg h]

theorem seedRecord_fits {bits ids endpoints : Nat}
    (w : Width bits (max ids endpoints)) (hi : 0 < ids)
    (hm : MapBound endpoints Map.identity) :
    (storedCodec w.tags).valid seedRecord :=
  stored_fits (ids := ids) (endpoints := endpoints) w seedRecord hi hi hm hm

/-- The caller supplies the physical slot. The forest witness is proof-only. -/
def seedWrite (bank : WriteResult bits words) (u : Nat) (hu : u < slots)
    {F : JumpForest} (_hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord) : WriteResult bits words :=
  writeBuilt tags base layout bank u hu seedRecord fit

theorem seedWrite_writes (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) {F : JumpForest} (hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord) :
    (seedWrite tags base layout bank u hu hs fit).writes = bank.writes + 18 :=
  writeBuilt_writes tags base layout bank u hu seedRecord fit

theorem seedWrite_roundTrip (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) {F : JumpForest} (hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord) :
    readSlot tags base layout (seedWrite tags base layout bank u hu hs fit) u hu =
      seedRecord :=
  readSlot_writeBuilt_same tags base layout bank u hu seedRecord fit

/-- Publish the seed and keep every other occupied slot exact. -/
theorem seedWrite_exact (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) {F : JumpForest} (hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord)
    {occupied : Nat → Prop} {old : Store}
    (hex : OccupiedExact tags base layout bank occupied old) :
    OccupiedExact tags base layout (seedWrite tags base layout bank u hu hs fit)
      (fun v => occupied v ∨ v = u)
      (fun v => if v = u then seedRecord else old v) := by
  intro v hv
  change occupied v ∨ v = u at hv
  by_cases h : v = u
  · subst v
    exact ⟨hu, by
      simpa only [if_pos (Eq.refl u), if_true] using
        seedWrite_roundTrip tags base layout bank u hu hs fit⟩
  · obtain ⟨hb, he⟩ := hex v (hv.resolve_right h)
    refine ⟨hb, ?_⟩
    dsimp only
    rw [if_neg h]
    exact (readSlot_writeBuilt_other tags base layout bank u v hu hb
      (Ne.symm h) seedRecord fit).trans he

private theorem writeBuilt_cell_outside (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) (r : Stored) (hr : (storedCodec tags).valid r)
    (cell : Nat) (hc : cell < words)
    (hout : cell < base.val + 18 * u ∨ base.val + 18 * u + 18 ≤ cell) :
    (writeBuilt tags base layout bank u hu r hr).mem[cell]'(
      (writeBuilt tags base layout bank u hu r hr).lt_size hc) =
      bank.mem[cell]'(bank.lt_size hc) := by
  cases bank with
  | mk mem hs n =>
    exact writeStoredAt_outside tags mem base u (layout.addrAt hu)
      (by rw [hs]; exact layout.memAt hu) r hr cell
      (by rw [hs]; exact hc) hout

theorem step_cell_outside (bank : WriteResult bits words) (j : Job)
    (hu : j.slot < slots)
    (fit : (storedCodec tags).valid (buildFromBank tags base layout bank j))
    (cell : Nat) (hc : cell < words)
    (hout : cell < base.val + 18 * j.slot ∨
      base.val + 18 * j.slot + 18 ≤ cell) :
    (step tags base layout bank j hu fit).mem[cell]'(
      (step tags base layout bank j hu fit).lt_size hc) =
      bank.mem[cell]'(bank.lt_size hc) :=
  writeBuilt_cell_outside tags base layout bank j.slot hu
    (buildFromBank tags base layout bank j) fit cell hc hout

theorem seedWrite_cell_outside (bank : WriteResult bits words) (u : Nat)
    (hu : u < slots) {F : JumpForest} (hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord)
    (cell : Nat) (hc : cell < words)
    (hout : cell < base.val + 18 * u ∨ base.val + 18 * u + 18 ≤ cell) :
    (seedWrite tags base layout bank u hu hs fit).mem[cell]'(
      (seedWrite tags base layout bank u hu hs fit).lt_size hc) =
      bank.mem[cell]'(bank.lt_size hc) :=
  writeBuilt_cell_outside tags base layout bank u hu seedRecord fit cell hc hout

theorem Layout.depthCell_before_slot {bits words slots : Nat} {base : Word bits}
    (l : Layout base words slots) {depthBase : Word bits}
    {depthWords i : Nat} (hBefore : depthBase.val + depthWords ≤ base.val)
    (hi : i < depthWords) (u : Nat) :
    depthBase.val + i < words ∧ depthBase.val + i < base.val + 18 * u := by
  have hcap := l.capacity
  constructor <;> omega


end PaperB.ExitPhysicalOneSlot
