module

public import PaperB.ExitPhysicalOneSlot
public import PaperB.ExitWordArrayQuery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitPhysicalDepthColumn

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitMap.JumpMapRoute.StoredExit (Region depthAt)

/-- The query region addresses the depth column in vertex order. -/
structure Column {bits words : Nat} (R : Region bits words)
    (depthBase : Word bits) : Prop where
  addr_eq : ∀ v : Fin R.slots, (R.depthAddr v).val = depthBase.val + v.val

variable {bits words : Nat} {R : Region bits words} {depthBase : Word bits}

theorem Column.cell_lt (C : Column R depthBase) (v : Fin R.slots) :
    depthBase.val + v.val < words := by
  rw [← C.addr_eq v]
  exact R.depthMem v

/-- View the same region in a bank of the prescribed size. Only the
array bounds are transported; all addresses are unchanged. -/
@[inline] def regionIn (bank : WriteResult bits words) (R : Region bits words) :
    Region bits bank.mem.size where
  slots := R.slots
  depthAddr := R.depthAddr
  depthMem v := bank.lt_size (R.depthMem v)
  base := R.base
  recordAddr := R.recordAddr
  recordMem v := bank.le_size (R.recordMem v)

private def readCell (bank : WriteResult bits words) (a : Nat)
    (ha : a < words) : Word bits :=
  bank.mem[a]'(bank.lt_size ha)

private theorem depthAt_eq_readCell (C : Column R depthBase)
    (bank : WriteResult bits words) (v : Fin R.slots) :
    depthAt bank.mem (regionIn bank R) v.val =
      (readCell bank (depthBase.val + v.val) (C.cell_lt v)).val := by
  have hv : v.val < (regionIn bank R).slots := v.isLt
  rw [depthAt, dif_pos hv]
  have ha :
      (⟨(R.depthAddr v).val, bank.lt_size (R.depthMem v)⟩ :
        Fin bank.mem.size) =
      ⟨depthBase.val + v.val, bank.lt_size (C.cell_lt v)⟩ :=
    Fin.ext (C.addr_eq v)
  exact congrArg (fun a : Fin bank.mem.size => (bank.mem[a.val]'(a.isLt)).val) ha

/-- The only array update in the depth writer. -/
@[inline] private def writeCell (bank : WriteResult bits words) (a : Nat)
    (ha : a < words) (x : Word bits) : WriteResult bits words :=
  match bank with
  | ⟨mem, hsize, writes⟩ =>
    have h : a < mem.size := by
      rw [hsize]
      exact ha
    ⟨mem.set a x h, by simp [hsize], writes + 1⟩

private theorem readCell_writeCell_same (bank : WriteResult bits words)
    (a : Nat) (ha : a < words) (x : Word bits) :
    readCell (writeCell bank a ha x) a ha = x := by
  cases bank with
  | mk mem hsize writes =>
    simp [readCell, writeCell, Array.getElem_set]

private theorem readCell_writeCell_ne (bank : WriteResult bits words)
    (a : Nat) (ha : a < words) (x : Word bits)
    (j : Nat) (hj : j < words) (hne : j ≠ a) :
    readCell (writeCell bank a ha x) j hj = readCell bank j hj := by
  cases bank with
  | mk mem hsize writes =>
    simp [readCell, writeCell, Array.getElem_set, hne, Ne.symm hne]

private theorem writeCell_writes (bank : WriteResult bits words)
    (a : Nat) (ha : a < words) (x : Word bits) :
    (writeCell bank a ha x).writes = bank.writes + 1 := by
  cases bank
  rfl

@[inline] private def depthWord (depth : Fin R.slots → Nat)
    (fit : ∀ v, depth v < 2 ^ bits) (v : Fin R.slots) : Word bits :=
  ⟨depth v, fit v⟩

/-- Write the suffix starting at vertex `i`, threading only the current
bank. `Array.set` can reuse the buffer when it is uniquely owned. -/
private def writeFrom (C : Column R depthBase)
    (depth : Fin R.slots → Nat) (fit : ∀ v, depth v < 2 ^ bits) :
    (left i : Nat) → i + left = R.slots →
      WriteResult bits words → WriteResult bits words
  | 0, _, _, bank => bank
  | n + 1, i, hi, bank =>
    let v : Fin R.slots := ⟨i, by omega⟩
    writeFrom C depth fit n (i + 1) (by omega)
      (writeCell bank (depthBase.val + i) (C.cell_lt v) (depthWord depth fit v))
termination_by structural left => left

private def FromSpec (C : Column R depthBase)
    (depth : Fin R.slots → Nat) (fit : ∀ v, depth v < 2 ^ bits)
    (left i : Nat) (bank out : WriteResult bits words) : Prop :=
  out.writes = bank.writes + left ∧
  (∀ v : Fin R.slots, i ≤ v.val →
    readCell out (depthBase.val + v.val) (C.cell_lt v) = depthWord depth fit v) ∧
  (∀ (a : Nat) (ha : a < words),
    (a < depthBase.val + i ∨ depthBase.val + R.slots ≤ a) →
    readCell out a ha = readCell bank a ha)

private theorem writeFrom_spec (C : Column R depthBase)
    (depth : Fin R.slots → Nat) (fit : ∀ v, depth v < 2 ^ bits)
    (left : Nat) :
    ∀ (i : Nat) (hi : i + left = R.slots) (bank : WriteResult bits words),
      FromSpec C depth fit left i bank (writeFrom C depth fit left i hi bank) := by
  induction left with
  | zero =>
    intro i hi bank
    rw [writeFrom]
    unfold FromSpec
    refine ⟨by simp only [Nat.add_zero], ?_, ?_⟩
    · intro v hv
      have hlt := v.isLt
      exfalso
      omega
    · intro a ha hout
      rfl
  | succ n ih =>
    intro i hi bank
    let v : Fin R.slots := ⟨i, by omega⟩
    let next := writeCell bank (depthBase.val + i) (C.cell_lt v)
      (depthWord depth fit v)
    have hn : (i + 1) + n = R.slots := by omega
    rw [writeFrom]
    change FromSpec C depth fit (n + 1) i bank
      (writeFrom C depth fit n (i + 1) hn next)
    have tail := ih (i + 1) hn next
    unfold FromSpec at tail ⊢
    obtain ⟨hw, hexact, hframe⟩ := tail
    refine ⟨?_, ?_, ?_⟩
    · have hnext : next.writes = bank.writes + 1 :=
        writeCell_writes bank (depthBase.val + i) (C.cell_lt v)
          (depthWord depth fit v)
      rw [hw, hnext]
      omega
    · intro u hu
      by_cases h : u.val = i
      · have huv : u = v := Fin.ext h
        subst u
        have hv : depthBase.val + v.val < depthBase.val + (i + 1) := by
          change depthBase.val + i < depthBase.val + (i + 1)
          omega
        exact (hframe (depthBase.val + v.val) (C.cell_lt v) (Or.inl hv)).trans
          (readCell_writeCell_same bank (depthBase.val + i) (C.cell_lt v)
            (depthWord depth fit v))
      · exact hexact u (by omega)
    · intro a ha hout
      have hne : a ≠ depthBase.val + i := by
        rcases hout with h | h <;> omega
      have htail : a < depthBase.val + (i + 1) ∨
          depthBase.val + R.slots ≤ a := by
        rcases hout with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      exact (hframe a ha htail).trans
        (readCell_writeCell_ne bank (depthBase.val + i) (C.cell_lt v)
          (depthWord depth fit v) a ha hne)

/-- Install one physical depth word per slot in the already allocated bank. -/
def writeDepthColumn (C : Column R depthBase) (bank : WriteResult bits words)
    (depth : Fin R.slots → Nat) (fit : ∀ v, depth v < 2 ^ bits) :
    WriteResult bits words :=
  writeFrom C depth fit R.slots 0 (Nat.zero_add R.slots) bank

private theorem writeDepthColumn_spec (C : Column R depthBase)
    (bank : WriteResult bits words) (depth : Fin R.slots → Nat)
    (fit : ∀ v, depth v < 2 ^ bits) :
    FromSpec C depth fit R.slots 0 bank (writeDepthColumn C bank depth fit) :=
  writeFrom_spec C depth fit R.slots 0 (Nat.zero_add R.slots) bank

theorem writeDepthColumn_writes (C : Column R depthBase)
    (bank : WriteResult bits words) (depth : Fin R.slots → Nat)
    (fit : ∀ v, depth v < 2 ^ bits) :
    (writeDepthColumn C bank depth fit).writes = bank.writes + R.slots := by
  have spec := writeDepthColumn_spec C bank depth fit
  unfold FromSpec at spec
  exact spec.1

theorem writeDepthColumn_cell_outside (C : Column R depthBase)
    (bank : WriteResult bits words) (depth : Fin R.slots → Nat)
    (fit : ∀ v, depth v < 2 ^ bits) (a : Nat) (ha : a < words)
    (hout : a < depthBase.val ∨ depthBase.val + R.slots ≤ a) :
    (writeDepthColumn C bank depth fit).mem[a]'(
      (writeDepthColumn C bank depth fit).lt_size ha) =
      bank.mem[a]'(bank.lt_size ha) := by
  have spec := writeDepthColumn_spec C bank depth fit
  unfold FromSpec at spec
  exact spec.2.2 a ha (by simpa only [Nat.add_zero] using hout)

/-- Agreement through the actual query reader, on every vertex of `R`. -/
def DepthAgrees (bank : WriteResult bits words) (R : Region bits words)
    (depth : Fin R.slots → Nat) : Prop :=
  ∀ v : Fin R.slots, depthAt bank.mem (regionIn bank R) v.val = depth v

theorem writeDepthColumn_depthAgrees (C : Column R depthBase)
    (bank : WriteResult bits words) (depth : Fin R.slots → Nat)
    (fit : ∀ v, depth v < 2 ^ bits) :
    DepthAgrees (writeDepthColumn C bank depth fit) R depth := by
  intro v
  rw [depthAt_eq_readCell C (writeDepthColumn C bank depth fit) v]
  have spec := writeDepthColumn_spec C bank depth fit
  unfold FromSpec at spec
  exact congrArg (fun x : Word bits => x.val) (spec.2.1 v (Nat.zero_le _))

private theorem depthAgrees_of_frame (C : Column R depthBase)
    (bank out : WriteResult bits words) {depth : Fin R.slots → Nat}
    (agree : DepthAgrees bank R depth)
    (frame : ∀ v : Fin R.slots,
      readCell out (depthBase.val + v.val) (C.cell_lt v) =
        readCell bank (depthBase.val + v.val) (C.cell_lt v)) :
    DepthAgrees out R depth := by
  intro v
  rw [depthAt_eq_readCell C out v, frame v, ← depthAt_eq_readCell C bank v]
  exact agree v

theorem step_preserves_depthAgrees (C : Column R depthBase)
    (tags : TagsFit bits) (layout : Layout R.base words R.slots)
    (hBefore : depthBase.val + R.slots ≤ R.base.val)
    (bank : WriteResult bits words) (j : Job) (hu : j.slot < R.slots)
    (fit : (storedCodec tags).valid
      (ExitPhysicalOneSlot.buildFromBank tags R.base layout bank j))
    {depth : Fin R.slots → Nat} (agree : DepthAgrees bank R depth) :
    DepthAgrees (ExitPhysicalOneSlot.step tags R.base layout bank j hu fit) R depth := by
  refine depthAgrees_of_frame C bank _ agree ?_
  intro v
  exact ExitPhysicalOneSlot.step_cell_outside tags R.base layout bank j hu fit
    (depthBase.val + v.val) (C.cell_lt v)
    (Or.inl (Layout.depthCell_before_slot layout hBefore v.isLt j.slot).2)

theorem seedWrite_preserves_depthAgrees (C : Column R depthBase)
    (tags : TagsFit bits) (layout : Layout R.base words R.slots)
    (hBefore : depthBase.val + R.slots ≤ R.base.val)
    (bank : WriteResult bits words) (u : Nat) (hu : u < R.slots)
    {F : JumpForest} (hs : SeedSlot F u)
    (fit : (storedCodec tags).valid seedRecord)
    {depth : Fin R.slots → Nat} (agree : DepthAgrees bank R depth) :
    DepthAgrees (ExitPhysicalOneSlot.seedWrite tags R.base layout bank u hu hs fit)
      R depth := by
  refine depthAgrees_of_frame C bank _ agree ?_
  intro v
  exact ExitPhysicalOneSlot.seedWrite_cell_outside tags R.base layout bank u hu hs fit
    (depthBase.val + v.val) (C.cell_lt v)
    (Or.inl (Layout.depthCell_before_slot layout hBefore v.isLt u).2)

end PaperB.ExitPhysicalDepthColumn
