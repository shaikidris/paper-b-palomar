module

public import PaperB.ExitPhysicalDepthColumn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitPhysicalBankLayout

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite
open PaperB.ExitMap.JumpMapRoute.StoredExit (Region)

/-- In one `words`-cell buffer, reserve `slots` depth cells at `start`,
    immediately followed by `18 * slots` record cells. The exclusive end
    may equal the address-space limit: it is not itself a cell address. -/
structure BankLayout {bits : Nat} (start : Word bits) (words slots : Nat) :
    Prop where
  address : start.val + slots + 18 * slots ≤ 2 ^ bits
  capacity : start.val + slots + 18 * slots ≤ words

namespace BankLayout

section
variable {bits words slots : Nat} {start : Word bits}
variable (b : BankLayout start words slots)
include b

/-- The record base still fits when `slots = 0`: in that case it is `start`. -/
theorem recordBase_lt : start.val + slots < 2 ^ bits := by
  by_cases hz : slots = 0
  · simpa only [hz, Nat.add_zero] using start.isLt
  · have h := b.address
    omega

def recordBase : Word bits :=
  ⟨start.val + slots, b.recordBase_lt⟩

def depthAddr (v : Fin slots) : Word bits :=
  ⟨start.val + v.val, by
    have h := b.recordBase_lt
    have hv := v.isLt
    omega⟩

def region : Region bits words where
  slots := slots
  depthAddr := b.depthAddr
  depthMem v := by
    change start.val + v.val < words
    have h := b.capacity
    have hv := v.isLt
    omega
  base := b.recordBase
  recordAddr v := by
    change start.val + slots + 18 * v.val + 18 ≤ 2 ^ bits
    have h := b.address
    have hv := v.isLt
    omega
  recordMem v := by
    change start.val + slots + 18 * v.val + 18 ≤ words
    have h := b.capacity
    have hv := v.isLt
    omega

def layout : ExitPhysicalOneSlot.Layout b.region.base words b.region.slots :=
  ⟨b.address, b.capacity⟩

def column : ExitPhysicalDepthColumn.Column b.region start :=
  ⟨fun _ => rfl⟩

-- These are constructor equalities, not modular-arithmetic lemmas.
@[simp] theorem region_slots : b.region.slots = slots := rfl

@[simp] theorem depthAddr_val (v : Fin slots) :
    (b.region.depthAddr v).val = start.val + v.val := rfl

@[simp] theorem recordBase_val :
    b.region.base.val = start.val + slots := rfl

theorem region_eq_of_bounds (b' : BankLayout start words slots) :
    b.region = b'.region := rfl

/-- The exact boundary, in the form also needed by the initializer. -/
theorem depthEnd_eq_recordBase :
    start.val + b.region.slots = b.region.base.val := rfl

theorem depthBeforeRecords :
    start.val + b.region.slots ≤ b.region.base.val :=
  Nat.le_of_eq b.depthEnd_eq_recordBase

/-- If the caller supplies a strict bound on the exclusive end, the same
    bound holds in the region's physical coordinates. -/
theorem strictEnd_capacity
    (h : start.val + slots + 18 * slots < 2 ^ bits) :
    b.region.base.val + 18 * b.region.slots < 2 ^ bits ∧
    b.region.base.val + 18 * b.region.slots ≤ words :=
  ⟨h, b.layout.capacity⟩

/-- A field address uses the very same record base as the region and layout. -/
def recordFieldAddr (v : Fin slots) (f : Fin 18) : Word bits :=
  ⟨b.region.base.val + 18 * v.val + f.val, by
    have h := b.region.recordAddr v
    have hf := f.isLt
    omega⟩

@[simp] theorem recordFieldAddr_val (v : Fin slots) (f : Fin 18) :
    (b.recordFieldAddr v f).val = b.region.base.val + 18 * v.val + f.val :=
  rfl

theorem depth_bounds (v : Fin slots) :
    (b.region.depthAddr v).val < 2 ^ bits ∧
    (b.region.depthAddr v).val < words :=
  ⟨(b.region.depthAddr v).isLt, b.region.depthMem v⟩

theorem recordField_bounds (v : Fin slots) (f : Fin 18) :
    (b.recordFieldAddr v f).val < 2 ^ bits ∧
    (b.recordFieldAddr v f).val < words := by
  refine ⟨(b.recordFieldAddr v f).isLt, ?_⟩
  rw [b.recordFieldAddr_val v f]
  have h := b.region.recordMem v
  have hf := f.isLt
  omega

theorem depth_in_column (v : Fin slots) :
    start.val ≤ (b.region.depthAddr v).val ∧
    (b.region.depthAddr v).val < b.region.base.val := by
  rw [b.depthAddr_val v, b.recordBase_val]
  have hv := v.isLt
  constructor <;> omega

theorem field_in_slot (v : Fin slots) (f : Fin 18) :
    b.region.base.val + 18 * v.val ≤ (b.recordFieldAddr v f).val ∧
    (b.recordFieldAddr v f).val < b.region.base.val + 18 * v.val + 18 := by
  rw [b.recordFieldAddr_val v f]
  have hf := f.isLt
  constructor <;> omega

/-- The depth column and the whole record area are disjoint half-open ranges. -/
theorem depth_records_disjoint (a : Nat) :
    ¬ ((start.val ≤ a ∧ a < start.val + slots) ∧
       (b.region.base.val ≤ a ∧ a < b.region.base.val + 18 * slots)) := by
  rw [b.recordBase_val]
  intro h
  exact (Nat.not_lt_of_ge h.2.1) h.1.2

/-- Distinct record slots also have disjoint half-open ranges. -/
theorem record_slots_disjoint (u v : Fin slots) (hne : u ≠ v) (a : Nat) :
    ¬ ((b.region.base.val + 18 * u.val ≤ a ∧
        a < b.region.base.val + 18 * u.val + 18) ∧
       (b.region.base.val + 18 * v.val ≤ a ∧
        a < b.region.base.val + 18 * v.val + 18)) := by
  have huv : u.val ≠ v.val := fun h => hne (Fin.ext h)
  intro h
  rcases h with ⟨⟨hu₀, hu₁⟩, ⟨hv₀, hv₁⟩⟩
  omega

/-- Both cell bounds apply to the same backing array. -/
theorem depth_lt_bank_size (bank : WriteResult bits words) (v : Fin slots) :
    (b.region.depthAddr v).val < bank.mem.size :=
  bank.lt_size (b.region.depthMem v)

theorem recordField_lt_bank_size (bank : WriteResult bits words)
    (v : Fin slots) (f : Fin 18) :
    (b.recordFieldAddr v f).val < bank.mem.size :=
  bank.lt_size (b.recordField_bounds v f).2

theorem end_le_bank_size (bank : WriteResult bits words) :
    b.region.base.val + 18 * b.region.slots ≤ bank.mem.size :=
  bank.le_size b.layout.capacity

end

/-- Construct the layout against an actual buffer's size. -/
def ofBuffer {bits slots : Nat} (mem : Array (Word bits)) (start : Word bits)
    (hAddr : start.val + slots + 18 * slots < 2 ^ bits)
    (hMem : start.val + slots + 18 * slots ≤ mem.size) :
    BankLayout start mem.size slots :=
  ⟨Nat.le_of_lt hAddr, hMem⟩

def zeroStart (bits : Nat) : Word bits :=
  ⟨0, Nat.two_pow_pos bits⟩

/-- Start-zero specialization. With zero slots both ranges are empty
    and both bases are zero, even if the buffer has size zero. -/
def direct {bits words slots : Nat}
    (hAddr : slots + 18 * slots ≤ 2 ^ bits)
    (hMem : slots + 18 * slots ≤ words) :
    BankLayout (zeroStart bits) words slots where
  address := by simpa only [zeroStart, Nat.zero_add] using hAddr
  capacity := by simpa only [zeroStart, Nat.zero_add] using hMem

/-- Tag fit is a codec requirement, independent of the address geometry.
    Carry it alongside the layout when handing off to the initializer. -/
structure TaggedDirect (bits words slots : Nat) where
  tags : TagsFit bits
  bounds : BankLayout (zeroStart bits) words slots

def directWithTags {bits words slots : Nat} (tags : TagsFit bits)
    (hAddr : slots + 18 * slots ≤ 2 ^ bits)
    (hMem : slots + 18 * slots ≤ words) :
    TaggedDirect bits words slots :=
  ⟨tags, direct hAddr hMem⟩

end BankLayout
end PaperB.ExitPhysicalBankLayout
