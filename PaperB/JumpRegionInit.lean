module

public import PaperB.Jumps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Jumps.ConcreteInit

def allocatedWords (maxNodes : Nat) : Nat :=
  1 + 3 * (maxNodes + 1)

/-- The width also accommodates the exclusive end address. -/
def width (maxNodes : Nat) : Nat :=
  Nat.log2 (allocatedWords maxNodes) + 1

theorem allocatedWords_lt_pow (n : Nat) :
    allocatedWords n < 2 ^ width n := by
  have hp : 0 < allocatedWords n := by unfold allocatedWords; omega
  unfold width
  first
  | apply Nat.lt_two_pow_succ_log2 <;> omega
  | exact (Nat.log2_lt (by omega : allocatedWords n ≠ 0)).mp (by omega)
  | exact (Nat.log2_lt hp).mp (by omega)
  | exact?

def region (maxNodes : Nat) : JumpWordRegion where
  W := width maxNodes
  baseAddr := 0
  maxNodes := maxNodes
  wordCapacity := by
    have h := allocatedWords_lt_pow maxNodes
    unfold allocatedWords at h
    omega

@[simp] theorem region_end (n : Nat) :
    (region n).endAddr = allocatedWords n := rfl

theorem end_fits (n : Nat) : (region n).endAddr < 2 ^ (region n).W :=
  allocatedWords_lt_pow n

private theorem header_inBounds (n : Nat) :
    (region n).baseAddr < allocatedWords n := by
  change 0 < 1 + 3 * (n + 1)
  omega

theorem header_fits (n : Nat) : (region n).baseAddr < 2 ^ (region n).W :=
  Nat.lt_trans (header_inBounds n) (allocatedWords_lt_pow n)

theorem slot_addresses_fit (n u : Nat) (hu : u ≤ n) :
    (region n).parentAddr u < 2 ^ (region n).W ∧
      (region n).depthAddr u < 2 ^ (region n).W ∧
      (region n).jumpAddr u < 2 ^ (region n).W := by
  have h := (region n).slot_addrs_inRegion (u := u) hu
  have he := end_fits n
  omega

def zeroMem (n : Nat) : Array Nat :=
  Array.replicate (allocatedWords n) 0

@[simp] theorem zeroMem_size (n : Nat) :
    (zeroMem n).size = allocatedWords n := by
  simp [zeroMem]

private theorem read_zeroMem (n a : Nat) :
    readWord (zeroMem n) a = 0 := by
  by_cases ha : a < allocatedWords n
  all_goals
    first
    | simpa [readWord, zeroMem, ha]
    | simpa [readWord, zeroMem, ha, getElem?_pos, getElem?_neg]
    | simpa [readWord, zeroMem, ha, Array.getD, getElem?_pos, getElem?_neg]
    | simpa [readWord, zeroMem, ha, getElem!_pos, getElem!_neg]

private theorem zeroMem_fit (n : Nat) :
    WordMemFit (region n).W (zeroMem n) := by
  exact
    { size_le := by
        rw [zeroMem_size]
        exact Nat.le_of_lt (allocatedWords_lt_pow n)
      word_lt := by
        intro i hi
        have hz : 0 < 2 ^ (region n).W := header_fits n
        simpa [zeroMem] using hz }

/-- Zero-fill the allocation, then write the size header. The trace records
    accesses after allocation; the zero-fill charge is accounted for separately. -/
def initImage (n : Nat) : Array Nat × List WordAccess :=
  (writeWord (zeroMem n) (region n).baseAddr 1,
    [WordAccess.write (region n).baseAddr 1])

@[simp] theorem initImage_size (n : Nat) :
    (initImage n).1.size = allocatedWords n := by
  change (writeWord (zeroMem n) (region n).baseAddr 1).size = _
  rw [writeWord_size, zeroMem_size]

theorem exact_allocated_words (maxNodes : Nat) :
    (initImage maxNodes).1.size = 1 + 3 * (maxNodes + 1) :=
  initImage_size maxNodes

theorem allocated_address_fits (n a : Nat) (ha : a < (initImage n).1.size) :
    a < 2 ^ (region n).W :=
  Nat.lt_trans (by simpa only [initImage_size] using ha) (allocatedWords_lt_pow n)

theorem init_header (n : Nat) :
    readWord (initImage n).1 (region n).baseAddr = 1 := by
  change readWord (writeWord (zeroMem n) (region n).baseAddr 1)
    (region n).baseAddr = 1
  exact readWord_writeWord_self (by simpa using header_inBounds n)

theorem init_nonheader (n a : Nat) (ha : a < allocatedWords n)
    (hne : a ≠ (region n).baseAddr) :
    readWord (initImage n).1 a = 0 := by
  have hb : (region n).baseAddr < (zeroMem n).size := by
    simpa using header_inBounds n
  have ha' : a < (zeroMem n).size := by simpa using ha
  have hne' : (region n).baseAddr ≠ a := Ne.symm hne
  change readWord (writeWord (zeroMem n) (region n).baseAddr 1) a = 0
  suffices h : readWord (writeWord (zeroMem n) (region n).baseAddr 1) a =
      readWord (zeroMem n) a from h.trans (read_zeroMem n a)
  first
  | apply readWord_writeWord_other <;> omega
  | apply readWord_writeWord_of_ne <;> omega
  | apply readWord_writeWord_ne <;> omega
  | simpa [writeWord, readWord, hb, ha', hne, hne', getElem?_pos]
  | exact?

theorem init_mem_fit (n : Nat) : WordMemFit (region n).W (initImage n).1 := by
  change WordMemFit (region n).W (writeWord (zeroMem n) (region n).baseAddr 1)
  have h := allocatedWords_lt_pow n
  change 1 + 3 * (n + 1) < 2 ^ (region n).W at h
  exact (zeroMem_fit n).writeWord (by simpa using header_inBounds n) (by omega)

theorem init_layout (n : Nat) :
    JumpWordLayout (region n) JumpForest.init (initImage n).1 := by
  have onlyRoot (u : Nat) (hu : u < JumpForest.init.size) : u = 0 := by
    change u < 1 at hu
    omega
  have hs := (region n).slot_addrs_inRegion (u := 0) (Nat.zero_le n)
  have he := region_end n
  have hp := init_nonheader n ((region n).parentAddr 0) (by omega) (by omega)
  have hd := init_nonheader n ((region n).depthAddr 0) (by omega) (by omega)
  have hj := init_nonheader n ((region n).jumpAddr 0) (by omega) (by omega)
  refine
    { valid := ValidJumpForest.init
      inserted_le := Nat.zero_le n
      region_inBounds := by simp
      mem_fit := init_mem_fit n
      size_word := init_header n
      slot_parent := ?_
      slot_depth := ?_
      slot_jump := ?_ }
  · intro u hu
    rw [onlyRoot u hu]
    exact hp
  · intro u hu
    rw [onlyRoot u hu]
    exact hd
  · intro u hu
    rw [onlyRoot u hu]
    exact hj

/-- One charge per zero-filled word and one per post-allocation access. -/
def initCharge (n : Nat) : Nat :=
  (zeroMem n).size + (initImage n).2.length

/-- Exactly one post-allocation write (and no reads), in addition to zero-fill. -/
theorem exact_init_charges (n : Nat) :
    (zeroMem n).size = 1 + 3 * (n + 1) ∧
    (initImage n).2 = [WordAccess.write 0 1] ∧
    (initImage n).2.length = 1 ∧
    initCharge n = (1 + 3 * (n + 1)) + 1 := by
  simp [initCharge, initImage, region, allocatedWords]

end PaperB.Jumps.ConcreteInit
