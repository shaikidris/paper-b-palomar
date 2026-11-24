module

public import PaperB.Machine
public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.WordOps

open PaperB.Machine

-- Charges below are word-model costs, not costs of evaluating the Nat
-- formulas in Lean. Zero is an immediate operand.

/-- Two primitives: subtract `x` from immediate zero, then AND with `x`. -/
def lowbit {bits : Nat} (x : Word bits) : Word bits :=
  let neg := sub (zero bits) x
  band x neg

theorem add_val {bits : Nat} (x y : Word bits) :
    (add x y).val = (x.val + y.val) % (2 ^ bits) :=
  rfl

theorem sub_val {bits : Nat} (x y : Word bits) :
    (sub x y).val = (2 ^ bits + x.val - y.val) % (2 ^ bits) :=
  rfl

theorem band_val {bits : Nat} (x y : Word bits) :
    (band x y).val = (x.val &&& y.val) :=
  rfl

theorem ltb_eq_true {bits : Nat} (x y : Word bits) :
    ltb x y = true ↔ x.val < y.val := by
  simp [ltb]

theorem add_no_wrap {bits : Nat} (x y : Word bits)
    (h : x.val + y.val < 2 ^ bits) :
    (add x y).val = x.val + y.val := by
  rw [add_val, Nat.mod_eq_of_lt h]

theorem lowbit_val {bits : Nat} (x : Word bits) :
    (lowbit x).val = (x.val &&& ((2 ^ bits - x.val) % (2 ^ bits))) := by
  simp [lowbit, band_val, sub_val, zero]

def addrBits (n m : Nat) : Nat :=
  Nat.log2 (n + m + 1) + 1

theorem address_bound (n m : Nat) :
    n + m + 1 < 2 ^ addrBits n m := by
  have h : n + m + 1 ≠ 0 := by omega
  unfold addrBits
  exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)

/-- Original vertex IDs and explicit arc occurrence IDs fit. Arc IDs also
fit when stored after the vertices, at addresses `n + e.val`. -/
theorem address_size (n m : Nat) :
    (∀ v : Fin n, v.val < 2 ^ addrBits n m) ∧
    (∀ e : Fin m, e.val < 2 ^ addrBits n m ∧
      n + e.val < 2 ^ addrBits n m) := by
  have h := address_bound n m
  constructor
  · intro v
    have hv := v.isLt
    omega
  · intro e
    have he := e.isLt
    constructor <;> omega

end PaperB.WordOps
