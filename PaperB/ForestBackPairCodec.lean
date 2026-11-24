module

public import PaperB.ForestSlimIndex
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace OptionalFinPair

def encode {n : Nat} : Option (Fin n × Fin n) → Nat × Nat
  | none => (0, 0)
  | some (x, y) => (x.val + 1, y.val)

def decode (n : Nat) : Nat × Nat → Option (Fin n × Fin n)
  | (0, _) => none
  | (a + 1, b) =>
    if ha : a < n then
      if hb : b < n then some (⟨a, ha⟩, ⟨b, hb⟩)
      else none
    else none

theorem decode_encode {n : Nat} (p : Option (Fin n × Fin n)) :
    decode n (encode p) = p := by
  cases p with
  | none => rfl
  | some p =>
    rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp [encode, decode, ha, hb]

theorem encode_injective {n : Nat} {p q : Option (Fin n × Fin n)}
    (h : encode p = encode q) : p = q := by
  simpa only [decode_encode] using congrArg (decode n) h

theorem encode_fields_lt {n bits : Nat} (h : n < 2 ^ bits)
    (p : Option (Fin n × Fin n)) :
    (encode p).1 < 2 ^ bits ∧ (encode p).2 < 2 ^ bits := by
  cases p with
  | none =>
    change 0 < 2 ^ bits ∧ 0 < 2 ^ bits
    constructor <;> omega
  | some p =>
    rcases p with ⟨x, y⟩
    have hx : x.val < n := x.isLt
    have hy : y.val < n := y.isLt
    change x.val + 1 < 2 ^ bits ∧ y.val < 2 ^ bits
    constructor <;> omega

end OptionalFinPair

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient

variable {H : LabelledQuotient}

def backPairFields (q : Option (CutPair H)) : Option (Fin H.vertexCount × Fin H.vertexCount) :=
  q.map (fun p => (p.fst, p.snd))

def encodeBackPair (q : Option (CutPair H)) : Nat × Nat :=
  OptionalFinPair.encode (backPairFields q)

theorem encodeBackPair_decode (q : Option (CutPair H)) :
    OptionalFinPair.decode H.vertexCount (encodeBackPair q) = backPairFields q :=
  OptionalFinPair.decode_encode _

theorem encodeBackPair_eq_iff (p q : Option (CutPair H)) :
    encodeBackPair p = encodeBackPair q ↔ p = q := by
  constructor
  · intro h
    have h' : backPairFields p = backPairFields q :=
      OptionalFinPair.encode_injective h
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q => simp [backPairFields] at h'
    | some p =>
      cases q with
      | none => simp [backPairFields] at h'
      | some q =>
        have hp := Option.some.inj h'
        exact congrArg some (CutPair.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp))
  · intro h
    rw [h]

theorem encodeBackPair_fits {bits : Nat} (h : H.vertexCount < 2 ^ bits)
    (q : Option (CutPair H)) :
    (encodeBackPair q).1 < 2 ^ bits ∧ (encodeBackPair q).2 < 2 ^ bits :=
  OptionalFinPair.encode_fields_lt h _

end PaperB.RetainedProperLoss
