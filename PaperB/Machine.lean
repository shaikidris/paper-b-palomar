module

public import Challenge
public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Machine

/-- A block name in one heap history. Slot numbers are never reused. -/
structure Handle (bits : Nat) where
  slot : Nat

structure Block where
  bits : Nat
  words : Array (Word bits)

/-- The outer array is a finite slot table. `none` marks a freed slot.
    Starting at `empty`, `liveWords` tracks the total live payload length. -/
structure Heap where
  slots : Array (Option Block)
  liveWords : Nat

def Heap.empty : Heap := ⟨#[], 0⟩

/-- Each slot costs one metadata unit, even when empty. -/
def Heap.space (heap : Heap) : Nat :=
  heap.slots.size + heap.liveWords

/-- Work is measured in abstract machine units, not Lean runtime costs.
    Space is sampled after each atomic operation. -/
structure Observation where
  work : Nat
  space : Nat

structure Step (α : Type) where
  value : α
  heap : Heap
  obs : Observation

private def finish {α : Type} (value : α) (heap : Heap) (work : Nat) :
    Step α :=
  ⟨value, heap, ⟨work, heap.space⟩⟩

variable {bits : Nat}

/-- Direct indexing, followed by a width check. Keep the slot bound for updates. -/
private def lookup (heap : Heap) (h : Handle bits) :
    Option { _words : Array (Word bits) // h.slot < heap.slots.size } :=
  if hs : h.slot < heap.slots.size then
    match heap.slots[h.slot]'hs with
    | none => none
    | some block =>
        if hw : block.bits = bits then
          let words := cast (congrArg (fun n => Array (Word n)) hw) block.words
          some ⟨words, hs⟩
        else
          none
  else
    none

/-- Charge one unit for the new slot and one per initialized word. -/
def allocate (heap : Heap) (count : Nat) (init : Word bits) :
    Step (Handle bits) :=
  let h : Handle bits := ⟨heap.slots.size⟩
  let block : Block := ⟨bits, Array.replicate count init⟩
  let next : Heap := ⟨heap.slots.push (some block), heap.liveWords + count⟩
  finish h next (count + 1)

/-- Direct accesses cost one unit, including failed attempts.
    Failure leaves the heap unchanged. -/
def read (heap : Heap) (h : Handle bits) (offset : Nat) :
    Step (Option (Word bits)) :=
  let result : Option (Word bits) := do
    let found ← lookup heap h
    found.val[offset]?
  finish result heap 1

def write (heap : Heap) (h : Handle bits) (offset : Nat) (value : Word bits) :
    Step (Option Unit) :=
  match lookup heap h with
  | none => finish none heap 1
  | some found =>
      if hi : offset < found.val.size then
        let block : Block := ⟨bits, found.val.set offset value hi⟩
        let slots := heap.slots.set h.slot (some block) found.property
        finish (some ()) { heap with slots := slots } 1
      else
        finish none heap 1

/-- Release the payload but keep the slot as metadata. -/
def free (heap : Heap) (h : Handle bits) : Step (Option Unit) :=
  match lookup heap h with
  | none => finish none heap 1
  | some found =>
      let slots := heap.slots.set h.slot none found.property
      let next : Heap := ⟨slots, heap.liveWords - found.val.size⟩
      finish (some ()) next 1

def totalWork : List Observation → Nat
  | [] => 0
  | o :: os => o.work + totalWork os

/-- Peak over the supplied samples. Include a zero-work initial sample
    if the starting heap should count toward the peak. -/
def peakSpace : List Observation → Nat
  | [] => 0
  | o :: os => max o.space (peakSpace os)

theorem totalWork_append (xs ys : List Observation) :
    totalWork (xs ++ ys) = totalWork xs + totalWork ys := by
  induction xs with
  | nil => simp [totalWork]
  | cons x xs ih => simp [totalWork, ih, Nat.add_assoc]

theorem space_le_peak (o : Observation) (xs : List Observation) :
    o ∈ xs → o.space ≤ peakSpace xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro h
      simp only [List.mem_cons] at h
      change o.space ≤ max x.space (peakSpace xs)
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

end PaperB.Machine
