module

public import PaperB.RamMultiReturn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram.FixedROM

variable {bits : Nat} {L : Layout bits}

def join (left right : Program L) (haltIdx : Nat)
    (h : haltIdx < left.size) : Program L :=
  (left.set haltIdx (.goto left.size) h) ++
    right.map (relocateInstr left.size)

variable (left right : Program L) {haltIdx : Nat} (h : haltIdx < left.size)

theorem fetch_left {i : Nat} {op : Instr bits L.registerCount}
    (hne : i ≠ haltIdx) (hop : left[i]? = some op) :
    (join left right haltIdx h)[i]? = some op := by
  have hi : i < left.size := by
    by_cases hi : i < left.size
    · exact hi
    · have hn : left[i]? = none :=
        Array.getElem?_eq_none_iff.mpr (by omega)
      simp [hop] at hn
  rw [join, Array.getElem?_append_left]
  · rw [Array.getElem?_set_ne h hne.symm, hop]
  · simpa only [Array.size_set] using hi

theorem fetch_halt :
    (join left right haltIdx h)[haltIdx]? = some (.goto left.size) ∧
      (0 < right.size → left.size < (join left right haltIdx h).size) := by
  constructor
  · rw [join, Array.getElem?_append_left]
    · exact Array.getElem?_set_self h
    · simpa only [Array.size_set] using h
  · intro hr
    rw [join, Array.size_append, Array.size_set, Array.size_map]
    omega

theorem relocated_right :
    RelocatedSlice right (join left right haltIdx h) left.size := by
  unfold RelocatedSlice
  intro i op hop
  rw [join, Array.getElem?_append_right]
  · rw [Array.size_set, Array.getElem?_map]
    first
    | rw [show left.size + i - left.size = i by omega]
    | rw [show i + left.size - left.size = i by omega]
    rw [hop, Option.map_some]
  · rw [Array.size_set]
    omega

end PaperB.RamProgram.FixedROM
