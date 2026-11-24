module

public import PaperB.ExitStoredCodec

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option maxHeartbeats 2000000

namespace PaperB.ExitStoredWrite

open PaperB.Machine (Word)
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.StoredPacking

structure WriteResult (bits words : Nat) where
  mem : Array (Word bits)
  size_eq : mem.size = words
  writes : Nat

theorem WriteResult.lt_size {bits words j : Nat}
    (s : WriteResult bits words) (hj : j < words) : j < s.mem.size := by
  rw [s.size_eq]
  exact hj

theorem WriteResult.le_size {bits words n : Nat}
    (s : WriteResult bits words) (hn : n ≤ words) : n ≤ s.mem.size := by
  rw [s.size_eq]
  exact hn

private def getCell {bits words : Nat} (s : WriteResult bits words)
    (j : Nat) (hj : j < words) : Word bits :=
  s.mem[j]'(s.lt_size hj)

/-- The only array update in the writer. Each update incurs one logical write. -/
@[inline] private def setCell {bits words : Nat} (s : WriteResult bits words)
    (a : Nat) (ha : a < words) (x : Word bits) : WriteResult bits words where
  mem := s.mem.set a x (s.lt_size ha)
  size_eq := by simp [s.size_eq]
  writes := s.writes + 1

private theorem get_setCell_same {bits words : Nat} (s : WriteResult bits words)
    (a : Nat) (ha : a < words) (x : Word bits) :
    getCell (setCell s a ha x) a ha = x := by
  first
  | simpa [getCell, setCell]
  | simp [getCell, setCell, Array.getElem_set]

private theorem get_setCell_ne {bits words : Nat} (s : WriteResult bits words)
    (a j : Nat) (ha : a < words) (hj : j < words) (x : Word bits)
    (hne : j ≠ a) :
    getCell (setCell s a ha x) j hj = getCell s j hj := by
  first
  | simpa [getCell, setCell, hne, Ne.symm hne]
  | simp [getCell, setCell, Array.getElem_set, hne, Ne.symm hne]

/-- Write offsets `n-1` down to `0`, carrying just the current array and charge. -/
private def run {bits words : Nat} (addr : Fin 18 → Nat)
    (bound : ∀ i, addr i < words) (block : Block bits 18) :
    (n : Nat) → n ≤ 18 → WriteResult bits words → WriteResult bits words
  | 0, _, s => s
  | n + 1, hn, s =>
      let i : Fin 18 := ⟨n, by omega⟩
      run addr bound block n (by omega) (setCell s (addr i) (bound i) (block i))
termination_by structural n => n

private theorem run_writes {bits words : Nat} (addr : Fin 18 → Nat)
    (bound : ∀ i, addr i < words) (block : Block bits 18) :
    ∀ (n : Nat) (hn : n ≤ 18) (s : WriteResult bits words),
      (run addr bound block n hn s).writes = s.writes + n := by
  intro n
  induction n with
  | zero =>
      intro hn s
      simp only [run, Nat.add_zero]
  | succ n ih =>
      intro hn s
      rw [run, ih]
      change (s.writes + 1) + n = s.writes + (n + 1)
      omega

private theorem run_frame {bits words : Nat} (addr : Fin 18 → Nat)
    (bound : ∀ i, addr i < words) (block : Block bits 18)
    (j : Nat) (hj : j < words) :
    ∀ (n : Nat) (hn : n ≤ 18) (s : WriteResult bits words),
      (∀ i : Fin 18, i.val < n → j ≠ addr i) →
      getCell (run addr bound block n hn s) j hj = getCell s j hj := by
  intro n
  induction n with
  | zero =>
      intro hn s hne
      simp only [run]
  | succ n ih =>
      intro hn s hne
      let i : Fin 18 := ⟨n, by omega⟩
      let t := setCell s (addr i) (bound i) (block i)
      rw [run]
      change getCell (run addr bound block n (by omega) t) j hj = getCell s j hj
      calc
        _ = getCell t j hj := ih (by omega) t (fun k hk => hne k (by omega))
        _ = _ := get_setCell_ne s (addr i) j (bound i) hj (block i)
          (hne i (by change n < n + 1; omega))

private theorem run_hit {bits words : Nat} (addr : Fin 18 → Nat)
    (bound : ∀ i, addr i < words) (block : Block bits 18)
    (inj : ∀ i j, addr i = addr j → i = j) (i : Fin 18) :
    ∀ (n : Nat) (hn : n ≤ 18) (s : WriteResult bits words),
      i.val < n →
      getCell (run addr bound block n hn s) (addr i) (bound i) = block i := by
  intro n
  induction n with
  | zero =>
      intro hn s hi
      omega
  | succ n ih =>
      intro hn s hi
      let k : Fin 18 := ⟨n, by omega⟩
      let t := setCell s (addr k) (bound k) (block k)
      rw [run]
      change getCell (run addr bound block n (by omega) t) (addr i) (bound i) =
        block i
      by_cases h : i.val < n
      · exact ih (by omega) t h
      · have e : i = k := Fin.ext (by change i.val = n; omega)
        rw [e]
        calc
          _ = getCell t (addr k) (bound k) := by
            apply run_frame
            intro l hl he
            have hv := congrArg Fin.val (inj k l he)
            change n = l.val at hv
            omega
          _ = _ := get_setCell_same s (addr k) (bound k) (block k)

private def slotIndex {bits : Nat} (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits) (i : Fin 18) : Nat :=
  (offsetWord (storedBase base u hAddr) i).val

private theorem slotIndex_lt {bits words : Nat} (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ words) (i : Fin 18) :
    slotIndex base u hAddr i < words := by
  simp only [slotIndex, stored_offset_no_wrap]
  have hi := i.isLt
  omega

private theorem slotIndex_inj {bits : Nat} (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits) (i j : Fin 18)
    (e : slotIndex base u hAddr i = slotIndex base u hAddr j) : i = j := by
  simp only [slotIndex, stored_offset_no_wrap] at e
  exact Fin.ext (by omega)

theorem stored_offsets_disjoint {bits : Nat} (base : Word bits) {u v : Nat}
    (hu : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hv : base.val + 18 * v + 18 ≤ 2 ^ bits) (hne : u ≠ v) (i j : Fin 18) :
    (offsetWord (storedBase base u hu) i).val ≠
      (offsetWord (storedBase base v hv) j).val := by
  intro e
  rw [stored_offset_no_wrap base u hu i, stored_offset_no_wrap base v hv j] at e
  have hi := i.isLt
  have hj := j.isLt
  omega

def writeStoredBlockAt {bits : Nat} (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) (block : Block bits 18) :
    WriteResult bits mem.size :=
  run (slotIndex base u hAddr) (slotIndex_lt base u hAddr hMem)
    block 18 (by decide) ⟨mem, rfl, 0⟩

theorem writeStoredBlockAt_writes {bits : Nat} (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) (block : Block bits 18) :
    (writeStoredBlockAt mem base u hAddr hMem block).writes = 18 :=
  run_writes (slotIndex base u hAddr) (slotIndex_lt base u hAddr hMem)
    block 18 (by decide) ⟨mem, rfl, 0⟩

theorem readStoredBlockAt_writeStoredBlockAt {bits : Nat} (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) (block : Block bits 18) :
    let out := writeStoredBlockAt mem base u hAddr hMem block
    readStoredBlockAt out.mem base u hAddr (out.le_size hMem) = block := by
  dsimp only
  funext i
  exact run_hit (slotIndex base u hAddr) (slotIndex_lt base u hAddr hMem)
    block (slotIndex_inj base u hAddr) i 18 (by decide) ⟨mem, rfl, 0⟩ i.isLt

theorem writeStoredBlockAt_frame {bits : Nat} (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) (block : Block bits 18)
    (j : Nat) (hj : j < mem.size)
    (hne : ∀ i : Fin 18, j ≠ (offsetWord (storedBase base u hAddr) i).val) :
    let out := writeStoredBlockAt mem base u hAddr hMem block
    out.mem[j]'(out.lt_size hj) = mem[j]'hj :=
  run_frame (slotIndex base u hAddr) (slotIndex_lt base u hAddr hMem)
    block j hj 18 (by decide) ⟨mem, rfl, 0⟩ (fun i _ => hne i)

def writeStoredAt {bits : Nat} (tags : TagsFit bits) (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r) :
    WriteResult bits mem.size :=
  writeStoredBlockAt mem base u hAddr hMem ((storedCodec tags).encode r hr)

theorem writeStoredAt_size {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r) :
    (writeStoredAt tags mem base u hAddr hMem r hr).mem.size = mem.size :=
  (writeStoredAt tags mem base u hAddr hMem r hr).size_eq

theorem writeStoredAt_writes {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r) :
    (writeStoredAt tags mem base u hAddr hMem r hr).writes = 18 :=
  writeStoredBlockAt_writes mem base u hAddr hMem ((storedCodec tags).encode r hr)

theorem readStoredAt_writeStoredAt {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r) :
    let out := writeStoredAt tags mem base u hAddr hMem r hr
    readStoredAt tags out.mem base u hAddr (out.le_size hMem) = r :=
  (congrArg (storedCodec tags).decode
    (readStoredBlockAt_writeStoredBlockAt mem base u hAddr hMem
      ((storedCodec tags).encode r hr))).trans (stored_decode_encode tags r hr)

theorem writeStoredAt_frame {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r)
    (j : Nat) (hj : j < mem.size)
    (hne : ∀ i : Fin 18, j ≠ (offsetWord (storedBase base u hAddr) i).val) :
    let out := writeStoredAt tags mem base u hAddr hMem r hr
    out.mem[j]'(out.lt_size hj) = mem[j]'hj :=
  writeStoredBlockAt_frame mem base u hAddr hMem ((storedCodec tags).encode r hr)
    j hj hne

theorem writeStoredAt_outside {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r)
    (j : Nat) (hj : j < mem.size)
    (hout : j < base.val + 18 * u ∨ base.val + 18 * u + 18 ≤ j) :
    let out := writeStoredAt tags mem base u hAddr hMem r hr
    out.mem[j]'(out.lt_size hj) = mem[j]'hj := by
  apply writeStoredAt_frame tags mem base u hAddr hMem r hr j hj
  intro i e
  rw [stored_offset_no_wrap base u hAddr i] at e
  have hi := i.isLt
  omega

theorem readStoredAt_writeStoredAt_other {bits : Nat} (tags : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u v : Nat)
    (hu : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hmu : base.val + 18 * u + 18 ≤ mem.size)
    (hv : base.val + 18 * v + 18 ≤ 2 ^ bits)
    (hmv : base.val + 18 * v + 18 ≤ mem.size) (hne : u ≠ v)
    (r : CheckedFold.Stored) (hr : (storedCodec tags).valid r) :
    let out := writeStoredAt tags mem base u hu hmu r hr
    readStoredAt tags out.mem base v hv (out.le_size hmv) =
      readStoredAt tags mem base v hv hmv := by
  dsimp only [readStoredAt]
  apply congrArg (storedCodec tags).decode
  funext i
  exact writeStoredAt_frame tags mem base u hu hmu r hr
    (slotIndex base v hv i) (slotIndex_lt base v hv hmv i)
    (fun j => stored_offsets_disjoint base hv hu (Ne.symm hne) i j)

end PaperB.ExitStoredWrite
