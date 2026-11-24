module

public import PaperB.JumpMapFold
public import PaperB.ExitMapRetention

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.StoredPacking

open PaperB.Machine (Word)
open PaperB.ExitMap
open PaperB.ExitMap.Retention

private theorem word_val_lt {bits : Nat} (w : Word bits) :
    w.val < 2 ^ bits := by
  obtain ⟨v, hv⟩ := w
  exact hv

private def idCodec (bits : Nat) : Codec bits 1 Nat where
  valid id := id < 2 ^ bits
  encode id h := fun _ => word id h
  decode r := (r ⟨0, by decide⟩).val
  decode_valid r := word_val_lt (r ⟨0, by decide⟩)
  decode_encode _ _ := rfl

/-- Physical order: parent ID, jump ID, parent map, jump map. -/
def storedCodec {bits : Nat} (h : TagsFit bits) :
    Codec bits 18 CheckedFold.Stored :=
  (Codec.prod (Codec.prod (idCodec bits) (idCodec bits))
    (Codec.prod (mapCodec h) (mapCodec h))).via
    (fun r : CheckedFold.Stored =>
      ((r.parent, r.jump), (r.parentMap, r.jumpMap)))
    (fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩)
    (by
      intro p
      obtain ⟨⟨parent, jump⟩, ⟨parentMap, jumpMap⟩⟩ := p
      rfl)
    (by
      intro r
      cases r
      rfl)

theorem stored_decode_encode {bits : Nat} (h : TagsFit bits)
    (r : CheckedFold.Stored) (hr : (storedCodec h).valid r) :
    (storedCodec h).decode ((storedCodec h).encode r hr) = r :=
  (storedCodec h).decode_encode r hr

/-- ID and map endpoint limits may be chosen independently. -/
theorem stored_fits {bits ids endpoints : Nat}
    (w : Width bits (max ids endpoints)) (r : CheckedFold.Stored)
    (hp : r.parent < ids) (hj : r.jump < ids)
    (hpm : MapBound endpoints r.parentMap)
    (hjm : MapBound endpoints r.jumpMap) :
    (storedCodec w.tags).valid r := by
  have wi : ids ≤ 2 ^ bits :=
    Nat.le_trans (Nat.le_max_left ids endpoints) w.ranks
  have wm : Width bits endpoints :=
    ⟨Nat.le_trans (Nat.le_max_right ids endpoints) w.ranks, w.tags⟩
  change (r.parent < 2 ^ bits ∧ r.jump < 2 ^ bits) ∧
    ((mapCodec w.tags).valid r.parentMap ∧ (mapCodec w.tags).valid r.jumpMap)
  exact ⟨⟨Nat.lt_of_lt_of_le hp wi, Nat.lt_of_lt_of_le hj wi⟩,
    ⟨map_fits wm r.parentMap hpm, map_fits wm r.jumpMap hjm⟩⟩

theorem stored_bitsFor_fits {ids endpoints : Nat} (r : CheckedFold.Stored)
    (hp : r.parent < ids) (hj : r.jump < ids)
    (hpm : MapBound endpoints r.parentMap)
    (hjm : MapBound endpoints r.jumpMap) :
    (storedCodec (bitsFor_width (max ids endpoints)).tags).valid r :=
  stored_fits (bitsFor_width (max ids endpoints)) r hp hj hpm hjm

/-- Word address of slot `u`; address capacity is separate from codec fit. -/
def storedBase {bits : Nat} (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits) : Word bits :=
  word (base.val + 18 * u) (by omega)

theorem stored_offset_no_wrap {bits : Nat} (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits) (i : Fin 18) :
    (offsetWord (storedBase base u hAddr) i).val =
      base.val + 18 * u + i.val :=
  offsetWord_no_wrap (storedBase base u hAddr) hAddr i

/-- Read the 18 cells of one slot in an existing flat array. -/
def readStoredBlockAt {bits : Nat} (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) : Block bits 18 :=
  fun i =>
    mem[(offsetWord (storedBase base u hAddr) i).val]'(by
      rw [stored_offset_no_wrap base u hAddr i]
      have hi := i.isLt
      omega)

def readStoredAt {bits : Nat} (h : TagsFit bits) (mem : Array (Word bits))
    (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size) : CheckedFold.Stored :=
  (storedCodec h).decode (readStoredBlockAt mem base u hAddr hMem)

private theorem arrayCell_eq {α : Type} (mem : Array α) {i j : Nat}
    (e : i = j) (hj : j < mem.size) :
    mem[i]'(by rw [e]; exact hj) = mem[j]'hj := by
  cases e
  rfl

/-- Only the 18 cells in the selected slot need to contain the encoding. -/
theorem readStoredAt_exact {bits : Nat} (h : TagsFit bits)
    (mem : Array (Word bits)) (base : Word bits) (u : Nat)
    (hAddr : base.val + 18 * u + 18 ≤ 2 ^ bits)
    (hMem : base.val + 18 * u + 18 ≤ mem.size)
    (r : CheckedFold.Stored) (hr : (storedCodec h).valid r)
    (packed : ∀ i : Fin 18,
      mem[base.val + 18 * u + i.val]'(by have hi := i.isLt; omega) =
        (storedCodec h).encode r hr i) :
    readStoredAt h mem base u hAddr hMem = r := by
  have hBlock :
      readStoredBlockAt mem base u hAddr hMem = (storedCodec h).encode r hr := by
    funext i
    have hi : base.val + 18 * u + i.val < mem.size := by
      have hlt := i.isLt
      omega
    exact (arrayCell_eq mem (stored_offset_no_wrap base u hAddr i) hi).trans
      (packed i)
  change (storedCodec h).decode (readStoredBlockAt mem base u hAddr hMem) = r
  exact (congrArg (storedCodec h).decode hBlock).trans (stored_decode_encode h r hr)

end PaperB.StoredPacking
