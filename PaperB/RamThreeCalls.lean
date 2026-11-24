module

public import PaperB.RamWideWorker

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

abbrev layout (bits cap : Nat) (hcap : cap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, cap, 0, hcap, Nat.zero_le _⟩

abbrev Setup (bits : Nat) := Vector (Vector (Instr bits 16) 8) 3

-- Saved slots, in order: three (base, len) pairs, cutLo, cutHi, target.
def savedReg (n : Fin 9) : Fin 16 :=
  ⟨7 + n.val, by have hn := n.isLt; omega⟩

variable {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)

def bank : ArenaMap (Predecessor.layout bits cap hcap) (layout bits cap hcap) :=
  fun r => ⟨r.val, Nat.lt_trans r.isLt (by change 7 < 16; decide)⟩

theorem bank_inj {a b : Fin 7} (h : bank hcap a = bank hcap b) : a = b :=
  Fin.ext (congrArg (fun r : Fin 16 => r.val) h)

theorem bank_ne_saved (r : Fin 7) (n : Fin 9) : bank hcap r ≠ savedReg n := by
  intro h
  have hv : r.val = 7 + n.val := congrArg Fin.val h
  have hr := r.isLt
  omega

def entryPC (c : Fin 3) : Nat := 20 * c.val + 8
def returnPC (c : Fin 3) : Nat := 20 * (c.val + 1)

variable (setup : Setup bits)

-- Each 20-cell block is eight setup cells, eleven worker cells, and a goto.
-- Setup starts at 0, 20, and 40. The final return lands on the halt at 60.
private def cell (p : Fin 61) : Instr bits 16 :=
  if hp : p.val < 60 then
    let c : Fin 3 := ⟨p.val / 20, by omega⟩
    let k := p.val % 20
    if hs : k < 8 then
      (setup[c.val]'(c.isLt))[k]'(hs)
    else if k = 19 then
      .goto (returnPC c)
    else
      embedInstr (bank hcap) (relocateInstr (entryPC c)
        ((Predecessor.worker hcap)[k - 8]'(by
          rw [Predecessor.worker_size]
          have hk : k < 20 := Nat.mod_lt _ (by decide)
          omega)))
  else
    .halt

/-- Materialize the linked array. The VM uses ordinary array fetches. -/
def program : Program (layout bits cap hcap) :=
  Array.ofFn (cell hcap setup)

@[simp] theorem program_size : (program hcap setup).size = 61 := by
  simp only [program, Array.size_ofFn]

private theorem fetch_program {p : Nat} (hp : p < 61) :
    (program hcap setup)[p]? = some (cell hcap setup ⟨p, hp⟩) := by
  simp only [program, getElem?_def, Array.size_ofFn, hp, dif_pos,
    Array.getElem_ofFn]

theorem fetch_body (c : Fin 3) (k : Nat) (op : Instr bits 7)
    (hk : k < 11) (hop : (Predecessor.worker hcap)[k]? = some op) :
    (program hcap setup)[entryPC c + k]? =
      some (embedInstr (bank hcap) (relocateInstr (entryPC c) op)) := by
  have hc := c.isLt
  have hp : entryPC c + k < 60 := by unfold entryPC; omega
  have hq : (entryPC c + k) / 20 = c.val := by unfold entryPC; omega
  have hm : (entryPC c + k) % 20 = 8 + k := by unfold entryPC; omega
  have hs : ¬ 8 + k < 8 := by omega
  have ht : 8 + k ≠ 19 := by omega
  have hi : 8 + k - 8 = k := by omega
  have hw : k < (Predecessor.worker hcap).size := by
    rw [Predecessor.worker_size]
    omega
  have he : (Predecessor.worker hcap)[k] = op := by
    simpa [getElem?_def, hw] using hop
  rw [fetch_program hcap setup (by omega : entryPC c + k < 61)]
  simp only [cell, Fin.val_mk, hp, dif_pos, hq, hm, hs, dif_neg,
    ht, if_neg, hi, he]
  simp

theorem fetch_return (c : Fin 3) :
    (program hcap setup)[entryPC c + 11]? = some (.goto (returnPC c)) := by
  have hc := c.isLt
  have hp : entryPC c + 11 < 60 := by unfold entryPC; omega
  have hq : (entryPC c + 11) / 20 = c.val := by unfold entryPC; omega
  have hm : (entryPC c + 11) % 20 = 19 := by unfold entryPC; omega
  have hs : ¬ (19 : Nat) < 8 := by decide
  rw [fetch_program hcap setup (by omega : entryPC c + 11 < 61)]
  simp only [cell, Fin.val_mk, hp, dif_pos, hq, hm, hs, dif_neg, if_pos]
  simp

theorem return_in_bounds (c : Fin 3) :
    returnPC c < (program hcap setup).size := by
  rw [program_size]
  have hc := c.isLt
  unfold returnPC
  omega

/-- The placed call, conditional on the caller having established entry agreement. -/
theorem run_site (c : Fin 3)
    {i : Input (Predecessor.layout bits cap hcap)}
    {j : Input (layout bits cap hcap)}
    {s : State (Predecessor.layout bits cap hcap)}
    {frame t : State (layout bits cap hcap)}
    {r : Result (Predecessor.layout bits cap hcap)} {fuel : Nat}
    (ok : run (Predecessor.worker hcap) i fuel s = some r)
    (hi : i.words = j.words)
    (ha : ArenaAgreement (bank hcap) frame (relocateStatePC (entryPC c) s) t) :
    ∃ v, Steps (program hcap setup) j r.executed t v ∧
      ArenaAgreement (bank hcap) frame { r.finalState with pc := returnPC c } v :=
  worker_return_embedOnPlaced (i := i) (s := s)
    (ρ := bank hcap) (wide := program hcap setup)
    (off := entryPC c) (ret := returnPC c)
    ok (bank_inj hcap) hi (fetch_body hcap setup c)
    (fetch_return hcap setup c) (return_in_bounds hcap setup c) ha

theorem fetch_setup_at {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (setup : Setup bits) (c : Fin 3) (k : Fin 8) :
    (program hcap setup)[20 * c.val + k.val]? =
      some ((setup[c.val]'(c.isLt))[k.val]'(k.isLt)) := by
  have hc := c.isLt
  have hk := k.isLt
  have hp : 20 * c.val + k.val < 60 := by omega
  have hq : (20 * c.val + k.val) / 20 = c.val := by omega
  have hm : (20 * c.val + k.val) % 20 = k.val := by omega
  rw [fetch_program hcap setup (by omega : 20 * c.val + k.val < 61)]
  simp [cell, hp, hq, hm, hk]

end PaperB.RamProgram.ThreeCalls
