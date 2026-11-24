module

public import PaperB.RamWorkerReturn
public import PaperB.RamPlacedTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram

private theorem returnFetchLt {bits : Nat} {L : Layout bits}
    {p : Program L} {k : Nat} {op : Instr bits L.registerCount}
    (h : p[k]? = some op) : k < p.size := by
  by_cases hk : k < p.size
  · exact hk
  · simp [getElem?_neg, hk] at h

private theorem returnStepsUnique {bits : Nat} {L : Layout bits}
    {p : Program L} {i : Input L} {n : Nat} {s u : State L}
    (h : Steps p i n s u) : ∀ {v}, Steps p i n s v → u = v := by
  induction h with
  | zero a =>
    intro v hv
    cases hv
    rfl
  | cons head tail ih =>
    intro v hv
    cases hv with
    | cons head' tail' =>
      have hh := Option.some.inj (head.symm.trans head')
      injection hh with he
      cases he
      exact ih tail'

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {i : Input (Predecessor.layout bits cap hcap)}
variable {s u : State (Predecessor.layout bits cap hcap)}

private theorem workerNextPC
    (h : step (Predecessor.worker hcap) i s = some (.next u)) : s.pc < 12 := by
  by_cases hb : s.pc < 12
  · exact hb
  · have hn : ¬ s.pc < (Predecessor.worker hcap).size := by
      simpa only [Predecessor.worker_size (hcap := hcap)] using hb
    have hf := getElem?_neg (Predecessor.worker hcap) s.pc hn
    simp [step, hf, Option.bind_eq_bind, Option.bind] at h

private theorem workerBoundedPrefix {n : Nat}
    (tr : Steps (Predecessor.worker hcap) i n s u) :
    u.pc < 12 → ∀ {k : Nat}, k ≤ n →
      ∃ x, Steps (Predecessor.worker hcap) i k s x ∧ x.pc < 12 := by
  induction tr with
  | zero a =>
    intro hb k hk
    have hz : k = 0 := by omega
    subst k
    exact ⟨a, Steps.zero a, hb⟩
  | cons head tail ih =>
    intro hb k hk
    cases k with
    | zero => exact ⟨_, Steps.zero _, workerNextPC head⟩
    | succ k =>
      obtain ⟨x, hx, hp⟩ := ih hb (k := k) (by omega)
      exact ⟨x, Steps.cons head hx, hp⟩

private def returnIsStore {bits : Nat} : Option (Instr bits 7) → Bool
  | some (.storeData _ _) => true
  | _ => false

private theorem workerRelocatedNoStore (off k : Nat) (hk : k < 11) :
    returnIsStore (((Predecessor.worker hcap)[k]?).map (relocateInstr off)) = false := by
  have hs : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Execute the placed worker through its return jump, preserving the arena frame. -/
theorem worker_return_embedOnPlaced {A : Layout bits}
    {ρ : ArenaMap (Predecessor.layout bits cap hcap) A}
    {wide : Program A} {j : Input A} {frame t : State A}
    {r : Result (Predecessor.layout bits cap hcap)} {fuel off ret : Nat}
    (ok : run (Predecessor.worker hcap) i fuel s = some r)
    (hinj : ∀ {a b}, ρ a = ρ b → a = b) (hi : i.words = j.words)
    (hbody : ∀ k op, k < 11 → (Predecessor.worker hcap)[k]? = some op →
      wide[off + k]? = some (embedInstr ρ (relocateInstr off op)))
    (hret : wide[off + 11]? = some (.goto ret)) (target : ret < wide.size)
    (ha : ArenaAgreement ρ frame (relocateStatePC off s) t) :
    ∃ v, Steps wide j r.executed t v ∧
      ArenaAgreement ρ frame { r.finalState with pc := ret } v := by
  obtain ⟨n, prehalt, trace, halt, count⟩ := run_has_steps_then_halt ok
  obtain ⟨hpc, _⟩ := worker_halt_pc halt
  have hs := returnFetchLt hret
  let shadow (last : Instr bits 7) : Program (Predecessor.layout bits cap hcap) :=
    Array.ofFn fun p : Fin wide.size =>
      if p.val = off + 11 then last
      else if off ≤ p.val then
        (((Predecessor.worker hcap)[p.val - off]?).map (relocateInstr off)).getD .halt
      else .halt
  have hlen (last : Instr bits 7) : (shadow last).size = wide.size := by simp [shadow]
  have fetch (last : Instr bits 7) (p : Nat) (hp : p < wide.size) :
      (shadow last)[p]? = some (if p = off + 11 then last else if off ≤ p then
        (((Predecessor.worker hcap)[p - off]?).map (relocateInstr off)).getD .halt
        else .halt) := by
    rw [getElem?_pos (shadow last) p (by simpa only [hlen] using hp)]
    simp [shadow]
  have slot (last : Instr bits 7) : (shadow last)[off + 11]? = some last := by
    rw [fetch last _ hs, if_pos rfl]
  have body (last : Instr bits 7) (k : Nat) (op : Instr bits 7) (hk : k < 11)
      (hf : (Predecessor.worker hcap)[k]? = some op) :
      (shadow last)[off + k]? = some (relocateInstr off op) := by
    rw [fetch last _ (by omega)]
    simp [Nat.ne_of_lt hk, show off ≤ off + k by omega,
      show off + k - off = k by omega, hf, Option.getD]
  have placed : RelocatedSlice (Predecessor.worker hcap) (shadow .halt) off := by
    intro k op hf
    by_cases he : k = 11
    · subst k
      have hh : (Predecessor.worker hcap)[11]? = some Instr.halt := rfl
      have he := Option.some.inj (hh.symm.trans hf)
      subst op
      exact slot .halt
    · have hb := returnFetchLt hf
      rw [Predecessor.worker_size (hcap := hcap)] at hb
      exact body .halt k op (by omega) hf
  have other (p : Nat) (hne : p ≠ off + 11) :
      (shadow (.goto ret))[p]? = (shadow .halt)[p]? := by
    by_cases hp : p < wide.size
    · simp only [fetch (.goto ret) p hp, fetch .halt p hp, if_neg hne]
    · rw [getElem?_neg (shadow (.goto ret)) p (by simpa only [hlen] using hp),
          getElem?_neg (shadow .halt) p (by simpa only [hlen] using hp)]
  have transfer {k : Nat} {a b : State (Predecessor.layout bits cap hcap)}
      (tr : Steps (shadow .halt) i k a b) : Steps (shadow (.goto ret)) i k a b := by
    induction tr with
    | zero a => exact Steps.zero a
    | cons head tail ih =>
      exact Steps.cons (step_next_of_halt_slot_patch (slot .halt)
        ((hlen .halt).trans (hlen (.goto ret)).symm) other head) ih
  obtain ⟨returned, _⟩ := worker_return_of_trace (linked := shadow (.goto ret))
    (base := off) (body (.goto ret)) (slot (.goto ret))
    (by simpa only [hlen] using target) trace halt
  have runtime {k : Nat} {x : State (Predecessor.layout bits cap hcap)}
      (pre : Steps (shadow (.goto ret)) i k (relocateStatePC off s) x) (hk : k < n + 1) :
      off ≤ x.pc ∧ x.pc < off + 12 := by
    obtain ⟨y, hy, hb⟩ := workerBoundedPrefix trace (by rw [hpc]; decide)
      (k := k) (by omega)
    rw [returnStepsUnique pre (transfer (hy.relocate placed))]
    change off ≤ off + y.pc ∧ off + y.pc < off + 12
    omega
  have matchSlot (p : Nat) (hp : off ≤ p ∧ p < off + 12) :
      ∃ op : Instr bits 7, (shadow (.goto ret))[p]? = some op ∧
        wide[p]? = some (embedInstr ρ op) ∧ returnIsStore (some op) = false := by
    obtain ⟨k, rfl⟩ : ∃ k : Nat, p = off + k := ⟨p - off, by omega⟩
    by_cases he : k = 11
    · subst k
      exact ⟨.goto ret, slot _, by simpa only [embedInstr] using hret, rfl⟩
    · have hk : k < 11 := by omega
      have hb : k < (Predecessor.worker hcap).size := by
        rw [Predecessor.worker_size (hcap := hcap)]; omega
      have hf := getElem?_pos (Predecessor.worker hcap) k hb
      exact ⟨_, body _ _ _ hk hf, hbody _ _ hk hf,
        by simpa only [hf, Option.map_some] using workerRelocatedNoStore (hcap := hcap) off k hk⟩
  rw [count]
  refine returned.embedOnPlaced (j := j) (good := fun p => off ≤ p ∧ p < off + 12)
    hinj (hlen _) hi ?_ ?_ runtime ha
  · intro p hp
    obtain ⟨op, hf, hw, _⟩ := matchSlot p hp
    simpa only [hf, Option.map_some] using hw
  · intro p hp op hf a b he
    obtain ⟨x, hx, _, hn⟩ := matchSlot p hp
    rw [Option.some.inj (hx.symm.trans hf), he] at hn
    cases hn

end PaperB.RamProgram
