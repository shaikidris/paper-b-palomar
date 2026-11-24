module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram

variable {bits : Nat} {L A : Layout bits}

/-- Embed register operands without changing instruction positions or jump targets. -/
def embedProgram (ρ : ArenaMap L A) (code : Program L) : Program A :=
  code.map (embedInstr ρ)

theorem size_embedProgram (ρ : ArenaMap L A) (code : Program L) :
    (embedProgram ρ code).size = code.size := by
  simp only [embedProgram, Array.size_map]

theorem getElem?_embedProgram (ρ : ArenaMap L A) (code : Program L) (p : Nat) :
    (embedProgram ρ code)[p]? = (code[p]?).map (embedInstr ρ) := by
  simp only [embedProgram, Array.getElem?_map]

/-- Every instruction in the source program is a non-store instruction. -/
def embedProgram.NoStores (code : Program L) : Prop :=
  ∀ (p : Nat) (op : Instr bits L.registerCount), code[p]? = some op →
    ∀ a r : Fin L.registerCount, op ≠ Instr.storeData a r

theorem step_embedProgramWithStore {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base t : State A} {s : State L}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t) :
    ArenaOutcome ρ base (step code i s) (step (embedProgram ρ code) j t) := by
  have hfetch :
      (embedProgram ρ code)[t.pc]? = (code[s.pc]?).map (embedInstr ρ) := by
    rw [getElem?_embedProgram, h.pc_eq]
  cases hf : code[s.pc]? with
  | none =>
    have hg : (embedProgram ρ code)[t.pc]? = none := by
      simpa only [hf, Option.map_none] using hfetch
    simp [step, hf, hg, ArenaOutcome]
  | some op =>
    have hg : (embedProgram ρ code)[t.pc]? = some (embedInstr ρ op) := by
      simpa only [hf, Option.map_some] using hfetch
    exact step_embedInstrWithStore hinj (size_embedProgram ρ code).symm hi h hf hg

private theorem step_embedProgramWithStore_next {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base t : State A} {s u : State L}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t) (hs : step code i s = some (.next u)) :
    ∃ v, step (embedProgram ρ code) j t = some (.next v) ∧
      ArenaAgreement ρ base u v := by
  have hout := step_embedProgramWithStore (code := code) (i := i) (j := j) hinj hi h
  rw [hs] at hout
  generalize step (embedProgram ρ code) j t = out at hout ⊢
  cases out with
  | none => cases hout
  | some tr =>
    cases tr with
    | next v => exact ⟨v, rfl, hout⟩
    | halted _ => cases hout

/-- Preserve the exact step count, final PC, and frame relative to the original base. -/
theorem Steps.embedRegisterFramesWithStore {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base : State A} {n : Nat} {s u : State L}
    (trace : Steps code i n s u)
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words) :
    ∀ {t : State A}, ArenaAgreement ρ base s t →
      ∃ v, Steps (embedProgram ρ code) j n t v ∧ ArenaAgreement ρ base u v := by
  induction trace with
  | zero s =>
    intro t h
    exact ⟨t, Steps.zero t, h⟩
  | cons head tail ih =>
    intro t h
    obtain ⟨w, hw, ha⟩ := step_embedProgramWithStore_next hinj hi h head
    obtain ⟨v, hv, hb⟩ := ih ha
    exact ⟨v, Steps.cons hw hv, hb⟩

/-- A successful halt after the trace is preserved as one further instruction. -/
theorem Steps.embedRegisterFramesWithStore_thenHalt {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base t : State A} {n : Nat} {s u f : State L}
    (trace : Steps code i n s u) (hh : step code i u = some (.halted f))
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t) :
    ∃ v w, Steps (embedProgram ρ code) j n t v ∧
      step (embedProgram ρ code) j v = some (.halted w) ∧
      ArenaAgreement ρ base f w := by
  obtain ⟨v, hv, ha⟩ := trace.embedRegisterFramesWithStore hinj hi h
  have hout := step_embedProgramWithStore (code := code) (i := i) (j := j) hinj hi ha
  rw [hh] at hout
  refine ⟨v, ?_⟩
  generalize step (embedProgram ρ code) j v = out at hout ⊢
  cases out with
  | none => cases hout
  | some tr =>
    cases tr with
    | next _ => cases hout
    | halted w => exact ⟨w, hv, rfl, hout⟩

theorem step_embedProgram {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base t : State A} {s : State L}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words) (_hns : embedProgram.NoStores code)
    (h : ArenaAgreement ρ base s t) :
    ArenaOutcome ρ base (step code i s) (step (embedProgram ρ code) j t) :=
  step_embedProgramWithStore hinj hi h

theorem Steps.embedRegisterFrames {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base : State A} {n : Nat} {s u : State L}
    (trace : Steps code i n s u)
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words) (_hns : embedProgram.NoStores code) :
    ∀ {t : State A}, ArenaAgreement ρ base s t →
      ∃ v, Steps (embedProgram ρ code) j n t v ∧ ArenaAgreement ρ base u v :=
  trace.embedRegisterFramesWithStore hinj hi

theorem Steps.embedRegisterFrames_thenHalt {ρ : ArenaMap L A} {code : Program L}
    {i : Input L} {j : Input A} {base t : State A} {n : Nat} {s u f : State L}
    (trace : Steps code i n s u) (hh : step code i u = some (.halted f))
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hi : i.words = j.words) (_hns : embedProgram.NoStores code)
    (h : ArenaAgreement ρ base s t) :
    ∃ v w, Steps (embedProgram ρ code) j n t v ∧
      step (embedProgram ρ code) j v = some (.halted w) ∧
      ArenaAgreement ρ base f w :=
  trace.embedRegisterFramesWithStore_thenHalt hh hinj hi h

end PaperB.RamProgram
