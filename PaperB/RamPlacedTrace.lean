module

public import PaperB.RamProgram
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram

variable {bits : Nat} {L A : Layout bits}

private theorem step_embedPlaced {ρ : ArenaMap L A}
    {code : Program L} {wide : Program A} {i : Input L} {j : Input A}
    {base t : State A} {s : State L}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hlen : code.size = wide.size) (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t)
    (hfetch : wide[s.pc]? = (code[s.pc]?).map (embedInstr ρ))
    (hns : ∀ op, code[s.pc]? = some op →
      ∀ a r : Fin L.registerCount, op ≠ Instr.storeData a r) :
    ArenaOutcome ρ base (step code i s) (step wide j t) := by
  have hm : wide[t.pc]? = (code[s.pc]?).map (embedInstr ρ) := by
    simpa only [← h.pc_eq] using hfetch
  cases hf : code[s.pc]? with
  | none =>
    have hg : wide[t.pc]? = none := by
      simpa only [hf, Option.map_none] using hm
    simp [step, hf, hg, ArenaOutcome]
  | some op =>
    have hg : wide[t.pc]? = some (embedInstr ρ op) := by
      simpa only [hf, Option.map_some] using hm
    exact step_embedInstr (i := i) (j := j) hinj hlen hi h hf hg (hns op hf)

/-- Lift the trace into already linked code, preserving the original arena frame. -/
theorem Steps.embedOnPlaced {ρ : ArenaMap L A}
    {code : Program L} {wide : Program A} {i : Input L} {j : Input A}
    {base : State A} {n : Nat} {s u : State L} {good : Nat → Prop}
    (trace : Steps code i n s u)
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hlen : code.size = wide.size) (hi : i.words = j.words)
    (hplaced : ∀ p, good p → wide[p]? = (code[p]?).map (embedInstr ρ))
    (hns : ∀ p, good p → ∀ op, code[p]? = some op →
      ∀ a r : Fin L.registerCount, op ≠ Instr.storeData a r) :
    (∀ {k : Nat} {x : State L}, Steps code i k s x → k < n → good x.pc) →
    ∀ {t : State A}, ArenaAgreement ρ base s t →
      ∃ v, Steps wide j n t v ∧ ArenaAgreement ρ base u v := by
  induction trace with
  | zero s =>
    intro _ t h
    exact ⟨t, Steps.zero t, h⟩
  | cons head tail ih =>
    intro hgood t h
    have hp := hgood (Steps.zero _) (by omega)
    have hout := step_embedPlaced (i := i) (j := j) hinj hlen hi h
      (hplaced _ hp) (hns _ hp)
    rw [head] at hout
    generalize hw : step wide j t = out at hout
    cases out with
    | none => cases hout
    | some tr =>
      cases tr with
      | halted _ => cases hout
      | next w =>
        obtain ⟨v, hv, hb⟩ := ih (by
          intro k x pre hk
          exact hgood (Steps.cons head pre) (by omega)) hout
        exact ⟨v, Steps.cons hw hv, hb⟩

/-- PC 0 is padding; the read-only scalar worker occupies PCs 1 and 2. -/
def readonlyScalarModel (d r : Fin L.registerCount) : Program L :=
  #[.halt, .shr1 d r, .halt]

theorem readonlyScalarModel_embedOnPlaced {ρ : ArenaMap L A}
    {wide : Program A} {i : Input L} {j : Input A} {base t : State A}
    {s u f : State L} {d r : Fin L.registerCount}
    (trace : Steps (readonlyScalarModel (L := L) d r) i 1 s u)
    (hs : s.pc = 1) (hu : u.pc = 2)
    (hh : step (readonlyScalarModel (L := L) d r) i u = some (.halted f))
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hlen : (readonlyScalarModel (L := L) d r).size = wide.size)
    (hi : i.words = j.words)
    (hbody : wide[1]? = some (.shr1 (ρ d) (ρ r)))
    (hhalt : wide[2]? = some .halt) (h : ArenaAgreement ρ base s t) :
    ∃ v w, Steps wide j 1 t v ∧ step wide j v = some (.halted w) ∧
      ArenaAgreement ρ base f w := by
  have hf1 : (readonlyScalarModel (L := L) d r)[1]? = some (.shr1 d r) := rfl
  obtain ⟨v, hv, ha⟩ := trace.embedOnPlaced (j := j) (good := fun p => p = 1)
      hinj hlen hi (by
        intro p hp
        subst p
        simpa only [hf1, Option.map_some, embedInstr] using hbody) (by
        intro p hp op hf a b hbad
        subst p
        rw [hf1, hbad] at hf
        cases hf) (by
        intro k x pre hk
        have hk0 : k = 0 := by omega
        subst k
        cases pre
        exact hs) h
  have hf2 : (readonlyScalarModel (L := L) d r)[2]? = some .halt := rfl
  have hf : (readonlyScalarModel (L := L) d r)[u.pc]? = some .halt := by
    simpa only [hu] using hf2
  have hg : wide[v.pc]? = some (embedInstr ρ Instr.halt) := by
    simpa only [← ha.pc_eq, hu, embedInstr] using hhalt
  have hout := step_embedInstr (i := i) (j := j) hinj hlen hi ha hf hg (by
    intro a b he
    cases he)
  rw [hh] at hout
  refine ⟨v, ?_⟩
  generalize step wide j v = out at hout ⊢
  cases out with
  | none => cases hout
  | some tr =>
    cases tr with
    | next _ => cases hout
    | halted w => exact ⟨w, hv, rfl, hout⟩

end PaperB.RamProgram
