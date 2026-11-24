module

public import PaperB.RamExitSummaryWordCodec
public import PaperB.RamExitSummarySetup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! Clear the fixed six-word value records used by the exit-summary sweep. -/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB PaperB.RamProgram PaperB.RamForestProgram
open PaperB.ExitMap PaperB.BuiltExit

variable {bits : Nat}

def clearWordsInstrs (tmp : Fin 15) (off : Nat) :
    (count : Nat) → off + count ≤ 2 ^ bits → List (Instr bits 15)
  | 0, _ => []
  | k + 1, h =>
    metaStoreInstrs reg0 tmp off (by omega) ++
    clearWordsInstrs tmp (off + 1) k (by omega)

variable {inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem clearWords_run {code : Program DomL} {input : Input DomL}
    {tmp : Fin 15} (hMetaTmp : tmp ≠ rMeta) (hZeroTmp : tmp ≠ reg0) :
    ∀ (count entry off metaBase : Nat) (hBound : metaBase + off + count ≤ workCap),
      Placed code entry (clearWordsInstrs tmp off count (by omega)) →
      entry + 3 * count < code.size →
      ∀ (st : State DomL), st.pc = entry →
      (reg st rMeta).val = metaBase → (reg st reg0).val = 0 →
      ∃ t, Steps code input (3 * count) st t ∧ t.pc = entry + 3 * count ∧
        (∀ i < count, (t.data[metaBase + off + i]?).map Fin.val = some 0) ∧
        (∀ j, (j < metaBase + off ∨ metaBase + off + count ≤ j) →
          t.data[j]? = st.data[j]?) ∧
        (∀ r, r ≠ tmp → reg t r = reg st r) := by
  intro count
  induction count with
  | zero =>
    intro entry off metaBase hBound hPl hSz st hpc hMeta hZero
    exact ⟨st, Steps.zero st, by omega, fun i hi => by omega, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ count ih =>
    intro entry off metaBase hBound hPl hSz st hpc hMeta hZero
    have hHead : Placed code entry (metaStoreInstrs reg0 tmp off (by omega)) :=
      Placed_append_left hPl
    obtain ⟨mid, hRun, hPc, hAt, hFrame, hRegs⟩ := run_metaStore_slice (input := input)
      hMetaTmp hZeroTmp hHead (by omega) hpc hMeta (by omega) (lt_data_size (by omega))
    have hRest : Placed code (entry + 3)
        (clearWordsInstrs tmp (off + 1) count (by omega)) := Placed_append_right hPl
    obtain ⟨t, hRunT, hPcT, hAtT, hFrameT, hRegsT⟩ := ih (entry + 3) (off + 1)
      metaBase (by omega) hRest (by omega) mid hPc
      (by rw [hRegs rMeta hMetaTmp.symm, hMeta]) (by rw [hRegs reg0 hZeroTmp.symm, hZero])
    have hCount : 3 * count.succ = 3 + 3 * count := by omega
    refine ⟨t, ?_, by omega, ?_, ?_, ?_⟩
    · rw [hCount]
      exact hRun.append hRunT
    · intro i hI
      cases i with
      | zero =>
        rw [Nat.add_zero, hFrameT _ (Or.inl (by omega)), hAt, Option.map_some, hZero]
      | succ i =>
        have hIndex : metaBase + off + i.succ = metaBase + (off + 1) + i := by omega
        rw [hIndex]
        exact hAtT i (by omega)
    · intro j hj
      rw [hFrameT j (by omega), hFrame j (by omega)]
    · intro r hr
      rw [hRegsT r hr, hRegs r hr]

theorem clearValues_run {code : Program DomL} {input : Input DomL}
    {tmp : Fin 15} (hMetaTmp : tmp ≠ rMeta) (hZeroTmp : tmp ≠ reg0)
    (entry off metaBase : Nat) (hBound : metaBase + off + 6 ≤ workCap)
    (hPl : Placed code entry (clearWordsInstrs tmp off 6 (by omega)))
    (hSz : entry + 18 < code.size)
    (st : State DomL) (hpc : st.pc = entry)
    (hMeta : (reg st rMeta).val = metaBase) (hZero : (reg st reg0).val = 0) :
    ∃ t, Steps code input 18 st t ∧ t.pc = entry + 18 ∧
      ValuesWordsAt t.data (metaBase + off) zero ∧
      (∀ j, (j < metaBase + off ∨ metaBase + off + 6 ≤ j) →
        t.data[j]? = st.data[j]?) ∧
      (∀ r, r ≠ tmp → reg t r = reg st r) := by
  obtain ⟨t, hTrace, hPc, hAt, hFrame, hRegs⟩ :=
    clearWords_run (input := input) hMetaTmp hZeroTmp 6 entry off metaBase hBound hPl hSz st hpc hMeta hZero
  have h0 := hAt 0 (by decide)
  rw [Nat.add_zero] at h0
  exact ⟨t, hTrace, hPc, ⟨⟨h0, hAt 1 (by decide), hAt 2 (by decide)⟩,
    ⟨hAt 3 (by decide), hAt 4 (by decide), hAt 5 (by decide)⟩⟩, hFrame, hRegs⟩

end PaperB.RamProgram.ExitSummaryBuild
