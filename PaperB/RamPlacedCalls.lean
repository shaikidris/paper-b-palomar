module

public import PaperB.RamSetupAgreement
public import PaperB.RamPairWorkerCalls

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine PaperB.WordOps PaperB.PairLookup
open PaperB.PairLookup.ColumnReduction
open PaperB.RamPairSliceBinding (toPredecessor)

/-- A placed scalar run returns the scalar lower in r0 and preserves every
register outside the worker's bank, relative to its agreement frame. -/
theorem placed_worker_saved_frame
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (ops : Setup bits)
    (site : Fin 3)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    {start : RamProgram.State (Predecessor.layout bits cap hcap)}
    {frame t : RamProgram.State (layout bits cap hcap)}
    {result : RamProgram.Result (Predecessor.layout bits cap hcap)}
    {fuel : Nat}
    (ok : run (Predecessor.worker hcap) i fuel start = some result)
    (hwords : i.words = j.words)
    (ha : ArenaAgreement (bank hcap) frame
      (relocateStatePC (entryPC site) start) t) :
    ∃ v, Steps (program hcap ops) j result.executed t v ∧
      v.pc = returnPC site ∧
      (setupReg v 0).val = Predecessor.lower result.finalState ∧
      ∀ q : Fin 16, 7 ≤ q.val → setupReg v q = setupReg frame q := by
  obtain ⟨v, hv, hag⟩ :=
    run_site (hcap := hcap) (setup := ops) site
      (i := i) (j := j) (s := start) (frame := frame) (t := t)
      (r := result) (fuel := fuel) ok hwords ha
  refine ⟨v, hv, hag.pc_eq.symm, ?_, ?_⟩
  · exact congrArg Fin.val (hag.reg_eq 0).symm
  · intro q hq
    apply hag.frame q
    intro r he
    have heval := congrArg Fin.val he
    change r.val = q.val at heval
    have hr : r.val < 7 := r.isLt
    omega

private theorem saved_ne_low {q r : Fin 16}
    (hq : 7 ≤ q.val) (hr : r.val < 7) : q ≠ r := by
  intro he
  have heval := congrArg Fin.val he
  omega

private theorem scalar_steps_append
    {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {code : Program (layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    {s t u : RamProgram.State (layout bits cap hcap)} {m n : Nat}
    (hst : Steps code j m s t) (htu : Steps code j n t u) :
    Steps code j (m + n) s u := by
  first
  | exact Steps.trans hst htu
  | exact Steps.append hst htu
  | induction hst <;>
      first
      | simpa only [Nat.zero_add] using htu
      | rw [Nat.succ_add]
        constructor <;> solve_by_elim
      | rw [Nat.add_assoc]
        constructor <;> solve_by_elim
  | induction htu <;>
      first
      | simpa only [Nat.add_zero] using hst
      | rw [Nat.add_succ]
        constructor <;> solve_by_elim
      | rw [← Nat.add_assoc]
        constructor <;> solve_by_elim
  | exact?

/- Infer the concrete setup from its checked PC20 trace, then check the PC40
   trace against that same setup. The code field is a definition, not a
   choice of an existential witness. -/
private structure CheckedScalarSetup
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits) where
  ops : Setup bits
  at20 : ∀ (j : RamProgram.Input (layout bits cap hcap))
    (s : RamProgram.State (layout bits cap hcap)), s.pc = 20 →
      Steps (program hcap ops) j 8 s (secondSetupState hone s)
  at40 : ∀ (j : RamProgram.Input (layout bits cap hcap))
    (s : RamProgram.State (layout bits cap hcap)), s.pc = 40 →
      Steps (program hcap ops) j 8 s (thirdSetupState hone s)

private def checkedScalarSetup
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits) :
    CheckedScalarSetup hcap hone :=
  ⟨concreteSetup bits hone, run_second_setup hcap hone, run_third_setup hcap hone⟩

def scalarCallSetup
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits) :
    Setup bits :=
  (checkedScalarSetup hcap hone).ops

/-- PC20 to PC40: the setup saves the incoming r0 in r13. The worker
preserves that saved value and all the other saved registers. -/
theorem second_scalar_placed
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    (p : Slice (bits := bits) i.words) (key : Word bits)
    (s : RamProgram.State (layout bits cap hcap))
    {r : RamProgram.Result (Predecessor.layout bits cap hcap)} {fuel : Nat}
    (hwords : i.words = j.words) (hpc : s.pc = 20)
    (hbase : setupReg s 7 = p.base)
    (hlen : (setupReg s 8).val = p.len)
    (hkey : setupReg s 11 = key)
    (ok : run (Predecessor.worker hcap) i fuel
      (Predecessor.init (toPredecessor (input := i) p) key) = some r) :
    ∃ u, Steps (program hcap (scalarCallSetup hcap hone)) j
        (8 + r.executed) s u ∧
      u.pc = 40 ∧
      (setupReg u 0).val = Predecessor.lower r.finalState ∧
      ∀ q : Fin 16, 7 ≤ q.val →
        setupReg u q = if q = 13 then setupReg s 0 else setupReg s q := by
  have hsetup : Steps (program hcap (scalarCallSetup hcap hone)) j
      8 s (secondSetupState hone s) :=
    (checkedScalarSetup hcap hone).at20 j s hpc
  have ha := secondSetupState_init_agreement hcap (i := i)
    p key hone s hbase hlen hkey
  obtain ⟨u, hw, hpcu, hout, hframe⟩ :=
    placed_worker_saved_frame hcap (scalarCallSetup hcap hone) 1
      (i := i) (j := j)
      (start := Predecessor.init (toPredecessor (input := i) p) key)
      (frame := secondSetupState hone s) (t := secondSetupState hone s)
      (result := r) (fuel := fuel) ok hwords ha
  refine ⟨u, scalar_steps_append hsetup hw, hpcu, hout, ?_⟩
  intro q hq
  simpa only [secondSetupState_regs,
    if_neg (saved_ne_low (r := 5) hq (by decide)),
    if_neg (saved_ne_low (r := 4) hq (by decide)),
    if_neg (saved_ne_low (r := 6) hq (by decide)),
    if_neg (saved_ne_low (r := 3) hq (by decide)),
    if_neg (saved_ne_low (r := 2) hq (by decide)),
    if_neg (saved_ne_low (r := 1) hq (by decide)),
    if_neg (saved_ne_low (r := 0) hq (by decide))] using hframe q hq

/-- PC40 to PC60: the setup saves the incoming r0 in r14. In particular,
r13 survives unchanged through both the setup and the worker. -/
theorem third_scalar_placed
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    (p : Slice (bits := bits) i.words) (key : Word bits)
    (s : RamProgram.State (layout bits cap hcap))
    {r : RamProgram.Result (Predecessor.layout bits cap hcap)} {fuel : Nat}
    (hwords : i.words = j.words) (hpc : s.pc = 40)
    (hbase : (setupReg s 9).val + (setupReg s 13).val = p.base.val)
    (horder : (setupReg s 13).val ≤ (setupReg s 0).val)
    (hlen : (setupReg s 0).val - (setupReg s 13).val = p.len)
    (hkey : setupReg s 12 = key)
    (ok : run (Predecessor.worker hcap) i fuel
      (Predecessor.init (toPredecessor (input := i) p) key) = some r) :
    ∃ v, Steps (program hcap (scalarCallSetup hcap hone)) j
        (8 + r.executed) s v ∧
      v.pc = 60 ∧
      (setupReg v 0).val = Predecessor.lower r.finalState ∧
      ∀ q : Fin 16, 7 ≤ q.val →
        setupReg v q = if q = 14 then setupReg s 0 else setupReg s q := by
  have hsetup : Steps (program hcap (scalarCallSetup hcap hone)) j
      8 s (thirdSetupState hone s) :=
    (checkedScalarSetup hcap hone).at40 j s hpc
  have ha := thirdSetupState_init_agreement hcap (i := i)
    p key hone s hbase horder hlen hkey
  obtain ⟨v, hw, hpcv, hout, hframe⟩ :=
    placed_worker_saved_frame hcap (scalarCallSetup hcap hone) 2
      (i := i) (j := j)
      (start := Predecessor.init (toPredecessor (input := i) p) key)
      (frame := thirdSetupState hone s) (t := thirdSetupState hone s)
      (result := r) (fuel := fuel) ok hwords ha
  refine ⟨v, scalar_steps_append hsetup hw, hpcv, hout, ?_⟩
  intro q hq
  simpa only [thirdSetupState_regs,
    if_neg (saved_ne_low (r := 5) hq (by decide)),
    if_neg (saved_ne_low (r := 4) hq (by decide)),
    if_neg (saved_ne_low (r := 6) hq (by decide)),
    if_neg (saved_ne_low (r := 0) hq (by decide)),
    if_neg (saved_ne_low (r := 3) hq (by decide)),
    if_neg (saved_ne_low (r := 1) hq (by decide)),
    if_neg (saved_ne_low (r := 2) hq (by decide))] using hframe q hq

/-- Link the actual first-column `x` run and the actual second-column
band run. The PC20 interface supplies the first call's lower cut and
the descriptors; neither setup requires a scratch-register hypothesis.

The band-base equation is over naturals, so it also supplies the
no-wrap condition for the address addition in the third setup. -/
theorem second_third_scalar_steps
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    {a : Array Key}
    (c : Columns (bits := bits) i.words a) (hs : StrictSorted a)
    (x y : Word bits) (hwords : i.words = j.words) :
    ∃ (lo hi k predSteps xSteps ySteps : Nat)
        (hlo : lo ≤ hi) (hhi : hi ≤ c.second.len),
      LowerCut c.first x lo ∧
      IsBand c.first x lo hi ∧
      finish c.first c.second x y lo k =
        (PairLookup.lookup a (x.val, y.val)).1 ∧
      predSteps + xSteps + ySteps ≤ 33 * (Nat.log2 (a.size + 1) + 1) ∧
      ∀ s : RamProgram.State (layout bits cap hcap),
        s.pc = 20 →
        (setupReg s 0).val = lo →
        setupReg s 7 = c.first.base →
        (setupReg s 8).val = c.first.len →
        setupReg s 11 = x →
        (setupReg s 9).val + lo = (c.second.sub lo hi hlo hhi).base.val →
        setupReg s 12 = y →
        ∃ u v,
          Steps (program hcap (scalarCallSetup hcap hone)) j
            (8 + xSteps) s u ∧
          u.pc = 40 ∧ (setupReg u 0).val = hi ∧
          (∀ q : Fin 16, 7 ≤ q.val →
            setupReg u q = if q = 13 then setupReg s 0 else setupReg s q) ∧
          Steps (program hcap (scalarCallSetup hcap hone)) j
            (8 + ySteps) u v ∧
          v.pc = 60 ∧ (setupReg v 0).val = k ∧
          (∀ q : Fin 16, 7 ≤ q.val →
            setupReg v q = if q = 14 then setupReg u 0 else setupReg u q) ∧
          Steps (program hcap (scalarCallSetup hcap hone)) j
            ((8 + xSteps) + (8 + ySteps)) s v := by
  obtain ⟨lo, hi, k, predSteps, xSteps, ySteps, hlo, hhi,
      hpred, hx, hband, hy, hfinish, hbudget⟩ :=
    PaperB.RamPairWorkerCalls.worker_calls_correct
      (bits := bits) (cap := cap) (hcap := hcap) (input := i) c hs x y
  have hcut : LowerCut c.first x lo := by
    unfold LowerCut
    by_cases hz : x.val = 0
    · simp only [if_pos hz] at hpred ⊢
      exact hpred.1
    · simp only [if_neg hz] at hpred ⊢
      exact hpred.1
  obtain ⟨_, _, rx, hrunx, hlowerx, _, hcountx⟩ := hx
  obtain ⟨_, _, ry, hruny, hlowery, _, hcounty⟩ := hy
  refine ⟨lo, hi, k, predSteps, xSteps, ySteps, hlo, hhi,
    hcut, hband, hfinish, hbudget, ?_⟩
  intro s hpcs hlo0 hfirstBase hfirstLen hxkey hbandBase hykey

  obtain ⟨u, hsu, hpcu, hu0, huframe⟩ :=
    second_scalar_placed hcap hone (i := i) (j := j)
      c.first x s (r := rx) hwords hpcs hfirstBase hfirstLen hxkey hrunx
  have huhi : (setupReg u 0).val = hi := hu0.trans hlowerx
  have hu13 : setupReg u 13 = setupReg s 0 := by
    simpa using huframe 13 (by decide)
  have hu9 : setupReg u 9 = setupReg s 9 := by
    simpa (disch := decide) only [if_neg] using huframe 9 (by decide)
  have hu12 : setupReg u 12 = y := by
    have h := huframe 12 (by decide)
    simp (disch := decide) only [if_neg] at h
    exact h.trans hykey

  have hbase : (setupReg u 9).val + (setupReg u 13).val =
      (c.second.sub lo hi hlo hhi).base.val := by
    simpa only [hu9, hu13, hlo0] using hbandBase
  have horder : (setupReg u 13).val ≤ (setupReg u 0).val := by
    simpa only [hu13, hlo0, huhi] using hlo
  have hsubLen : hi - lo = (c.second.sub lo hi hlo hhi).len := by
    first
    | rfl
    | simpa [ColumnReduction.Slice.sub]
  have hlen : (setupReg u 0).val - (setupReg u 13).val =
      (c.second.sub lo hi hlo hhi).len := by
    simpa only [huhi, hu13, hlo0] using hsubLen

  obtain ⟨v, huv, hpcv, hv0, hvframe⟩ :=
    third_scalar_placed hcap hone (i := i) (j := j)
      (c.second.sub lo hi hlo hhi) y u (r := ry)
      hwords hpcu hbase horder hlen hu12 hruny
  rw [hcountx] at hsu
  rw [hcounty] at huv
  exact ⟨u, v, hsu, hpcu, huhi, huframe, huv, hpcv,
    hv0.trans hlowery, hvframe, scalar_steps_append hsu huv⟩

end PaperB.RamProgram.ThreeCalls
