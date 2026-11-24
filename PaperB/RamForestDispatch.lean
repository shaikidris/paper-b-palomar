module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamForestDispatch

open PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.WordOps (sub sub_val ltb ltb_eq_true)

variable {bits : Nat} {L : Layout bits}

def exitCode (cmd count base clk tmp : Fin L.registerCount) :
    List (Instr bits L.registerCount) := by
  first
  | exact [.sub cmd cmd count] ++ indexedDataWrite (L := L) tmp base cmd clk
  | exact [.sub cmd cmd count] ++ indexedDataWrite tmp base cmd clk

theorem exit_steps
    {code : Program L} {input : Input L} {s : State L}
    {entry node : Nat} {cmd count base clk tmp : Fin L.registerCount}
    (hpc : s.pc = entry)
    (placed : Placed code entry (exitCode (L := L) cmd count base clk tmp))
    (hexit : entry + 3 < code.size)
    (hcount : (reg s cmd).val = (reg s count).val + node)
    (hbound : (reg s base).val + node < L.workCap)
    (hbaseCmd : base ≠ cmd) (hclkCmd : clk ≠ cmd)
    (hclkTmp : clk ≠ tmp) (hcmdTmp : cmd ≠ tmp) :
    ∃ t : State L,
      Steps code input 3 s t ∧
      t.pc = entry + 3 ∧
      (reg t cmd).val = node ∧
      t.data = s.data.set ((reg s base).val + node) (reg s clk)
        (by rw [s.data_size]; exact hbound) ∧
      (∀ r : Fin L.registerCount, r ≠ cmd → r ≠ tmp → reg t r = reg s r) := by
  have hf : code[s.pc]? = some (.sub cmd cmd count) := by
    rw [hpc]
    simpa only [Nat.add_zero] using placed 0 (.sub cmd cmd count) (by rfl)

  have htail :
      Placed code (entry + 1)
        ([.add tmp base cmd, .storeData tmp clk] : List (Instr bits L.registerCount)) := by
    intro i op hi
    have hi' : (exitCode (L := L) cmd count base clk tmp)[i + 1]? = some op := by
      change ([.add tmp base cmd, .storeData tmp clk] :
        List (Instr bits L.registerCount))[i]? = some op
      exact hi
    have hfetch := placed (i + 1) op hi'
    have hoffset : entry + (i + 1) = (entry + 1) + i := by omega
    rw [hoffset] at hfetch
    exact hfetch

  have hcmdLt : (reg s cmd).val < 2 ^ bits := (reg s cmd).isLt
  have hnode : node < 2 ^ bits := by omega
  have hdiff : 2 ^ bits + (reg s cmd).val - (reg s count).val =
      2 ^ bits + node := by omega
  have hsub : (sub (reg s cmd) (reg s count)).val = node := by
    simp only [sub_val (reg s cmd) (reg s count), hdiff,
      Nat.add_mod (2 ^ bits) node (2 ^ bits), Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hnode]

  have hnext : s.pc + 1 < code.size := by
    rw [hpc]
    omega
  obtain ⟨u, huStep, huPC₀, huCmdWord, huRegs, huData⟩ :=
    step_sub_at (input := input) (s := s) hf hnext

  have huPC : u.pc = entry + 1 :=
    huPC₀.trans (congrArg (fun p : Nat => p + 1) hpc)
  have huCmd : (reg u cmd).val = node :=
    (congrArg (fun w : Word bits => w.val) huCmdWord).trans hsub
  have huBase : reg u base = reg s base := huRegs base hbaseCmd
  have huClk : reg u clk = reg s clk := huRegs clk hclkCmd
  have haddr : (reg u base).val + (reg u cmd).val =
      (reg s base).val + node := by
    rw [huBase, huCmd]
  have huBound : (reg u base).val + (reg u cmd).val < L.workCap := by
    rw [haddr]
    exact hbound
  have htailExit : (entry + 1) + 2 < code.size := by omega

  obtain ⟨t, htSteps, htPC, htData, _htTmp, htRegs⟩ :=
    indexedDataWrite_steps (input := input) (s := u)
      (tmp := tmp) (base := base) (index := cmd) (src := clk)
      htail huPC htailExit hclkTmp huBound

  -- Transport the write across equality of the array, address, and value.
  have hset :
      ∀ {a b : Array (Word bits)} {i j : Nat} {v w : Word bits},
        a = b → i = j → v = w →
        ∀ (hi : i < a.size) (hj : j < b.size), a.set i v hi = b.set j w hj := by
    intro a b i j v w ha hi hv hia hjb
    cases ha
    cases hi
    cases hv
    rfl

  have htDataExact :
      t.data = s.data.set ((reg s base).val + node) (reg s clk)
        (by rw [s.data_size]; exact hbound) :=
    htData.trans (hset huData haddr huClk
      (by rw [u.data_size]; exact huBound)
      (by rw [s.data_size]; exact hbound))
  have htCmd : (reg t cmd).val = node :=
    (congrArg (fun w : Word bits => w.val) (htRegs cmd hcmdTmp)).trans huCmd
  have htRegsExact :
      ∀ r : Fin L.registerCount, r ≠ cmd → r ≠ tmp → reg t r = reg s r := by
    intro r hrCmd hrTmp
    exact (htRegs r hrTmp).trans (huRegs r hrCmd)
  have htPCExact : t.pc = entry + 3 := htPC
  exact ⟨t, Steps.cons huStep htSteps, htPCExact, htCmd, htDataExact, htRegsExact⟩

def dispatchCode (cmd count : Fin L.registerCount) (enterPC exitPC : Nat) :
    List (Instr bits L.registerCount) :=
  [.branchLt cmd count enterPC exitPC]

theorem dispatch_steps
    {code : Program L} {input : Input L} {s : State L}
    {entry enterPC exitPC : Nat} {cmd count : Fin L.registerCount}
    (placed : Placed code entry (dispatchCode (L := L) cmd count enterPC exitPC))
    (hpc : s.pc = entry)
    (henter : enterPC < code.size) (hexit : exitPC < code.size) :
    ∃ t : State L,
      Steps code input 1 s t ∧
      (∀ r : Fin L.registerCount, reg t r = reg s r) ∧
      t.data = s.data ∧
      t.pc = (if (reg s cmd).val < (reg s count).val then enterPC else exitPC) := by
  have hf : code[s.pc]? = some (.branchLt cmd count enterPC exitPC) := by
    rw [hpc]
    simpa only [Nat.add_zero] using
      placed 0 (.branchLt cmd count enterPC exitPC) (by rfl)
  have htarget :
      (if ltb (reg s cmd) (reg s count) then enterPC else exitPC) < code.size := by
    split
    · exact henter
    · exact hexit

  have hstep := step_branchLt_at (input := input) (s := s) hf htarget
  let t : State L :=
    { s with pc := if ltb (reg s cmd) (reg s count) then enterPC else exitPC }
  have hsteps : Steps code input 1 s t := Steps.cons hstep (Steps.zero t)
  have hregs : ∀ r : Fin L.registerCount, reg t r = reg s r := by
    intro r
    rfl
  have htPC :
      t.pc = (if (reg s cmd).val < (reg s count).val then enterPC else exitPC) := by
    change (if ltb (reg s cmd) (reg s count) then enterPC else exitPC) =
      (if (reg s cmd).val < (reg s count).val then enterPC else exitPC)
    by_cases hlt : (reg s cmd).val < (reg s count).val
    · have hb : ltb (reg s cmd) (reg s count) = true :=
        (ltb_eq_true (reg s cmd) (reg s count)).2 hlt
      rw [ite_eq_left hb, ite_eq_left hlt]
    · have hb : ltb (reg s cmd) (reg s count) ≠ true := by
        intro hbTrue
        exact hlt ((ltb_eq_true (reg s cmd) (reg s count)).1 hbTrue)
      rw [ite_eq_right hb, ite_eq_right hlt]
  exact ⟨t, hsteps, hregs, rfl, htPC⟩

theorem dispatch_compose
    {code : Program L} {input : Input L} {s : State L}
    {entry enterPC exitPC k₁ k₂ : Nat} {cmd count : Fin L.registerCount}
    {P₁ Q₁ P₂ Q₂ : State L → Prop}
    (placed : Placed code entry (dispatchCode (L := L) cmd count enterPC exitPC))
    (hpc : s.pc = entry)
    (henter : enterPC < code.size) (hexit : exitPC < code.size)
    (enterSpec : BlockSpec code input k₁ P₁ Q₁)
    (exitSpec : BlockSpec code input k₂ P₂ Q₂)
    (enterPre : (reg s cmd).val < (reg s count).val →
      ∀ u : State L, u.pc = enterPC →
        (∀ r : Fin L.registerCount, reg u r = reg s r) →
        u.data = s.data → P₁ u)
    (exitPre : ¬ ((reg s cmd).val < (reg s count).val) →
      ∀ u : State L, u.pc = exitPC →
        (∀ r : Fin L.registerCount, reg u r = reg s r) →
        u.data = s.data → P₂ u) :
    ∃ t : State L,
      Steps code input
        (1 + (if (reg s cmd).val < (reg s count).val then k₁ else k₂)) s t ∧
      (if (reg s cmd).val < (reg s count).val then Q₁ t else Q₂ t) := by
  obtain ⟨u, huSteps, huRegs, huData, huPC⟩ :=
    dispatch_steps (input := input) placed hpc henter hexit
  by_cases hlt : (reg s cmd).val < (reg s count).val
  · have huEnter : u.pc = enterPC := huPC.trans (ite_eq_left hlt)
    obtain ⟨t, htSteps, htPost⟩ :=
      enterSpec u (enterPre hlt u huEnter huRegs huData)
    simp only [ite_eq_left hlt]
    exact ⟨t, Steps.append huSteps htSteps, htPost⟩
  · have huExit : u.pc = exitPC := huPC.trans (ite_eq_right hlt)
    obtain ⟨t, htSteps, htPost⟩ :=
      exitSpec u (exitPre hlt u huExit huRegs huData)
    simp only [ite_eq_right hlt]
    exact ⟨t, Steps.append huSteps htSteps, htPost⟩

end PaperB.RamForestDispatch
