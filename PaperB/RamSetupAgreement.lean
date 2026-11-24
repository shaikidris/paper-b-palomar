module

public import PaperB.RamConcreteSetup
public import PaperB.RamPairSliceBinding

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine PaperB.WordOps PaperB.PairLookup
open PaperB.RamPairSliceBinding (toPredecessor)

theorem predecessor_init_agreement
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    (p : ColumnReduction.Slice (bits := bits) i.words)
    (key : Word bits) (hone : 1 < 2 ^ bits) (c)
    (t : RamProgram.State (layout bits cap hcap))
    (hpc : t.pc = entryPC c)
    (h0 : setupReg t 0 = zero bits)
    (h1 : (setupReg t 1).val = p.len)
    (h2 : setupReg t 2 = p.base)
    (h3 : setupReg t 3 = key)
    (h4 : setupReg t 4 = zero bits)
    (h5 : setupReg t 5 = zero bits)
    (h6 : setupReg t 6 = setupOne bits hone) :
    ArenaAgreement (bank hcap) t
      (relocateStatePC (entryPC c)
        (Predecessor.init (toPredecessor (input := i) p) key)) t := by
  let u : RamProgram.State (Predecessor.layout bits cap hcap) :=
    relocateStatePC (entryPC c)
      (Predecessor.init (toPredecessor (input := i) p) key)
  change ArenaAgreement (bank hcap) t u t
  have hz : (zero bits).val = 0 := by
    simp [zero]
  have hr0 : reg u 0 = reg t (bank hcap 0) := by
    apply Fin.ext
    change 0 = (setupReg t 0).val
    simpa only [h0] using hz.symm
  have hr1 : reg u 1 = reg t (bank hcap 1) := by
    apply Fin.ext
    change p.len = (setupReg t 1).val
    exact h1.symm
  have hr2 : reg u 2 = reg t (bank hcap 2) := by
    change p.base = setupReg t 2
    exact h2.symm
  have hr3 : reg u 3 = reg t (bank hcap 3) := by
    change key = setupReg t 3
    exact h3.symm
  have hr4 : reg u 4 = reg t (bank hcap 4) := by
    apply Fin.ext
    change 0 = (setupReg t 4).val
    simpa only [h4] using hz.symm
  have hr5 : reg u 5 = reg t (bank hcap 5) := by
    apply Fin.ext
    change 0 = (setupReg t 5).val
    simpa only [h5] using hz.symm
  have hr6 : reg u 6 = reg t (bank hcap 6) := by
    apply Fin.ext
    change
      (if h : 1 < 2 ^ bits then (⟨1, h⟩ : Word bits)
       else ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) p.base.isLt⟩).val =
        (setupReg t 6).val
    simp only [dif_pos hone, h6, setupOne]
  have htdata : t.data.size = 0 := t.data_size
  refine ⟨?_, ?_, ?_, ?_⟩
  · change entryPC c + 0 = t.pc
    simpa only [Nat.add_zero] using hpc.symm
  · change (#[] : Array (Word bits)) = t.data
    apply Array.ext
    · exact htdata.symm
    · intro j hj _
      change j < 0 at hj
      exact (Nat.not_lt_zero j hj).elim
  · intro r
    exact
      match r with
      | ⟨0, _⟩ => hr0
      | ⟨1, _⟩ => hr1
      | ⟨2, _⟩ => hr2
      | ⟨3, _⟩ => hr3
      | ⟨4, _⟩ => hr4
      | ⟨5, _⟩ => hr5
      | ⟨6, _⟩ => hr6
      | ⟨n + 7, hn⟩ => False.elim (by
          change n + 7 < 7 at hn
          omega)
  · intro r _
    rfl

theorem secondSetupState_init_agreement
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    (p : ColumnReduction.Slice (bits := bits) i.words)
    (key : Word bits) (hone : 1 < 2 ^ bits)
    (s : RamProgram.State (layout bits cap hcap))
    (hbase : setupReg s 7 = p.base)
    (hlen : (setupReg s 8).val = p.len)
    (hkey : setupReg s 11 = key) :
    ArenaAgreement (bank hcap) (secondSetupState hone s)
      (relocateStatePC (entryPC 1)
        (Predecessor.init (toPredecessor (input := i) p) key))
      (secondSetupState hone s) := by
  obtain ⟨h4, h5⟩ := secondSetupState_scratch hone s
  refine predecessor_init_agreement hcap (i := i) p key hone 1
    (secondSetupState hone s) ?_ ?_ ?_ ?_ ?_ h4 h5 ?_
  · rfl
  · simp (disch := decide) only [secondSetupState_regs, if_pos, if_neg]
  · simpa (disch := decide) only [secondSetupState_regs, if_pos, if_neg]
      using hlen
  · simpa (disch := decide) only [secondSetupState_regs, if_pos, if_neg]
      using hbase
  · simpa (disch := decide) only [secondSetupState_regs, if_pos, if_neg]
      using hkey
  · simp (disch := decide) only [secondSetupState_regs, if_pos, if_neg]

theorem thirdSetupState_init_agreement
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    (p : ColumnReduction.Slice (bits := bits) i.words)
    (key : Word bits) (hone : 1 < 2 ^ bits)
    (s : RamProgram.State (layout bits cap hcap))
    (hbase : (setupReg s 9).val + (setupReg s 13).val = p.base.val)
    (horder : (setupReg s 13).val ≤ (setupReg s 0).val)
    (hlen : (setupReg s 0).val - (setupReg s 13).val = p.len)
    (hkey : setupReg s 12 = key) :
    ArenaAgreement (bank hcap) (thirdSetupState hone s)
      (relocateStatePC (entryPC 2)
        (Predecessor.init (toPredecessor (input := i) p) key))
      (thirdSetupState hone s) := by
  have hfit : (setupReg s 9).val + (setupReg s 13).val < 2 ^ bits :=
    hbase.symm ▸ p.base.isLt
  obtain ⟨hb, hl⟩ := thirdSetupState_worker_values hone s hfit horder
  obtain ⟨h4, h5⟩ := thirdSetupState_scratch hone s
  refine predecessor_init_agreement hcap (i := i) p key hone 2
    (thirdSetupState hone s) ?_ ?_ (hl.trans hlen)
    (Fin.ext (hb.trans hbase)) ?_ h4 h5 ?_
  · rfl
  · simp (disch := decide) only [thirdSetupState_regs, if_pos, if_neg]
  · simpa (disch := decide) only [thirdSetupState_regs, if_pos, if_neg]
      using hkey
  · simp (disch := decide) only [thirdSetupState_regs, if_pos, if_neg]

end PaperB.RamProgram.ThreeCalls
