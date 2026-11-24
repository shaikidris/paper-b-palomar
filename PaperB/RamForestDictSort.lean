module

public import PaperB.RamForestRawInterface
public import PaperB.ForestPackedOrderedSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.DictSort

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.RawBuild
open PaperB.ForestHead (Vertex preparedKey)
open PaperB.ForestDictionary (Rows collectFrom collect mem_collect collect_length_le
  packedDictionary packedDictionary_eq packedDictionary_spec)
open PaperB.ForestSlimIndex
open PaperB.PairLookup (Key lexLess)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedPairCode)

private theorem serialize_val_eq {bits : Nat} {H : LabelledQuotient}
    (s : PaperB.RetainedProperLoss.Columns H) (f : FlatPairDictionary.Fits bits s)
    (j : Nat) (hjSer : j < (FlatPairDictionary.serialize s f).size)
    (hjBound : j < 1 + s.dict.size + s.dict.size + s.slots.size) :
    ((FlatPairDictionary.serialize s f)[j]'hjSer).val =
      if h0 : j = 0 then s.dict.size
      else if h1 : j < 1 + s.dict.size then
        (s.dict[j - 1]'(by omega)).1
      else if h2 : j < 1 + 2 * s.dict.size then
        (s.dict[j - (1 + s.dict.size)]'(by omega)).2
      else (s.slots[j - (1 + 2 * s.dict.size)]?).getD 0 := by
  let ser := FlatPairDictionary.serialize s f
  have hRep := FlatPairDictionary.serialize_represents s f
  have getSame (k1 k2 : Nat) (h1 : k1 < ser.size) (h2 : k2 < ser.size) (e : k1 = k2) :
      (ser[k1]'h1) = (ser[k2]'h2) := by subst k2; rfl
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceDIte]
    have hget0 : FlatPairDictionary.rowCount ser = (ser[0]'hjSer).val := by
      unfold FlatPairDictionary.rowCount
      rw [getElem?_pos _ 0 hjSer]
      rfl
    exact hget0.symm.trans hRep.rows
  · simp only [hj0, ↓reduceDIte]
    by_cases hj1 : j < 1 + s.dict.size
    · simp only [hj1, ↓reduceDIte]
      have hiD : j - 1 < s.dict.size := by omega
      have hfirst := hRep.first_eq (j - 1) (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hiD) hiD
      have hgetS : ((FlatPairDictionary.firstSlice ser hRep.valid).get (j - 1)
          (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hiD)).val = (ser[j]'hjSer).val := by
        unfold PaperB.PairLookup.ColumnReduction.Slice.get
        exact congrArg Fin.val (getSame _ _ _ _ (by show 1 + (j - 1) = j; omega))
      exact hgetS.symm.trans hfirst
    · simp only [hj1, ↓reduceDIte]
      by_cases hj2 : j < 1 + 2 * s.dict.size
      · simp only [hj2, ↓reduceDIte]
        have hiD : j - (1 + s.dict.size) < s.dict.size := by omega
        have hsecond := hRep.second_eq (j - (1 + s.dict.size)) (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hiD) hiD
        have hgetS : ((FlatPairDictionary.secondSlice ser hRep.valid).get (j - (1 + s.dict.size))
            (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hiD)).val = (ser[j]'hjSer).val := by
          unfold PaperB.PairLookup.ColumnReduction.Slice.get
          exact congrArg Fin.val (getSame _ _ _ _ (by
            change FlatPairDictionary.secondBase (FlatPairDictionary.rowCount ser) + (j - (1 + s.dict.size)) = j
            rw [hRep.rows]; unfold FlatPairDictionary.secondBase; omega))
        exact hgetS.symm.trans hsecond
      · simp only [hj2, ↓reduceDIte]
        have hiS : j - (1 + 2 * s.dict.size) < s.slots.size := by omega
        have hslot := hRep.slot_eq (j - (1 + 2 * s.dict.size)) (by rw [hRep.slot_len]; exact hiS) hiS
        have hgetS : ((FlatPairDictionary.slotSlice ser hRep.valid).get (j - (1 + 2 * s.dict.size))
            (by rw [hRep.slot_len]; exact hiS)).val = (ser[j]'hjSer).val := by
          unfold PaperB.PairLookup.ColumnReduction.Slice.get
          exact congrArg Fin.val (getSame _ _ _ _ (by
            change FlatPairDictionary.slotBase (FlatPairDictionary.rowCount ser) + (j - (1 + 2 * s.dict.size)) = j
            rw [hRep.rows]; unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase; omega))
        exact hgetS.symm.trans hslot

/-! ### Reusable low-level step helpers for 15-register word-RAM -/

section StepHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private theorem array_set_congr {α : Type} {a b : Array α} {i j : Nat} {v w : α}
    (ha : i < a.size) (hb : j < b.size) (hab : a = b) (hij : i = j) (hvw : v = w) :
    a.set i v ha = b.set j w hb := by
  subst hab; subst hij; subst hvw; rfl

private def putReg (s : State L) (d : Fin 15) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_putReg (s : State L) (d r : Fin 15) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, Ne.symm hv]

private theorem step_imm_at {code : Program L} {input : Input L} {s : State L}
    {d : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

private theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {d src : Fin 15}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d (reg s src), ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then
      some (Transition.next (putReg s d (reg s src))) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

private theorem step_add15_at {code : Program L} {input : Input L} {s : State L}
    {d lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.add d lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = add (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_add_at (input := input) hf hn

private theorem step_sub15_at {code : Program L} {input : Input L} {s : State L}
    {d lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.sub d lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = sub (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_sub_at (input := input) hf hn

private theorem step_loadInput_at {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d addr)) (hn : s.pc + 1 < code.size)
    (hw' : input.words[(reg s addr).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (input.words[(reg s addr).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw']
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

private theorem step_loadData15_at {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData d addr))
    (hread : s.data[(reg s addr).val]? = some w) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadData_at (input := input) hf hread hn

private theorem step_storeData_at {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin 15}
    (hf : code[s.pc]? = some (.storeData addr src)) (hn : s.pc + 1 < code.size)
    (hbound : (reg s addr).val < workCap) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.data = s.data.set (reg s addr).val (reg s src)
        (by simpa only [s.data_size] using hbound) ∧
      (∀ r : Fin 15, reg t r = reg s r) := by
  have ha : (reg s addr).val < s.data.size := by simpa only [s.data_size] using hbound
  let t : State L :=
    { s with
      data := s.data.set (reg s addr).val (reg s src) ha
      pc := s.pc + 1
      data_size := by simp only [Array.size_set, s.data_size] }
  refine ⟨t, ?_, rfl, rfl, fun _ => rfl⟩
  unfold step
  rw [hf]
  change (if h : (reg s addr).val < s.data.size then
    if s.pc + 1 < code.size then some (Transition.next _) else none else none) = _
  rw [dite_eq_left ha, ite_eq_left hn]

private theorem step_branchLt_true {code : Program L} {input : Input L} {s : State L}
    {x y : Fin 15} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (hlt : (reg s x).val < (reg s y).val) (hyes : yesPC < code.size) :
    step code input s = some (.next { s with pc := yesPC }) := by
  have hc : ltb (reg s x) (reg s y) = true := (PaperB.WordOps.ltb_eq_true _ _).mpr hlt
  simpa only [hc, ite_true] using
    step_branchLt_at (input := input) hf (by rw [hc]; exact hyes)

private theorem step_branchLt_false {code : Program L} {input : Input L} {s : State L}
    {x y : Fin 15} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (hle : (reg s y).val ≤ (reg s x).val) (hno : noPC < code.size) :
    step code input s = some (.next { s with pc := noPC }) := by
  have hc : ltb (reg s x) (reg s y) = false := by
    cases h : ltb (reg s x) (reg s y) with
    | false => rfl
    | true =>
      have hlt := (PaperB.WordOps.ltb_eq_true _ _).mp h
      omega
  simpa only [hc, Bool.false_eq_true, ite_false] using
    step_branchLt_at (input := input) hf (by rw [hc]; exact hno)

private theorem sub_val_exact {s : State L} {x y : Fin 15}
    (hle : (reg s y).val ≤ (reg s x).val) :
    (sub (reg s x) (reg s y)).val = (reg s x).val - (reg s y).val := by
  have hb : (reg s x).val - (reg s y).val < 2 ^ bits :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (reg s x).isLt
  change (2 ^ bits + (reg s x).val - (reg s y).val) % (2 ^ bits) =
    (reg s x).val - (reg s y).val
  rw [Nat.add_sub_assoc hle, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hb]

private theorem nonHalt_append (xs ys : List (Instr bits 15)) :
    (xs ++ ys).all (@nonHalt bits L) =
      (xs.all (@nonHalt bits L) && ys.all (@nonHalt bits L)) :=
  List.all_append

private def mkPhase (body : List (Instr bits 15))
    (hNoHalt : body.all (@nonHalt bits L) = true) :
    Phase L :=
  let code : Program L := (body ++ [Instr.halt]).toArray
  Phase.ofLast code body.length (by simp [code])
    (by
      have h : body.length < (body ++ [Instr.halt]).length := by simp
      simp [code])
    (by
      have ht : code.toList.take body.length = body := by simp [code]
      rw [ht]
      exact hNoHalt)

private theorem word_mem_eq_of_map_val {data : Array (Word bits)} {j v : Nat}
    (h : (data[j]?).map Fin.val = some v) :
    ∃ w : Word bits, data[j]? = some w ∧ w.val = v := by
  cases hj : data[j]? with
  | none => simp [hj] at h
  | some w =>
    rw [hj, Option.map_some] at h
    exact ⟨w, rfl, Option.some.inj h⟩

private theorem immStore_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp src : Fin 15} {slot : Word bits}
    (h0 : code[entry]? = some (.imm tmp slot))
    (h1 : code[entry + 1]? = some (.storeData tmp src))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hne : src ≠ tmp) (hbound : slot.val < workCap) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set slot.val (reg s src)
        (by simpa only [s.data_size] using hbound) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg s r) := by
  obtain ⟨u, su, upc, ur, uk, ud⟩ := step_imm_at (input := input)
    (by rw [hpc]; exact h0) (by omega)
  have hpc1 : code[u.pc]? = some (.storeData tmp src) := by rw [upc, hpc]; exact h1
  have hboundU : (reg u tmp).val < workCap := by rw [ur]; exact hbound
  obtain ⟨t, ut, tpc, td, tk⟩ := step_storeData_at (input := input) hpc1 (by omega) hboundU
  refine ⟨t, .cons su (.cons ut (.zero t)), by omega, ?_, fun r hr => (tk r).symm ▸ uk r hr⟩
  rw [td]
  exact array_set_congr _ _ ud (by rw [ur]) (uk _ hne)

private theorem loadAtOffset_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp dst base idx : Fin 15} {w : Word bits}
    (h0 : code[entry]? = some (.add tmp base idx))
    (h1 : code[entry + 1]? = some (.loadData dst tmp))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hbound : (reg s base).val + (reg s idx).val < workCap)
    (hread : s.data[(reg s base).val + (reg s idx).val]? = some w) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      reg t dst = w ∧
      (∀ r : Fin 15, r ≠ tmp → r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  have hpc0 : code[s.pc]? = some (.add tmp base idx) := by rw [hpc]; exact h0
  obtain ⟨u, su, upc, ur, uk, ud⟩ := step_add15_at (input := input) hpc0 (by omega)
  have hfit : (reg s base).val + (reg s idx).val < 2 ^ bits :=
    Nat.lt_of_lt_of_le hbound hw
  have had : (reg u tmp).val = (reg s base).val + (reg s idx).val := by
    rw [ur, PaperB.WordOps.add_no_wrap _ _ hfit]
  have hpc1 : code[u.pc]? = some (.loadData dst tmp) := by rw [upc, hpc]; exact h1
  have huRead : u.data[(reg u tmp).val]? = some w := by rw [ud, had]; exact hread
  obtain ⟨t, ut, tpc, tr, tk, td⟩ := step_loadData15_at (input := input) hpc1 huRead (by omega)
  refine ⟨t, .cons su (.cons ut (.zero t)), by omega, tr, ?_, td.trans ud⟩
  intro r hnt hnd
  exact (tk r hnd).trans (uk r hnt)

private theorem storeAtOffset_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp base idx src : Fin 15}
    (h0 : code[entry]? = some (.add tmp base idx))
    (h1 : code[entry + 1]? = some (.storeData tmp src))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hsrc : src ≠ tmp) (hbound : (reg s base).val + (reg s idx).val < workCap) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set ((reg s base).val + (reg s idx).val) (reg s src)
        (by simpa only [s.data_size] using hbound) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg s r) := by
  have hpc0 : code[s.pc]? = some (.add tmp base idx) := by rw [hpc]; exact h0
  obtain ⟨u, su, upc, ur, uk, ud⟩ := step_add15_at (input := input) hpc0 (by omega)
  have hfit : (reg s base).val + (reg s idx).val < 2 ^ bits :=
    Nat.lt_of_lt_of_le hbound hw
  have had : (reg u tmp).val = (reg s base).val + (reg s idx).val := by
    rw [ur, PaperB.WordOps.add_no_wrap _ _ hfit]
  have hpc1 : code[u.pc]? = some (.storeData tmp src) := by rw [upc, hpc]; exact h1
  have hboundU : (reg u tmp).val < workCap := by rw [had]; exact hbound
  obtain ⟨t, ut, tpc, td, tk⟩ := step_storeData_at (input := input) hpc1 (by omega) hboundU
  refine ⟨t, .cons su (.cons ut (.zero t)), by omega, ?_, fun r hr => (tk r).symm ▸ uk r hr⟩
  rw [td]
  exact array_set_congr _ _ ud had (uk _ hsrc)

private theorem immLoad_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp dst : Fin 15} {slot : Word bits} {w : Word bits}
    (h0 : code[entry]? = some (.imm tmp slot))
    (h1 : code[entry + 1]? = some (.loadData dst tmp))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hread : s.data[slot.val]? = some w) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      reg t dst = w ∧
      (∀ r : Fin 15, r ≠ tmp → r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  obtain ⟨u, su, upc, ur, uk, ud⟩ := step_imm_at (input := input)
    (by rw [hpc]; exact h0) (by omega)
  have hpc1 : code[u.pc]? = some (.loadData dst tmp) := by rw [upc, hpc]; exact h1
  have hreadU : u.data[(reg u tmp).val]? = some w := by rw [ud, ur]; exact hread
  obtain ⟨t, ut, tpc, tr, tk, td⟩ := step_loadData15_at (input := input) hpc1 hreadU (by omega)
  refine ⟨t, .cons su (.cons ut (.zero t)), by omega, tr, ?_, td.trans ud⟩
  intro r hnt hnd
  exact (tk r hnd).trans (uk r hnt)

private theorem copyPair_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp val srcFst srcSnd srcIdx dstFst dstSnd dstIdx : Fin 15}
    {w1 w2 : Word bits}
    (h0 : code[entry]? = some (.add tmp srcFst srcIdx))
    (h1 : code[entry + 1]? = some (.loadData val tmp))
    (h2 : code[entry + 2]? = some (.add tmp dstFst dstIdx))
    (h3 : code[entry + 3]? = some (.storeData tmp val))
    (h4 : code[entry + 4]? = some (.add tmp srcSnd srcIdx))
    (h5 : code[entry + 5]? = some (.loadData val tmp))
    (h6 : code[entry + 6]? = some (.add tmp dstSnd dstIdx))
    (h7 : code[entry + 7]? = some (.storeData tmp val))
    (hpc : s.pc = entry) (hexit : entry + 8 < code.size)
    (hnt : tmp ≠ srcFst ∧ tmp ≠ srcSnd ∧ tmp ≠ srcIdx ∧
      tmp ≠ dstFst ∧ tmp ≠ dstSnd ∧ tmp ≠ dstIdx ∧ tmp ≠ val)
    (hnv : val ≠ srcSnd ∧ val ≠ srcIdx ∧ val ≠ dstFst ∧ val ≠ dstSnd ∧ val ≠ dstIdx)
    (hb1 : (reg s dstFst).val + (reg s dstIdx).val < workCap)
    (hb2 : (reg s dstSnd).val + (reg s dstIdx).val < workCap)
    (hr1 : s.data[(reg s srcFst).val + (reg s srcIdx).val]? = some w1)
    (hr2 : s.data[(reg s srcSnd).val + (reg s srcIdx).val]? = some w2)
    (hne12 : (reg s dstFst).val + (reg s dstIdx).val ≠ (reg s srcSnd).val + (reg s srcIdx).val) :
    ∃ t : State L, Steps code input 8 s t ∧ t.pc = entry + 8 ∧
      (∀ hA1 hA2, t.data =
        (s.data.set ((reg s dstFst).val + (reg s dstIdx).val) w1 hA1).set
          ((reg s dstSnd).val + (reg s dstIdx).val) w2 hA2) ∧
      (∀ r : Fin 15, r ≠ tmp → r ≠ val → reg t r = reg s r) := by
  have hsds : s.data.size = workCap := s.data_size
  have hbound1 : (reg s srcFst).val + (reg s srcIdx).val < workCap :=
    Nat.lt_of_lt_of_eq (Array.getElem?_eq_some_iff.mp hr1).1 hsds
  have hbound2 : (reg s srcSnd).val + (reg s srcIdx).val < workCap :=
    Nat.lt_of_lt_of_eq (Array.getElem?_eq_some_iff.mp hr2).1 hsds
  obtain ⟨s2, st02, pc2, r2, k2, d2⟩ := loadAtOffset_steps (code := code) (input := input)
    h0 h1 hpc (by omega) hbound1 hr1
  have hb1' : (reg s2 dstFst).val + (reg s2 dstIdx).val < workCap := by
    rw [k2 dstFst hnt.2.2.2.1.symm hnv.2.2.1.symm, k2 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm]; exact hb1
  obtain ⟨s4, st24, pc4, d4, k4⟩ := storeAtOffset_steps (code := code) (input := input)
    h2 h3 pc2 (by omega) hnt.2.2.2.2.2.2.symm hb1'
  have h4b2 : (reg s4 srcSnd).val + (reg s4 srcIdx).val < workCap := by
    rw [k4 srcSnd hnt.2.1.symm, k2 srcSnd hnt.2.1.symm hnv.1.symm, k4 srcIdx hnt.2.2.1.symm,
      k2 srcIdx hnt.2.2.1.symm hnv.2.1.symm]
    exact hbound2
  have hs4d : s4.data = s.data.set ((reg s dstFst).val + (reg s dstIdx).val) w1
      (by simpa only [s.data_size] using hb1) := by
    rw [d4]
    exact array_set_congr _ _ d2
      (by rw [k2 dstFst hnt.2.2.2.1.symm hnv.2.2.1.symm, k2 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm]) r2
  have hr2' : s4.data[(reg s4 srcSnd).val + (reg s4 srcIdx).val]? = some w2 := by
    rw [hs4d, k4 srcSnd hnt.2.1.symm, k2 srcSnd hnt.2.1.symm hnv.1.symm, k4 srcIdx hnt.2.2.1.symm,
      k2 srcIdx hnt.2.2.1.symm hnv.2.1.symm, Array.getElem?_set_ne _ hne12]
    exact hr2
  obtain ⟨s6, st46, pc6, r6, k6, d6⟩ := loadAtOffset_steps (code := code) (input := input)
    h4 h5 pc4 (by omega) h4b2 hr2'
  have hb2' : (reg s6 dstSnd).val + (reg s6 dstIdx).val < workCap := by
    rw [k6 dstSnd hnt.2.2.2.2.1.symm hnv.2.2.2.1.symm, k4 dstSnd hnt.2.2.2.2.1.symm, k2 dstSnd hnt.2.2.2.2.1.symm hnv.2.2.2.1.symm,
        k6 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm, k4 dstIdx hnt.2.2.2.2.2.1.symm, k2 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm]
    exact hb2
  obtain ⟨s8, st68, pc8, d8, k8⟩ := storeAtOffset_steps (code := code) (input := input)
    h6 h7 pc6 (by omega) hnt.2.2.2.2.2.2.symm hb2'
  refine ⟨s8, st02.append (st24.append (st46.append st68)), pc8, ?_, ?_⟩
  · intro hA1 hA2
    rw [d8]
    have hd6 : s6.data = s.data.set ((reg s dstFst).val + (reg s dstIdx).val) w1
        (by simpa only [s.data_size] using hb1) := d6.trans hs4d
    have hidx6 : (reg s6 dstSnd).val + (reg s6 dstIdx).val = (reg s dstSnd).val + (reg s dstIdx).val := by
      rw [k6 dstSnd hnt.2.2.2.2.1.symm hnv.2.2.2.1.symm, k4 dstSnd hnt.2.2.2.2.1.symm, k2 dstSnd hnt.2.2.2.2.1.symm hnv.2.2.2.1.symm,
          k6 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm, k4 dstIdx hnt.2.2.2.2.2.1.symm, k2 dstIdx hnt.2.2.2.2.2.1.symm hnv.2.2.2.2.symm]
    exact array_set_congr _ _ hd6 hidx6 r6
  · intro r hrt hrv
    exact (k8 r hrt).trans ((k6 r hrt hrv).trans ((k4 r hrt).trans (k2 r hrt hrv)))

end StepHelpers

/-! ### Phase 1: Candidate-pair collection -/

section CollectPhase

private def slotK : Nat := 0
private def slotFstA : Nat := 1
private def slotSndA : Nat := 2
private def slotFstB : Nat := 3
private def slotSndB : Nat := 4
private def slotDict : Nat := 5
private def slotWidth : Nat := 6
private def slotI : Nat := 7

private abbrev cZero : Fin 15 := registers.zero      -- 7
private abbrev cOne : Fin 15 := registers.one        -- 5
private abbrev cY : Fin 15 := registers.ptr          -- 0
private abbrev cN : Fin 15 := count                  -- 9
private abbrev cRoot : Fin 15 := cmd                 -- 8
private abbrev cRowStart : Fin 15 := tinBase         -- 11
private abbrev cRowEnd : Fin 15 := toutBase          -- 12
private abbrev cPredBuf : Fin 15 := offsetBase       -- 13
private abbrev cFstA : Fin 15 := childrenBase        -- 14
private abbrev cSndA : Fin 15 := registers.stackBase -- 1
private abbrev cK : Fin 15 := clk                    -- 10
private abbrev cA : Fin 15 := registers.value        -- 4
private abbrev cB : Fin 15 := registers.remain       -- 2
private abbrev cLo : Fin 15 := registers.childBase   -- 3
private abbrev cTmp : Fin 15 := registers.tmp        -- 6

private def collectInit {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm cZero ⟨0, by omega⟩,
    .imm cOne ⟨1, by omega⟩,
    .imm cK ⟨0, by omega⟩,
    .imm cY ⟨0, by omega⟩,
    .loadInput cN cZero,
    .loadInput cB cOne,
    .imm cTmp ⟨2, by omega⟩,
    .loadInput cRoot cTmp,
    .add cTmp cN cN,
    .add cA cTmp cTmp,
    .add cA cA cA,
    .add cLo cB cB,
    .add cTmp cLo cLo,
    .add cLo cLo cTmp,
    .add cA cA cLo,
    .imm cTmp ⟨7, by omega⟩,
    .add cA cA cTmp,
    .add cRowStart cA cN,
    .add cRowStart cRowStart cN,
    .add cRowEnd cRowStart cN,
    .add cPredBuf cRowEnd cN,
    .add cFstA cPredBuf cB,
    .add cSndA cFstA cN,
    .imm cTmp ⟨1, by omega⟩, .storeData cTmp cFstA,
    .imm cTmp ⟨2, by omega⟩, .storeData cTmp cSndA,
    .add cA cSndA cN,
    .imm cTmp ⟨3, by omega⟩, .storeData cTmp cA,
    .add cA cA cN,
    .imm cTmp ⟨4, by omega⟩, .storeData cTmp cA,
    .add cA cA cN,
    .imm cTmp ⟨5, by omega⟩, .storeData cTmp cA ]

private def collectLoop {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .branchLt cY cN 37 64, -- 36
    .add cTmp cRowStart cY, -- 37
    .loadData cLo cTmp, -- 38
    .add cTmp cRowEnd cY, -- 39
    .loadData cA cTmp, -- 40
    .sub cA cA cLo, -- 41
    .imm cTmp ⟨2, by omega⟩, -- 42
    .branchLt cA cTmp 62 44, -- 43
    .branchLt cTmp cA 62 45, -- 44
    .add cTmp cPredBuf cLo, -- 45
    .loadData cA cTmp, -- 46
    .add cTmp cTmp cOne, -- 47
    .loadData cB cTmp, -- 48
    .branchLt cA cRoot 51 50, -- 49
    .branchLt cRoot cA 51 62, -- 50
    .branchLt cB cRoot 53 52, -- 51
    .branchLt cRoot cB 53 62, -- 52
    .branchLt cA cB 57 54, -- 53
    .mov cTmp cA, -- 54
    .mov cA cB, -- 55
    .mov cB cTmp, -- 56
    .add cTmp cFstA cK, -- 57
    .storeData cTmp cA, -- 58
    .add cTmp cSndA cK, -- 59
    .storeData cTmp cB, -- 60
    .add cK cK cOne, -- 61
    .add cY cY cOne, -- 62
    .goto 36 ] -- 63

private def collectExit {bits : Nat} : List (Instr bits 15) :=
  [ .storeData cZero cK ] -- 64

private def collectBody {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  collectInit h8 ++ collectLoop h8 ++ collectExit

private theorem collectBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (collectBody h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold collectBody
  rw [nonHalt_append, nonHalt_append]
  have h1 : (collectInit (bits := bits) h8).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by rfl
  have h2 : (collectLoop (bits := bits) h8).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by rfl
  have h3 : (collectExit (bits := bits)).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by rfl
  simp only [h1, h2, h3, Bool.and_self]

def collectPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (hi := hi) (hw := hw) (collectBody h8) (collectBody_nonHalt h8)

private theorem collectFrom_take_succ {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) (i : Fin H.vertexCount) :
    collectFrom rows code ((List.finRange H.vertexCount).take (i.val + 1)) =
      collectFrom rows code ((List.finRange H.vertexCount).take i.val) ++
        ((preparedKey H (rows.row i)).map code).toList := by
  have hi : i.val < (List.finRange H.vertexCount).length := by simp
  rw [List.take_succ_eq_append_getElem hi, List.getElem_finRange]
  unfold collectFrom
  rw [List.filterMap_append]
  cases h : preparedKey H (rows.row i) <;> simp [List.filterMap, h]

private theorem preparedKey_eq_none_of_len_ne_two {H : LabelledQuotient}
    (xs : List (Vertex H)) (h : xs.length ≠ 2) :
    preparedKey H xs = none := by
  cases xs with
  | nil => rfl
  | cons a tl =>
    cases tl with
    | nil => rfl
    | cons b tl2 =>
      cases tl2 with
      | nil => simp at h
      | cons c tl3 => rfl

private theorem preparedKey_of_two {H : LabelledQuotient}
    (a b : Vertex H) (hne : a ≠ b) :
    ((preparedKey H [a, b]).map orderedPairCode) =
      if a ≠ H.root ∧ b ≠ H.root then
        some (if a.val < b.val then (a.val, b.val) else (b.val, a.val))
      else none := by
  by_cases hab : a.val < b.val
  · have hab' : a < b := hab
    simp only [preparedKey, ite_eq_left hab', candidatePairOfPreds]
    by_cases ha : a ≠ H.root <;> by_cases hb : b ≠ H.root
    · simp only [dite_eq_left ha, dite_eq_left hb, dite_eq_left hab', Option.map_some,
        orderedPairCode, ite_eq_left hab, ite_eq_left (And.intro ha hb)]
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  · have hba : b < a := by
      change b.val < a.val
      have : a.val ≠ b.val := fun e => hne (Fin.ext e)
      omega
    have hnot : ¬ (a < b) := hab
    simp only [preparedKey, ite_eq_right hnot, candidatePairOfPreds]
    by_cases ha : a ≠ H.root <;> by_cases hb : b ≠ H.root
    · simp only [dite_eq_left ha, dite_eq_left hb, dite_eq_left hba, Option.map_some,
        orderedPairCode, ite_eq_right hab, ite_eq_left (And.intro ha hb)]
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private structure CollectInv {H : LabelledQuotient} (rows : Rows H)
    (orig : Array (Word bits)) (y : Nat) (s : State L) : Prop where
  pc : s.pc = 36
  zero : (reg s cZero).val = 0
  one : (reg s cOne).val = 1
  nVal : (reg s cN).val = H.vertexCount
  rootVal : (reg s cRoot).val = H.root.val
  rowStartVal : (reg s cRowStart).val = rowStartBase H.vertexCount H.arcCount
  rowEndVal : (reg s cRowEnd).val = rowEndBase H.vertexCount H.arcCount
  predBufVal : (reg s cPredBuf).val = predBufBase H.vertexCount H.arcCount
  fstAVal : (reg s cFstA).val = candFstABase H.vertexCount H.arcCount
  sndAVal : (reg s cSndA).val = candSndABase H.vertexCount H.arcCount
  yVal : (reg s cY).val = y
  kVal : (reg s cK).val =
    (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)).length
  bases :
    (s.data[slotFstA]?).map Fin.val = some (candFstABase H.vertexCount H.arcCount) ∧
    (s.data[slotSndA]?).map Fin.val = some (candSndABase H.vertexCount H.arcCount) ∧
    (s.data[slotFstB]?).map Fin.val = some (candFstBBase H.vertexCount H.arcCount) ∧
    (s.data[slotSndB]?).map Fin.val = some (candSndBBase H.vertexCount H.arcCount) ∧
    (s.data[slotDict]?).map Fin.val = some (dictBase H.vertexCount H.arcCount)
  collected :
    let xs := collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)
    ∀ j : Fin xs.length,
      (s.data[candFstABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).1 ∧
      (s.data[candSndABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).2
  frame : ∀ j,
    (orderBase H.vertexCount H.arcCount ≤ j ∧ j < candFstABase H.vertexCount H.arcCount) ∨
    candSndABase H.vertexCount H.arcCount + H.vertexCount ≤ j →
    s.data[j]? = orig[j]?

private theorem collectInit_part1 {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hRaw : RawQuotientInput input H) (s : State L) :
    let code := (collectPhase hi hw h8).code
    ∃ s8 : State L, Steps code input 8 (Phase.initial s) s8 ∧ s8.pc = 8 ∧
      (reg s8 cZero).val = 0 ∧ (reg s8 cOne).val = 1 ∧
      (reg s8 cK).val = 0 ∧ (reg s8 cY).val = 0 ∧
      (reg s8 cN).val = H.vertexCount ∧ (reg s8 cB).val = H.arcCount ∧
      (reg s8 cRoot).val = H.root.val ∧ s8.data = s.data := by
  intro code
  have hSize : code.size = 66 := rfl
  obtain ⟨wN, hwN, hwNv⟩ := word_mem_eq_of_map_val hRaw.hdr_n
  obtain ⟨wM, hwM, hwMv⟩ := word_mem_eq_of_map_val hRaw.hdr_m
  obtain ⟨wR, hwR, hwRv⟩ := word_mem_eq_of_map_val hRaw.hdr_root
  let s0 := Phase.initial s
  have pc0 : s0.pc = 0 := rfl
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_imm_at (code := code) (input := input)
    (s := s0) (d := cZero) (w := ⟨0, by omega⟩) (by rw [pc0]; rfl) (by omega)
  have hpc1 : s1.pc = 1 := by omega
  obtain ⟨s2, st1, pc2, r2, k2, d2⟩ := step_imm_at (code := code) (input := input)
    (s := s1) (d := cOne) (w := ⟨1, by omega⟩) (by rw [hpc1]; rfl) (by omega)
  have hpc2 : s2.pc = 2 := by omega
  obtain ⟨s3, st2, pc3, r3, k3, d3⟩ := step_imm_at (code := code) (input := input)
    (s := s2) (d := cK) (w := ⟨0, by omega⟩) (by rw [hpc2]; rfl) (by omega)
  have hpc3 : s3.pc = 3 := by omega
  obtain ⟨s4, st3, pc4, r4, k4, d4⟩ := step_imm_at (code := code) (input := input)
    (s := s3) (d := cY) (w := ⟨0, by omega⟩) (by rw [hpc3]; rfl) (by omega)
  have hpc4 : s4.pc = 4 := by omega
  have s4Zero : (reg s4 cZero).val = 0 := by
    rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), r1]
  have s4One : (reg s4 cOne).val = 1 := by
    rw [k4 _ (by decide), k3 _ (by decide), r2]
  obtain ⟨s5, st4, pc5, r5, k5, d5⟩ := step_loadInput_at (code := code) (input := input)
    (s := s4) (d := cN) (addr := cZero) (w := wN) (by rw [hpc4]; rfl) (by omega)
    (by rw [s4Zero]; exact hwN)
  have hpc5 : s5.pc = 5 := by omega
  obtain ⟨s6, st5, pc6, r6, k6, d6⟩ := step_loadInput_at (code := code) (input := input)
    (s := s5) (d := cB) (addr := cOne) (w := wM) (by rw [hpc5]; rfl) (by omega)
    (by rw [k5 _ (by decide), s4One]; exact hwM)
  have hpc6 : s6.pc = 6 := by omega
  obtain ⟨s7, st6, pc7, r7, k7, d7⟩ := step_imm_at (code := code) (input := input)
    (s := s6) (d := cTmp) (w := ⟨2, by omega⟩) (by rw [hpc6]; rfl) (by omega)
  have hpc7 : s7.pc = 7 := by omega
  obtain ⟨s8, st7, pc8, r8, k8, d8⟩ := step_loadInput_at (code := code) (input := input)
    (s := s7) (d := cRoot) (addr := cTmp) (w := wR) (by rw [hpc7]; rfl) (by omega)
    (by rw [r7]; exact hwR)
  refine ⟨s8, .cons st0 (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 (.zero s8)))))))),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), s4Zero]
  · rw [k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), s4One]
  · rw [k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), r3]
  · rw [k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), r4]
  · rw [k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), r5, hwNv]
  · rw [k8 _ (by decide), k7 _ (by decide), r6, hwMv]
  · rw [r8, hwRv]
  · exact d8.trans (d7.trans (d6.trans (d5.trans (d4.trans (d3.trans (d2.trans d1))))))

private theorem collectInit_part2 {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s8 : State L) (hpc : s8.pc = 8)
    (hN : (reg s8 cN).val = H.vertexCount) (hB : (reg s8 cB).val = H.arcCount) :
    let code := (collectPhase hi hw h8).code
    ∃ s23 : State L, Steps code input 15 s8 s23 ∧ s23.pc = 23 ∧
      (reg s23 cN).val = H.vertexCount ∧
      (reg s23 cRowStart).val = rowStartBase H.vertexCount H.arcCount ∧
      (reg s23 cRowEnd).val = rowEndBase H.vertexCount H.arcCount ∧
      (reg s23 cPredBuf).val = predBufBase H.vertexCount H.arcCount ∧
      (reg s23 cFstA).val = candFstABase H.vertexCount H.arcCount ∧
      (reg s23 cSndA).val = candSndABase H.vertexCount H.arcCount ∧
      (∀ r : Fin 15, r ∈ ([cZero, cOne, cRoot, cY, cK] : List (Fin 15)) →
        reg s23 r = reg s8 r) ∧
      s23.data = s8.data := by
  intro code
  have hSize : code.size = 66 := rfl
  have hWorkLe : workCap ≤ 2 ^ bits := hw
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ 2 ^ bits := by
    unfold rawWorkCap at hCap; omega
  have hOrderEq : orderBase H.vertexCount H.arcCount =
      8 * H.vertexCount + 6 * H.arcCount + 7 := by
    unfold orderBase stampsBase indegBase csrArenaWords; omega
  obtain ⟨s9, st8, pc9, r9, k9, d9⟩ := step_add15_at (code := code) (input := input)
    (s := s8) (d := cTmp) (lhs := cN) (rhs := cN) (by rw [hpc]; rfl) (by omega)
  have hpc9 : s9.pc = 9 := by omega
  obtain ⟨s10, st9, pc10, r10, k10, d10⟩ := step_add15_at (code := code) (input := input)
    (s := s9) (d := cA) (lhs := cTmp) (rhs := cTmp) (by rw [hpc9]; rfl) (by omega)
  have hpc10 : s10.pc = 10 := by omega
  obtain ⟨s11, st10, pc11, r11, k11, d11⟩ := step_add15_at (code := code) (input := input)
    (s := s10) (d := cA) (lhs := cA) (rhs := cA) (by rw [hpc10]; rfl) (by omega)
  have hpc11 : s11.pc = 11 := by omega
  obtain ⟨s12, st11, pc12, r12, k12, d12⟩ := step_add15_at (code := code) (input := input)
    (s := s11) (d := cLo) (lhs := cB) (rhs := cB) (by rw [hpc11]; rfl) (by omega)
  have hpc12 : s12.pc = 12 := by omega
  obtain ⟨s13, st12, pc13, r13, k13, d13⟩ := step_add15_at (code := code) (input := input)
    (s := s12) (d := cTmp) (lhs := cLo) (rhs := cLo) (by rw [hpc12]; rfl) (by omega)
  have hpc13 : s13.pc = 13 := by omega
  obtain ⟨s14, st13, pc14, r14, k14, d14⟩ := step_add15_at (code := code) (input := input)
    (s := s13) (d := cLo) (lhs := cLo) (rhs := cTmp) (by rw [hpc13]; rfl) (by omega)
  have hpc14 : s14.pc = 14 := by omega
  obtain ⟨s15, st14, pc15, r15, k15, d15⟩ := step_add15_at (code := code) (input := input)
    (s := s14) (d := cA) (lhs := cA) (rhs := cLo) (by rw [hpc14]; rfl) (by omega)
  have hpc15 : s15.pc = 15 := by omega
  obtain ⟨s16, st15, pc16, r16, k16, d16⟩ := step_imm_at (code := code) (input := input)
    (s := s15) (d := cTmp) (w := ⟨7, by omega⟩) (by rw [hpc15]; rfl) (by omega)
  have hpc16 : s16.pc = 16 := by omega
  obtain ⟨s17, st16, pc17, r17, k17, d17⟩ := step_add15_at (code := code) (input := input)
    (s := s16) (d := cA) (lhs := cA) (rhs := cTmp) (by rw [hpc16]; rfl) (by omega)
  have hpc17 : s17.pc = 17 := by omega
  have s17N : (reg s17 cN).val = H.vertexCount := by
    rw [k17 _ (by decide), k16 _ (by decide), k15 _ (by decide),
      k14 _ (by decide), k13 _ (by decide), k12 _ (by decide),
      k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), hN]
  have s17B : (reg s17 cB).val = H.arcCount := by
    rw [k17 _ (by decide), k16 _ (by decide), k15 _ (by decide),
      k14 _ (by decide), k13 _ (by decide), k12 _ (by decide),
      k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), hB]
  have s17A : (reg s17 cA).val = orderBase H.vertexCount H.arcCount := by
    have v9 : (reg s9 cTmp).val = 2 * H.vertexCount := by
      rw [r9, PaperB.WordOps.add_no_wrap _ _ (by rw [hN]; omega), hN]; omega
    have v10 : (reg s10 cA).val = 4 * H.vertexCount := by
      rw [r10, PaperB.WordOps.add_no_wrap _ _ (by rw [v9]; omega), v9]; omega
    have v11 : (reg s11 cA).val = 8 * H.vertexCount := by
      rw [r11, PaperB.WordOps.add_no_wrap _ _ (by rw [v10]; omega), v10]; omega
    have s11B : (reg s11 cB).val = H.arcCount := by
      rw [k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), hB]
    have v12 : (reg s12 cLo).val = 2 * H.arcCount := by
      rw [r12, PaperB.WordOps.add_no_wrap _ _ (by rw [s11B]; omega), s11B]; omega
    have v13 : (reg s13 cTmp).val = 4 * H.arcCount := by
      rw [r13, PaperB.WordOps.add_no_wrap _ _ (by rw [v12]; omega), v12]; omega
    have s13Lo : (reg s13 cLo).val = 2 * H.arcCount := by rw [k13 _ (by decide), v12]
    have v14 : (reg s14 cLo).val = 6 * H.arcCount := by
      rw [r14, PaperB.WordOps.add_no_wrap _ _ (by rw [s13Lo, v13]; omega), s13Lo, v13]; omega
    have s14A : (reg s14 cA).val = 8 * H.vertexCount := by
      rw [k14 _ (by decide), k13 _ (by decide), k12 _ (by decide), v11]
    have v15 : (reg s15 cA).val = 8 * H.vertexCount + 6 * H.arcCount := by
      rw [r15, PaperB.WordOps.add_no_wrap _ _ (by rw [s14A, v14]; omega), s14A, v14]
    have s16A : (reg s16 cA).val = 8 * H.vertexCount + 6 * H.arcCount := by
      rw [k16 _ (by decide), v15]
    rw [r17, PaperB.WordOps.add_no_wrap _ _ (by rw [s16A, r16]; dsimp; omega), s16A, r16]
    dsimp; omega
  obtain ⟨s18, st17, pc18, r18, k18, d18⟩ := step_add15_at (code := code) (input := input)
    (s := s17) (d := cRowStart) (lhs := cA) (rhs := cN) (by rw [hpc17]; rfl) (by omega)
  have hpc18 : s18.pc = 18 := by omega
  obtain ⟨s19, st18, pc19, r19, k19, d19⟩ := step_add15_at (code := code) (input := input)
    (s := s18) (d := cRowStart) (lhs := cRowStart) (rhs := cN) (by rw [hpc18]; rfl) (by omega)
  have hpc19 : s19.pc = 19 := by omega
  obtain ⟨s20, st19, pc20, r20, k20, d20⟩ := step_add15_at (code := code) (input := input)
    (s := s19) (d := cRowEnd) (lhs := cRowStart) (rhs := cN) (by rw [hpc19]; rfl) (by omega)
  have hpc20 : s20.pc = 20 := by omega
  obtain ⟨s21, st20, pc21, r21, k21, d21⟩ := step_add15_at (code := code) (input := input)
    (s := s20) (d := cPredBuf) (lhs := cRowEnd) (rhs := cN) (by rw [hpc20]; rfl) (by omega)
  have hpc21 : s21.pc = 21 := by omega
  obtain ⟨s22, st21, pc22, r22, k22, d22⟩ := step_add15_at (code := code) (input := input)
    (s := s21) (d := cFstA) (lhs := cPredBuf) (rhs := cB) (by rw [hpc21]; rfl) (by omega)
  have hpc22 : s22.pc = 22 := by omega
  obtain ⟨s23, st22, pc23, r23, k23, d23⟩ := step_add15_at (code := code) (input := input)
    (s := s22) (d := cSndA) (lhs := cFstA) (rhs := cN) (by rw [hpc22]; rfl) (by omega)
  have hRS : rowStartBase H.vertexCount H.arcCount =
      orderBase H.vertexCount H.arcCount + 2 * H.vertexCount := by
    unfold rowStartBase ranksBase; omega
  have hRE : rowEndBase H.vertexCount H.arcCount =
      rowStartBase H.vertexCount H.arcCount + H.vertexCount := rfl
  have hPB : predBufBase H.vertexCount H.arcCount =
      rowEndBase H.vertexCount H.arcCount + H.vertexCount := rfl
  have hFA : candFstABase H.vertexCount H.arcCount =
      predBufBase H.vertexCount H.arcCount + H.arcCount := rfl
  have hSA : candSndABase H.vertexCount H.arcCount =
      candFstABase H.vertexCount H.arcCount + H.vertexCount := rfl
  have v18 : (reg s18 cRowStart).val = orderBase H.vertexCount H.arcCount + H.vertexCount := by
    rw [r18, PaperB.WordOps.add_no_wrap _ _ (by rw [s17A, s17N]; omega), s17A, s17N]
  have s18N : (reg s18 cN).val = H.vertexCount := by rw [k18 _ (by decide), s17N]
  have v19 : (reg s19 cRowStart).val = rowStartBase H.vertexCount H.arcCount := by
    rw [r19, PaperB.WordOps.add_no_wrap _ _ (by rw [v18, s18N]; omega), v18, s18N]; omega
  have s19N : (reg s19 cN).val = H.vertexCount := by rw [k19 _ (by decide), s18N]
  have v20 : (reg s20 cRowEnd).val = rowEndBase H.vertexCount H.arcCount := by
    rw [r20, PaperB.WordOps.add_no_wrap _ _ (by rw [v19, s19N]; omega), v19, s19N]; omega
  have s20N : (reg s20 cN).val = H.vertexCount := by rw [k20 _ (by decide), s19N]
  have v21 : (reg s21 cPredBuf).val = predBufBase H.vertexCount H.arcCount := by
    rw [r21, PaperB.WordOps.add_no_wrap _ _ (by rw [v20, s20N]; omega), v20, s20N]; omega
  have s21B : (reg s21 cB).val = H.arcCount := by
    rw [k21 _ (by decide), k20 _ (by decide), k19 _ (by decide),
      k18 _ (by decide), s17B]
  have v22 : (reg s22 cFstA).val = candFstABase H.vertexCount H.arcCount := by
    rw [r22, PaperB.WordOps.add_no_wrap _ _ (by rw [v21, s21B]; omega), v21, s21B]; omega
  have s22N : (reg s22 cN).val = H.vertexCount := by
    rw [k22 _ (by decide), k21 _ (by decide), s20N]
  have v23 : (reg s23 cSndA).val = candSndABase H.vertexCount H.arcCount := by
    rw [r23, PaperB.WordOps.add_no_wrap _ _ (by rw [v22, s22N]; omega), v22, s22N]; omega
  refine ⟨s23,
    .cons st8 (.cons st9 (.cons st10 (.cons st11 (.cons st12 (.cons st13 (.cons st14
      (.cons st15 (.cons st16 (.cons st17 (.cons st18 (.cons st19 (.cons st20
      (.cons st21 (.cons st22 (.zero s23))))))))))))))),
    by omega, ?_, ?_, ?_, ?_, ?_, v23, ?_, ?_⟩
  · rw [k23 _ (by decide), s22N]
  · rw [k23 _ (by decide), k22 _ (by decide), k21 _ (by decide),
      k20 _ (by decide), v19]
  · rw [k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), v20]
  · rw [k23 _ (by decide), k22 _ (by decide), v21]
  · rw [k23 _ (by decide), v22]
  · intro r hr
    have hneq : r ≠ cRowStart ∧ r ≠ cRowEnd ∧ r ≠ cPredBuf ∧ r ≠ cFstA ∧
        r ≠ cSndA ∧ r ≠ cTmp ∧ r ≠ cA ∧ r ≠ cLo := by revert r hr; decide
    exact (k23 r hneq.2.2.2.2.1).trans ((k22 r hneq.2.2.2.1).trans ((k21 r hneq.2.2.1).trans
      ((k20 r hneq.2.1).trans ((k19 r hneq.1).trans ((k18 r hneq.1).trans ((k17 r hneq.2.2.2.2.2.2.1).trans
      ((k16 r hneq.2.2.2.2.2.1).trans ((k15 r hneq.2.2.2.2.2.2.1).trans ((k14 r hneq.2.2.2.2.2.2.2).trans
      ((k13 r hneq.2.2.2.2.2.1).trans ((k12 r hneq.2.2.2.2.2.2.2).trans ((k11 r hneq.2.2.2.2.2.2.1).trans
      ((k10 r hneq.2.2.2.2.2.2.1).trans (k9 r hneq.2.2.2.2.2.1))))))))))))))
  · exact d23.trans (d22.trans (d21.trans (d20.trans (d19.trans (d18.trans (d17.trans
      (d16.trans (d15.trans (d14.trans (d13.trans (d12.trans (d11.trans (d10.trans d9)))))))))))))

private theorem collectInit_part3 {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s23 : State L) (hpc : s23.pc = 23)
    (hN : (reg s23 cN).val = H.vertexCount)
    (hFA : (reg s23 cFstA).val = candFstABase H.vertexCount H.arcCount)
    (hSA : (reg s23 cSndA).val = candSndABase H.vertexCount H.arcCount) :
    let code := (collectPhase hi hw h8).code
    ∃ s36 : State L, Steps code input 13 s23 s36 ∧ s36.pc = 36 ∧
      (∀ r : Fin 15, r ≠ cTmp → r ≠ cA → reg s36 r = reg s23 r) ∧
      (s36.data[slotFstA]?).map Fin.val = some (candFstABase H.vertexCount H.arcCount) ∧
      (s36.data[slotSndA]?).map Fin.val = some (candSndABase H.vertexCount H.arcCount) ∧
      (s36.data[slotFstB]?).map Fin.val = some (candFstBBase H.vertexCount H.arcCount) ∧
      (s36.data[slotSndB]?).map Fin.val = some (candSndBBase H.vertexCount H.arcCount) ∧
      (s36.data[slotDict]?).map Fin.val = some (dictBase H.vertexCount H.arcCount) ∧
      (∀ j, 6 ≤ j → s36.data[j]? = s23.data[j]?) := by
  intro code
  have hSize : code.size = 66 := rfl
  have hWorkLe : workCap ≤ 2 ^ bits := hw
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := by
    unfold rawWorkCap at hCap; exact hCap
  have hBaseEq : candSndABase H.vertexCount H.arcCount =
      13 * H.vertexCount + 7 * H.arcCount + 7 := by
    unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase
      orderBase stampsBase indegBase csrArenaWords; omega
  have hFstBEq : candFstBBase H.vertexCount H.arcCount =
      candSndABase H.vertexCount H.arcCount + H.vertexCount := rfl
  have hSndBEq : candSndBBase H.vertexCount H.arcCount =
      candFstBBase H.vertexCount H.arcCount + H.vertexCount := rfl
  have hDictEq : dictBase H.vertexCount H.arcCount =
      candSndBBase H.vertexCount H.arcCount + H.vertexCount := rfl
  obtain ⟨s25, st23_25, pc25, d25, k25⟩ := immStore_steps (code := code) (input := input)
    (s := s23) (entry := 23) (tmp := cTmp) (src := cFstA) (slot := ⟨1, by omega⟩)
    rfl rfl hpc (by omega) (by decide) (by dsimp; omega)
  obtain ⟨s27, st25_27, pc27, d27, k27⟩ := immStore_steps (code := code) (input := input)
    (s := s25) (entry := 25) (tmp := cTmp) (src := cSndA) (slot := ⟨2, by omega⟩)
    rfl rfl pc25 (by omega) (by decide) (by dsimp; omega)
  obtain ⟨s28, st27, pc28, r28, k28, d28⟩ := step_add15_at (code := code) (input := input)
    (s := s27) (d := cA) (lhs := cSndA) (rhs := cN) (by rw [pc27]; rfl) (by omega)
  have s27SA : (reg s27 cSndA).val = candSndABase H.vertexCount H.arcCount := by
    rw [k27 _ (by decide), k25 _ (by decide), hSA]
  have s27N : (reg s27 cN).val = H.vertexCount := by
    rw [k27 _ (by decide), k25 _ (by decide), hN]
  have s28A : (reg s28 cA).val = candFstBBase H.vertexCount H.arcCount := by
    rw [r28, PaperB.WordOps.add_no_wrap _ _ (by rw [s27SA, s27N]; omega), s27SA, s27N]; omega
  obtain ⟨s30, st28_30, pc30, d30, k30⟩ := immStore_steps (code := code) (input := input)
    (s := s28) (entry := 28) (tmp := cTmp) (src := cA) (slot := ⟨3, by omega⟩)
    rfl rfl (by omega) (by omega) (by decide) (by dsimp; omega)
  obtain ⟨s31, st30, pc31, r31, k31, d31⟩ := step_add15_at (code := code) (input := input)
    (s := s30) (d := cA) (lhs := cA) (rhs := cN) (by rw [pc30]; rfl) (by omega)
  have s30A : (reg s30 cA).val = candFstBBase H.vertexCount H.arcCount := by
    rw [k30 _ (by decide), s28A]
  have s30N : (reg s30 cN).val = H.vertexCount := by
    rw [k30 _ (by decide), k28 _ (by decide), s27N]
  have s31A : (reg s31 cA).val = candSndBBase H.vertexCount H.arcCount := by
    rw [r31, PaperB.WordOps.add_no_wrap _ _ (by rw [s30A, s30N]; omega), s30A, s30N]; omega
  obtain ⟨s33, st31_33, pc33, d33, k33⟩ := immStore_steps (code := code) (input := input)
    (s := s31) (entry := 31) (tmp := cTmp) (src := cA) (slot := ⟨4, by omega⟩)
    rfl rfl (by omega) (by omega) (by decide) (by dsimp; omega)
  obtain ⟨s34, st33, pc34, r34, k34, d34⟩ := step_add15_at (code := code) (input := input)
    (s := s33) (d := cA) (lhs := cA) (rhs := cN) (by rw [pc33]; rfl) (by omega)
  have s33A : (reg s33 cA).val = candSndBBase H.vertexCount H.arcCount := by
    rw [k33 _ (by decide), s31A]
  have s33N : (reg s33 cN).val = H.vertexCount := by
    rw [k33 _ (by decide), k31 _ (by decide), s30N]
  have s34A : (reg s34 cA).val = dictBase H.vertexCount H.arcCount := by
    rw [r34, PaperB.WordOps.add_no_wrap _ _ (by rw [s33A, s33N]; omega), s33A, s33N]; omega
  obtain ⟨s36, st34_36, pc36, d36, k36⟩ := immStore_steps (code := code) (input := input)
    (s := s34) (entry := 34) (tmp := cTmp) (src := cA) (slot := ⟨5, by omega⟩)
    rfl rfl (by omega) (by omega) (by decide) (by dsimp; omega)
  refine ⟨s36, st23_25.append (st25_27.append (.cons st27 (st28_30.append (.cons st30
    (st31_33.append (.cons st33 st34_36)))))), pc36, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h1 h2
    exact (k36 r h1).trans ((k34 r h2).trans ((k33 r h1).trans ((k31 r h2).trans
      ((k30 r h1).trans ((k28 r h2).trans ((k27 r h1).trans (k25 r h1)))))))
  · change (s36.data[1]?).map Fin.val = _
    rw [d36, Array.getElem?_set_ne _ (by dsimp; omega), d34, d33,
      Array.getElem?_set_ne _ (by dsimp; omega), d31, d30,
      Array.getElem?_set_ne _ (by dsimp; omega), d28, d27,
      Array.getElem?_set_ne _ (by dsimp; omega), d25]
    change ((s23.data.set 1 (reg s23 cFstA) _)[1]?).map Fin.val = _
    rw [Array.getElem?_set_self, Option.map_some, hFA]
  · change (s36.data[2]?).map Fin.val = _
    rw [d36, Array.getElem?_set_ne _ (by dsimp; omega), d34, d33,
      Array.getElem?_set_ne _ (by dsimp; omega), d31, d30,
      Array.getElem?_set_ne _ (by dsimp; omega), d28, d27]
    change ((s25.data.set 2 (reg s25 cSndA) _)[2]?).map Fin.val = _
    rw [Array.getElem?_set_self, Option.map_some, k25 _ (by decide), hSA]
  · change (s36.data[3]?).map Fin.val = _
    rw [d36, Array.getElem?_set_ne _ (by dsimp; omega), d34, d33,
      Array.getElem?_set_ne _ (by dsimp; omega), d31, d30]
    change ((s28.data.set 3 (reg s28 cA) _)[3]?).map Fin.val = _
    rw [Array.getElem?_set_self, Option.map_some, s28A]
  · change (s36.data[4]?).map Fin.val = _
    rw [d36, Array.getElem?_set_ne _ (by dsimp; omega), d34, d33]
    change ((s31.data.set 4 (reg s31 cA) _)[4]?).map Fin.val = _
    rw [Array.getElem?_set_self, Option.map_some, s31A]
  · change (s36.data[5]?).map Fin.val = _
    rw [d36]
    change ((s34.data.set 5 (reg s34 cA) _)[5]?).map Fin.val = _
    rw [Array.getElem?_set_self, Option.map_some, s34A]
  · intro j hj
    rw [d36, Array.getElem?_set_ne _ (by dsimp; omega), d34, d33,
      Array.getElem?_set_ne _ (by dsimp; omega), d31, d30,
      Array.getElem?_set_ne _ (by dsimp; omega), d28, d27,
      Array.getElem?_set_ne _ (by dsimp; omega), d25,
      Array.getElem?_set_ne _ (by dsimp; omega)]

private theorem collectInit_steps {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {rows : Rows H} (s : State L) :
    ∃ t : State L, Steps (collectPhase hi hw h8).code input 36
      (Phase.initial s) t ∧ CollectInv rows s.data 0 t := by
  obtain ⟨s8, st1, pc8, z8, o8, k8, y8, n8, b8, r8, d8⟩ := collectInit_part1 h8 input hRaw s
  obtain ⟨s23, st2, pc23, n23, rs23, re23, pb23, fa23, sa23, keep23, d23⟩ :=
    collectInit_part2 h8 input hCap s8 pc8 n8 b8
  obtain ⟨s36, st3, pc36, keep36, b1, b2, b3, b4, b5, hmem⟩ :=
    collectInit_part3 h8 input hCap s23 pc23 n23 fa23 sa23
  have hOrderGe7 : 7 ≤ orderBase H.vertexCount H.arcCount := by
    unfold orderBase stampsBase indegBase csrArenaWords; omega
  have hSndGe : 6 ≤ candSndABase H.vertexCount H.arcCount + H.vertexCount := by
    unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase
      orderBase stampsBase indegBase csrArenaWords; omega
  have keepAll (r : Fin 15) (hr : r ∈ ([cZero, cOne, cRoot, cY, cK] : List (Fin 15))) :
      reg s36 r = reg s8 r := by
    have h1 : r ≠ cTmp ∧ r ≠ cA := by revert r hr; decide
    exact (keep36 r h1.1 h1.2).trans (keep23 r hr)
  refine ⟨s36, st1.append (st2.append st3), pc36, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨b1, b2, b3, b4, b5⟩, fun j => j.elim0, ?_⟩
  · rw [keepAll _ (by decide), z8]
  · rw [keepAll _ (by decide), o8]
  · rw [keep36 _ (by decide) (by decide), n23]
  · rw [keepAll _ (by decide), r8]
  · rw [keep36 _ (by decide) (by decide), rs23]
  · rw [keep36 _ (by decide) (by decide), re23]
  · rw [keep36 _ (by decide) (by decide), pb23]
  · rw [keep36 _ (by decide) (by decide), fa23]
  · rw [keep36 _ (by decide) (by decide), sa23]
  · rw [keepAll _ (by decide), y8]
  · rw [keepAll _ (by decide), k8]; rfl
  · intro j hj
    rcases hj with hj | hj
    · rw [hmem j (by omega), d23, d8]
    · rw [hmem j (by omega), d23, d8]

private theorem collectFrom_length_le {H : LabelledQuotient} (rows : Rows H)
    (code : CutPair H → Key) (ys : List (Vertex H)) :
    (collectFrom rows code ys).length ≤ ys.length := by
  induction ys with
  | nil => simp [collectFrom]
  | cons y ys ih =>
    unfold collectFrom
    cases h : preparedKey H (rows.row y) <;>
      simp only [List.length_cons, List.filterMap_cons, h]
    · exact Nat.le_succ_of_le ih
    · exact Nat.succ_le_succ ih

private theorem collectLoop_step {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {rows : Rows H} {orig : Array (Word bits)}
    (hS1 : ∀ y : Vertex H, ∃ lo hi : Nat,
      (orig[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
      (orig[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
      lo ≤ hi ∧ hi ≤ H.arcCount ∧
      hi - lo = (rows.row y).length ∧
      ∀ j : Fin (rows.row y).length,
        (orig[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
          some ((rows.row y)[j.val]'j.isLt).val)
    (y : Nat) (hy : y < H.vertexCount) (s : State L) (inv : CollectInv rows orig y s) :
    ∃ t : State L, ∃ cost, cost ≤ 28 ∧
      Steps (collectPhase hi hw h8).code input cost s t ∧
      CollectInv rows orig (y + 1) t := by
  let code := (collectPhase hi hw h8).code
  have hSize : code.size = 66 := rfl
  have hWorkLe : workCap ≤ 2 ^ bits := hw
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := by
    unfold rawWorkCap at hCap; exact hCap
  have hOrderGe7 : 7 ≤ orderBase H.vertexCount H.arcCount := by
    unfold orderBase stampsBase indegBase csrArenaWords; omega
  have hRS_ge : orderBase H.vertexCount H.arcCount ≤ rowStartBase H.vertexCount H.arcCount := by
    unfold rowStartBase ranksBase; omega
  have hRE_ge : orderBase H.vertexCount H.arcCount ≤ rowEndBase H.vertexCount H.arcCount := by
    unfold rowEndBase rowStartBase ranksBase; omega
  have hPB_ge : orderBase H.vertexCount H.arcCount ≤ predBufBase H.vertexCount H.arcCount := by
    unfold predBufBase rowEndBase rowStartBase ranksBase; omega
  have hFA_eq : candFstABase H.vertexCount H.arcCount = predBufBase H.vertexCount H.arcCount + H.arcCount := rfl
  have hSA_eq : candSndABase H.vertexCount H.arcCount = candFstABase H.vertexCount H.arcCount + H.vertexCount := rfl
  let vy : Vertex H := ⟨y, hy⟩
  obtain ⟨lo, hi', hrsOrig, hreOrig, hle, hhiM, hlen, hpredsOrig⟩ := hS1 vy
  have hrsCur : (s.data[rowStartBase H.vertexCount H.arcCount + y]?).map Fin.val = some lo := by
    rw [inv.frame _ (Or.inl ⟨by omega, by
      unfold candFstABase predBufBase rowEndBase rowStartBase; omega⟩)]
    exact hrsOrig
  have hreCur : (s.data[rowEndBase H.vertexCount H.arcCount + y]?).map Fin.val = some hi' := by
    rw [inv.frame _ (Or.inl ⟨by omega, by
      unfold candFstABase predBufBase rowEndBase; omega⟩)]
    exact hreOrig
  obtain ⟨wLo, hwLo, hwLov⟩ := word_mem_eq_of_map_val hrsCur
  obtain ⟨wHi, hwHi, hwHiv⟩ := word_mem_eq_of_map_val hreCur
  -- Step 36: branchLt cY cN 37 64
  have sg : step code input s = some (.next { s with pc := 37 }) :=
    step_branchLt_true (by rw [inv.pc]; rfl) (by rw [inv.yVal, inv.nVal]; exact hy) (by omega)
  let s37 : State L := { s with pc := 37 }
  -- 37..38: cLo := rowStart[y]
  have fitRS : (reg s37 cRowStart).val + (reg s37 cY).val < workCap := by
    change (reg s cRowStart).val + (reg s cY).val < workCap
    rw [inv.rowStartVal, inv.yVal]
    unfold rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords; omega
  obtain ⟨s39, st37_39, pc39, r39, k39, d39⟩ := loadAtOffset_steps (code := code) (input := input)
    (s := s37) (entry := 37) (tmp := cTmp) (dst := cLo) (base := cRowStart) (idx := cY) (w := wLo)
    rfl rfl rfl (by omega) fitRS
    (by change s.data[(reg s cRowStart).val + (reg s cY).val]? = _; rw [inv.rowStartVal, inv.yVal]; exact hwLo)
  -- 39..40: cA := rowEnd[y]
  have s39RE : (reg s39 cRowEnd).val = rowEndBase H.vertexCount H.arcCount := by
    rw [k39 _ (by decide) (by decide)]; exact inv.rowEndVal
  have s39Y : (reg s39 cY).val = y := by
    rw [k39 _ (by decide) (by decide)]; exact inv.yVal
  have fitRE : (reg s39 cRowEnd).val + (reg s39 cY).val < workCap := by
    rw [s39RE, s39Y]; unfold rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords; omega
  obtain ⟨s41, st39_41, pc41, r41, k41, d41⟩ := loadAtOffset_steps (code := code) (input := input)
    (s := s39) (entry := 39) (tmp := cTmp) (dst := cA) (base := cRowEnd) (idx := cY) (w := wHi)
    rfl rfl pc39 (by omega) fitRE (by rw [d39, s39RE, s39Y]; exact hwHi)
  -- 41: sub cA cA cLo
  obtain ⟨s42, st41, pc42, r42, k42, d42⟩ := step_sub15_at (code := code) (input := input)
    (s := s41) (d := cA) (lhs := cA) (rhs := cLo) (by rw [pc41]; rfl) (by omega)
  have s41Lo : (reg s41 cLo).val = lo := by
    rw [k41 _ (by decide) (by decide), r39, hwLov]
  have s41A : (reg s41 cA).val = hi' := by rw [r41, hwHiv]
  have s42A : (reg s42 cA).val = (rows.row vy).length := by
    rw [r42, sub_val_exact (by rw [s41Lo, s41A]; exact hle), s41A, s41Lo, hlen]
  -- 42: imm cTmp 2
  have hpc42 : s42.pc = 42 := by omega
  obtain ⟨s43, st42, pc43, r43, k43, d43⟩ := step_imm_at (code := code) (input := input)
    (s := s42) (d := cTmp) (w := ⟨2, by omega⟩) (by rw [hpc42]; rfl) (by omega)
  have hpc43 : s43.pc = 43 := by omega
  have s43A : (reg s43 cA).val = (rows.row vy).length := by
    rw [k43 _ (by decide), s42A]
  have s43Tmp : (reg s43 cTmp).val = 2 := by rw [r43]
  have s43Data : s43.data = s.data := d43.trans (d42.trans (d41.trans d39))
  have keep43 (r : Fin 15) (hr : r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15))) :
      reg s43 r = reg s r := by
    have hneq : r ≠ cTmp ∧ r ≠ cA ∧ r ≠ cLo := by revert r hr; decide
    exact (k43 r hneq.1).trans ((k42 r hneq.2.1).trans ((k41 r hneq.1 hneq.2.1).trans (k39 r hneq.1 hneq.2.2)))
  -- Helper for tail 62..63 -> 36 when skipping (k unchanged, data unchanged)
  have finishSkip (u : State L) (upc : u.pc = 62) (udata : u.data = s.data)
      (ukeep : ∀ r : Fin 15, r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15)) → reg u r = reg s r)
      (hne2 : (rows.row vy).length ≠ 2 ∨ preparedKey H (rows.row vy) = none) :
      ∃ t : State L, Steps code input 2 u t ∧ CollectInv rows orig (y + 1) t := by
    obtain ⟨v, uv, vpc, vr, vk, vd⟩ := step_add15_at (code := code) (input := input)
      (s := u) (d := cY) (lhs := cY) (rhs := cOne) (by rw [upc]; rfl) (by omega)
    have hpc63 : v.pc = 63 := by omega
    let t : State L := { v with pc := 36 }
    have vt : step code input v = some (.next t) :=
      step_goto_at (by rw [hpc63]; rfl) (by omega)
    have uY : (reg u cY).val = y := by rw [ukeep _ (by decide)]; exact inv.yVal
    have uOne : (reg u cOne).val = 1 := by rw [ukeep _ (by decide)]; exact inv.one
    have uN : (reg u cN).val = H.vertexCount := by rw [ukeep _ (by decide)]; exact inv.nVal
    have hkeyNone : preparedKey H (rows.row vy) = none := by
      rcases hne2 with hlen2 | hk
      · exact preparedKey_eq_none_of_len_ne_two _ hlen2
      · exact hk
    have hvy : vy.val = y := rfl
    have hTake : collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)) =
        collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y) := by
      have hsucc := collectFrom_take_succ rows orderedPairCode vy
      rw [hvy] at hsucc
      rw [hsucc, hkeyNone]
      simp
    refine ⟨t, .cons uv (.cons vt (.zero t)), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (reg v cZero).val = 0; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.zero
    · change (reg v cOne).val = 1; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.one
    · change (reg v cN).val = H.vertexCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.nVal
    · change (reg v cRoot).val = H.root.val; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.rootVal
    · change (reg v cRowStart).val = rowStartBase H.vertexCount H.arcCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.rowStartVal
    · change (reg v cRowEnd).val = rowEndBase H.vertexCount H.arcCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.rowEndVal
    · change (reg v cPredBuf).val = predBufBase H.vertexCount H.arcCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.predBufVal
    · change (reg v cFstA).val = candFstABase H.vertexCount H.arcCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.fstAVal
    · change (reg v cSndA).val = candSndABase H.vertexCount H.arcCount; rw [vk _ (by decide), ukeep _ (by decide)]; exact inv.sndAVal
    · change (reg v cY).val = y + 1
      rw [vr, PaperB.WordOps.add_no_wrap _ _ (by rw [uY, uOne]; have := inv.nVal; omega), uY, uOne]
    · change (reg v cK).val = _
      rw [vk _ (by decide), ukeep _ (by decide), hTake]; exact inv.kVal
    · change (_ ∧ _)
      rw [vd, udata]; exact inv.bases
    · dsimp only
      intro j
      have hj' : j.val < (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)).length := by
        rw [← hTake]; exact j.isLt
      have hcol := inv.collected ⟨j.val, hj'⟩
      change (v.data[_]?).map Fin.val = _ ∧ (v.data[_]?).map Fin.val = _
      rw [vd, udata]
      simpa only [hTake] using hcol
    · intro j hj
      change v.data[j]? = _
      rw [vd, udata]
      exact inv.frame j hj
  -- Branch on deg < 2
  by_cases hlt2 : (rows.row vy).length < 2
  · have sb : step code input s43 = some (.next { s43 with pc := 62 }) :=
      step_branchLt_true (by rw [hpc43]; rfl) (by rw [s43A, s43Tmp]; exact hlt2) (by omega)
    obtain ⟨t, st62, hinv'⟩ := finishSkip { s43 with pc := 62 } rfl s43Data
      (fun r hr => keep43 r hr) (Or.inl (by omega))
    exact ⟨t, 10, by decide,
      .cons sg (st37_39.append (st39_41.append (.cons st41 (.cons st42 (.cons sb st62))))), hinv'⟩
  · have sb1 : step code input s43 = some (.next { s43 with pc := 44 }) :=
      step_branchLt_false (by rw [hpc43]; rfl) (by rw [s43A, s43Tmp]; omega) (by omega)
    let s44 : State L := { s43 with pc := 44 }
    by_cases hgt2 : 2 < (rows.row vy).length
    · have sb2 : step code input s44 = some (.next { s44 with pc := 62 }) :=
        step_branchLt_true rfl (by change (reg s43 cTmp).val < (reg s43 cA).val; rw [s43A, s43Tmp]; exact hgt2) (by omega)
      obtain ⟨t, st62, hinv'⟩ := finishSkip { s44 with pc := 62 } rfl s43Data
        (fun r hr => keep43 r hr) (Or.inl (by omega))
      exact ⟨t, 11, by decide,
        .cons sg (st37_39.append (st39_41.append (.cons st41 (.cons st42 (.cons sb1 (.cons sb2 st62)))))), hinv'⟩
    · have hlen2 : (rows.row vy).length = 2 := by omega
      have sb2 : step code input s44 = some (.next { s44 with pc := 45 }) :=
        step_branchLt_false rfl (by change (reg s43 cA).val ≤ (reg s43 cTmp).val; rw [s43A, s43Tmp]; omega) (by omega)
      let s45 : State L := { s44 with pc := 45 }
      -- Obtain [va, vb] = rows.row vy
      have hexTwo : ∃ va vb : Vertex H, rows.row vy = [va, vb] := by
        cases hrow : rows.row vy with
        | nil => simp [hrow] at hlen2
        | cons va tl =>
          cases tl with
          | nil => simp [hrow] at hlen2
          | cons vb tl2 =>
            cases tl2 with
            | cons _ _ => simp [hrow] at hlen2
            | nil => exact ⟨va, vb, rfl⟩
      obtain ⟨va, vb, hrowEq⟩ := hexTwo
      have hnd : va ≠ vb := by
        have hnodup := (rows.spec vy).nodup
        rw [hrowEq] at hnodup
        intro h
        exact (List.nodup_cons.mp hnodup).1 (by rw [h]; exact List.Mem.head _)
      have haOrig : (orig[predBufBase H.vertexCount H.arcCount + lo]?).map Fin.val = some va.val := by
        have h0 := hpredsOrig ⟨0, by rw [hlen2]; decide⟩
        simp only [hrowEq, List.getElem_cons_zero, Nat.add_zero] at h0
        exact h0
      have hbOrig : (orig[predBufBase H.vertexCount H.arcCount + lo + 1]?).map Fin.val = some vb.val := by
        have h1 := hpredsOrig ⟨1, by rw [hlen2]; decide⟩
        simp only [hrowEq, List.getElem_cons_succ, List.getElem_cons_zero, Nat.add_assoc] at h1
        exact h1
      have haCur : (s45.data[predBufBase H.vertexCount H.arcCount + lo]?).map Fin.val = some va.val := by
        change (s43.data[_]?).map Fin.val = _; rw [s43Data]
        rw [inv.frame _ (Or.inl ⟨by omega, by omega⟩)]; exact haOrig
      have hbCur : (s45.data[predBufBase H.vertexCount H.arcCount + lo + 1]?).map Fin.val = some vb.val := by
        change (s43.data[_]?).map Fin.val = _; rw [s43Data]
        have hlo1 : lo + 1 < H.arcCount ∨ lo + 1 = H.arcCount := by omega
        -- wait: hi' - lo = 2 and hi' ≤ arcCount, so lo + 1 < hi' ≤ arcCount!
        have hlt : lo + 1 < H.arcCount := by omega
        rw [inv.frame _ (Or.inl ⟨by omega, by omega⟩)]; exact hbOrig
      obtain ⟨wA, hwA, hwAv⟩ := word_mem_eq_of_map_val haCur
      obtain ⟨wB, hwB, hwBv⟩ := word_mem_eq_of_map_val hbCur
      have s45PB : (reg s45 cPredBuf).val = predBufBase H.vertexCount H.arcCount := by
        change (reg s43 cPredBuf).val = _; rw [keep43 _ (by decide), inv.predBufVal]
      have s45Lo : (reg s45 cLo).val = lo := by
        change (reg s43 cLo).val = _; rw [k43 _ (by decide), k42 _ (by decide), k41 _ (by decide) (by decide), r39, hwLov]
      -- 45: add cTmp cPredBuf cLo
      have hPB_bound : predBufBase H.vertexCount H.arcCount + H.arcCount < 2 ^ bits := by
        unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
          indegBase csrArenaWords; omega
      obtain ⟨s46, st45, pc46, r46, k46, d46⟩ := step_add15_at (code := code) (input := input)
        (s := s45) (d := cTmp) (lhs := cPredBuf) (rhs := cLo) rfl (by change 45 + 1 < code.size; omega)
      have hpc46 : s46.pc = 46 := by omega
      have s46Tmp : (reg s46 cTmp).val = predBufBase H.vertexCount H.arcCount + lo := by
        rw [r46, PaperB.WordOps.add_no_wrap _ _ (by rw [s45PB, s45Lo]; omega), s45PB, s45Lo]
      -- 46: loadData cA cTmp
      obtain ⟨s47, st46, pc47, r47, k47, d47⟩ := step_loadData15_at (code := code) (input := input)
        (s := s46) (d := cA) (addr := cTmp) (w := wA) (by rw [hpc46]; rfl)
        (by rw [d46, s46Tmp]; exact hwA) (by omega)
      have hpc47 : s47.pc = 47 := by omega
      -- 47: add cTmp cTmp cOne
      obtain ⟨s48, st47, pc48, r48, k48, d48⟩ := step_add15_at (code := code) (input := input)
        (s := s47) (d := cTmp) (lhs := cTmp) (rhs := cOne) (by rw [hpc47]; rfl) (by omega)
      have hpc48 : s48.pc = 48 := by omega
      have s47Tmp : (reg s47 cTmp).val = predBufBase H.vertexCount H.arcCount + lo := by
        rw [k47 _ (by decide), s46Tmp]
      have s47One : (reg s47 cOne).val = 1 := by
        rw [k47 _ (by decide), k46 _ (by decide)]; change (reg s43 cOne).val = 1
        rw [keep43 _ (by decide), inv.one]
      have s48Tmp : (reg s48 cTmp).val = predBufBase H.vertexCount H.arcCount + lo + 1 := by
        rw [r48, PaperB.WordOps.add_no_wrap _ _ (by rw [s47Tmp, s47One]; omega), s47Tmp, s47One]
      -- 48: loadData cB cTmp
      obtain ⟨s49, st48, pc49, r49, k49, d49⟩ := step_loadData15_at (code := code) (input := input)
        (s := s48) (d := cB) (addr := cTmp) (w := wB) (by rw [hpc48]; rfl)
        (by rw [d48, d47, d46, s48Tmp]; exact hwB) (by omega)
      have hpc49 : s49.pc = 49 := by omega
      have s49A : (reg s49 cA).val = va.val := by
        rw [k49 _ (by decide), k48 _ (by decide), r47, hwAv]
      have s49B : (reg s49 cB).val = vb.val := by rw [r49, hwBv]
      have s49Data : s49.data = s.data := d49.trans (d48.trans (d47.trans (d46.trans s43Data)))
      have keep49 (r : Fin 15) (hr : r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15))) :
          reg s49 r = reg s r := by
        have hneq : r ≠ cTmp ∧ r ≠ cA ∧ r ≠ cB := by revert r hr; decide
        exact (k49 r hneq.2.2).trans ((k48 r hneq.1).trans ((k47 r hneq.2.1).trans
          ((k46 r hneq.1).trans (keep43 r hr))))
      have s49Root : (reg s49 cRoot).val = H.root.val := by
        rw [keep49 _ (by decide), inv.rootVal]
      have prefixSteps : Steps code input 13 s s49 :=
        .cons sg (st37_39.append (st39_41.append (.cons st41 (.cons st42 (.cons sb1 (.cons sb2
          (.cons st45 (.cons st46 (.cons st47 (.cons st48 (.zero s49)))))))))))
      -- Helper to advance from pc = 62 to pc = 36 (2 steps)
      have finishStep : ∀ t : State L, t.pc = 62 →
          (reg t cY).val = y → (reg t cOne).val = 1 →
          ∃ t' : State L, Steps code input 2 t t' ∧ t'.pc = 36 ∧
            t'.data = t.data ∧ (reg t' cY).val = y + 1 ∧
            (∀ r : Fin 15, r ≠ cY → reg t' r = reg t r) := by
        intro t htpc htY htOne
        obtain ⟨t1, st62, pc63, r63, k63, d63⟩ := step_add15_at (code := code) (input := input)
          (s := t) (d := cY) (lhs := cY) (rhs := cOne) (by rw [htpc]; rfl) (by omega)
        have st63 : step code input t1 = some (.next { t1 with pc := 36 }) :=
          step_goto_at (code := code) (input := input) (s := t1) (target := 36)
            (by rw [show t1.pc = 63 by omega]; rfl) (by omega)
        refine ⟨{ t1 with pc := 36 }, .cons st62 (.cons st63 (.zero _)), rfl, d63, ?_, ?_⟩
        · change (reg t1 cY).val = y + 1
          rw [r63, PaperB.WordOps.add_no_wrap _ _ (by rw [htY, htOne]; omega), htY, htOne]
        · intro r hr
          exact k63 r hr
      -- Helper to check x ≠ root at pc = p (49 or 51):
      -- takes 2 steps to 62 if x = root, or (1 or 2) steps to succ2 if x ≠ root
      have checkANeRoot : va = H.root →
          ∃ t : State L, Steps code input 2 s49 t ∧ t.pc = 62 ∧
            t.data = s.data ∧
            (∀ r : Fin 15, r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15)) → reg t r = reg s r) := by
        intro heq
        have b49 : step code input s49 = some (.next { s49 with pc := 50 }) :=
          step_branchLt_false (by rw [hpc49]; rfl)
            (by change (reg s49 cRoot).val ≤ (reg s49 cA).val; rw [s49A, s49Root, heq]; exact Nat.le_refl _) (by omega)
        have b50 : step code input { s49 with pc := 50 } = some (.next { s49 with pc := 62 }) :=
          step_branchLt_false rfl
            (by change (reg s49 cA).val ≤ (reg s49 cRoot).val; rw [s49A, s49Root, heq]; exact Nat.le_refl _) (by omega)
        exact ⟨{ s49 with pc := 62 }, .cons b49 (.cons b50 (.zero _)), rfl, s49Data, fun r hr => keep49 r hr⟩
      have checkANeq : va ≠ H.root →
          ∃ cA_steps : Nat, cA_steps ≤ 2 ∧
            Steps code input cA_steps s49 { s49 with pc := 51 } := by
        intro hne
        have hvalNe : va.val ≠ H.root.val := fun h => hne (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hvalNe with hlt | hgt
        · have b49 : step code input s49 = some (.next { s49 with pc := 51 }) :=
            step_branchLt_true (by rw [hpc49]; rfl)
              (by change (reg s49 cA).val < (reg s49 cRoot).val; rw [s49A, s49Root]; exact hlt) (by omega)
          exact ⟨1, by omega, .cons b49 (.zero _)⟩
        · have b49 : step code input s49 = some (.next { s49 with pc := 50 }) :=
            step_branchLt_false (by rw [hpc49]; rfl)
              (by change (reg s49 cRoot).val ≤ (reg s49 cA).val; rw [s49A, s49Root]; omega) (by omega)
          have b50 : step code input { s49 with pc := 50 } = some (.next { s49 with pc := 51 }) :=
            step_branchLt_true rfl
              (by change (reg s49 cRoot).val < (reg s49 cA).val; rw [s49A, s49Root]; exact hgt) (by omega)
          exact ⟨2, by omega, .cons b49 (.cons b50 (.zero _))⟩
      have hvy : vy.val = y := rfl
      by_cases haR : va = H.root
      · obtain ⟨s62, st62, pc62, d62, keep62⟩ := checkANeRoot haR
        obtain ⟨t, stEnd, pcEnd, dEnd, yEnd, kEnd⟩ := finishStep s62 pc62
          (by rw [keep62 _ (by decide), inv.yVal])
          (by rw [keep62 _ (by decide), inv.one])
        have pkNoneMap : (preparedKey H (rows.row vy)).map orderedPairCode = none := by
          rw [hrowEq, preparedKey_of_two va vb hnd]; simp [haR]
        have pkNone : preparedKey H (rows.row vy) = none := by
          cases hk : preparedKey H (rows.row vy) with
          | none => rfl
          | some _ => simp [hk] at pkNoneMap
        have xsEq : collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)) =
            collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y) := by
          have hsucc := collectFrom_take_succ rows orderedPairCode vy
          rw [hvy] at hsucc
          rw [hsucc, pkNone]; simp
        refine ⟨t, 13 + 2 + 2, by omega, prefixSteps.append (st62.append stEnd), ?_⟩
        refine ⟨pcEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, yEnd, ?_, ?_, ?_, ?_⟩
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.zero]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.one]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.nVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rootVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rowStartVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rowEndVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.predBufVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.fstAVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.sndAVal]
        · rw [kEnd _ (by decide), keep62 _ (by decide), inv.kVal, xsEq]
        · rw [dEnd, d62]; exact inv.bases
        · dsimp only
          intro j
          have hj' : j.val < (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)).length := by
            rw [← xsEq]; exact j.isLt
          rw [dEnd, d62]
          simpa only [xsEq] using inv.collected ⟨j.val, hj'⟩
        · intro j hj; rw [dEnd, d62]; exact inv.frame j hj
      · obtain ⟨cA_steps, hcA_le, st51⟩ := checkANeq haR
        let s51 : State L := { s49 with pc := 51 }
        by_cases hbR : vb = H.root
        · have b51 : step code input s51 = some (.next { s51 with pc := 52 }) :=
            step_branchLt_false rfl
              (by change (reg s49 cRoot).val ≤ (reg s49 cB).val; rw [s49B, s49Root, hbR]; exact Nat.le_refl _) (by omega)
          have b52 : step code input { s51 with pc := 52 } = some (.next { s51 with pc := 62 }) :=
            step_branchLt_false rfl
              (by change (reg s49 cB).val ≤ (reg s49 cRoot).val; rw [s49B, s49Root, hbR]; exact Nat.le_refl _) (by omega)
          let s62 : State L := { s51 with pc := 62 }
          obtain ⟨t, stEnd, pcEnd, dEnd, yEnd, kEnd⟩ := finishStep s62 rfl
            (by change (reg s49 cY).val = y; rw [keep49 _ (by decide), inv.yVal])
            (by change (reg s49 cOne).val = 1; rw [keep49 _ (by decide), inv.one])
          have pkNoneMap : (preparedKey H (rows.row vy)).map orderedPairCode = none := by
            rw [hrowEq, preparedKey_of_two va vb hnd]; simp [hbR]
          have pkNone : preparedKey H (rows.row vy) = none := by
            cases hk : preparedKey H (rows.row vy) with
            | none => rfl
            | some _ => simp [hk] at pkNoneMap
          have xsEq : collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)) =
              collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y) := by
            have hsucc := collectFrom_take_succ rows orderedPairCode vy
            rw [hvy] at hsucc
            rw [hsucc, pkNone]; simp
          refine ⟨t, 13 + cA_steps + 2 + 2, by omega,
            prefixSteps.append (st51.append (.cons b51 (.cons b52 stEnd))), ?_⟩
          refine ⟨pcEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, yEnd, ?_, ?_, ?_, ?_⟩
          · rw [kEnd _ (by decide)]; change (reg s49 cZero).val = 0; rw [keep49 _ (by decide), inv.zero]
          · rw [kEnd _ (by decide)]; change (reg s49 cOne).val = 1; rw [keep49 _ (by decide), inv.one]
          · rw [kEnd _ (by decide)]; change (reg s49 cN).val = _; rw [keep49 _ (by decide), inv.nVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cRoot).val = _; rw [keep49 _ (by decide), inv.rootVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cRowStart).val = _; rw [keep49 _ (by decide), inv.rowStartVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cRowEnd).val = _; rw [keep49 _ (by decide), inv.rowEndVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cPredBuf).val = _; rw [keep49 _ (by decide), inv.predBufVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cFstA).val = _; rw [keep49 _ (by decide), inv.fstAVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cSndA).val = _; rw [keep49 _ (by decide), inv.sndAVal]
          · rw [kEnd _ (by decide)]; change (reg s49 cK).val = _; rw [keep49 _ (by decide), inv.kVal, xsEq]
          · rw [dEnd]; change (_ ∧ _); rw [s49Data]; exact inv.bases
          · dsimp only
            intro j
            have hj' : j.val < (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)).length := by
              rw [← xsEq]; exact j.isLt
            rw [dEnd]; change (s49.data[_]?).map Fin.val = _ ∧ (s49.data[_]?).map Fin.val = _
            rw [s49Data]
            simpa only [xsEq] using inv.collected ⟨j.val, hj'⟩
          · intro j hj; rw [dEnd]; change s49.data[j]? = _; rw [s49Data]; exact inv.frame j hj
        · -- Both va ≠ H.root and vb ≠ H.root
          have hBvalNe : vb.val ≠ H.root.val := fun h => hbR (Fin.ext h)
          have hcheckB : ∃ cB_steps : Nat, cB_steps ≤ 2 ∧
              Steps code input cB_steps s51 { s51 with pc := 53 } := by
            rcases Nat.lt_or_gt_of_ne hBvalNe with hlt | hgt
            · have b51 : step code input s51 = some (.next { s51 with pc := 53 }) :=
                step_branchLt_true rfl
                  (by change (reg s49 cB).val < (reg s49 cRoot).val; rw [s49B, s49Root]; exact hlt) (by omega)
              exact ⟨1, by omega, .cons b51 (.zero _)⟩
            · have b51 : step code input s51 = some (.next { s51 with pc := 52 }) :=
                step_branchLt_false rfl
                  (by change (reg s49 cRoot).val ≤ (reg s49 cB).val; rw [s49B, s49Root]; omega) (by omega)
              have b52 : step code input { s51 with pc := 52 } = some (.next { s51 with pc := 53 }) :=
                step_branchLt_true rfl
                  (by change (reg s49 cRoot).val < (reg s49 cB).val; rw [s49B, s49Root]; exact hgt) (by omega)
              exact ⟨2, by omega, .cons b51 (.cons b52 (.zero _))⟩
          obtain ⟨cB_steps, hcB_le, st53⟩ := hcheckB
          let s53 : State L := { s51 with pc := 53 }
          -- Normalize order at pc = 53..57
          have hSort : ∃ cS_steps : Nat, cS_steps ≤ 4 ∧ ∃ s57 : State L,
              Steps code input cS_steps s53 s57 ∧ s57.pc = 57 ∧
              (reg s57 cA).val = min va.val vb.val ∧
              (reg s57 cB).val = max va.val vb.val ∧
              s57.data = s.data ∧
              (∀ r : Fin 15, r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15)) →
                reg s57 r = reg s r) := by
            by_cases hlt : va.val < vb.val
            · have b53 : step code input s53 = some (.next { s53 with pc := 57 }) :=
                step_branchLt_true rfl
                  (by change (reg s49 cA).val < (reg s49 cB).val; rw [s49A, s49B]; exact hlt) (by omega)
              refine ⟨1, by omega, { s53 with pc := 57 }, .cons b53 (.zero _), rfl, ?_, ?_, s49Data, fun r hr => keep49 r hr⟩
              · change (reg s49 cA).val = _; rw [s49A]; omega
              · change (reg s49 cB).val = _; rw [s49B]; omega
            · have hgt : vb.val < va.val := by
                have : va.val ≠ vb.val := fun h => hnd (Fin.ext h)
                omega
              have b53 : step code input s53 = some (.next { s53 with pc := 54 }) :=
                step_branchLt_false rfl
                  (by change (reg s49 cB).val ≤ (reg s49 cA).val; rw [s49A, s49B]; omega) (by omega)
              obtain ⟨s55, st54, pc55, r55, k55, d55⟩ := step_mov_at (code := code) (input := input)
                (s := { s53 with pc := 54 }) (d := cTmp) (src := cA) rfl (by change 54 + 1 < code.size; omega)
              have hpc55 : s55.pc = 55 := by dsimp at pc55; exact pc55
              obtain ⟨s56, st55, pc56, r56, k56, d56⟩ := step_mov_at (code := code) (input := input)
                (s := s55) (d := cA) (src := cB) (by rw [hpc55]; rfl) (by omega)
              have hpc56 : s56.pc = 56 := by omega
              obtain ⟨s57, st56, pc57, r57, k57, d57⟩ := step_mov_at (code := code) (input := input)
                (s := s56) (d := cB) (src := cTmp) (by rw [hpc56]; rfl) (by omega)
              refine ⟨4, by omega, s57, .cons b53 (.cons st54 (.cons st55 (.cons st56 (.zero s57)))),
                by omega, ?_, ?_, ?_, ?_⟩
              · rw [k57 _ (by decide), r56, k55 _ (by decide)]; change (reg s49 cB).val = _
                rw [s49B]; omega
              · rw [r57, k56 _ (by decide), r55]; change (reg s49 cA).val = _
                rw [s49A]; omega
              · exact d57.trans (d56.trans (d55.trans s49Data))
              · intro r hr
                have hneq : r ≠ cTmp ∧ r ≠ cA ∧ r ≠ cB := by revert r hr; decide
                exact (k57 r hneq.2.2).trans ((k56 r hneq.2.1).trans ((k55 r hneq.1).trans (keep49 r hr)))
          obtain ⟨cS_steps, hcS_le, s57, st57, pc57, s57A, s57B, s57Data, keep57⟩ := hSort
          let xs := collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take y)
          have hxs_le : xs.length ≤ y := by
            exact Nat.le_trans (collectFrom_length_le rows orderedPairCode _)
              (by simp [List.length_take, List.length_finRange]; omega)
          have hkVal : (reg s57 cK).val = xs.length := by
            rw [keep57 _ (by decide), inv.kVal]
          have hFAVal : (reg s57 cFstA).val = candFstABase H.vertexCount H.arcCount := by
            rw [keep57 _ (by decide), inv.fstAVal]
          have hSAVal : (reg s57 cSndA).val = candSndABase H.vertexCount H.arcCount := by
            rw [keep57 _ (by decide), inv.sndAVal]
          have hOneVal : (reg s57 cOne).val = 1 := by
            rw [keep57 _ (by decide), inv.one]
          have hFstLen : candFstABase H.vertexCount H.arcCount + xs.length < workCap := by
            unfold candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
              indegBase csrArenaWords; omega
          have hSndLen : candSndABase H.vertexCount H.arcCount + xs.length < workCap := by
            unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase
              stampsBase indegBase csrArenaWords; omega
          -- 57..58: fstA[k] := a
          obtain ⟨s59, st57_59, pc59, d59, k59⟩ := storeAtOffset_steps (code := code) (input := input)
            (s := s57) (entry := 57) (tmp := cTmp) (base := cFstA) (idx := cK) (src := cA)
            rfl rfl pc57 (by omega) (by decide) (by rw [hFAVal, hkVal]; exact hFstLen)
          -- 59..60: sndA[k] := b
          have s59SA : (reg s59 cSndA).val = candSndABase H.vertexCount H.arcCount := by
            rw [k59 _ (by decide), hSAVal]
          have s59K : (reg s59 cK).val = xs.length := by
            rw [k59 _ (by decide), hkVal]
          obtain ⟨s61, st59_61, pc61, d61, k61⟩ := storeAtOffset_steps (code := code) (input := input)
            (s := s59) (entry := 59) (tmp := cTmp) (base := cSndA) (idx := cK) (src := cB)
            rfl rfl pc59 (by omega) (by decide) (by rw [s59SA, s59K]; exact hSndLen)
          -- 61: add cK cK cOne
          obtain ⟨s62, st61, pc62, r62, k62, d62⟩ := step_add15_at (code := code) (input := input)
            (s := s61) (d := cK) (lhs := cK) (rhs := cOne) (by rw [pc61]; rfl) (by omega)
          have s61K : (reg s61 cK).val = xs.length := by
            rw [k61 _ (by decide), s59K]
          have s61One : (reg s61 cOne).val = 1 := by
            rw [k61 _ (by decide), k59 _ (by decide), hOneVal]
          have s62K : (reg s62 cK).val = xs.length + 1 := by
            rw [r62, PaperB.WordOps.add_no_wrap _ _ (by rw [s61K, s61One]; omega), s61K, s61One]
          have keep62 (r : Fin 15) (hr : r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA] : List (Fin 15))) :
              reg s62 r = reg s r := by
            have hneq : r ≠ cK ∧ r ≠ cTmp := by revert r hr; decide
            have hmem11 : r ∈ ([cZero, cOne, cY, cN, cRoot, cRowStart, cRowEnd, cPredBuf, cFstA, cSndA, cK] : List (Fin 15)) := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
            exact (k62 r hneq.1).trans ((k61 r hneq.2).trans ((k59 r hneq.2).trans (keep57 r hmem11)))
          have hpc62 : s62.pc = 62 := by omega
          obtain ⟨t, stEnd, pcEnd, dEnd, yEnd, kEnd⟩ := finishStep s62 hpc62
            (by rw [keep62 _ (by decide), inv.yVal])
            (by rw [keep62 _ (by decide), inv.one])
          -- Identify xs' = xs ++ [(min va.val vb.val, max va.val vb.val)]
          have pkSome : (preparedKey H (rows.row vy)).map orderedPairCode =
              some (min va.val vb.val, max va.val vb.val) := by
            rw [hrowEq, preparedKey_of_two va vb hnd]
            simp only [ite_eq_left (And.intro haR hbR)]
            by_cases hlt : va.val < vb.val
            · simp only [ite_eq_left hlt]
              have hle' : va.val ≤ vb.val := Nat.le_of_lt hlt
              rw [Nat.min_eq_left hle', Nat.max_eq_right hle']
            · simp only [ite_eq_right hlt]
              have hle' : vb.val ≤ va.val := Nat.le_of_not_lt hlt
              rw [Nat.min_eq_right hle', Nat.max_eq_left hle']
          have xsSucc : collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)) =
              xs ++ [(min va.val vb.val, max va.val vb.val)] := by
            have hsucc := collectFrom_take_succ rows orderedPairCode vy
            rw [hvy] at hsucc
            rw [hsucc, pkSome]; rfl
          have hFstData : candFstABase H.vertexCount H.arcCount + xs.length < s57.data.size := by
            rw [s57Data, s.data_size]; exact hFstLen
          have hSndData : candSndABase H.vertexCount H.arcCount + xs.length <
              (s57.data.set (candFstABase H.vertexCount H.arcCount + xs.length) (reg s57 cA) hFstData).size := by
            rw [Array.size_set, s57Data, s.data_size]; exact hSndLen
          have hd59' : s59.data = s57.data.set (candFstABase H.vertexCount H.arcCount + xs.length) (reg s57 cA) hFstData :=
            d59.trans (array_set_congr _ _ rfl (by rw [hFAVal, hkVal]) rfl)
          have htData : t.data =
              (s57.data.set (candFstABase H.vertexCount H.arcCount + xs.length) (reg s57 cA) hFstData).set
                (candSndABase H.vertexCount H.arcCount + xs.length) (reg s59 cB) hSndData := by
            rw [dEnd, d62]
            exact d61.trans (array_set_congr _ _ hd59' (by rw [s59SA, s59K]) rfl)
          have hcB59 : (reg s59 cB).val = max va.val vb.val := by
            rw [k59 _ (by decide), s57B]
          have idx_ne : candFstABase H.vertexCount H.arcCount + xs.length ≠
              candSndABase H.vertexCount H.arcCount + xs.length := by omega
          have htSlot : ∀ idx, idx < 7 → t.data[idx]? = s57.data[idx]? := by
            intro idx hidx
            have hne1 : candFstABase H.vertexCount H.arcCount + xs.length ≠ idx := by
              unfold candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase
                stampsBase indegBase csrArenaWords; omega
            have hne2 : candSndABase H.vertexCount H.arcCount + xs.length ≠ idx := by
              unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase
                orderBase stampsBase indegBase csrArenaWords; omega
            rw [htData, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
          refine ⟨t, 13 + (cA_steps + (cB_steps + (cS_steps + 7))), by omega,
            prefixSteps.append (st51.append (st53.append (st57.append
              (st57_59.append (st59_61.append (.cons st61 stEnd)))))), ?_⟩
          refine ⟨pcEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, yEnd, ?_, ?_, ?_, ?_⟩
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.zero]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.one]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.nVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rootVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rowStartVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.rowEndVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.predBufVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.fstAVal]
          · rw [kEnd _ (by decide), keep62 _ (by decide), inv.sndAVal]
          · rw [kEnd _ (by decide), s62K, xsSucc, List.length_append, List.length_singleton]
          · rw [htSlot slotFstA (by decide), htSlot slotSndA (by decide),
                htSlot slotFstB (by decide), htSlot slotSndB (by decide),
                htSlot slotDict (by decide), s57Data]
            exact inv.bases
          · dsimp only
            intro j
            rw [htData]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa only [xsSucc, List.length_append, List.length_singleton] using j.isLt)) with hj | hj
            · have jlt : j.val < xs.length := hj
              have jne1 : candFstABase H.vertexCount H.arcCount + xs.length ≠ candFstABase H.vertexCount H.arcCount + j.val := by omega
              have jne2 : candSndABase H.vertexCount H.arcCount + xs.length ≠ candFstABase H.vertexCount H.arcCount + j.val := by omega
              have jne3 : candFstABase H.vertexCount H.arcCount + xs.length ≠ candSndABase H.vertexCount H.arcCount + j.val := by omega
              have jne4 : candSndABase H.vertexCount H.arcCount + xs.length ≠ candSndABase H.vertexCount H.arcCount + j.val := by omega
              rw [Array.getElem?_set_ne _ jne2, Array.getElem?_set_ne _ jne1,
                  Array.getElem?_set_ne _ jne4, Array.getElem?_set_ne _ jne3, s57Data]
              have hget : ∀ (hlt' : j.val < (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1))).length),
                  (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)))[j.val]'hlt' =
                  xs[j.val]'jlt := by
                intro hlt'
                simp only [xsSucc]
                exact List.getElem_append_left jlt
              rw [hget j.isLt]
              exact inv.collected ⟨j.val, jlt⟩
            · have hget : ∀ (hlt' : j.val < (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1))).length),
                  (collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take (y + 1)))[j.val]'hlt' =
                  (min va.val vb.val, max va.val vb.val) := by
                intro hlt'
                simp only [xsSucc, hj]
                exact (List.getElem_append_right (Nat.le_refl _)).trans
                  (by simp only [Nat.sub_self, List.getElem_cons_zero])
              rw [hget j.isLt]
              constructor
              · rw [Array.getElem?_set_ne _ (by omega), hj]
                rw [Array.getElem?_set_self, Option.map_some, s57A]
              · rw [hj, Array.getElem?_set_self, Option.map_some, hcB59]
          · intro j hj
            rw [htData]
            have hne1 : candSndABase H.vertexCount H.arcCount + xs.length ≠ j := by
              rcases hj with hj | hj <;> omega
            have hne2 : candFstABase H.vertexCount H.arcCount + xs.length ≠ j := by
              rcases hj with hj | hj <;> omega
            rw [Array.getElem?_set_ne _ hne1, Array.getElem?_set_ne _ hne2, s57Data]
            exact inv.frame j hj

private theorem collectLoop_run {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {rows : Rows H} {orig : Array (Word bits)}
    (hS1 : ∀ y : Vertex H, ∃ lo hi : Nat,
      (orig[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
      (orig[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
      lo ≤ hi ∧ hi ≤ H.arcCount ∧
      hi - lo = (rows.row y).length ∧
      ∀ j : Fin (rows.row y).length,
        (orig[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
          some ((rows.row y)[j.val]'j.isLt).val) :
    ∀ k ≤ H.vertexCount, ∀ s : State L, CollectInv rows orig k s →
      ∃ t : State L, ∃ cost, cost ≤ 28 * (H.vertexCount - k) ∧
        Steps (collectPhase hi hw h8).code input cost s t ∧
        CollectInv rows orig H.vertexCount t := by
  intro k hk
  induction hd : H.vertexCount - k generalizing k with
  | zero =>
    intro s inv
    have hkeq : k = H.vertexCount := by omega
    subst hkeq
    exact ⟨s, 0, by omega, .zero s, inv⟩
  | succ d ih =>
    intro s inv
    have hklt : k < H.vertexCount := by omega
    obtain ⟨s', c1, hc1, st1, inv'⟩ := collectLoop_step h8 input hCap hS1 k hklt s inv
    obtain ⟨t, c2, hc2, st2, invFin⟩ := ih (k + 1) (by omega) (by omega) s' inv'
    exact ⟨t, c1 + c2, by omega, st1.append st2, invFin⟩

theorem run_collectPhase {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {rows : Rows H} (s : State L)
    (hS1 : ∀ y : Vertex H, ∃ lo hi : Nat,
      (s.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
      (s.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
      lo ≤ hi ∧ hi ≤ H.arcCount ∧
      hi - lo = (rows.row y).length ∧
      ∀ j : Fin (rows.row y).length,
        (s.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
          some ((rows.row y)[j.val]'j.isLt).val) :
    let ph := collectPhase hi hw h8
    let xs := collectFrom rows orderedPairCode (List.finRange H.vertexCount)
    ∃ t : State L, ∃ cost, cost ≤ 28 * H.vertexCount + 38 ∧
      Steps ph.code input cost (Phase.initial s) t ∧
      t.pc = ph.code.size - 1 ∧
      (reg t cZero).val = 0 ∧ (reg t cOne).val = 1 ∧
      (reg t cN).val = H.vertexCount ∧ (reg t cK).val = xs.length ∧
      (reg t cFstA).val = candFstABase H.vertexCount H.arcCount ∧
      (reg t cSndA).val = candSndABase H.vertexCount H.arcCount ∧
      (t.data[slotK]?).map Fin.val = some xs.length ∧
      (t.data[slotFstA]?).map Fin.val = some (candFstABase H.vertexCount H.arcCount) ∧
      (t.data[slotSndA]?).map Fin.val = some (candSndABase H.vertexCount H.arcCount) ∧
      (t.data[slotFstB]?).map Fin.val = some (candFstBBase H.vertexCount H.arcCount) ∧
      (t.data[slotSndB]?).map Fin.val = some (candSndBBase H.vertexCount H.arcCount) ∧
      (t.data[slotDict]?).map Fin.val = some (dictBase H.vertexCount H.arcCount) ∧
      (∀ j : Fin xs.length,
        (t.data[candFstABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).1 ∧
        (t.data[candSndABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).2) ∧
      (∀ j,
        (orderBase H.vertexCount H.arcCount ≤ j ∧ j < candFstABase H.vertexCount H.arcCount) ∨
        candSndABase H.vertexCount H.arcCount + H.vertexCount ≤ j →
        t.data[j]? = s.data[j]?) := by
  intro ph xs
  obtain ⟨s36, stInit, inv0⟩ := collectInit_steps h8 input hRaw hCap s
  obtain ⟨sEnd, cLoop, hcLoop, stLoop, invEnd⟩ :=
    collectLoop_run h8 input hCap hS1 0 (Nat.zero_le _) s36 inv0
  have hSize : ph.code.size = 66 := rfl
  have bExit : step ph.code input sEnd = some (.next { sEnd with pc := 64 }) :=
    step_branchLt_false (by rw [invEnd.pc]; rfl) (by rw [invEnd.yVal, invEnd.nVal]; exact Nat.le_refl _)
      (by rw [hSize]; omega)
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  have hOrderGe7 : 7 ≤ orderBase H.vertexCount H.arcCount := by
    unfold orderBase stampsBase indegBase csrArenaWords; omega
  have hSndGe : 6 ≤ candSndABase H.vertexCount H.arcCount + H.vertexCount := by
    unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase
      orderBase stampsBase indegBase csrArenaWords; omega
  obtain ⟨t, st64, pcEnd, dEnd, kEnd⟩ := step_storeData_at (code := ph.code) (input := input)
    (s := { sEnd with pc := 64 }) (addr := cZero) (src := cK) rfl (by rw [hSize]; change 64 + 1 < 66; omega)
    (by change (reg sEnd cZero).val < workCap; rw [invEnd.zero]; unfold rawWorkCap at hCap; omega)
  have hxsTake : collectFrom rows orderedPairCode ((List.finRange H.vertexCount).take H.vertexCount) = xs := by
    simp [xs, List.take_of_length_le]
  have invK : (reg sEnd cK).val = xs.length := by
    rw [invEnd.kVal, hxsTake]
  have hZeroLt : 0 < sEnd.data.size := by
    change 0 < sEnd.data.size
    rw [sEnd.data_size]
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 16) (Nat.le_trans (by unfold rawWorkCap; omega) hCap)
  have htData : t.data = sEnd.data.set 0 (reg sEnd cK) hZeroLt := by
    rw [dEnd]; exact array_set_congr _ _ rfl invEnd.zero rfl
  refine ⟨t, 36 + cLoop + 2, by rw [Nat.sub_zero] at hcLoop; omega,
    stInit.append (stLoop.append (.cons bExit (.cons st64 (.zero t)))),
    by dsimp at pcEnd; rw [pcEnd, hSize], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kEnd]; change (reg sEnd cZero).val = 0; rw [invEnd.zero]
  · rw [kEnd]; change (reg sEnd cOne).val = 1; rw [invEnd.one]
  · rw [kEnd]; change (reg sEnd cN).val = _; rw [invEnd.nVal]
  · rw [kEnd]; change (reg sEnd cK).val = _; rw [invK]
  · rw [kEnd]; change (reg sEnd cFstA).val = _; rw [invEnd.fstAVal]
  · rw [kEnd]; change (reg sEnd cSndA).val = _; rw [invEnd.sndAVal]
  · change (t.data[0]?).map Fin.val = some xs.length
    rw [htData, Array.getElem?_set_self, Option.map_some, invK]
  · rw [htData, Array.getElem?_set_ne _ (by decide)]; exact invEnd.bases.1
  · rw [htData, Array.getElem?_set_ne _ (by decide)]; exact invEnd.bases.2.1
  · rw [htData, Array.getElem?_set_ne _ (by decide)]; exact invEnd.bases.2.2.1
  · rw [htData, Array.getElem?_set_ne _ (by decide)]; exact invEnd.bases.2.2.2.1
  · rw [htData, Array.getElem?_set_ne _ (by decide)]; exact invEnd.bases.2.2.2.2
  · intro j
    have hneq1 : 0 ≠ candFstABase H.vertexCount H.arcCount + j.val := by
      unfold candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
        indegBase csrArenaWords; omega
    have hneq2 : 0 ≠ candSndABase H.vertexCount H.arcCount + j.val := by
      unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase
        stampsBase indegBase csrArenaWords; omega
    rw [htData, Array.getElem?_set_ne _ hneq1, Array.getElem?_set_ne _ hneq2]
    have hcol := invEnd.collected ⟨j.val, by simpa only [hxsTake] using j.isLt⟩
    simpa only [hxsTake] using hcol
  · intro j hj
    rw [htData, Array.getElem?_set_ne _ (by rcases hj with hj | hj <;> omega)]
    exact invEnd.frame j hj

end CollectPhase

/-! ### Phase 2: Bottom-up RAM merge sort (`sortPhase`) -/

section SortPhase

private abbrev rZero : Fin 15 := registers.zero      -- 7
private abbrev rOne : Fin 15 := registers.one        -- 5
private abbrev rK : Fin 15 := clk                    -- 10
private abbrev rFstA : Fin 15 := childrenBase        -- 14
private abbrev rSndA : Fin 15 := registers.stackBase -- 1
private abbrev rFstB : Fin 15 := tinBase             -- 11
private abbrev rSndB : Fin 15 := toutBase            -- 12
private abbrev rW : Fin 15 := count                  -- 9
private abbrev rB : Fin 15 := count                  -- 9 (aliased with rW when saved in slotWidth)
private abbrev rI : Fin 15 := registers.ptr          -- 0
private abbrev rA : Fin 15 := registers.ptr          -- 0 (aliased with rI inside merge/copyBack)
private abbrev rP : Fin 15 := registers.remain       -- 2
private abbrev rQ : Fin 15 := registers.childBase    -- 3
private abbrev rOut : Fin 15 := registers.value      -- 4
private abbrev rTmp : Fin 15 := registers.tmp        -- 6
private abbrev rEnd : Fin 15 := cmd                  -- 8
private abbrev rMid : Fin 15 := offsetBase           -- 13

def keyLe (x y : Key) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

private theorem keyLe_refl (x : Key) : keyLe x x :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

private theorem keyLe_trans {x y z : Key} (hxy : keyLe x y) (hyz : keyLe y z) :
    keyLe x z := by
  rcases hxy with h | ⟨he1, hle1⟩ <;> rcases hyz with h2 | ⟨he2, hle2⟩
  · exact Or.inl (Nat.lt_trans h h2)
  · exact Or.inl (by rw [← he2]; exact h)
  · exact Or.inl (by rw [he1]; exact h2)
  · exact Or.inr ⟨he1.trans he2, Nat.le_trans hle1 hle2⟩

private theorem keyLe_antisymm {x y : Key} (hxy : keyLe x y) (hyx : keyLe y x) :
    x = y := by
  rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
  rcases hxy with h1 | ⟨e1, l1⟩ <;> rcases hyx with h2 | ⟨e2, l2⟩
  · omega
  · simp_all
  · simp_all
  · simp_all; omega

private theorem keyLe_total (x y : Key) : keyLe x y ∨ keyLe y x := by
  rcases Nat.lt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.le_total x.2 y.2 with h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
  · exact Or.inr (Or.inl h)

def BlockSorted (xs : List Key) (w : Nat) : Prop :=
  ∀ i j (hi : i < xs.length) (hj : j < xs.length),
    i ≤ j → i / w = j / w → keyLe (xs[i]'hi) (xs[j]'hj)

private theorem blockSorted_one (xs : List Key) : BlockSorted xs 1 := by
  intro i j hi hj hij hdiv
  have heq : i = j := by simpa only [Nat.div_one] using hdiv
  subst heq
  exact keyLe_refl _

private theorem blockSorted_ge_sorted {xs : List Key} {w : Nat} (hw : xs.length ≤ w)
    (hb : BlockSorted xs w) :
    ∀ i j (hi : i < xs.length) (hj : j < xs.length), i ≤ j →
      keyLe (xs[i]'hi) (xs[j]'hj) := by
  intro i j hi hj hij
  exact hb i j hi hj hij (by rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hi hw),
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hj hw)])

private def sortBody {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ -- 0..6: init
    .imm rTmp ⟨3, by omega⟩,
    .loadData rFstB rTmp,
    .imm rTmp ⟨4, by omega⟩,
    .loadData rSndB rTmp,
    .mov rW rOne,
    .imm rTmp ⟨6, by omega⟩,
    .storeData rTmp rW,
    -- 7..10: passHead
    .branchLt rW rK 8 77,
    .imm rTmp ⟨6, by omega⟩,
    .storeData rTmp rW,
    .mov rI rZero,
    -- 11..22: chunkHead
    .branchLt rI rK 12 61,
    .imm rTmp ⟨6, by omega⟩,
    .loadData rW rTmp,
    .add rMid rI rW,
    .branchLt rMid rK 17 16,
    .mov rMid rK,
    .add rEnd rMid rW,
    .branchLt rEnd rK 20 19,
    .mov rEnd rK,
    .mov rP rI,
    .mov rQ rMid,
    .mov rOut rI,
    -- 23..35: mergeHead
    .branchLt rP rMid 24 58,
    .branchLt rQ rEnd 25 36,
    .add rTmp rFstA rP,
    .loadData rA rTmp,
    .add rTmp rFstA rQ,
    .loadData rB rTmp,
    .branchLt rA rB 36 30,
    .branchLt rB rA 47 31,
    .add rTmp rSndA rP,
    .loadData rA rTmp,
    .add rTmp rSndA rQ,
    .loadData rB rTmp,
    .branchLt rB rA 47 36,
    -- 36..46: takeP
    .add rTmp rFstA rP,
    .loadData rA rTmp,
    .add rTmp rFstB rOut,
    .storeData rTmp rA,
    .add rTmp rSndA rP,
    .loadData rA rTmp,
    .add rTmp rSndB rOut,
    .storeData rTmp rA,
    .add rP rP rOne,
    .add rOut rOut rOne,
    .goto 23,
    -- 47..57: takeQ
    .add rTmp rFstA rQ,
    .loadData rA rTmp,
    .add rTmp rFstB rOut,
    .storeData rTmp rA,
    .add rTmp rSndA rQ,
    .loadData rA rTmp,
    .add rTmp rSndB rOut,
    .storeData rTmp rA,
    .add rQ rQ rOne,
    .add rOut rOut rOne,
    .goto 23,
    -- 58..60: checkQ & chunkTail
    .branchLt rQ rEnd 47 59,
    .mov rI rEnd,
    .goto 11,
    -- 61..72: copyBack
    .mov rOut rZero,
    .branchLt rOut rK 63 73,
    .add rTmp rFstB rOut,
    .loadData rA rTmp,
    .add rTmp rFstA rOut,
    .storeData rTmp rA,
    .add rTmp rSndB rOut,
    .loadData rA rTmp,
    .add rTmp rSndA rOut,
    .storeData rTmp rA,
    .add rOut rOut rOne,
    .goto 62,
    -- 73..76: passTail
    .imm rTmp ⟨6, by omega⟩,
    .loadData rW rTmp,
    .add rW rW rW,
    .goto 7 ]

private theorem sortBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (sortBody h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  rfl

def sortPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (hi := hi) (hw := hw) (sortBody h8) (sortBody_nonHalt h8)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def MemPairAt (data : Array (Word bits)) (fstBase sndBase idx : Nat) (x : Key) : Prop :=
  (data[fstBase + idx]?).map Fin.val = some x.1 ∧
  (data[sndBase + idx]?).map Fin.val = some x.2

private theorem memPairAt_word {data : Array (Word bits)} {fstBase sndBase idx : Nat} {x : Key}
    (h : MemPairAt data fstBase sndBase idx x) :
    (∃ w1 : Word bits, data[fstBase + idx]? = some w1 ∧ w1.val = x.1) ∧
    (∃ w2 : Word bits, data[sndBase + idx]? = some w2 ∧ w2.val = x.2) :=
  ⟨word_mem_eq_of_map_val h.1, word_mem_eq_of_map_val h.2⟩

private structure SortPassInv (H : LabelledQuotient) (xs : List Key) (orig : Array (Word bits))
    (cur : List Key) (w : Nat) (s : State L) : Prop where
  pc : s.pc = 7
  zero : (reg s rZero).val = 0
  one : (reg s rOne).val = 1
  kVal : (reg s rK).val = xs.length
  fstAVal : (reg s rFstA).val = candFstABase H.vertexCount H.arcCount
  sndAVal : (reg s rSndA).val = candSndABase H.vertexCount H.arcCount
  fstBVal : (reg s rFstB).val = candFstBBase H.vertexCount H.arcCount
  sndBVal : (reg s rSndB).val = candSndBBase H.vertexCount H.arcCount
  wVal : (reg s rW).val = w
  wPos : 1 ≤ w
  lenEq : cur.length = xs.length
  lenBound : xs.length ≤ H.vertexCount
  sorted : BlockSorted cur w
  memEq : ∀ z : Key, z ∈ cur ↔ z ∈ xs
  inA : ∀ j : Fin cur.length,
    MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt)
  frame : ∀ j, j < 6 ∨
    (orderBase H.vertexCount H.arcCount ≤ j ∧ j < candFstABase H.vertexCount H.arcCount) ∨
    dictBase H.vertexCount H.arcCount ≤ j →
    s.data[j]? = orig[j]?

private theorem sortInit_steps {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {xs : List Key} (hlen : xs.length ≤ H.vertexCount) (s : State L)
    (hZero : (reg s rZero).val = 0) (hOne : (reg s rOne).val = 1)
    (hK : (reg s rK).val = xs.length)
    (hFA : (reg s rFstA).val = candFstABase H.vertexCount H.arcCount)
    (hSA : (reg s rSndA).val = candSndABase H.vertexCount H.arcCount)
    (hFBslot : (s.data[slotFstB]?).map Fin.val = some (candFstBBase H.vertexCount H.arcCount))
    (hSBslot : (s.data[slotSndB]?).map Fin.val = some (candSndBBase H.vertexCount H.arcCount))
    (hInA : ∀ j : Fin xs.length,
      MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (xs[j.val]'j.isLt)) :
    ∃ s7 : State L, Steps (sortPhase hi hw h8).code input 7 (Phase.initial s) s7 ∧
      SortPassInv H xs s.data xs 1 s7 := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  have hOrderGe7 : 7 ≤ orderBase H.vertexCount H.arcCount := by
    unfold orderBase stampsBase indegBase csrArenaWords; omega
  obtain ⟨wFB, hwFB, hwFBv⟩ := word_mem_eq_of_map_val hFBslot
  obtain ⟨wSB, hwSB, hwSBv⟩ := word_mem_eq_of_map_val hSBslot
  let s0 := Phase.initial s
  -- 0..1: rFstB := slotFstB (3)
  obtain ⟨s2, st02, pc2, r2, k2, d2⟩ := immLoad_steps (code := code) (input := input)
    (s := s0) (entry := 0) (tmp := rTmp) (dst := rFstB) (slot := ⟨3, by omega⟩) (w := wFB)
    rfl rfl rfl (by omega) hwFB
  -- 2..3: rSndB := slotSndB (4)
  obtain ⟨s4, st24, pc4, r4, k4, d4⟩ := immLoad_steps (code := code) (input := input)
    (s := s2) (entry := 2) (tmp := rTmp) (dst := rSndB) (slot := ⟨4, by omega⟩) (w := wSB)
    rfl rfl pc2 (by omega) (by rw [d2]; exact hwSB)
  -- 4: mov rW rOne
  obtain ⟨s5, st4, pc5, r5, k5, d5⟩ := step_mov_at (code := code) (input := input)
    (s := s4) (d := rW) (src := rOne) (by rw [pc4]; rfl) (by omega)
  -- 5..6: slotWidth (6) := rW
  have hpc5 : s5.pc = 5 := by omega
  obtain ⟨s7, st57, pc7, d7, k7⟩ := immStore_steps (code := code) (input := input)
    (s := s5) (entry := 5) (tmp := rTmp) (src := rW) (slot := ⟨6, by omega⟩)
    rfl rfl hpc5 (by omega) (by decide) (by dsimp; unfold rawWorkCap at hCap; omega)
  have keep5 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA] : List (Fin 15))) :
      reg s5 r = reg s r := by
    have hneq : r ≠ rTmp ∧ r ≠ rFstB ∧ r ≠ rSndB ∧ r ≠ rW := by revert r hr; decide
    exact (k5 r hneq.2.2.2).trans ((k4 r hneq.1 hneq.2.2.1).trans (k2 r hneq.1 hneq.2.1))
  have hs5d : s5.data = s.data := d5.trans (d4.trans d2)
  have hsds : s.data.size = workCap := s.data_size
  have h6lt : 6 < s.data.size := by
    rw [hsds]; unfold rawWorkCap at hCap; omega
  have hs7Data : s7.data = s.data.set 6 (reg s5 rW) h6lt := by
    rw [d7]; exact array_set_congr _ _ hs5d rfl rfl
  refine ⟨s7, st02.append (st24.append (.cons st4 st57)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Nat.le_refl 1, rfl, hlen, blockSorted_one xs, fun _ => Iff.rfl, ?_, ?_⟩
  · omega
  · rw [k7 _ (by decide), keep5 _ (by decide), hZero]
  · rw [k7 _ (by decide), keep5 _ (by decide), hOne]
  · rw [k7 _ (by decide), keep5 _ (by decide), hK]
  · rw [k7 _ (by decide), keep5 _ (by decide), hFA]
  · rw [k7 _ (by decide), keep5 _ (by decide), hSA]
  · rw [k7 _ (by decide), k5 _ (by decide), k4 _ (by decide) (by decide), r2, hwFBv]
  · rw [k7 _ (by decide), k5 _ (by decide), r4, hwSBv]
  · rw [k7 _ (by decide), r5, k4 _ (by decide) (by decide), k2 _ (by decide) (by decide)]
    change (reg s rOne).val = 1; exact hOne
  · intro j
    have hneq1 : 6 ≠ candFstABase H.vertexCount H.arcCount + j.val := by
      unfold candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
        indegBase csrArenaWords; omega
    have hneq2 : 6 ≠ candSndABase H.vertexCount H.arcCount + j.val := by
      unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase
        stampsBase indegBase csrArenaWords; omega
    have h := hInA j
    exact ⟨by rw [hs7Data, Array.getElem?_set_ne _ hneq1]; exact h.1,
           by rw [hs7Data, Array.getElem?_set_ne _ hneq2]; exact h.2⟩
  · intro j hj
    have hneq6 : 6 ≠ j := by
      rcases hj with hj | hj | hj
      · omega
      · unfold candFstABase predBufBase rowEndBase rowStartBase ranksBase orderBase
          stampsBase indegBase csrArenaWords at hj; omega
      · simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
          rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hj
        omega
    rw [hs7Data, Array.getElem?_set_ne _ hneq6]

private structure MergeInv (H : LabelledQuotient) (cur : List Key) (origB : Array (Word bits))
    (lo mid end_ p q out : Nat) (s : State L) : Prop where
  pc : s.pc = 23
  zero : (reg s rZero).val = 0
  one : (reg s rOne).val = 1
  kVal : (reg s rK).val = cur.length
  fstAVal : (reg s rFstA).val = candFstABase H.vertexCount H.arcCount
  sndAVal : (reg s rSndA).val = candSndABase H.vertexCount H.arcCount
  fstBVal : (reg s rFstB).val = candFstBBase H.vertexCount H.arcCount
  sndBVal : (reg s rSndB).val = candSndBBase H.vertexCount H.arcCount
  midVal : (reg s rMid).val = mid
  endVal : (reg s rEnd).val = end_
  pVal : (reg s rP).val = p
  qVal : (reg s rQ).val = q
  outVal : (reg s rOut).val = out
  pRange : lo ≤ p ∧ p ≤ mid
  qRange : mid ≤ q ∧ q ≤ end_
  outEq : out = lo + (p - lo) + (q - mid)
  outPairs : ∀ t, lo ≤ t → t < out → ∃ x : Key,
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) t x
  outSorted : ∀ u v x y, lo ≤ u → u ≤ v → v < out →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) u x →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) v y →
    keyLe x y
  outLeP : ∀ u x p' (hp' : p' < cur.length), lo ≤ u → u < out → p ≤ p' → p' < mid →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) u x →
    keyLe x (cur[p']'hp')
  outLeQ : ∀ u x q' (hq' : q' < cur.length), lo ≤ u → u < out → q ≤ q' → q' < end_ →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) u x →
    keyLe x (cur[q']'hq')
  memPart : ∀ z : Key,
    ((∃ t, lo ≤ t ∧ t < out ∧
      MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) t z) ∨
     (∃ p', ∃ hp' : p' < cur.length, p ≤ p' ∧ p' < mid ∧ cur[p']'hp' = z) ∨
     (∃ q', ∃ hq' : q' < cur.length, q ≤ q' ∧ q' < end_ ∧ cur[q']'hq' = z)) ↔
    (∃ t, ∃ ht : t < cur.length, lo ≤ t ∧ t < end_ ∧ cur[t]'ht = z)
  frameB : ∀ j,
    (j < candFstBBase H.vertexCount H.arcCount + lo ∨ candFstBBase H.vertexCount H.arcCount + end_ ≤ j) →
    (j < candSndBBase H.vertexCount H.arcCount + lo ∨ candSndBBase H.vertexCount H.arcCount + end_ ≤ j) →
    s.data[j]? = origB[j]?

private theorem mergeLoop_step {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} (hLen : cur.length ≤ H.vertexCount)
    {origB : Array (Word bits)}
    (hInA : ∀ j : Fin cur.length,
      MemPairAt origB (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt))
    {lo mid end_ : Nat} (_hle1 : lo ≤ mid) (hle2 : mid ≤ end_) (hle3 : end_ ≤ cur.length)
    (hLeftSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      lo ≤ u → u ≤ v → v < mid → keyLe (cur[u]'hu) (cur[v]'hv))
    (hRightSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      mid ≤ u → u ≤ v → v < end_ → keyLe (cur[u]'hu) (cur[v]'hv))
    (p q out : Nat) (hrem : p < mid ∨ q < end_)
    (s : State L) (inv : MergeInv H cur origB lo mid end_ p q out s) :
    ∃ p' q' out', ∃ t : State L, ∃ cost,
      cost ≤ 24 ∧
      (mid - p') + (end_ - q') < (mid - p) + (end_ - q) ∧
      Steps (sortPhase hi hw h8).code input cost s t ∧
      MergeInv H cur origB lo mid end_ p' q' out' t := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  have hInACur : ∀ j : Fin cur.length,
      MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt) := by
    intro j
    have hjlt : j.val < H.vertexCount := Nat.lt_of_lt_of_le j.isLt hLen
    have hdisj1 : candFstABase H.vertexCount H.arcCount + j.val < candFstBBase H.vertexCount H.arcCount + lo ∧
        candFstABase H.vertexCount H.arcCount + j.val < candSndBBase H.vertexCount H.arcCount + lo := by
      simp only [candSndBBase, candFstBBase, candSndABase]
      exact ⟨by omega, by omega⟩
    have hdisj2 : candSndABase H.vertexCount H.arcCount + j.val < candFstBBase H.vertexCount H.arcCount + lo ∧
        candSndABase H.vertexCount H.arcCount + j.val < candSndBBase H.vertexCount H.arcCount + lo := by
      simp only [candSndBBase, candFstBBase, candSndABase]
      exact ⟨by omega, by omega⟩
    exact ⟨by rw [inv.frameB _ (Or.inl hdisj1.1) (Or.inl hdisj1.2)]; exact (hInA j).1,
           by rw [inv.frameB _ (Or.inl hdisj2.1) (Or.inl hdisj2.2)]; exact (hInA j).2⟩
  have hOutLt : out < end_ := by
    have hp1 := inv.pRange.1; have hp2 := inv.pRange.2
    have hq1 := inv.qRange.1; have hq2 := inv.qRange.2
    have := inv.outEq
    rcases hrem with hp | hq <;> omega
  have hFstBBound : (reg s rFstB).val + (reg s rOut).val < workCap := by
    rw [inv.fstBVal, inv.outVal]
    simp only [candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase,
      ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
  have hSndBBound : (reg s rSndB).val + (reg s rOut).val < workCap := by
    rw [inv.sndBVal, inv.outVal]
    simp only [candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase,
      rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
  -- Take P helper starting from pc = 36 (for State u with p < mid and ∀ q' ∈ [q, end_), cur[p] ≤ cur[q'])
  have takePBlock : ∀ (u : State L), u.pc = 36 → u.data = s.data →
      (∀ r : Fin 15, r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15)) →
        reg u r = reg s r) →
      (hp : p < mid) →
      (hleQ : ∀ q' (hq' : q' < cur.length), q ≤ q' → q' < end_ →
        keyLe (cur[p]'(by omega)) (cur[q']'hq')) →
      ∃ t : State L, Steps code input 11 u t ∧
        MergeInv H cur origB lo mid end_ (p + 1) q (out + 1) t := by
    intro u hupc hudata hukeep hp hleQ
    have hplt : p < cur.length := by omega
    obtain ⟨⟨w1, hw1, hw1v⟩, ⟨w2, hw2, hw2v⟩⟩ := memPairAt_word (hInACur ⟨p, hplt⟩)
    have hr1 : u.data[(reg u rFstA).val + (reg u rP).val]? = some w1 := by
      rw [hudata, hukeep _ (by decide), hukeep _ (by decide), inv.fstAVal, inv.pVal]; exact hw1
    have hr2 : u.data[(reg u rSndA).val + (reg u rP).val]? = some w2 := by
      rw [hudata, hukeep _ (by decide), hukeep _ (by decide), inv.sndAVal, inv.pVal]; exact hw2
    have hb1 : (reg u rFstB).val + (reg u rOut).val < workCap := by
      rw [hukeep _ (by decide), hukeep _ (by decide)]; exact hFstBBound
    have hb2 : (reg u rSndB).val + (reg u rOut).val < workCap := by
      rw [hukeep _ (by decide), hukeep _ (by decide)]; exact hSndBBound
    have hne12 : (reg u rFstB).val + (reg u rOut).val ≠ (reg u rSndA).val + (reg u rP).val := by
      rw [hukeep _ (by decide), hukeep _ (by decide), hukeep _ (by decide), hukeep _ (by decide),
          inv.fstBVal, inv.outVal, inv.sndAVal, inv.pVal]
      unfold candFstBBase candSndABase candFstABase predBufBase rowEndBase rowStartBase
        ranksBase orderBase stampsBase indegBase csrArenaWords; omega
    obtain ⟨u8, st36_44, pc44, hd44, k44⟩ := copyPair_steps (code := code) (input := input)
      (s := u) (entry := 36) (tmp := rTmp) (val := rA) (srcFst := rFstA) (srcSnd := rSndA)
      (srcIdx := rP) (dstFst := rFstB) (dstSnd := rSndB) (dstIdx := rOut)
      rfl rfl rfl rfl rfl rfl rfl rfl hupc (by omega)
      (by decide) (by decide) hb1 hb2 hr1 hr2 hne12
    -- 44: add rP rP rOne
    obtain ⟨u9, st44, pc45, r45, k45, d45⟩ := step_add15_at (code := code) (input := input)
      (s := u8) (d := rP) (lhs := rP) (rhs := rOne) (by rw [pc44]; rfl) (by omega)
    -- 45: add rOut rOut rOne
    obtain ⟨u10, st45, pc46, r46, k46, d46⟩ := step_add15_at (code := code) (input := input)
      (s := u9) (d := rOut) (lhs := rOut) (rhs := rOne) (by rw [show u9.pc = 45 by omega]; rfl) (by omega)
    -- 46: goto 23
    let t : State L := { u10 with pc := 23 }
    have st46 : step code input u10 = some (.next t) :=
      step_goto_at (code := code) (input := input) (s := u10) (target := 23)
        (by rw [show u10.pc = 46 by omega]; rfl) (by omega)
    have hsdsU : u.data.size = workCap := u.data_size
    have hsdsS : s.data.size = workCap := s.data_size
    have hdst1Lt : candFstBBase H.vertexCount H.arcCount + out < u.data.size := by
      rw [hsdsU, ← inv.fstBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb1
    have hdst1S : candFstBBase H.vertexCount H.arcCount + out < s.data.size := by
      rw [hsdsS, ← inv.fstBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb1
    have hdst2S : candSndBBase H.vertexCount H.arcCount + out <
        (s.data.set (candFstBBase H.vertexCount H.arcCount + out) w1 hdst1S).size := by
      rw [Array.size_set, hsdsS, ← inv.sndBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb2
    have hdataEq : t.data =
        (s.data.set (candFstBBase H.vertexCount H.arcCount + out) w1 hdst1S).set
          (candSndBBase H.vertexCount H.arcCount + out) w2 hdst2S := by
      change u10.data = _
      rw [d46, d45]
      have h1 : (reg u rFstB).val + (reg u rOut).val = candFstBBase H.vertexCount H.arcCount + out := by
        rw [hukeep _ (by decide), hukeep _ (by decide), inv.fstBVal, inv.outVal]
      have h2 : (reg u rSndB).val + (reg u rOut).val = candSndBBase H.vertexCount H.arcCount + out := by
        rw [hukeep _ (by decide), hukeep _ (by decide), inv.sndBVal, inv.outVal]
      have hsub := hd44 (by rw [h1]; exact hdst1Lt) (by rw [Array.size_set, hsdsU]; exact hb2)
      have ha1 := array_set_congr (v := w1) (w := w1) (by rw [h1]; exact hdst1Lt) hdst1S hudata h1 rfl
      exact hsub.trans (array_set_congr (v := w2) (w := w2) (by rw [Array.size_set, hsdsU]; exact hb2) hdst2S ha1 h2 rfl)
    have hkeep (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rQ] : List (Fin 15))) :
        reg t r = reg s r := by
      have hneq : r ≠ rTmp ∧ r ≠ rA ∧ r ≠ rP ∧ r ≠ rOut := by revert r hr; decide
      have hmem12 : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact (k46 r hneq.2.2.2).trans ((k45 r hneq.2.2.1).trans ((k44 r hneq.1 hneq.2.1).trans (hukeep r hmem12)))
    have hpNext : (reg t rP).val = p + 1 := by
      change (reg u10 rP).val = _
      rw [k46 _ (by decide), r45]
      have hP8 : (reg u8 rP).val = p := by
        rw [k44 _ (by decide) (by decide), hukeep _ (by decide), inv.pVal]
      have hO8 : (reg u8 rOne).val = 1 := by
        rw [k44 _ (by decide) (by decide), hukeep _ (by decide), inv.one]
      rw [PaperB.WordOps.add_no_wrap _ _ (by rw [hP8, hO8]; omega), hP8, hO8]
    have hOutNext : (reg t rOut).val = out + 1 := by
      change (reg u10 rOut).val = _
      rw [r46]
      have hOut9 : (reg u9 rOut).val = out := by
        rw [k45 _ (by decide), k44 _ (by decide) (by decide), hukeep _ (by decide), inv.outVal]
      have hO9 : (reg u9 rOne).val = 1 := by
        rw [k45 _ (by decide), k44 _ (by decide) (by decide), hukeep _ (by decide), inv.one]
      rw [PaperB.WordOps.add_no_wrap _ _ (by rw [hOut9, hO9]; omega), hOut9, hO9]
    have hIdxNe : candFstBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + out := by
      unfold candSndBBase candFstBBase; omega
    have hNewPair : MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) out (cur[p]'hplt) := by
      constructor
      · rw [hdataEq, Array.getElem?_set_ne _ (Ne.symm hIdxNe), Array.getElem?_set_self, Option.map_some, hw1v]
      · rw [hdataEq, Array.getElem?_set_self, Option.map_some, hw2v]
    have hOldPair : ∀ idx, idx < out → ∀ z,
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx z ↔
        MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx z := by
      intro idx hidx z
      have hne1 : candFstBBase H.vertexCount H.arcCount + out ≠ candFstBBase H.vertexCount H.arcCount + idx := by omega
      have hne2 : candSndBBase H.vertexCount H.arcCount + out ≠ candFstBBase H.vertexCount H.arcCount + idx := by
        unfold candSndBBase candFstBBase; omega
      have hne3 : candFstBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + idx := by
        unfold candSndBBase candFstBBase; omega
      have hne4 : candSndBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + idx := by omega
      simp only [MemPairAt, hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1,
        Array.getElem?_set_ne _ hne4, Array.getElem?_set_ne _ hne3]
    have memAtEq : ∀ idx x y,
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx x →
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx y →
        x = y := by
      intro idx x y hx hy
      have h1 := hx.1.symm.trans hy.1
      have h2 := hx.2.symm.trans hy.2
      exact Prod.ext (Option.some.inj h1) (Option.some.inj h2)
    refine ⟨t, st36_44.append (.cons st44 (.cons st45 (.cons st46 (.zero t)))), rfl,
      by rw [hkeep _ (by decide), inv.zero], by rw [hkeep _ (by decide), inv.one],
      by rw [hkeep _ (by decide), inv.kVal], by rw [hkeep _ (by decide), inv.fstAVal],
      by rw [hkeep _ (by decide), inv.sndAVal], by rw [hkeep _ (by decide), inv.fstBVal],
      by rw [hkeep _ (by decide), inv.sndBVal], by rw [hkeep _ (by decide), inv.midVal],
      by rw [hkeep _ (by decide), inv.endVal], hpNext, by rw [hkeep _ (by decide), inv.qVal],
      hOutNext, ⟨Nat.le_trans inv.pRange.1 (Nat.le_succ p), hp⟩, inv.qRange,
      by have := inv.outEq; have := inv.pRange.1; omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro idx hlo hlt
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | rfl
      · obtain ⟨x, hx⟩ := inv.outPairs idx hlo hlt'
        exact ⟨x, (hOldPair idx hlt' x).mpr hx⟩
      · exact ⟨cur[p]'hplt, hNewPair⟩
    · intro u1 v1 x y hu1 huv hv1 hx hy
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv1) with hv1' | rfl
      · have hu1' : u1 < out := Nat.lt_of_le_of_lt huv hv1'
        exact inv.outSorted u1 v1 x y hu1 huv hv1' ((hOldPair u1 hu1' x).mp hx) ((hOldPair v1 hv1' y).mp hy)
      · have hy' : y = cur[p]'hplt := memAtEq v1 y _ hy hNewPair
        subst hy'
        rcases Nat.lt_or_eq_of_le huv with huv' | rfl
        · exact inv.outLeP u1 x p hplt hu1 huv' (Nat.le_refl p) hp
            ((hOldPair u1 huv' x).mp hx)
        · have hx' : x = cur[p]'hplt := memAtEq u1 x _ hx hNewPair
          subst hx'
          exact keyLe_refl _
    · intro u1 x p1 hp1 hu1 hu1o hp1ge hp1lt hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu1o) with hu1o' | rfl
      · exact inv.outLeP u1 x p1 hp1 hu1 hu1o' (Nat.le_trans (Nat.le_succ p) hp1ge) hp1lt
          ((hOldPair u1 hu1o' x).mp hx)
      · have hx' : x = cur[p]'hplt := memAtEq u1 x _ hx hNewPair
        subst hx'
        exact hLeftSorted p p1 hplt hp1 inv.pRange.1 (Nat.le_of_succ_le hp1ge) hp1lt
    · intro u1 x q1 hq1 hu1 hu1o hq1ge hq1lt hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu1o) with hu1o' | rfl
      · exact inv.outLeQ u1 x q1 hq1 hu1 hu1o' hq1ge hq1lt ((hOldPair u1 hu1o' x).mp hx)
      · have hx' : x = cur[p]'hplt := memAtEq u1 x _ hx hNewPair
        subst hx'
        exact hleQ q1 hq1 hq1ge hq1lt
    · intro z
      rw [← inv.memPart z]
      constructor
      · rintro (⟨idx, hidx1, hidx2, hz⟩ | ⟨p1, hp1, hp1a, hp1b, hz⟩ | ⟨q1, hq1, hq1a, hq1b, hz⟩)
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx2) with hidx' | rfl
          · exact Or.inl ⟨idx, hidx1, hidx', (hOldPair idx hidx' z).mp hz⟩
          · have hz' : z = cur[p]'hplt := memAtEq idx z _ hz hNewPair
            exact Or.inr (Or.inl ⟨p, hplt, Nat.le_refl p, hp, hz'.symm⟩)
        · exact Or.inr (Or.inl ⟨p1, hp1, Nat.le_trans (Nat.le_succ p) hp1a, hp1b, hz⟩)
        · exact Or.inr (Or.inr ⟨q1, hq1, hq1a, hq1b, hz⟩)
      · rintro (⟨idx, hidx1, hidx2, hz⟩ | ⟨p1, hp1, hp1a, hp1b, hz⟩ | ⟨q1, hq1, hq1a, hq1b, hz⟩)
        · exact Or.inl ⟨idx, hidx1, Nat.lt_succ_of_lt hidx2, (hOldPair idx hidx2 z).mpr hz⟩
        · rcases Nat.lt_or_eq_of_le hp1a with hp1gt | rfl
          · exact Or.inr (Or.inl ⟨p1, hp1, hp1gt, hp1b, hz⟩)
          · exact Or.inl ⟨out, Nat.le_trans inv.pRange.1 (by have := inv.outEq; have := inv.qRange.1; omega),
              Nat.lt_succ_self out, by rw [hz] at hNewPair; exact hNewPair⟩
        · exact Or.inr (Or.inr ⟨q1, hq1, hq1a, hq1b, hz⟩)
    · intro j hjF hjS
      have hlo_out : lo ≤ out := Nat.le_trans inv.pRange.1 (by have := inv.outEq; have := inv.qRange.1; omega)
      have hne1 : candFstBBase H.vertexCount H.arcCount + out ≠ j := by
        rcases hjF with hjF | hjF <;> omega
      have hne2 : candSndBBase H.vertexCount H.arcCount + out ≠ j := by
        rcases hjS with hjS | hjS <;> omega
      rw [hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
      exact inv.frameB j hjF hjS
  -- Take Q helper starting from pc = 47
  have takeQBlock : ∀ (u : State L), u.pc = 47 → u.data = s.data →
      (∀ r : Fin 15, r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15)) →
        reg u r = reg s r) →
      (hq : q < end_) →
      (hleP : ∀ p' (hp' : p' < cur.length), p ≤ p' → p' < mid →
        keyLe (cur[q]'(by omega)) (cur[p']'hp')) →
      ∃ t : State L, Steps code input 11 u t ∧
        MergeInv H cur origB lo mid end_ p (q + 1) (out + 1) t := by
    intro u hupc hudata hukeep hq hleP
    have hqlt : q < cur.length := by omega
    obtain ⟨⟨w1, hw1, hw1v⟩, ⟨w2, hw2, hw2v⟩⟩ := memPairAt_word (hInACur ⟨q, hqlt⟩)
    have hr1 : u.data[(reg u rFstA).val + (reg u rQ).val]? = some w1 := by
      rw [hudata, hukeep _ (by decide), hukeep _ (by decide), inv.fstAVal, inv.qVal]; exact hw1
    have hr2 : u.data[(reg u rSndA).val + (reg u rQ).val]? = some w2 := by
      rw [hudata, hukeep _ (by decide), hukeep _ (by decide), inv.sndAVal, inv.qVal]; exact hw2
    have hb1 : (reg u rFstB).val + (reg u rOut).val < workCap := by
      rw [hukeep _ (by decide), hukeep _ (by decide)]; exact hFstBBound
    have hb2 : (reg u rSndB).val + (reg u rOut).val < workCap := by
      rw [hukeep _ (by decide), hukeep _ (by decide)]; exact hSndBBound
    have hne12 : (reg u rFstB).val + (reg u rOut).val ≠ (reg u rSndA).val + (reg u rQ).val := by
      rw [hukeep _ (by decide), hukeep _ (by decide), hukeep _ (by decide), hukeep _ (by decide),
          inv.fstBVal, inv.outVal, inv.sndAVal, inv.qVal]
      unfold candFstBBase candSndABase candFstABase predBufBase rowEndBase rowStartBase
        ranksBase orderBase stampsBase indegBase csrArenaWords; omega
    obtain ⟨u8, st47_55, pc55, hd55, k55⟩ := copyPair_steps (code := code) (input := input)
      (s := u) (entry := 47) (tmp := rTmp) (val := rA) (srcFst := rFstA) (srcSnd := rSndA)
      (srcIdx := rQ) (dstFst := rFstB) (dstSnd := rSndB) (dstIdx := rOut)
      rfl rfl rfl rfl rfl rfl rfl rfl hupc (by omega)
      (by decide) (by decide) hb1 hb2 hr1 hr2 hne12
    obtain ⟨u9, st55, pc56, r56, k56, d56⟩ := step_add15_at (code := code) (input := input)
      (s := u8) (d := rQ) (lhs := rQ) (rhs := rOne) (by rw [pc55]; rfl) (by omega)
    obtain ⟨u10, st56, pc57, r57, k57, d57⟩ := step_add15_at (code := code) (input := input)
      (s := u9) (d := rOut) (lhs := rOut) (rhs := rOne) (by rw [show u9.pc = 56 by omega]; rfl) (by omega)
    let t : State L := { u10 with pc := 23 }
    have st57 : step code input u10 = some (.next t) :=
      step_goto_at (code := code) (input := input) (s := u10) (target := 23)
        (by rw [show u10.pc = 57 by omega]; rfl) (by omega)
    have hsdsU : u.data.size = workCap := u.data_size
    have hsdsS : s.data.size = workCap := s.data_size
    have hdst1Lt : candFstBBase H.vertexCount H.arcCount + out < u.data.size := by
      rw [hsdsU, ← inv.fstBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb1
    have hdst1S : candFstBBase H.vertexCount H.arcCount + out < s.data.size := by
      rw [hsdsS, ← inv.fstBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb1
    have hdst2S : candSndBBase H.vertexCount H.arcCount + out <
        (s.data.set (candFstBBase H.vertexCount H.arcCount + out) w1 hdst1S).size := by
      rw [Array.size_set, hsdsS, ← inv.sndBVal, ← inv.outVal, ← hukeep _ (by decide), ← hukeep _ (by decide)]
      exact hb2
    have hdataEq : t.data =
        (s.data.set (candFstBBase H.vertexCount H.arcCount + out) w1 hdst1S).set
          (candSndBBase H.vertexCount H.arcCount + out) w2 hdst2S := by
      change u10.data = _
      rw [d57, d56]
      have h1 : (reg u rFstB).val + (reg u rOut).val = candFstBBase H.vertexCount H.arcCount + out := by
        rw [hukeep _ (by decide), hukeep _ (by decide), inv.fstBVal, inv.outVal]
      have h2 : (reg u rSndB).val + (reg u rOut).val = candSndBBase H.vertexCount H.arcCount + out := by
        rw [hukeep _ (by decide), hukeep _ (by decide), inv.sndBVal, inv.outVal]
      have hsub := hd55 (by rw [h1]; exact hdst1Lt) (by rw [Array.size_set, hsdsU]; exact hb2)
      have ha1 := array_set_congr (v := w1) (w := w1) (by rw [h1]; exact hdst1Lt) hdst1S hudata h1 rfl
      exact hsub.trans (array_set_congr (v := w2) (w := w2) (by rw [Array.size_set, hsdsU]; exact hb2) hdst2S ha1 h2 rfl)
    have hkeep (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP] : List (Fin 15))) :
        reg t r = reg s r := by
      have hneq : r ≠ rTmp ∧ r ≠ rA ∧ r ≠ rQ ∧ r ≠ rOut := by revert r hr; decide
      have hmem12 : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact (k57 r hneq.2.2.2).trans ((k56 r hneq.2.2.1).trans ((k55 r hneq.1 hneq.2.1).trans (hukeep r hmem12)))
    have hqNext : (reg t rQ).val = q + 1 := by
      change (reg u10 rQ).val = _
      rw [k57 _ (by decide), r56]
      have hQ8 : (reg u8 rQ).val = q := by
        rw [k55 _ (by decide) (by decide), hukeep _ (by decide), inv.qVal]
      have hO8 : (reg u8 rOne).val = 1 := by
        rw [k55 _ (by decide) (by decide), hukeep _ (by decide), inv.one]
      rw [PaperB.WordOps.add_no_wrap _ _ (by rw [hQ8, hO8]; omega), hQ8, hO8]
    have hOutNext : (reg t rOut).val = out + 1 := by
      change (reg u10 rOut).val = _
      rw [r57]
      have hOut9 : (reg u9 rOut).val = out := by
        rw [k56 _ (by decide), k55 _ (by decide) (by decide), hukeep _ (by decide), inv.outVal]
      have hO9 : (reg u9 rOne).val = 1 := by
        rw [k56 _ (by decide), k55 _ (by decide) (by decide), hukeep _ (by decide), inv.one]
      rw [PaperB.WordOps.add_no_wrap _ _ (by rw [hOut9, hO9]; omega), hOut9, hO9]
    have hIdxNe : candFstBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + out := by
      unfold candSndBBase candFstBBase; omega
    have hNewPair : MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) out (cur[q]'hqlt) := by
      constructor
      · rw [hdataEq, Array.getElem?_set_ne _ (Ne.symm hIdxNe), Array.getElem?_set_self, Option.map_some, hw1v]
      · rw [hdataEq, Array.getElem?_set_self, Option.map_some, hw2v]
    have hOldPair : ∀ idx, idx < out → ∀ z,
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx z ↔
        MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx z := by
      intro idx hidx z
      have hne1 : candFstBBase H.vertexCount H.arcCount + out ≠ candFstBBase H.vertexCount H.arcCount + idx := by omega
      have hne2 : candSndBBase H.vertexCount H.arcCount + out ≠ candFstBBase H.vertexCount H.arcCount + idx := by
        unfold candSndBBase candFstBBase; omega
      have hne3 : candFstBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + idx := by
        unfold candSndBBase candFstBBase; omega
      have hne4 : candSndBBase H.vertexCount H.arcCount + out ≠ candSndBBase H.vertexCount H.arcCount + idx := by omega
      simp only [MemPairAt, hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1,
        Array.getElem?_set_ne _ hne4, Array.getElem?_set_ne _ hne3]
    have memAtEq : ∀ idx x y,
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx x →
        MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx y →
        x = y := by
      intro idx x y hx hy
      exact Prod.ext (Option.some.inj (hx.1.symm.trans hy.1)) (Option.some.inj (hx.2.symm.trans hy.2))
    refine ⟨t, st47_55.append (.cons st55 (.cons st56 (.cons st57 (.zero t)))), rfl,
      by rw [hkeep _ (by decide), inv.zero], by rw [hkeep _ (by decide), inv.one],
      by rw [hkeep _ (by decide), inv.kVal], by rw [hkeep _ (by decide), inv.fstAVal],
      by rw [hkeep _ (by decide), inv.sndAVal], by rw [hkeep _ (by decide), inv.fstBVal],
      by rw [hkeep _ (by decide), inv.sndBVal], by rw [hkeep _ (by decide), inv.midVal],
      by rw [hkeep _ (by decide), inv.endVal], by rw [hkeep _ (by decide), inv.pVal],
      hqNext, hOutNext, inv.pRange, ⟨Nat.le_trans inv.qRange.1 (Nat.le_succ q), hq⟩,
      by have := inv.outEq; have := inv.qRange.1; omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro idx hlo hlt
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | rfl
      · obtain ⟨x, hx⟩ := inv.outPairs idx hlo hlt'
        exact ⟨x, (hOldPair idx hlt' x).mpr hx⟩
      · exact ⟨cur[q]'hqlt, hNewPair⟩
    · intro u1 v1 x y hu1 huv hv1 hx hy
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv1) with hv1' | rfl
      · have hu1' : u1 < out := Nat.lt_of_le_of_lt huv hv1'
        exact inv.outSorted u1 v1 x y hu1 huv hv1' ((hOldPair u1 hu1' x).mp hx) ((hOldPair v1 hv1' y).mp hy)
      · have hy' : y = cur[q]'hqlt := memAtEq v1 y _ hy hNewPair
        subst hy'
        rcases Nat.lt_or_eq_of_le huv with huv' | rfl
        · exact inv.outLeQ u1 x q hqlt hu1 huv' (Nat.le_refl q) hq
            ((hOldPair u1 huv' x).mp hx)
        · have hx' : x = cur[q]'hqlt := memAtEq u1 x _ hx hNewPair
          subst hx'
          exact keyLe_refl _
    · intro u1 x p1 hp1 hu1 hu1o hp1ge hp1lt hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu1o) with hu1o' | rfl
      · exact inv.outLeP u1 x p1 hp1 hu1 hu1o' hp1ge hp1lt ((hOldPair u1 hu1o' x).mp hx)
      · have hx' : x = cur[q]'hqlt := memAtEq u1 x _ hx hNewPair
        subst hx'
        exact hleP p1 hp1 hp1ge hp1lt
    · intro u1 x q1 hq1 hu1 hu1o hq1ge hq1lt hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu1o) with hu1o' | rfl
      · exact inv.outLeQ u1 x q1 hq1 hu1 hu1o' (Nat.le_trans (Nat.le_succ q) hq1ge) hq1lt
          ((hOldPair u1 hu1o' x).mp hx)
      · have hx' : x = cur[q]'hqlt := memAtEq u1 x _ hx hNewPair
        subst hx'
        exact hRightSorted q q1 hqlt hq1 inv.qRange.1 (Nat.le_of_succ_le hq1ge) hq1lt
    · intro z
      rw [← inv.memPart z]
      constructor
      · rintro (⟨idx, hidx1, hidx2, hz⟩ | ⟨p1, hp1, hp1a, hp1b, hz⟩ | ⟨q1, hq1, hq1a, hq1b, hz⟩)
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx2) with hidx' | rfl
          · exact Or.inl ⟨idx, hidx1, hidx', (hOldPair idx hidx' z).mp hz⟩
          · have hz' : z = cur[q]'hqlt := memAtEq idx z _ hz hNewPair
            exact Or.inr (Or.inr ⟨q, hqlt, Nat.le_refl q, hq, hz'.symm⟩)
        · exact Or.inr (Or.inl ⟨p1, hp1, hp1a, hp1b, hz⟩)
        · exact Or.inr (Or.inr ⟨q1, hq1, Nat.le_trans (Nat.le_succ q) hq1a, hq1b, hz⟩)
      · rintro (⟨idx, hidx1, hidx2, hz⟩ | ⟨p1, hp1, hp1a, hp1b, hz⟩ | ⟨q1, hq1, hq1a, hq1b, hz⟩)
        · exact Or.inl ⟨idx, hidx1, Nat.lt_succ_of_lt hidx2, (hOldPair idx hidx2 z).mpr hz⟩
        · exact Or.inr (Or.inl ⟨p1, hp1, hp1a, hp1b, hz⟩)
        · rcases Nat.lt_or_eq_of_le hq1a with hq1gt | rfl
          · exact Or.inr (Or.inr ⟨q1, hq1, hq1gt, hq1b, hz⟩)
          · exact Or.inl ⟨out, Nat.le_trans inv.pRange.1 (by have := inv.outEq; have := inv.qRange.1; omega),
              Nat.lt_succ_self out, by rw [hz] at hNewPair; exact hNewPair⟩
    · intro j hjF hjS
      have hlo_out : lo ≤ out := Nat.le_trans inv.pRange.1 (by have := inv.outEq; have := inv.qRange.1; omega)
      have hne1 : candFstBBase H.vertexCount H.arcCount + out ≠ j := by
        rcases hjF with hjF | hjF <;> omega
      have hne2 : candSndBBase H.vertexCount H.arcCount + out ≠ j := by
        rcases hjS with hjS | hjS <;> omega
      rw [hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
      exact inv.frameB j hjF hjS
  -- Main dispatch from pc = 23
  by_cases hp : p < mid
  · have b23 : step code input s = some (.next { s with pc := 24 }) :=
      step_branchLt_true (by rw [inv.pc]; rfl) (by rw [inv.pVal, inv.midVal]; exact hp) (by omega)
    let s24 : State L := { s with pc := 24 }
    by_cases hq : q < end_
    · have b24 : step code input s24 = some (.next { s24 with pc := 25 }) :=
        step_branchLt_true rfl (by change (reg s rQ).val < (reg s rEnd).val; rw [inv.qVal, inv.endVal]; exact hq) (by omega)
      -- 25..28: load fstA[p] -> rA, fstA[q] -> rB
      have hplt : p < cur.length := by omega
      have hqlt : q < cur.length := by omega
      obtain ⟨⟨wp1, hwp1, hwp1v⟩, ⟨wp2, hwp2, hwp2v⟩⟩ := memPairAt_word (hInACur ⟨p, hplt⟩)
      obtain ⟨⟨wq1, hwq1, hwq1v⟩, ⟨wq2, hwq2, hwq2v⟩⟩ := memPairAt_word (hInACur ⟨q, hqlt⟩)
      have hbPA1 : (reg { s24 with pc := 25 } rFstA).val + (reg { s24 with pc := 25 } rP).val < workCap := by
        change (reg s rFstA).val + (reg s rP).val < workCap
        rw [inv.fstAVal, inv.pVal]; unfold candFstABase predBufBase rowEndBase rowStartBase
          ranksBase orderBase stampsBase indegBase csrArenaWords; omega
      obtain ⟨s27, st25_27, pc27, r27, k27, d27⟩ := loadAtOffset_steps (code := code) (input := input)
        (s := { s24 with pc := 25 }) (entry := 25) (tmp := rTmp) (dst := rA) (base := rFstA) (idx := rP)
        (w := wp1) rfl rfl rfl (by omega) hbPA1
        (by change s.data[(reg s rFstA).val + (reg s rP).val]? = _; rw [inv.fstAVal, inv.pVal]; exact hwp1)
      have hbQA1 : (reg s27 rFstA).val + (reg s27 rQ).val < workCap := by
        rw [k27 _ (by decide) (by decide), k27 _ (by decide) (by decide)]
        change (reg s rFstA).val + (reg s rQ).val < workCap
        rw [inv.fstAVal, inv.qVal]; unfold candFstABase predBufBase rowEndBase rowStartBase
          ranksBase orderBase stampsBase indegBase csrArenaWords; omega
      obtain ⟨s29, st27_29, pc29, r29, k29, d29⟩ := loadAtOffset_steps (code := code) (input := input)
        (s := s27) (entry := 27) (tmp := rTmp) (dst := rB) (base := rFstA) (idx := rQ)
        (w := wq1) rfl rfl pc27 (by omega) hbQA1
        (by rw [d27, k27 _ (by decide) (by decide), k27 _ (by decide) (by decide)]
            change s.data[(reg s rFstA).val + (reg s rQ).val]? = _; rw [inv.fstAVal, inv.qVal]; exact hwq1)
      have keep29 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15))) :
          reg s29 r = reg s r := by
        have hneq : r ≠ rTmp ∧ r ≠ rA ∧ r ≠ rB := by revert r hr; decide
        exact (k29 r hneq.1 hneq.2.2).trans (k27 r hneq.1 hneq.2.1)
      have s29A : (reg s29 rA).val = (cur[p]'hplt).1 := by rw [k29 _ (by decide) (by decide), r27, hwp1v]
      have s29B : (reg s29 rB).val = (cur[q]'hqlt).1 := by rw [r29, hwq1v]
      have s29Data : s29.data = s.data := d29.trans d27
      by_cases hlt1 : (cur[p]'hplt).1 < (cur[q]'hqlt).1
      · have b29 : step code input s29 = some (.next { s29 with pc := 36 }) :=
          step_branchLt_true (by rw [pc29]; rfl) (by rw [s29A, s29B]; exact hlt1) (by omega)
        obtain ⟨t, st36, inv'⟩ := takePBlock { s29 with pc := 36 } rfl s29Data keep29 hp
          (fun q1 hq1 hq1ge hq1lt => keyLe_trans (Or.inl hlt1) (hRightSorted q q1 hqlt hq1 inv.qRange.1 hq1ge hq1lt))
        exact ⟨p + 1, q, out + 1, t, 2 + 4 + 1 + 11, by omega, by omega,
          .cons b23 (.cons b24 (st25_27.append (st27_29.append (.cons b29 st36)))), inv'⟩
      · have b29 : step code input s29 = some (.next { s29 with pc := 30 }) :=
          step_branchLt_false (by rw [pc29]; rfl) (by rw [s29A, s29B]; omega) (by omega)
        let s30 : State L := { s29 with pc := 30 }
        by_cases hgt1 : (cur[q]'hqlt).1 < (cur[p]'hplt).1
        · have b30 : step code input s30 = some (.next { s30 with pc := 47 }) :=
            step_branchLt_true rfl (by change (reg s29 rB).val < (reg s29 rA).val; rw [s29A, s29B]; exact hgt1) (by omega)
          obtain ⟨t, st47, inv'⟩ := takeQBlock { s30 with pc := 47 } rfl s29Data keep29 hq
            (fun p1 hp1 hp1ge hp1lt => keyLe_trans (Or.inl hgt1) (hLeftSorted p p1 hplt hp1 inv.pRange.1 hp1ge hp1lt))
          exact ⟨p, q + 1, out + 1, t, 2 + 4 + 2 + 11, by omega, by omega,
            .cons b23 (.cons b24 (st25_27.append (st27_29.append (.cons b29 (.cons b30 st47))))), inv'⟩
        · have heq1 : (cur[p]'hplt).1 = (cur[q]'hqlt).1 := by omega
          have b30 : step code input s30 = some (.next { s30 with pc := 31 }) :=
            step_branchLt_false rfl (by change (reg s29 rA).val ≤ (reg s29 rB).val; rw [s29A, s29B]; omega) (by omega)
          let s31 : State L := { s30 with pc := 31 }
          have hbPA2 : (reg s31 rSndA).val + (reg s31 rP).val < workCap := by
            change (reg s29 rSndA).val + (reg s29 rP).val < workCap
            rw [keep29 _ (by decide), keep29 _ (by decide), inv.sndAVal, inv.pVal]
            unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase
              ranksBase orderBase stampsBase indegBase csrArenaWords; omega
          obtain ⟨s33, st31_33, pc33, r33, k33, d33⟩ := loadAtOffset_steps (code := code) (input := input)
            (s := s31) (entry := 31) (tmp := rTmp) (dst := rA) (base := rSndA) (idx := rP)
            (w := wp2) rfl rfl rfl (by omega) hbPA2
            (by change s30.data[(reg s29 rSndA).val + (reg s29 rP).val]? = _
                rw [show s30.data = s.data from s29Data, keep29 _ (by decide), keep29 _ (by decide), inv.sndAVal, inv.pVal]
                exact hwp2)
          have hbQA2 : (reg s33 rSndA).val + (reg s33 rQ).val < workCap := by
            rw [k33 _ (by decide) (by decide), k33 _ (by decide) (by decide)]
            change (reg s29 rSndA).val + (reg s29 rQ).val < workCap
            rw [keep29 _ (by decide), keep29 _ (by decide), inv.sndAVal, inv.qVal]
            unfold candSndABase candFstABase predBufBase rowEndBase rowStartBase
              ranksBase orderBase stampsBase indegBase csrArenaWords; omega
          obtain ⟨s35, st33_35, pc35, r35, k35, d35⟩ := loadAtOffset_steps (code := code) (input := input)
            (s := s33) (entry := 33) (tmp := rTmp) (dst := rB) (base := rSndA) (idx := rQ)
            (w := wq2) rfl rfl pc33 (by omega) hbQA2
            (by rw [d33, k33 _ (by decide) (by decide), k33 _ (by decide) (by decide)]
                change s31.data[(reg s29 rSndA).val + (reg s29 rQ).val]? = _
                rw [show s31.data = s.data from s29Data,
                    keep29 _ (by decide), keep29 _ (by decide), inv.sndAVal, inv.qVal]; exact hwq2)
          have keep35 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rMid, rEnd, rP, rQ, rOut] : List (Fin 15))) :
              reg s35 r = reg s r := by
            have hneq : r ≠ rTmp ∧ r ≠ rA ∧ r ≠ rB := by revert r hr; decide
            exact (k35 r hneq.1 hneq.2.2).trans ((k33 r hneq.1 hneq.2.1).trans (keep29 r hr))
          have s35A : (reg s35 rA).val = (cur[p]'hplt).2 := by rw [k35 _ (by decide) (by decide), r33, hwp2v]
          have s35B : (reg s35 rB).val = (cur[q]'hqlt).2 := by rw [r35, hwq2v]
          have s35Data : s35.data = s.data := d35.trans (d33.trans s29Data)
          by_cases hlt2 : (cur[q]'hqlt).2 < (cur[p]'hplt).2
          · have b35 : step code input s35 = some (.next { s35 with pc := 47 }) :=
              step_branchLt_true (by rw [pc35]; rfl) (by rw [s35A, s35B]; exact hlt2) (by omega)
            obtain ⟨t, st47, inv'⟩ := takeQBlock { s35 with pc := 47 } rfl s35Data keep35 hq
              (fun p1 hp1 hp1ge hp1lt => keyLe_trans (Or.inr ⟨heq1.symm, Nat.le_of_lt hlt2⟩)
                (hLeftSorted p p1 hplt hp1 inv.pRange.1 hp1ge hp1lt))
            exact ⟨p, q + 1, out + 1, t, 2 + 4 + 2 + 4 + 1 + 11, by omega, by omega,
              .cons b23 (.cons b24 (st25_27.append (st27_29.append
                (.cons b29 (.cons b30 (st31_33.append (st33_35.append (.cons b35 st47)))))))), inv'⟩
          · have b35 : step code input s35 = some (.next { s35 with pc := 36 }) :=
              step_branchLt_false (by rw [pc35]; rfl) (by rw [s35A, s35B]; omega) (by omega)
            obtain ⟨t, st36, inv'⟩ := takePBlock { s35 with pc := 36 } rfl s35Data keep35 hp
              (fun q1 hq1 hq1ge hq1lt => keyLe_trans (Or.inr ⟨heq1, Nat.le_of_not_lt hlt2⟩)
                (hRightSorted q q1 hqlt hq1 inv.qRange.1 hq1ge hq1lt))
            exact ⟨p + 1, q, out + 1, t, 2 + 4 + 2 + 4 + 1 + 11, by omega, by omega,
              .cons b23 (.cons b24 (st25_27.append (st27_29.append
                (.cons b29 (.cons b30 (st31_33.append (st33_35.append (.cons b35 st36)))))))), inv'⟩
    · have hqeq : q = end_ := by have := inv.qRange.2; omega
      have b24 : step code input s24 = some (.next { s24 with pc := 36 }) :=
        step_branchLt_false rfl (by change (reg s rEnd).val ≤ (reg s rQ).val; rw [inv.qVal, inv.endVal, hqeq]; exact Nat.le_refl _) (by omega)
      obtain ⟨t, st36, inv'⟩ := takePBlock { s24 with pc := 36 } rfl rfl (fun _ _ => rfl) hp
        (fun q1 _ hq1ge hq1lt => by omega)
      exact ⟨p + 1, q, out + 1, t, 2 + 11, by omega, by omega,
        .cons b23 (.cons b24 st36), inv'⟩
  · have hpeq : p = mid := by have := inv.pRange.2; omega
    have hq : q < end_ := by
      rcases hrem with h | h
      · exact False.elim (hp h)
      · exact h
    have b23 : step code input s = some (.next { s with pc := 58 }) :=
      step_branchLt_false (by rw [inv.pc]; rfl) (by rw [inv.pVal, inv.midVal, hpeq]; exact Nat.le_refl _) (by omega)
    have b58 : step code input { s with pc := 58 } = some (.next { s with pc := 47 }) :=
      step_branchLt_true rfl (by change (reg s rQ).val < (reg s rEnd).val; rw [inv.qVal, inv.endVal]; exact hq) (by omega)
    obtain ⟨t, st47, inv'⟩ := takeQBlock { s with pc := 47 } rfl rfl (fun _ _ => rfl) hq
      (fun p1 _ hp1ge hp1lt => by omega)
    exact ⟨p, q + 1, out + 1, t, 2 + 11, by omega, by omega,
      .cons b23 (.cons b58 st47), inv'⟩

private theorem mergeLoop_run {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} (hLen : cur.length ≤ H.vertexCount)
    {origB : Array (Word bits)}
    (hInA : ∀ j : Fin cur.length,
      MemPairAt origB (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt))
    {lo mid end_ : Nat} (hle1 : lo ≤ mid) (hle2 : mid ≤ end_) (hle3 : end_ ≤ cur.length)
    (hLeftSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      lo ≤ u → u ≤ v → v < mid → keyLe (cur[u]'hu) (cur[v]'hv))
    (hRightSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      mid ≤ u → u ≤ v → v < end_ → keyLe (cur[u]'hu) (cur[v]'hv)) :
    ∀ rem p q out (s : State L),
      (mid - p) + (end_ - q) = rem →
      MergeInv H cur origB lo mid end_ p q out s →
      ∃ t : State L, ∃ cost, cost ≤ 24 * rem ∧
        Steps (sortPhase hi hw h8).code input cost s t ∧
        MergeInv H cur origB lo mid end_ mid end_ end_ t := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro p q out s hrem inv
    by_cases hdone : rem = 0
    · have hp : p = mid := by have := inv.pRange.2; omega
      have hq : q = end_ := by have := inv.qRange.2; omega
      have hout : out = end_ := by have := inv.outEq; have := inv.pRange.1; have := inv.qRange.1; omega
      subst hp; subst hq; subst hout
      exact ⟨s, 0, by omega, .zero s, inv⟩
    · have hremPos : p < mid ∨ q < end_ := by
        have hp2 := inv.pRange.2; have hq2 := inv.qRange.2; omega
      obtain ⟨p', q', out', s', c1, hc1, hdec, st1, inv'⟩ :=
        mergeLoop_step h8 input hCap hLen hInA hle1 hle2 hle3 hLeftSorted hRightSorted p q out hremPos s inv
      obtain ⟨t, c2, hc2, st2, invEnd⟩ := ih ((mid - p') + (end_ - q')) (by omega) p' q' out' s' rfl inv'
      exact ⟨t, c1 + c2, by omega, st1.append st2, invEnd⟩

private structure ChunkInv (H : LabelledQuotient) (cur : List Key) (origA : Array (Word bits))
    (w i : Nat) (s : State L) : Prop where
  pc : s.pc = 11
  zero : (reg s rZero).val = 0
  one : (reg s rOne).val = 1
  kVal : (reg s rK).val = cur.length
  fstAVal : (reg s rFstA).val = candFstABase H.vertexCount H.arcCount
  sndAVal : (reg s rSndA).val = candSndABase H.vertexCount H.arcCount
  fstBVal : (reg s rFstB).val = candFstBBase H.vertexCount H.arcCount
  sndBVal : (reg s rSndB).val = candSndBBase H.vertexCount H.arcCount
  iVal : (reg s rI).val = i
  slotW : (s.data[slotWidth]?).map Fin.val = some w
  wPos : 1 ≤ w
  wLt : w < cur.length
  iLe : i ≤ cur.length
  iAlign : i = cur.length ∨ (2 * w) ∣ i
  bPairs : ∀ t, t < i → ∃ x : Key,
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) t x
  bSorted : ∀ u v x y, u ≤ v → v < i → u / (2 * w) = v / (2 * w) →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) u x →
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) v y →
    keyLe x y
  bMem : ∀ z : Key,
    (∃ t, t < i ∧ MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) t z) ↔
    (∃ t, ∃ ht : t < cur.length, t < i ∧ cur[t]'ht = z)
  frameChunk : ∀ j,
    (j < candFstBBase H.vertexCount H.arcCount ∨ candFstBBase H.vertexCount H.arcCount + i ≤ j) →
    (j < candSndBBase H.vertexCount H.arcCount ∨ candSndBBase H.vertexCount H.arcCount + i ≤ j) →
    s.data[j]? = origA[j]?

private theorem div_eq_two_mul {w c u : Nat} (hw : 1 ≤ w)
    (h1 : 2 * w * c ≤ u) (h2 : u < 2 * w * c + w) :
    u / w = 2 * c := by
  have hmul : w * (2 * c) = 2 * w * c := Nat.mul_comm w (2 * c) |>.trans (Nat.mul_right_comm 2 c w)
  have hu : u = (u - 2 * w * c) + w * (2 * c) := by omega
  rw [hu, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]

private theorem div_eq_two_mul_add_one {w c u : Nat} (hw : 1 ≤ w)
    (h1 : 2 * w * c + w ≤ u) (h2 : u < 2 * w * c + 2 * w) :
    u / w = 2 * c + 1 := by
  have hmul : w * (2 * c + 1) = 2 * w * c + w := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w (2 * c), Nat.mul_right_comm 2 c w]
  have hu : u = (u - (2 * w * c + w)) + w * (2 * c + 1) := by omega
  rw [hu, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]

private theorem seven_le_candFstBBase (n m : Nat) : 7 ≤ candFstBBase n m := by
  unfold candFstBBase candSndABase candFstABase predBufBase rowEndBase rowStartBase
    ranksBase orderBase stampsBase indegBase csrArenaWords
  omega

private theorem min_min_add_eq (i w k : Nat) (h : min (i + w) k + w < k) :
    min (min (i + w) k + w) k = i + 2 * w := by
  omega

private theorem chunkSetup_steps {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} {w : Nat} (hLen : cur.length ≤ H.vertexCount)
    {origA : Array (Word bits)} (i : Nat) (hiLt : i < cur.length)
    (s : State L) (inv : ChunkInv H cur origA w i s) :
    let mid := min (i + w) cur.length
    let end_ := min (mid + w) cur.length
    ∃ cPre, cPre ≤ 12 ∧ ∃ s23 : State L,
      Steps (sortPhase hi hw h8).code input cPre s s23 ∧
      s23.pc = 23 ∧
      (reg s23 rZero).val = 0 ∧ (reg s23 rOne).val = 1 ∧ (reg s23 rK).val = cur.length ∧
      (reg s23 rFstA).val = candFstABase H.vertexCount H.arcCount ∧
      (reg s23 rSndA).val = candSndABase H.vertexCount H.arcCount ∧
      (reg s23 rFstB).val = candFstBBase H.vertexCount H.arcCount ∧
      (reg s23 rSndB).val = candSndBBase H.vertexCount H.arcCount ∧
      (reg s23 rMid).val = mid ∧ (reg s23 rEnd).val = end_ ∧
      (reg s23 rP).val = i ∧ (reg s23 rQ).val = mid ∧ (reg s23 rOut).val = i ∧
      s23.data = s.data := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  have hwLt := inv.wLt
  let mid := min (i + w) cur.length
  let end_ := min (mid + w) cur.length
  have hmidRange : i ≤ mid ∧ mid ≤ cur.length := ⟨by omega, Nat.min_le_right _ _⟩
  have b11 : step code input s = some (.next { s with pc := 12 }) :=
    step_branchLt_true (by rw [inv.pc]; rfl) (by rw [inv.iVal, inv.kVal]; exact hiLt) (by omega)
  obtain ⟨wW, hwW, hwWv⟩ := word_mem_eq_of_map_val inv.slotW
  obtain ⟨s14, st12_14, pc14, r14, k14, d14⟩ := immLoad_steps (code := code) (input := input)
    (s := { s with pc := 12 }) (entry := 12) (tmp := rTmp) (dst := rW) (slot := ⟨6, by omega⟩) (w := wW)
    rfl rfl rfl (by omega) hwW
  obtain ⟨s15, st14, pc15, r15, k15, d15⟩ := step_add15_at (code := code) (input := input)
    (s := s14) (d := rMid) (lhs := rI) (rhs := rW) (by rw [pc14]; rfl) (by omega)
  have s14I : (reg s14 rI).val = i := by rw [k14 _ (by decide) (by decide)]; exact inv.iVal
  have s14W : (reg s14 rW).val = w := by rw [r14, hwWv]
  have s15Mid : (reg s15 rMid).val = i + w := by
    rw [r15, PaperB.WordOps.add_no_wrap _ _ (by rw [s14I, s14W]; omega), s14I, s14W]
  have s15K : (reg s15 rK).val = cur.length := by
    rw [k15 _ (by decide), k14 _ (by decide) (by decide)]; exact inv.kVal
  have hpc15 : s15.pc = 15 := by omega
  have hiLtB : i < H.vertexCount := Nat.lt_of_lt_of_le hiLt hLen
  have hwLtB : w < H.vertexCount := Nat.lt_of_lt_of_le hwLt hLen
  have hmidB : mid ≤ H.vertexCount := Nat.le_trans hmidRange.2 hLen
  have hMinMid : ∃ cM, cM ≤ 2 ∧ ∃ s17 : State L, Steps code input cM s15 s17 ∧ s17.pc = 17 ∧
      (reg s17 rMid).val = mid ∧ s17.data = s.data ∧
      (∀ r : Fin 15, r ≠ rMid → reg s17 r = reg s15 r) := by
    by_cases hm : i + w < cur.length
    · have b15 : step code input s15 = some (.next { s15 with pc := 17 }) :=
        step_branchLt_true (by rw [hpc15]; rfl) (by rw [s15Mid, s15K]; exact hm) (by omega)
      refine ⟨1, by omega, { s15 with pc := 17 }, .cons b15 (.zero _), rfl, ?_, ?_, fun _ _ => rfl⟩
      · change (reg s15 rMid).val = mid; rw [s15Mid]; omega
      · exact d15.trans d14
    · have b15 : step code input s15 = some (.next { s15 with pc := 16 }) :=
        step_branchLt_false (by rw [hpc15]; rfl) (by rw [s15Mid, s15K]; omega) (by omega)
      obtain ⟨s17, st16, pc17, r17, k17, d17⟩ := step_mov_at (code := code) (input := input)
        (s := { s15 with pc := 16 }) (d := rMid) (src := rK) rfl (by dsimp; omega)
      refine ⟨2, by omega, s17, .cons b15 (.cons st16 (.zero _)), by omega, ?_, ?_, k17⟩
      · rw [r17]; change (reg s15 rK).val = mid; rw [s15K]; omega
      · exact d17.trans (d15.trans d14)
  obtain ⟨cM, hcM, s17, st15_17, pc17, s17Mid, s17Data, k17⟩ := hMinMid
  obtain ⟨s18, st17, pc18, r18, k18, d18⟩ := step_add15_at (code := code) (input := input)
    (s := s17) (d := rEnd) (lhs := rMid) (rhs := rW) (by rw [pc17]; rfl) (by omega)
  have hpc18 : s18.pc = 18 := by omega
  have s17W : (reg s17 rW).val = w := by rw [k17 _ (by decide), k15 _ (by decide), s14W]
  have s18End : (reg s18 rEnd).val = mid + w := by
    rw [r18, PaperB.WordOps.add_no_wrap _ _ (by rw [s17Mid, s17W]; omega), s17Mid, s17W]
  have s18K : (reg s18 rK).val = cur.length := by
    rw [k18 _ (by decide), k17 _ (by decide)]; exact s15K
  have hMinEnd : ∃ cE, cE ≤ 2 ∧ ∃ s20 : State L, Steps code input cE s18 s20 ∧ s20.pc = 20 ∧
      (reg s20 rEnd).val = end_ ∧ s20.data = s.data ∧
      (∀ r : Fin 15, r ≠ rEnd → reg s20 r = reg s18 r) := by
    by_cases he : mid + w < cur.length
    · have b18 : step code input s18 = some (.next { s18 with pc := 20 }) :=
        step_branchLt_true (by rw [hpc18]; rfl) (by rw [s18End, s18K]; exact he) (by omega)
      refine ⟨1, by omega, { s18 with pc := 20 }, .cons b18 (.zero _), rfl, ?_, ?_, fun _ _ => rfl⟩
      · change (reg s18 rEnd).val = end_; rw [s18End]; omega
      · exact d18.trans s17Data
    · have b18 : step code input s18 = some (.next { s18 with pc := 19 }) :=
        step_branchLt_false (by rw [hpc18]; rfl) (by rw [s18End, s18K]; omega) (by omega)
      obtain ⟨s20, st19, pc20, r20, k20, d20⟩ := step_mov_at (code := code) (input := input)
        (s := { s18 with pc := 19 }) (d := rEnd) (src := rK) rfl (by dsimp; omega)
      refine ⟨2, by omega, s20, .cons b18 (.cons st19 (.zero _)), by omega, ?_, ?_, k20⟩
      · rw [r20]; change (reg s18 rK).val = end_; rw [s18K]; omega
      · exact d20.trans (d18.trans s17Data)
  obtain ⟨cE, hcE, s20, st18_20, pc20, s20End, s20Data, k20⟩ := hMinEnd
  obtain ⟨s21, st20, pc21, r21, k21, d21⟩ := step_mov_at (code := code) (input := input)
    (s := s20) (d := rP) (src := rI) (by rw [pc20]; rfl) (by omega)
  obtain ⟨s22, st21, pc22, r22, k22, d22⟩ := step_mov_at (code := code) (input := input)
    (s := s21) (d := rQ) (src := rMid) (by rw [show s21.pc = 21 by omega]; rfl) (by omega)
  obtain ⟨s23, st22, pc23, r23, k23, d23⟩ := step_mov_at (code := code) (input := input)
    (s := s22) (d := rOut) (src := rI) (by rw [show s22.pc = 22 by omega]; rfl) (by omega)
  have keep20 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rI] : List (Fin 15))) :
      reg s20 r = reg s r := by
    have hneq : r ≠ rTmp ∧ r ≠ rW ∧ r ≠ rMid ∧ r ≠ rEnd := by revert r hr; decide
    exact (k20 r hneq.2.2.2).trans ((k18 r hneq.2.2.2).trans ((k17 r hneq.2.2.1).trans
      ((k15 r hneq.2.2.1).trans (k14 r hneq.1 hneq.2.1))))
  have keep23 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB] : List (Fin 15))) :
      reg s23 r = reg s r := by
    have hneq : r ≠ rP ∧ r ≠ rQ ∧ r ≠ rOut := by revert r hr; decide
    have hm20 : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rI] : List (Fin 15)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact (k23 r hneq.2.2).trans ((k22 r hneq.2.1).trans ((k21 r hneq.1).trans (keep20 r hm20)))
  have s20Mid : (reg s20 rMid).val = mid := by rw [k20 _ (by decide), k18 _ (by decide), s17Mid]
  have s23I : (reg s20 rI).val = i := by rw [keep20 _ (by decide), inv.iVal]
  refine ⟨(2 + (cM + (cE + 3).succ).succ).succ, by omega, s23, ?_, by omega,
    by rw [keep23 _ (by decide), inv.zero], by rw [keep23 _ (by decide), inv.one],
    by rw [keep23 _ (by decide), inv.kVal], by rw [keep23 _ (by decide), inv.fstAVal],
    by rw [keep23 _ (by decide), inv.sndAVal], by rw [keep23 _ (by decide), inv.fstBVal],
    by rw [keep23 _ (by decide), inv.sndBVal],
    by rw [k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), s20Mid],
    by rw [k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), s20End],
    by rw [k23 _ (by decide), k22 _ (by decide), r21, s23I],
    by rw [k23 _ (by decide), r22, k21 _ (by decide), s20Mid],
    by rw [r23, k22 _ (by decide), k21 _ (by decide), s23I],
    d23.trans (d22.trans (d21.trans s20Data))⟩
  exact Steps.cons b11 (st12_14.append (Steps.cons st14 (st15_17.append (Steps.cons st17 (st18_20.append
    (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.zero s23)))))))))

private theorem chunkLoop_step {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} {w : Nat} (hLen : cur.length ≤ H.vertexCount)
    (hBlk : BlockSorted cur w)
    {origA : Array (Word bits)}
    (hInA : ∀ j : Fin cur.length,
      MemPairAt origA (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt))
    (i : Nat) (hiLt : i < cur.length)
    (s : State L) (inv : ChunkInv H cur origA w i s) :
    ∃ i', ∃ t : State L, ∃ cost,
      i < i' ∧ i' ≤ cur.length ∧
      cost ≤ 40 * (i' - i) ∧
      Steps (sortPhase hi hw h8).code input cost s t ∧
      ChunkInv H cur origA w i' t := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hwPos := inv.wPos
  have hwLt := inv.wLt
  have h2wDvd : (2 * w) ∣ i := by
    rcases inv.iAlign with h | h
    · omega
    · exact h
  obtain ⟨c, hc⟩ := h2wDvd
  let mid := min (i + w) cur.length
  let end_ := min (mid + w) cur.length
  have hmidRange : i ≤ mid ∧ mid ≤ cur.length := ⟨by omega, Nat.min_le_right _ _⟩
  have hendRange : mid ≤ end_ ∧ end_ ≤ cur.length := ⟨by omega, Nat.min_le_right _ _⟩
  have hiLtEnd : i < end_ := by omega
  have hInACur : ∀ j : Fin cur.length,
      MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt) := by
    intro j
    have hjlt : j.val < H.vertexCount := Nat.lt_of_lt_of_le j.isLt hLen
    have hf1 : candFstABase H.vertexCount H.arcCount + j.val < candFstBBase H.vertexCount H.arcCount ∧
        candFstABase H.vertexCount H.arcCount + j.val < candSndBBase H.vertexCount H.arcCount := by
      simp only [candSndBBase, candFstBBase, candSndABase]; exact ⟨by omega, by omega⟩
    have hf2 : candSndABase H.vertexCount H.arcCount + j.val < candFstBBase H.vertexCount H.arcCount ∧
        candSndABase H.vertexCount H.arcCount + j.val < candSndBBase H.vertexCount H.arcCount := by
      simp only [candSndBBase, candFstBBase, candSndABase]; exact ⟨by omega, by omega⟩
    exact ⟨by rw [inv.frameChunk _ (Or.inl hf1.1) (Or.inl hf1.2)]; exact (hInA j).1,
           by rw [inv.frameChunk _ (Or.inl hf2.1) (Or.inl hf2.2)]; exact (hInA j).2⟩
  obtain ⟨cPre, hcPre, s23, stPre, pc23, z23, o23, k23, fa23, sa23, fb23, sb23,
      s23Mid, s23End, s23P, s23Q, s23Out, s23Data⟩ :=
    chunkSetup_steps h8 input hCap hLen i hiLt s inv
  -- Prove left/right subblock sortedness using 2*w | i
  have hLeftSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      i ≤ u → u ≤ v → v < mid → keyLe (cur[u]'hu) (cur[v]'hv) := by
    intro u v hu hv h1 h2 h3
    have hudiv : u / w = 2 * c :=
      div_eq_two_mul hwPos (by omega) (by omega)
    have hvdiv : v / w = 2 * c :=
      div_eq_two_mul hwPos (by omega) (by omega)
    exact hBlk u v hu hv h2 (hudiv.trans hvdiv.symm)
  have hRightSorted : ∀ u v (hu : u < cur.length) (hv : v < cur.length),
      mid ≤ u → u ≤ v → v < end_ → keyLe (cur[u]'hu) (cur[v]'hv) := by
    intro u v hu hv h1 h2 h3
    have hudiv : u / w = 2 * c + 1 :=
      div_eq_two_mul_add_one hwPos (by omega) (by omega)
    have hvdiv : v / w = 2 * c + 1 :=
      div_eq_two_mul_add_one hwPos (by omega) (by omega)
    exact hBlk u v hu hv h2 (hudiv.trans hvdiv.symm)
  have hInAS23 : ∀ j : Fin cur.length,
      MemPairAt s23.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt) := by
    intro j; rw [s23Data]; exact hInACur j
  have invM0 : MergeInv H cur s23.data i mid end_ i mid i s23 := by
    refine ⟨pc23, z23, o23, k23, fa23, sa23, fb23, sb23, s23Mid, s23End, s23P, s23Q, s23Out,
      ⟨Nat.le_refl i, hmidRange.1⟩, ⟨Nat.le_refl mid, hendRange.1⟩, by omega,
      fun _ h1 h2 => by omega, fun _ _ _ _ h1 h2 h3 => by omega,
      fun _ _ _ _ h1 h2 => by omega, fun _ _ _ _ h1 h2 => by omega, ?_, fun _ _ _ => rfl⟩
    intro z
    constructor
    · rintro (⟨t, h1, h2, _⟩ | ⟨p1, hp1, hp1a, hp1b, hz⟩ | ⟨q1, hq1, hq1a, hq1b, hz⟩)
      · omega
      · exact ⟨p1, hp1, hp1a, Nat.lt_of_lt_of_le hp1b hendRange.1, hz⟩
      · exact ⟨q1, hq1, Nat.le_trans hmidRange.1 hq1a, hq1b, hz⟩
    · rintro ⟨t, ht, ht1, ht2, hz⟩
      by_cases htm : t < mid
      · exact Or.inr (Or.inl ⟨t, ht, ht1, htm, hz⟩)
      · exact Or.inr (Or.inr ⟨t, ht, Nat.le_of_not_lt htm, ht2, hz⟩)
  obtain ⟨sM, cMerge, hcMerge, stMerge, invM⟩ :=
    mergeLoop_run h8 input hCap hLen hInAS23 hmidRange.1 hendRange.1 hendRange.2 hLeftSorted hRightSorted
      ((mid - i) + (end_ - mid)) i mid i s23 rfl invM0
  -- Exit merge: 23 -> 58 -> 59 -> 60 -> 11 (4 steps)
  have b23 : step code input sM = some (.next { sM with pc := 58 }) :=
    step_branchLt_false (by rw [invM.pc]; rfl) (by rw [invM.pVal, invM.midVal]; exact Nat.le_refl _) (by omega)
  have b58 : step code input { sM with pc := 58 } = some (.next { sM with pc := 59 }) :=
    step_branchLt_false rfl (by change (reg sM rEnd).val ≤ (reg sM rQ).val; rw [invM.qVal, invM.endVal]; exact Nat.le_refl _) (by omega)
  obtain ⟨s60, st59, pc60, r60, k60, d60⟩ := step_mov_at (code := code) (input := input)
    (s := { sM with pc := 59 }) (d := rI) (src := rEnd) rfl (by dsimp; omega)
  let t : State L := { s60 with pc := 11 }
  have st60 : step code input s60 = some (.next t) :=
    step_goto_at (code := code) (input := input) (s := s60) (target := 11)
      (by rw [show s60.pc = 60 by dsimp at pc60; omega]; rfl) (by omega)
  have hkeepT (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB] : List (Fin 15))) :
      reg t r = reg sM r := by
    have hneq : r ≠ rI := by revert r hr; decide
    exact k60 r hneq
  have htData : t.data = sM.data := d60
  have hOldPres : ∀ j, j < i → ∀ x,
      MemPairAt t.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) j x ↔
      MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) j x := by
    intro j hj x
    have hf1 : candFstBBase H.vertexCount H.arcCount + j < candFstBBase H.vertexCount H.arcCount + i ∧
        candFstBBase H.vertexCount H.arcCount + j < candSndBBase H.vertexCount H.arcCount + i := by
      simp only [candSndBBase, candFstBBase]; exact ⟨by omega, by omega⟩
    have hf2 : candFstBBase H.vertexCount H.arcCount + end_ ≤ candSndBBase H.vertexCount H.arcCount + j ∧
        candSndBBase H.vertexCount H.arcCount + j < candSndBBase H.vertexCount H.arcCount + i := by
      simp only [candSndBBase, candFstBBase]; have := hendRange.2; exact ⟨by omega, by omega⟩
    simp only [MemPairAt, htData, invM.frameB _ (Or.inl hf1.1) (Or.inl hf1.2),
      invM.frameB _ (Or.inr hf2.1) (Or.inl hf2.2), s23Data]
  have hSlotW : (t.data[slotWidth]?).map Fin.val = some w := by
    have hge7 : 7 ≤ candFstBBase H.vertexCount H.arcCount :=
      seven_le_candFstBBase H.vertexCount H.arcCount
    have hf1 : slotWidth < candFstBBase H.vertexCount H.arcCount + i := by
      change 6 < _; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 6 < 7) hge7) (Nat.le_add_right _ i)
    have hf2 : slotWidth < candSndBBase H.vertexCount H.arcCount + i := by
      simp only [candSndBBase]
      exact Nat.lt_of_lt_of_le hf1 (Nat.add_le_add_right (Nat.le_add_right _ _) i)
    have hmSlot : sM.data[slotWidth]? = s23.data[slotWidth]? :=
      invM.frameB slotWidth (Or.inl hf1) (Or.inl hf2)
    rw [htData, hmSlot, s23Data]
    exact inv.slotW
  have hIAlign : end_ = cur.length ∨ (2 * w) ∣ end_ := by
    by_cases hlt : mid + w < cur.length
    · right
      have hendEq : end_ = i + 2 * w := min_min_add_eq i w cur.length hlt
      rw [hendEq, hc]; exact ⟨c + 1, by rw [Nat.mul_add, Nat.mul_one]⟩
    · left; exact Nat.min_eq_right (Nat.le_of_not_lt hlt)
  have stAll : Steps code input (cPre + cMerge + 4) s t :=
    stPre.append (stMerge.append (.cons b23 (.cons b58 (.cons st59 (.cons st60 (.zero t))))))
  refine ⟨end_, t, cPre + cMerge + 4, hiLtEnd, hendRange.2,
    by have : 1 ≤ end_ - i := by omega
       have : (mid - i) + (end_ - mid) = end_ - i := by omega
       omega,
    stAll, ?_⟩
  refine ⟨rfl, by rw [hkeepT _ (by decide), invM.zero], by rw [hkeepT _ (by decide), invM.one],
    by rw [hkeepT _ (by decide), invM.kVal], by rw [hkeepT _ (by decide), invM.fstAVal],
    by rw [hkeepT _ (by decide), invM.sndAVal], by rw [hkeepT _ (by decide), invM.fstBVal],
    by rw [hkeepT _ (by decide), invM.sndBVal],
    by change (reg s60 rI).val = end_; rw [r60]; exact invM.endVal,
    hSlotW, hwPos, hwLt, hendRange.2, hIAlign, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    by_cases hi : idx < i
    · obtain ⟨x, hx⟩ := inv.bPairs idx hi
      exact ⟨x, (hOldPres idx hi x).mpr hx⟩
    · obtain ⟨x, hx⟩ := invM.outPairs idx (Nat.le_of_not_lt hi) hidx
      exact ⟨x, by rw [htData]; exact hx⟩
  · intro u v x y hu hv hdiv hx hy
    by_cases hvi : v < i
    · exact inv.bSorted u v x y hu hvi hdiv
        ((hOldPres u (Nat.lt_of_le_of_lt hu hvi) x).mp hx)
        ((hOldPres v hvi y).mp hy)
    · have hvge : i ≤ v := Nat.le_of_not_lt hvi
      by_cases hui : u < i
      · have huc : u / (2 * w) < c :=
          Nat.div_lt_of_lt_mul (by rw [← hc]; exact hui)
        have hvc : c ≤ v / (2 * w) := by
          have := Nat.div_le_div_right (c := 2 * w) hvge
          rwa [hc, Nat.mul_div_cancel_left _ (by omega)] at this
        omega
      · exact invM.outSorted u v x y (Nat.le_of_not_lt hui) hu hv
          (by rw [← htData]; exact hx) (by rw [← htData]; exact hy)
  · intro z
    constructor
    · rintro ⟨idx, hidx, hz⟩
      by_cases hji : idx < i
      · obtain ⟨t0, ht0, ht0lt, htz⟩ := (inv.bMem z).mp ⟨idx, hji, (hOldPres idx hji z).mp hz⟩
        exact ⟨t0, ht0, Nat.lt_trans ht0lt hiLtEnd, htz⟩
      · have := (invM.memPart z).mp (Or.inl ⟨idx, Nat.le_of_not_lt hji, hidx, by rw [← htData]; exact hz⟩)
        obtain ⟨t0, ht0, _, ht0lt, htz⟩ := this
        exact ⟨t0, ht0, ht0lt, htz⟩
    · rintro ⟨t0, ht0, ht0lt, htz⟩
      by_cases hti : t0 < i
      · obtain ⟨idx, hidx, hz⟩ := (inv.bMem z).mpr ⟨t0, ht0, hti, htz⟩
        exact ⟨idx, Nat.lt_trans hidx hiLtEnd, (hOldPres idx hidx z).mpr hz⟩
      · have := (invM.memPart z).mpr ⟨t0, ht0, Nat.le_of_not_lt hti, ht0lt, htz⟩
        rcases this with ⟨idx, _, hidx2, hz⟩ | ⟨p1, hp1, hp1a, hp1b, _⟩ | ⟨q1, hq1, hq1a, hq1b, _⟩
        · exact ⟨idx, hidx2, by rw [htData]; exact hz⟩
        · omega
        · omega
  · intro j hjF hjS
    rw [htData]
    by_cases h1 : (j < candFstBBase H.vertexCount H.arcCount + i ∨ candFstBBase H.vertexCount H.arcCount + end_ ≤ j) ∧
        (j < candSndBBase H.vertexCount H.arcCount + i ∨ candSndBBase H.vertexCount H.arcCount + end_ ≤ j)
    · rw [invM.frameB j h1.1 h1.2, s23Data]
      exact inv.frameChunk j (by rcases hjF with hjF | hjF; left; exact hjF; right; omega)
        (by rcases hjS with hjS | hjS; left; exact hjS; right; omega)
    · exfalso
      rcases hjF with hjF | hjF <;> rcases hjS with hjS | hjS <;> apply h1 <;> constructor <;>
        first | exact Or.inl (by omega) | exact Or.inr (by omega)

private theorem chunkLoop_run {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} {w : Nat} (hLen : cur.length ≤ H.vertexCount)
    (hBlk : BlockSorted cur w)
    {origA : Array (Word bits)}
    (hInA : ∀ j : Fin cur.length,
      MemPairAt origA (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt)) :
    ∀ rem i (s : State L),
      cur.length - i = rem →
      ChunkInv H cur origA w i s →
      ∃ t : State L, ∃ cost, cost ≤ 40 * rem ∧
        Steps (sortPhase hi hw h8).code input cost s t ∧
        ChunkInv H cur origA w cur.length t := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i s hrem inv
    by_cases hdone : rem = 0
    · have hiEq : i = cur.length := by have := inv.iLe; omega
      subst hiEq
      exact ⟨s, 0, by omega, .zero s, inv⟩
    · have hiLt : i < cur.length := by have := inv.iLe; omega
      obtain ⟨i', s', c1, hgt, hle, hc1, st1, inv'⟩ :=
        chunkLoop_step h8 input hCap hLen hBlk hInA i hiLt s inv
      obtain ⟨t, c2, hc2, st2, invEnd⟩ := ih (cur.length - i') (by omega) i' s' rfl inv'
      exact ⟨t, c1 + c2, by omega, st1.append st2, invEnd⟩

private noncomputable def readPairs (data : Array (Word bits))
    (fstBase sndBase k : Nat) : List Key :=
  List.ofFn (fun j : Fin k =>
    (((data[fstBase + j.val]?).map Fin.val).getD 0,
     ((data[sndBase + j.val]?).map Fin.val).getD 0))

private theorem readPairs_memPairAt {data : Array (Word bits)} {fstBase sndBase k : Nat}
    (hPairs : ∀ j, j < k → ∃ x : Key, MemPairAt data fstBase sndBase j x)
    (j : Fin k) :
    MemPairAt data fstBase sndBase j.val ((readPairs data fstBase sndBase k)[j.val]'(by simp [readPairs])) := by
  obtain ⟨x, hx⟩ := hPairs j.val j.isLt
  have hget : (readPairs data fstBase sndBase k)[j.val]'(by simp [readPairs]) = x := by
    simp only [readPairs, List.getElem_ofFn, hx.1, hx.2, Option.getD_some]
  rw [hget]
  exact hx

private theorem copyBack_loop {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {nextCur : List Key} (hLen : nextCur.length ≤ H.vertexCount)
    {origB : Array (Word bits)}
    (hInB : ∀ j : Fin nextCur.length,
      MemPairAt origB (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) j.val (nextCur[j.val]'j.isLt)) :
    ∀ k ≤ nextCur.length, ∀ s : State L,
      s.pc = 62 →
      (reg s rZero).val = 0 → (reg s rOne).val = 1 → (reg s rK).val = nextCur.length →
      (reg s rFstA).val = candFstABase H.vertexCount H.arcCount →
      (reg s rSndA).val = candSndABase H.vertexCount H.arcCount →
      (reg s rFstB).val = candFstBBase H.vertexCount H.arcCount →
      (reg s rSndB).val = candSndBBase H.vertexCount H.arcCount →
      (reg s rOut).val = k →
      (∀ j, j < k → ∀ hlt : j < nextCur.length,
        MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j (nextCur[j]'hlt)) →
      (∀ j,
        (j < candFstABase H.vertexCount H.arcCount ∨ candFstABase H.vertexCount H.arcCount + k ≤ j) →
        (j < candSndABase H.vertexCount H.arcCount ∨ candSndABase H.vertexCount H.arcCount + k ≤ j) →
        s.data[j]? = origB[j]?) →
      ∃ t : State L, ∃ cost, cost ≤ 11 * (nextCur.length - k) + 1 ∧
        Steps (sortPhase hi hw h8).code input cost s t ∧ t.pc = 73 ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rK).val = nextCur.length ∧
        (reg t rFstA).val = candFstABase H.vertexCount H.arcCount ∧
        (reg t rSndA).val = candSndABase H.vertexCount H.arcCount ∧
        (reg t rFstB).val = candFstBBase H.vertexCount H.arcCount ∧
        (reg t rSndB).val = candSndBBase H.vertexCount H.arcCount ∧
        (∀ j : Fin nextCur.length,
          MemPairAt t.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (nextCur[j.val]'j.isLt)) ∧
        (∀ j,
          (j < candFstABase H.vertexCount H.arcCount ∨ candSndABase H.vertexCount H.arcCount + H.vertexCount ≤ j) →
          t.data[j]? = origB[j]?) := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  intro k hk
  induction hd : nextCur.length - k generalizing k with
  | zero =>
    intro s hpc h0 h1 hK hFA hSA hFB hSB hOut hA hFr
    have hkeq : k = nextCur.length := by omega
    subst hkeq
    have b62 : step code input s = some (.next { s with pc := 73 }) :=
      step_branchLt_false (by rw [hpc]; rfl) (by rw [hOut, hK]; exact Nat.le_refl _) (by omega)
    refine ⟨{ s with pc := 73 }, 1, by omega, .cons b62 (.zero _), rfl, h0, h1, hK, hFA, hSA, hFB, hSB,
      fun j => hA j.val j.isLt j.isLt, fun j hj => ?_⟩
    rcases hj with hj | hj
    · exact hFr j (Or.inl hj) (Or.inl (by simp only [candSndABase]; omega))
    · exact hFr j (Or.inr (by simp only [candSndABase] at hj; omega)) (Or.inr (by omega))
  | succ d ih =>
    intro s hpc h0 h1 hK hFA hSA hFB hSB hOut hA hFr
    have hklt : k < nextCur.length := by omega
    have b62 : step code input s = some (.next { s with pc := 63 }) :=
      step_branchLt_true (by rw [hpc]; rfl) (by rw [hOut, hK]; exact hklt) (by omega)
    have hInBCur : MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) k (nextCur[k]'hklt) := by
      have hf1 : candFstBBase H.vertexCount H.arcCount + k < candFstABase H.vertexCount H.arcCount ∨
          candFstABase H.vertexCount H.arcCount + k ≤ candFstBBase H.vertexCount H.arcCount + k := by
        right; simp only [candFstBBase, candSndABase]; omega
      have hf2 : candFstBBase H.vertexCount H.arcCount + k < candSndABase H.vertexCount H.arcCount ∨
          candSndABase H.vertexCount H.arcCount + k ≤ candFstBBase H.vertexCount H.arcCount + k := by
        right; simp only [candFstBBase, candSndABase]; omega
      have hf3 : candSndBBase H.vertexCount H.arcCount + k < candFstABase H.vertexCount H.arcCount ∨
          candFstABase H.vertexCount H.arcCount + k ≤ candSndBBase H.vertexCount H.arcCount + k := by
        right; simp only [candSndBBase, candFstBBase, candSndABase]; omega
      have hf4 : candSndBBase H.vertexCount H.arcCount + k < candSndABase H.vertexCount H.arcCount ∨
          candSndABase H.vertexCount H.arcCount + k ≤ candSndBBase H.vertexCount H.arcCount + k := by
        right; simp only [candSndBBase, candFstBBase, candSndABase]; omega
      exact ⟨by rw [hFr _ hf1 hf2]; exact (hInB ⟨k, hklt⟩).1,
             by rw [hFr _ hf3 hf4]; exact (hInB ⟨k, hklt⟩).2⟩
    obtain ⟨⟨w1, hw1, hw1v⟩, ⟨w2, hw2, hw2v⟩⟩ := memPairAt_word hInBCur
    let s63 : State L := { s with pc := 63 }
    have hb1 : (reg s63 rFstA).val + (reg s63 rOut).val < workCap := by
      change (reg s rFstA).val + (reg s rOut).val < workCap
      rw [hFA, hOut]; simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
        orderBase, stampsBase, indegBase, csrArenaWords]; omega
    have hb2 : (reg s63 rSndA).val + (reg s63 rOut).val < workCap := by
      change (reg s rSndA).val + (reg s rOut).val < workCap
      rw [hSA, hOut]; simp only [candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase,
        ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    have hne12 : (reg s63 rFstA).val + (reg s63 rOut).val ≠ (reg s63 rSndB).val + (reg s63 rOut).val := by
      change (reg s rFstA).val + (reg s rOut).val ≠ (reg s rSndB).val + (reg s rOut).val
      rw [hFA, hSB, hOut]; simp only [candSndBBase, candFstBBase, candSndABase]; omega
    obtain ⟨s71, st63_71, pc71, hd71, k71⟩ := copyPair_steps (code := code) (input := input)
      (s := s63) (entry := 63) (tmp := rTmp) (val := rA) (srcFst := rFstB) (srcSnd := rSndB)
      (srcIdx := rOut) (dstFst := rFstA) (dstSnd := rSndA) (dstIdx := rOut)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl (by omega)
      (by decide) (by decide) hb1 hb2
      (by change s.data[(reg s rFstB).val + (reg s rOut).val]? = _; rw [hFB, hOut]; exact hw1)
      (by change s.data[(reg s rSndB).val + (reg s rOut).val]? = _; rw [hSB, hOut]; exact hw2)
      hne12
    obtain ⟨s72, st71, pc72, r72, k72, d72⟩ := step_add15_at (code := code) (input := input)
      (s := s71) (d := rOut) (lhs := rOut) (rhs := rOne) (by rw [pc71]; rfl) (by omega)
    let s' : State L := { s72 with pc := 62 }
    have st72 : step code input s72 = some (.next s') :=
      step_goto_at (code := code) (input := input) (s := s72) (target := 62)
        (by rw [show s72.pc = 72 by omega]; rfl) (by omega)
    have hkeep (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB] : List (Fin 15))) :
        reg s' r = reg s r := by
      have hneq : r ≠ rTmp ∧ r ≠ rA ∧ r ≠ rOut := by revert r hr; decide
      exact (k72 r hneq.2.2).trans (k71 r hneq.1 hneq.2.1)
    have hsds : s.data.size = workCap := s.data_size
    have haddr1 : (reg s63 rFstA).val + (reg s63 rOut).val = candFstABase H.vertexCount H.arcCount + k := by
      change (reg s rFstA).val + (reg s rOut).val = _; rw [hFA, hOut]
    have haddr2 : (reg s63 rSndA).val + (reg s63 rOut).val = candSndABase H.vertexCount H.arcCount + k := by
      change (reg s rSndA).val + (reg s rOut).val = _; rw [hSA, hOut]
    have hdst1Lt : candFstABase H.vertexCount H.arcCount + k < s.data.size := by
      rw [hsds, ← haddr1]; exact hb1
    have hdst2Lt : candSndABase H.vertexCount H.arcCount + k <
        (s.data.set (candFstABase H.vertexCount H.arcCount + k) w1 hdst1Lt).size := by
      rw [Array.size_set, hsds, ← haddr2]; exact hb2
    have hdataEq : s'.data =
        (s.data.set (candFstABase H.vertexCount H.arcCount + k) w1 hdst1Lt).set
          (candSndABase H.vertexCount H.arcCount + k) w2 hdst2Lt := by
      change s72.data = _
      rw [d72]
      have hsub := hd71 (by rw [haddr1]; exact hdst1Lt) (by rw [Array.size_set, hsds]; exact hb2)
      have ha1 := array_set_congr (v := w1) (w := w1) (by rw [haddr1]; exact hdst1Lt) hdst1Lt rfl haddr1 rfl
      exact hsub.trans (array_set_congr (v := w2) (w := w2) (by rw [Array.size_set, hsds]; exact hb2) hdst2Lt ha1 haddr2 rfl)
    have hOut71 : (reg s71 rOut).val = k := by rw [k71 _ (by decide) (by decide)]; exact hOut
    have hO71 : (reg s71 rOne).val = 1 := by rw [k71 _ (by decide) (by decide)]; exact h1
    have hOut' : (reg s' rOut).val = k + 1 := by
      change (reg s72 rOut).val = _
      rw [r72, PaperB.WordOps.add_no_wrap _ _ (by rw [hOut71, hO71]; omega), hOut71, hO71]
    have hIdxNe : candFstABase H.vertexCount H.arcCount + k ≠ candSndABase H.vertexCount H.arcCount + k := by
      simp only [candSndABase]; omega
    obtain ⟨t, c2, hc2, st2, hFin⟩ := ih (k + 1) (by omega) (by omega) s' rfl
      (by rw [hkeep _ (by decide), h0]) (by rw [hkeep _ (by decide), h1]) (by rw [hkeep _ (by decide), hK])
      (by rw [hkeep _ (by decide), hFA]) (by rw [hkeep _ (by decide), hSA])
      (by rw [hkeep _ (by decide), hFB]) (by rw [hkeep _ (by decide), hSB]) hOut'
      (by intro idx hidx hlt
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt' | rfl
          · have hne1 : candFstABase H.vertexCount H.arcCount + k ≠ candFstABase H.vertexCount H.arcCount + idx := by omega
            have hne2 : candSndABase H.vertexCount H.arcCount + k ≠ candFstABase H.vertexCount H.arcCount + idx := by
              simp only [candSndABase]; omega
            have hne3 : candFstABase H.vertexCount H.arcCount + k ≠ candSndABase H.vertexCount H.arcCount + idx := by
              simp only [candSndABase]; omega
            have hne4 : candSndABase H.vertexCount H.arcCount + k ≠ candSndABase H.vertexCount H.arcCount + idx := by omega
            have hprev := hA idx hlt' hlt
            exact ⟨by rw [hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]; exact hprev.1,
                   by rw [hdataEq, Array.getElem?_set_ne _ hne4, Array.getElem?_set_ne _ hne3]; exact hprev.2⟩
          · exact ⟨by rw [hdataEq, Array.getElem?_set_ne _ (Ne.symm hIdxNe), Array.getElem?_set_self, Option.map_some, hw1v],
                   by rw [hdataEq, Array.getElem?_set_self, Option.map_some, hw2v]⟩)
      (by intro j hjF hjS
          have hne1 : candFstABase H.vertexCount H.arcCount + k ≠ j := by
            rcases hjF with hjF | hjF <;> omega
          have hne2 : candSndABase H.vertexCount H.arcCount + k ≠ j := by
            rcases hjS with hjS | hjS <;> omega
          rw [hdataEq, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
          exact hFr j (by rcases hjF with hjF | hjF; left; exact hjF; right; omega)
            (by rcases hjS with hjS | hjS; left; exact hjS; right; omega))
    refine ⟨t, 1 + 8 + 2 + c2, by omega, ?_, hFin⟩
    exact (Steps.cons b62 (st63_71.append (.cons st71 (.cons st72 (.zero s'))))).append st2

private theorem pass_step {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {xs : List Key} {orig : Array (Word bits)} {cur : List Key} {w : Nat}
    (hwLt : w < xs.length) (s : State L) (inv : SortPassInv H xs orig cur w s) :
    ∃ nextCur, ∃ t : State L, ∃ cost,
      cost ≤ 51 * xs.length + 11 ∧
      Steps (sortPhase hi hw h8).code input cost s t ∧
      SortPassInv H xs orig nextCur (2 * w) t := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  have hLen := inv.lenEq
  have hLenB := inv.lenBound
  -- 7: branchLt rW rK 8 77
  have b7 : step code input s = some (.next { s with pc := 8 }) :=
    step_branchLt_true (by rw [inv.pc]; rfl) (by rw [inv.wVal, inv.kVal]; exact hwLt) (by omega)
  -- 8..9: slotWidth := rW
  obtain ⟨s10, st8_10, pc10, d10, k10⟩ := immStore_steps (code := code) (input := input)
    (s := { s with pc := 8 }) (entry := 8) (tmp := rTmp) (src := rW) (slot := ⟨6, by omega⟩)
    rfl rfl rfl (by omega) (by decide) (by dsimp; unfold rawWorkCap at hCap; omega)
  -- 10: mov rI rZero
  obtain ⟨s11, st10, pc11, r11, k11, d11⟩ := step_mov_at (code := code) (input := input)
    (s := s10) (d := rI) (src := rZero) (by rw [pc10]; rfl) (by omega)
  have hkeep11 (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB, rW] : List (Fin 15))) :
      reg s11 r = reg s r := by
    have hneq : r ≠ rTmp ∧ r ≠ rI := by revert r hr; decide
    exact (k11 r hneq.2).trans (k10 r hneq.1)
  have hsds : s.data.size = workCap := s.data_size
  have h6lt : 6 < s.data.size := by rw [hsds]; unfold rawWorkCap at hCap; omega
  have hs11Data : s11.data = s.data.set 6 (reg s rW) h6lt := by
    rw [d11, d10]; exact array_set_congr _ _ rfl rfl rfl
  have hInA11 : ∀ j : Fin cur.length,
      MemPairAt s11.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt) := by
    intro j
    have hne1 : 6 ≠ candFstABase H.vertexCount H.arcCount + j.val := by
      simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
        stampsBase, indegBase, csrArenaWords]; omega
    have hne2 : 6 ≠ candSndABase H.vertexCount H.arcCount + j.val := by
      simp only [candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
        orderBase, stampsBase, indegBase, csrArenaWords]; omega
    exact ⟨by rw [hs11Data, Array.getElem?_set_ne _ hne1]; exact (inv.inA j).1,
           by rw [hs11Data, Array.getElem?_set_ne _ hne2]; exact (inv.inA j).2⟩
  have invC0 : ChunkInv H cur s11.data w 0 s11 := by
    refine ⟨by omega, by rw [hkeep11 _ (by decide), inv.zero], by rw [hkeep11 _ (by decide), inv.one],
      by rw [hkeep11 _ (by decide), inv.kVal, hLen], by rw [hkeep11 _ (by decide), inv.fstAVal],
      by rw [hkeep11 _ (by decide), inv.sndAVal], by rw [hkeep11 _ (by decide), inv.fstBVal],
      by rw [hkeep11 _ (by decide), inv.sndBVal],
      by rw [r11, k10 _ (by decide)]; change (reg s rZero).val = 0; exact inv.zero,
      by rw [hs11Data]; change Option.map Fin.val (s.data.set 6 (reg s rW) h6lt)[6]? = some w
         rw [Array.getElem?_set_self, Option.map_some, inv.wVal],
      inv.wPos, by omega, Nat.zero_le _, Or.inr ⟨0, by simp⟩,
      fun _ h => by omega, fun _ _ _ _ _ h => by omega,
      fun z => ⟨fun ⟨_, h, _⟩ => by omega, fun ⟨_, _, h, _⟩ => by omega⟩, fun _ _ _ => rfl⟩
  obtain ⟨sC, cChunk, hcChunk, stChunk, invC⟩ :=
    chunkLoop_run h8 input hCap (by omega) inv.sorted hInA11 cur.length 0 s11 (by omega) invC0
  -- Extract nextCur from B[0..cur.length)
  let nextCur := readPairs sC.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) cur.length
  have hNextLen : nextCur.length = cur.length := by simp [nextCur, readPairs]
  have hInBC : ∀ j : Fin nextCur.length,
      MemPairAt sC.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) j.val (nextCur[j.val]'j.isLt) := by
    intro j
    have hlt' : j.val < cur.length := by rw [← hNextLen]; exact j.isLt
    simpa only [nextCur] using readPairs_memPairAt invC.bPairs ⟨j.val, hlt'⟩
  -- 11 -> 61 -> 62 -> copyBack -> 73
  have b11 : step code input sC = some (.next { sC with pc := 61 }) :=
    step_branchLt_false (by rw [invC.pc]; rfl) (by rw [invC.iVal, invC.kVal]; exact Nat.le_refl _) (by omega)
  obtain ⟨s62, st61, pc62, r62, k62, d62⟩ := step_mov_at (code := code) (input := input)
    (s := { sC with pc := 61 }) (d := rOut) (src := rZero) rfl (by dsimp; omega)
  have hInBS62 : ∀ j : Fin nextCur.length,
      MemPairAt s62.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) j.val (nextCur[j.val]'j.isLt) := by
    intro j; rw [d62]; exact hInBC j
  obtain ⟨s73, cCopy, hcCopy, stCopy, pc73, z73, o73, k73, fa73, sa73, fb73, sb73, inA73, fr73⟩ :=
    copyBack_loop h8 input hCap (by omega) hInBS62 0 (Nat.zero_le _) s62 (by dsimp at pc62; omega)
      (by rw [k62 _ (by decide)]; change (reg sC rZero).val = 0; exact invC.zero)
      (by rw [k62 _ (by decide)]; change (reg sC rOne).val = 1; exact invC.one)
      (by rw [k62 _ (by decide)]; change (reg sC rK).val = _; rw [invC.kVal, hNextLen])
      (by rw [k62 _ (by decide)]; change (reg sC rFstA).val = _; exact invC.fstAVal)
      (by rw [k62 _ (by decide)]; change (reg sC rSndA).val = _; exact invC.sndAVal)
      (by rw [k62 _ (by decide)]; change (reg sC rFstB).val = _; exact invC.fstBVal)
      (by rw [k62 _ (by decide)]; change (reg sC rSndB).val = _; exact invC.sndBVal)
      (by rw [r62]; change (reg sC rZero).val = 0; exact invC.zero)
      (fun _ h => by omega) (fun _ _ _ => rfl)
  -- 73..76: reload w from slotWidth, double w, goto 7
  have hwSlot73 : (s73.data[slotWidth]?).map Fin.val = some w := by
    have hf : slotWidth < candFstABase H.vertexCount H.arcCount := by
      simp only [slotWidth, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
        orderBase, stampsBase, indegBase, csrArenaWords]; omega
    rw [fr73 _ (Or.inl hf), d62]
    exact invC.slotW
  obtain ⟨wW, hwW73, hwW73v⟩ := word_mem_eq_of_map_val hwSlot73
  obtain ⟨s75, st73_75, pc75, r75, k75, d75⟩ := immLoad_steps (code := code) (input := input)
    (s := s73) (entry := 73) (tmp := rTmp) (dst := rW) (slot := ⟨6, by omega⟩) (w := wW)
    rfl rfl pc73 (by omega) hwW73
  obtain ⟨s76, st75, pc76, r76, k76, d76⟩ := step_add15_at (code := code) (input := input)
    (s := s75) (d := rW) (lhs := rW) (rhs := rW) (by rw [pc75]; rfl) (by omega)
  let t : State L := { s76 with pc := 7 }
  have st76 : step code input s76 = some (.next t) :=
    step_goto_at (code := code) (input := input) (s := s76) (target := 7)
      (by rw [show s76.pc = 76 by omega]; rfl) (by omega)
  have hkeepT (r : Fin 15) (hr : r ∈ ([rZero, rOne, rK, rFstA, rSndA, rFstB, rSndB] : List (Fin 15))) :
      reg t r = reg s73 r := by
    have hneq : r ≠ rTmp ∧ r ≠ rW := by revert r hr; decide
    exact (k76 r hneq.2).trans (k75 r hneq.1 hneq.2)
  have hW75 : (reg s75 rW).val = w := by rw [r75, hwW73v]
  have hWt : (reg t rW).val = 2 * w := by
    change (reg s76 rW).val = _
    rw [r76, PaperB.WordOps.add_no_wrap _ _ (by rw [hW75]; omega), hW75]
    omega
  have htData : t.data = s73.data := d76.trans d75
  refine ⟨nextCur, t, (2 + cChunk.succ).succ + (cCopy + (2 + (Nat.succ 0).succ)).succ.succ,
    by rw [hNextLen, Nat.sub_zero] at hcCopy; omega, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Steps.cons b7 (st8_10.append (.cons st10 stChunk))).append
      (.cons b11 (.cons st61 (stCopy.append (st73_75.append (.cons st75 (.cons st76 (.zero t)))))))
  · rfl
  · rw [hkeepT _ (by decide), z73]
  · rw [hkeepT _ (by decide), o73]
  · rw [hkeepT _ (by decide), k73, hNextLen, hLen]
  · rw [hkeepT _ (by decide), fa73]
  · rw [hkeepT _ (by decide), sa73]
  · rw [hkeepT _ (by decide), fb73]
  · rw [hkeepT _ (by decide), sb73]
  · exact hWt
  · have := inv.wPos; omega
  · omega
  · exact hLenB
  · intro u v hu hv huv hdiv
    have hu' : u < cur.length := by omega
    have hv' : v < cur.length := by omega
    obtain ⟨xu, hxu⟩ := invC.bPairs u hu'
    obtain ⟨xv, hxv⟩ := invC.bPairs v hv'
    have hmu := hInBC ⟨u, by omega⟩
    have hmv := hInBC ⟨v, by omega⟩
    have heu : nextCur[u]'hu = xu := by
      have h1 := hmu.1.symm.trans hxu.1; have h2 := hmu.2.symm.trans hxu.2
      exact Prod.ext (Option.some.inj h1) (Option.some.inj h2)
    have hev : nextCur[v]'hv = xv := by
      have h1 := hmv.1.symm.trans hxv.1; have h2 := hmv.2.symm.trans hxv.2
      exact Prod.ext (Option.some.inj h1) (Option.some.inj h2)
    rw [heu, hev]
    exact invC.bSorted u v xu xv huv hv' hdiv hxu hxv
  · intro z
    rw [← inv.memEq z]
    constructor
    · intro hz
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
      have hmp := hInBC ⟨j, hj⟩
      obtain ⟨t0, ht0, _, htz⟩ := (invC.bMem _).mp ⟨j, by omega, hmp⟩
      rw [← htz]; exact List.getElem_mem ht0
    · intro hz
      obtain ⟨t0, ht0, rfl⟩ := List.mem_iff_getElem.mp hz
      obtain ⟨idx, hidx, hmp⟩ := (invC.bMem _).mpr ⟨t0, ht0, ht0, rfl⟩
      have hmp' := hInBC ⟨idx, by omega⟩
      have heq : nextCur[idx]'(by omega) = cur[t0]'ht0 :=
        Prod.ext (Option.some.inj (hmp'.1.symm.trans hmp.1)) (Option.some.inj (hmp'.2.symm.trans hmp.2))
      rw [← heq]; exact List.getElem_mem (by omega)
  · intro j
    rw [htData]; exact inA73 j
  · intro j hj
    rw [htData]
    have hfr1 : j < candFstABase H.vertexCount H.arcCount ∨
        candSndABase H.vertexCount H.arcCount + H.vertexCount ≤ j := by
      rcases hj with hj | hj | hj
      · left; simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
          orderBase, stampsBase, indegBase, csrArenaWords]; omega
      · left; exact hj.2
      · right; simp only [dictBase, candSndBBase, candFstBBase, candSndABase] at hj ⊢; omega
    rw [fr73 j hfr1, d62]
    have hfChunk : (j < candFstBBase H.vertexCount H.arcCount ∨
          candFstBBase H.vertexCount H.arcCount + cur.length ≤ j) ∧
        (j < candSndBBase H.vertexCount H.arcCount ∨
          candSndBBase H.vertexCount H.arcCount + cur.length ≤ j) := by
      rcases hj with hj | hj | hj
      · simp only [candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
          rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
        exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
      · simp only [candSndBBase, candFstBBase, candSndABase]
        exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
      · simp only [dictBase, candSndBBase, candFstBBase] at hj ⊢
        exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    rw [invC.frameChunk j hfChunk.1 hfChunk.2]
    have hne6 : 6 ≠ j := by
      rcases hj with hj | hj | hj
      · omega
      · simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
          stampsBase, indegBase, csrArenaWords] at hj; omega
      · simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
          rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hj
        omega
    rw [hs11Data, Array.getElem?_set_ne _ hne6]
    exact inv.frame j hj

private theorem passLoop_run {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {xs : List Key} {orig : Array (Word bits)} :
    ∀ rem w cur (s : State L),
      xs.length < w * 2 ^ rem →
      SortPassInv H xs orig cur w s →
      ∃ cur', ∃ w', ∃ t : State L, ∃ cost,
        cost ≤ (51 * xs.length + 11) * rem + 1 ∧
        Steps (sortPhase hi hw h8).code input cost s t ∧
        t.pc = (sortPhase hi hw h8).code.size - 1 ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (reg t rK).val = xs.length ∧
        (reg t rFstA).val = candFstABase H.vertexCount H.arcCount ∧
        (reg t rSndA).val = candSndABase H.vertexCount H.arcCount ∧
        (reg t rFstB).val = candFstBBase H.vertexCount H.arcCount ∧
        (reg t rSndB).val = candSndBBase H.vertexCount H.arcCount ∧
        cur'.length = xs.length ∧ xs.length ≤ w' ∧ BlockSorted cur' w' ∧
        (∀ z : Key, z ∈ cur' ↔ z ∈ xs) ∧
        (∀ j : Fin cur'.length,
          MemPairAt t.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur'[j.val]'j.isLt)) ∧
        (∀ j, j < 6 ∨
          (orderBase H.vertexCount H.arcCount ≤ j ∧ j < candFstABase H.vertexCount H.arcCount) ∨
          dictBase H.vertexCount H.arcCount ≤ j →
          t.data[j]? = orig[j]?) := by
  let code := (sortPhase hi hw h8).code
  have hSize : code.size = 78 := rfl
  intro rem
  induction rem with
  | zero =>
    intro w cur s hlt inv
    have hle : xs.length ≤ w := by simp at hlt; omega
    have b7 : step code input s = some (.next { s with pc := 77 }) :=
      step_branchLt_false (by rw [inv.pc]; rfl) (by rw [inv.wVal, inv.kVal]; exact hle) (by omega)
    exact ⟨cur, w, { s with pc := 77 }, 1, by omega, .cons b7 (.zero _), by rw [hSize],
      inv.zero, inv.one, inv.kVal, inv.fstAVal, inv.sndAVal, inv.fstBVal, inv.sndBVal,
      inv.lenEq, hle, inv.sorted, inv.memEq, inv.inA, inv.frame⟩
  | succ rem ih =>
    intro w cur s hlt inv
    by_cases hwLt : w < xs.length
    · obtain ⟨nextCur, s', c1, hc1, st1, inv'⟩ := pass_step h8 input hCap hwLt s inv
      have hlt' : xs.length < (2 * w) * 2 ^ rem := by
        rw [Nat.pow_succ] at hlt
        exact Nat.lt_of_lt_of_eq hlt (by rw [Nat.mul_comm (2 ^ rem) 2, ← Nat.mul_assoc, Nat.mul_comm w 2])
      obtain ⟨cur', w', t, c2, hc2, st2, hRest⟩ := ih (2 * w) nextCur s' hlt' inv'
      refine ⟨cur', w', t, c1 + c2, ?_, st1.append st2, hRest⟩
      rw [Nat.mul_succ]; omega
    · have hle : xs.length ≤ w := Nat.le_of_not_lt hwLt
      have b7 : step code input s = some (.next { s with pc := 77 }) :=
        step_branchLt_false (by rw [inv.pc]; rfl) (by rw [inv.wVal, inv.kVal]; exact hle) (by omega)
      refine ⟨cur, w, { s with pc := 77 }, 1, by omega, .cons b7 (.zero _), by rw [hSize],
        inv.zero, inv.one, inv.kVal, inv.fstAVal, inv.sndAVal, inv.fstBVal, inv.sndBVal,
        inv.lenEq, hle, inv.sorted, inv.memEq, inv.inA, inv.frame⟩

private theorem lt_two_pow_log2_succ (n : Nat) : n < 2 ^ (Nat.log2 n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h2 : n < 2
    · have : Nat.log2 n = 0 := by
        rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> decide
      rw [this]; omega
    · have hge : 2 ≤ n := Nat.le_of_not_lt h2
      have hdiv : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have hlog : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
        rw [Nat.log2_def]; simp [hge]
      have hih := ih (n / 2) hdiv
      rw [hlog, Nat.pow_succ]
      omega

private theorem vertexCount_lt_two_pow_L (n : Nat) :
    n < 2 ^ OracleContract.L n := by
  have h := lt_two_pow_log2_succ (n + 1)
  unfold OracleContract.L
  omega

theorem run_sortPhase {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {xs : List Key} (hlen : xs.length ≤ H.vertexCount) (s : State L)
    (hZero : (reg s rZero).val = 0) (hOne : (reg s rOne).val = 1)
    (hK : (reg s rK).val = xs.length)
    (hFA : (reg s rFstA).val = candFstABase H.vertexCount H.arcCount)
    (hSA : (reg s rSndA).val = candSndABase H.vertexCount H.arcCount)
    (hFBslot : (s.data[slotFstB]?).map Fin.val = some (candFstBBase H.vertexCount H.arcCount))
    (hSBslot : (s.data[slotSndB]?).map Fin.val = some (candSndBBase H.vertexCount H.arcCount))
    (hInA : ∀ j : Fin xs.length,
      MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (xs[j.val]'j.isLt)) :
    let ph := sortPhase hi hw h8
    ∃ cur' : List Key, ∃ t : State L, ∃ cost,
      cost ≤ (51 * H.vertexCount + 11) * OracleContract.L H.vertexCount + 8 ∧
      Steps ph.code input cost (Phase.initial s) t ∧
      t.pc = ph.code.size - 1 ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rK).val = xs.length ∧
      (reg t rFstA).val = candFstABase H.vertexCount H.arcCount ∧
      (reg t rSndA).val = candSndABase H.vertexCount H.arcCount ∧
      (reg t rFstB).val = candFstBBase H.vertexCount H.arcCount ∧
      (reg t rSndB).val = candSndBBase H.vertexCount H.arcCount ∧
      cur'.length = xs.length ∧
      (∀ i j (hi' : i < cur'.length) (hj' : j < cur'.length), i ≤ j →
        keyLe (cur'[i]'hi') (cur'[j]'hj')) ∧
      (∀ z : Key, z ∈ cur' ↔ z ∈ xs) ∧
      (∀ j : Fin cur'.length,
        MemPairAt t.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur'[j.val]'j.isLt)) ∧
      (∀ j, j < 6 ∨
        (orderBase H.vertexCount H.arcCount ≤ j ∧ j < candFstABase H.vertexCount H.arcCount) ∨
        dictBase H.vertexCount H.arcCount ≤ j →
        t.data[j]? = s.data[j]?) := by
  intro ph
  obtain ⟨s7, stInit, inv0⟩ := sortInit_steps h8 input hCap hlen s hZero hOne hK hFA hSA hFBslot hSBslot hInA
  have hltL : xs.length < 1 * 2 ^ OracleContract.L H.vertexCount := by
    rw [Nat.one_mul]; exact Nat.lt_of_le_of_lt hlen (vertexCount_lt_two_pow_L H.vertexCount)
  obtain ⟨cur', w', t, cLoop, hcLoop, stLoop, hpc, h0, h1, hk, hfa, hsa, hfb, hsb, hlen', hle', hblk, hmem, hinA, hfr⟩ :=
    passLoop_run h8 input hCap (OracleContract.L H.vertexCount) 1 xs s7 hltL inv0
  have hcost : 7 + cLoop ≤ (51 * H.vertexCount + 11) * OracleContract.L H.vertexCount + 8 := by
    have hmul : 51 * xs.length + 11 ≤ 51 * H.vertexCount + 11 := by omega
    have hmul2 := Nat.mul_le_mul_right (OracleContract.L H.vertexCount) hmul
    omega
  exact ⟨cur', t, 7 + cLoop, hcost, stInit.append stLoop, hpc, h0, h1, hk, hfa, hsa, hfb, hsb,
    hlen', fun i j hi' hj' hij => blockSorted_ge_sorted (by rw [hlen']; exact hle') hblk i j hi' hj' hij,
    hmem, hinA, hfr⟩

end SortPhase

/-! ### Phase 3: Deduplication and serialized dictionary construction (`dedupPhase`) -/

section DedupPhase

private abbrev dZero : Fin 15 := registers.zero      -- 7
private abbrev dOne : Fin 15 := registers.one        -- 5
private abbrev dK : Fin 15 := clk                    -- 10
private abbrev dFstA : Fin 15 := childrenBase        -- 14
private abbrev dSndA : Fin 15 := registers.stackBase -- 1
private abbrev dFstB : Fin 15 := tinBase             -- 11
private abbrev dSndB : Fin 15 := toutBase            -- 12
private abbrev dDict : Fin 15 := cmd                 -- 8
private abbrev dJ : Fin 15 := registers.ptr          -- 0
private abbrev dD : Fin 15 := count                  -- 9
private abbrev dPF : Fin 15 := registers.remain      -- 2
private abbrev dPS : Fin 15 := registers.childBase   -- 3
private abbrev dA : Fin 15 := registers.value        -- 4
private abbrev dB : Fin 15 := offsetBase             -- 13
private abbrev dTmp : Fin 15 := registers.tmp        -- 6

private def dedupBody {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ -- 0..3: load dictBase, init j := 0, d := 0
    .imm dTmp ⟨5, by omega⟩,
    .loadData dDict dTmp,
    .mov dJ dZero,
    .mov dD dZero,
    -- 4..13: dedupHead
    .branchLt dJ dK 5 23,
    .add dTmp dFstA dJ,
    .loadData dA dTmp,
    .add dTmp dSndA dJ,
    .loadData dB dTmp,
    .branchLt dZero dD 10 14,
    .branchLt dPF dA 14 11,
    .branchLt dA dPF 14 12,
    .branchLt dPS dB 14 13,
    .branchLt dB dPS 14 21,
    -- 14..22: emit and advance
    .add dTmp dFstB dD,
    .storeData dTmp dA,
    .add dTmp dSndB dD,
    .storeData dTmp dB,
    .mov dPF dA,
    .mov dPS dB,
    .add dD dD dOne,
    .add dJ dJ dOne,
    .goto 4,
    -- 23..27: serInit
    .storeData dDict dD,
    .add dPF dDict dOne,
    .add dPS dPF dD,
    .add dK dPS dD,
    .mov dJ dZero,
    -- 28..40: serLoop
    .branchLt dJ dD 29 41,
    .add dTmp dFstB dJ,
    .loadData dA dTmp,
    .add dTmp dPF dJ,
    .storeData dTmp dA,
    .add dTmp dSndB dJ,
    .loadData dA dTmp,
    .add dTmp dPS dJ,
    .storeData dTmp dA,
    .add dTmp dK dJ,
    .storeData dTmp dZero,
    .add dJ dJ dOne,
    .goto 28 ]

private theorem dedupBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (dedupBody h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  rfl

def dedupPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (hi := hi) (hw := hw) (dedupBody h8) (dedupBody_nonHalt h8)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private theorem strictSortedList_unique :
    ∀ (xs ys : List Key),
      PairLookup.StrictSorted xs.toArray →
      PairLookup.StrictSorted ys.toArray →
      (∀ k : Key, k ∈ xs ↔ k ∈ ys) →
      xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ hm
    cases ys with
    | nil => rfl
    | cons y _ =>
      have h := (hm y).mpr List.mem_cons_self
      simp at h
  | cons x xs ih =>
    intro ys hxs hys hm
    cases ys with
    | nil =>
      have h := (hm x).mp List.mem_cons_self
      simp at h
    | cons y ys =>
      have hxHead : ∀ z ∈ xs, PairLookup.lexLess x z := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        exact hxs 0 (i + 1) (by simp) (by simp; omega) (by omega)
      have hyHead : ∀ z ∈ ys, PairLookup.lexLess y z := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        exact hys 0 (i + 1) (by simp) (by simp; omega) (by omega)
      have hxTail : PairLookup.StrictSorted xs.toArray := by
        intro i j hi hj hij
        exact hxs (i + 1) (j + 1) (by simp at hi ⊢; omega) (by simp at hj ⊢; omega) (by omega)
      have hyTail : PairLookup.StrictSorted ys.toArray := by
        intro i j hi hj hij
        exact hys (i + 1) (j + 1) (by simp at hi ⊢; omega) (by simp at hj ⊢; omega) (by omega)
      have hxy : x = y := by
        by_cases he : x = y
        · exact he
        · have h1 := List.mem_cons.mp ((hm x).mp List.mem_cons_self) |>.resolve_left he
          have h2 := List.mem_cons.mp ((hm y).mpr List.mem_cons_self) |>.resolve_left (fun e => he e.symm)
          exact False.elim (PairLookup.lexLess_irrefl x (PairLookup.lexLess_trans (hxHead y h2) (hyHead x h1)))
      subst y
      apply congrArg (List.cons x)
      apply ih ys hxTail hyTail
      intro z
      by_cases hz : z = x
      · subst z
        have hnx : x ∉ xs := fun h => PairLookup.lexLess_irrefl x (hxHead x h)
        have hny : x ∉ ys := fun h => PairLookup.lexLess_irrefl x (hyHead x h)
        simp [hnx, hny]
      · simpa only [List.mem_cons, hz, false_or] using hm z

private theorem keyLe_and_ne_implies_lexLess {x y : Key} (hle : keyLe x y) (hne : x ≠ y) :
    PairLookup.lexLess x y := by
  rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
  rcases hle with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · dsimp only at h1 h2
    refine Or.inr ⟨h1, ?_⟩
    have : b1 ≠ b2 := fun hb => hne (Prod.ext h1 hb)
    omega

private structure DedupInv (H : LabelledQuotient) (cur : List Key) (origA : Array (Word bits))
    (j : Nat) (acc : List Key) (s : State L) : Prop where
  pc : s.pc = 4
  zero : (reg s dZero).val = 0
  one : (reg s dOne).val = 1
  kVal : (reg s dK).val = cur.length
  fstAVal : (reg s dFstA).val = candFstABase H.vertexCount H.arcCount
  sndAVal : (reg s dSndA).val = candSndABase H.vertexCount H.arcCount
  fstBVal : (reg s dFstB).val = candFstBBase H.vertexCount H.arcCount
  sndBVal : (reg s dSndB).val = candSndBBase H.vertexCount H.arcCount
  dictVal : (reg s dDict).val = dictBase H.vertexCount H.arcCount
  jVal : (reg s dJ).val = j
  dVal : (reg s dD).val = acc.length
  jLe : j ≤ cur.length
  accLe : acc.length ≤ j
  strict : PairLookup.StrictSorted acc.toArray
  lastLe : ∀ (hx : 0 < acc.length) (hjl : j < cur.length),
    keyLe (acc[acc.length - 1]'(by omega)) (cur[j]'hjl)
  pfSpec : ∀ hx : 0 < acc.length,
    (reg s dPF).val = (acc[acc.length - 1]'(by omega)).1 ∧
    (reg s dPS).val = (acc[acc.length - 1]'(by omega)).2
  memAcc : ∀ z : Key, z ∈ acc ↔ ∃ t, ∃ ht : t < cur.length, t < j ∧ cur[t]'ht = z
  inB : ∀ idx : Fin acc.length,
    MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx.val (acc[idx.val]'idx.isLt)
  frameDedup : ∀ idx,
    idx < candFstBBase H.vertexCount H.arcCount ∨ dictBase H.vertexCount H.arcCount ≤ idx →
    s.data[idx]? = origA[idx]?

private theorem dedup_loop {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {cur : List Key} (hLen : cur.length ≤ H.vertexCount)
    (hSorted : ∀ i j (hi : i < cur.length) (hj : j < cur.length), i ≤ j → keyLe (cur[i]'hi) (cur[j]'hj))
    {origA : Array (Word bits)}
    (hInA : ∀ j : Fin cur.length,
      MemPairAt origA (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt)) :
    ∀ rem j acc (s : State L),
      cur.length - j = rem →
      DedupInv H cur origA j acc s →
      ∃ acc' : List Key, ∃ t : State L, ∃ cost,
        cost ≤ 19 * rem ∧
        Steps (dedupPhase hi hw h8).code input cost s t ∧
        DedupInv H cur origA cur.length acc' t := by
  let code := (dedupPhase hi hw h8).code
  have hSize : code.size = 42 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  intro rem
  induction rem with
  | zero =>
    intro j acc s hrem inv
    have hjeq : j = cur.length := by have := inv.jLe; omega
    subst hjeq
    exact ⟨acc, s, 0, by omega, .zero s, inv⟩
  | succ rem ih =>
    intro j acc s hrem inv
    have hjlt : j < cur.length := by have := inv.jLe; omega
    have hjB : j < H.vertexCount := Nat.lt_of_lt_of_le hjlt hLen
    have haccB : acc.length ≤ H.vertexCount := by have := inv.accLe; have := inv.jLe; omega
    have hInACur : MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j (cur[j]'hjlt) := by
      have hf1 : candFstABase H.vertexCount H.arcCount + j < candFstBBase H.vertexCount H.arcCount := by
        simp only [candFstBBase, candSndABase]; omega
      have hf2 : candSndABase H.vertexCount H.arcCount + j < candFstBBase H.vertexCount H.arcCount := by
        simp only [candFstBBase, candSndABase]; omega
      exact ⟨by rw [inv.frameDedup _ (Or.inl hf1)]; exact (hInA ⟨j, hjlt⟩).1,
             by rw [inv.frameDedup _ (Or.inl hf2)]; exact (hInA ⟨j, hjlt⟩).2⟩
    obtain ⟨⟨w1, hw1, hw1v⟩, ⟨w2, hw2, hw2v⟩⟩ := memPairAt_word hInACur
    -- 4: branchLt dJ dK 5 23
    have b4 : step code input s = some (.next { s with pc := 5 }) :=
      step_branchLt_true (by rw [inv.pc]; rfl) (by rw [inv.jVal, inv.kVal]; exact hjlt) (by omega)
    -- 5..8: load fstA[j] -> dA, sndA[j] -> dB
    have hb1 : (reg { s with pc := 5 } dFstA).val + (reg { s with pc := 5 } dJ).val < workCap := by
      change (reg s dFstA).val + (reg s dJ).val < workCap
      rw [inv.fstAVal, inv.jVal]; simp only [candFstABase, predBufBase, rowEndBase, rowStartBase,
        ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    obtain ⟨s7, st57, pc7, r7, k7, d7⟩ := loadAtOffset_steps (code := code) (input := input)
      (s := { s with pc := 5 }) (entry := 5) (tmp := dTmp) (dst := dA) (base := dFstA) (idx := dJ)
      (w := w1) rfl rfl rfl (by omega) hb1
      (by change s.data[(reg s dFstA).val + (reg s dJ).val]? = _; rw [inv.fstAVal, inv.jVal]; exact hw1)
    have hb2 : (reg s7 dSndA).val + (reg s7 dJ).val < workCap := by
      rw [k7 _ (by decide) (by decide), k7 _ (by decide) (by decide)]
      change (reg s dSndA).val + (reg s dJ).val < workCap
      rw [inv.sndAVal, inv.jVal]; simp only [candSndABase, candFstABase, predBufBase, rowEndBase,
        rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    obtain ⟨s9, st79, pc9, r9, k9, d9⟩ := loadAtOffset_steps (code := code) (input := input)
      (s := s7) (entry := 7) (tmp := dTmp) (dst := dB) (base := dSndA) (idx := dJ)
      (w := w2) rfl rfl pc7 (by omega) hb2
      (by rw [d7, k7 _ (by decide) (by decide), k7 _ (by decide) (by decide)]
          change s.data[(reg s dSndA).val + (reg s dJ).val]? = _; rw [inv.sndAVal, inv.jVal]; exact hw2)
    have keep9 (r : Fin 15) (hr : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dJ, dD, dPF, dPS] : List (Fin 15))) :
        reg s9 r = reg s r := by
      have hneq : r ≠ dTmp ∧ r ≠ dA ∧ r ≠ dB := by revert r hr; decide
      exact (k9 r hneq.1 hneq.2.2).trans (k7 r hneq.1 hneq.2.1)
    have s9A : (reg s9 dA).val = (cur[j]'hjlt).1 := by rw [k9 _ (by decide) (by decide), r7, hw1v]
    have s9B : (reg s9 dB).val = (cur[j]'hjlt).2 := by rw [r9, hw2v]
    have s9Data : s9.data = s.data := d9.trans d7
    -- Helper for emit at pc = 14 (9 steps -> 4)
    have emitBlock : ∀ (u : State L), u.pc = 14 → u.data = s.data →
        (∀ r : Fin 15, r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dJ, dD, dA, dB] : List (Fin 15)) →
          reg u r = reg s9 r) →
        (hStrictNext : acc.length = 0 ∨ ∀ hx : 0 < acc.length, acc[acc.length - 1]'(by omega) ≠ cur[j]'hjlt) →
        ∃ t : State L, Steps code input 9 u t ∧
          DedupInv H cur origA (j + 1) (acc ++ [cur[j]'hjlt]) t := by
      intro u hupc hudata hukeep hne
      have hDlt : acc.length < H.vertexCount := by have := inv.accLe; omega
      have hbFB : (reg u dFstB).val + (reg u dD).val < workCap := by
        rw [hukeep _ (by decide), hukeep _ (by decide), keep9 _ (by decide), keep9 _ (by decide), inv.fstBVal, inv.dVal]
        simp only [candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase,
          ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
      obtain ⟨u2, st14, pc16, d16, k16⟩ := storeAtOffset_steps (code := code) (input := input)
        (s := u) (entry := 14) (tmp := dTmp) (base := dFstB) (idx := dD) (src := dA)
        rfl rfl hupc (by omega) (by decide) hbFB
      have hbSB : (reg u2 dSndB).val + (reg u2 dD).val < workCap := by
        rw [k16 _ (by decide), k16 _ (by decide), hukeep _ (by decide), hukeep _ (by decide),
            keep9 _ (by decide), keep9 _ (by decide), inv.sndBVal, inv.dVal]
        simp only [candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase,
          rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
      obtain ⟨u4, st16, pc18, d18, k18⟩ := storeAtOffset_steps (code := code) (input := input)
        (s := u2) (entry := 16) (tmp := dTmp) (base := dSndB) (idx := dD) (src := dB)
        rfl rfl pc16 (by omega) (by decide) hbSB
      obtain ⟨u5, st18, pc19, r19, k19, d19⟩ := step_mov_at (code := code) (input := input)
        (s := u4) (d := dPF) (src := dA) (by rw [pc18]; rfl) (by omega)
      obtain ⟨u6, st19, pc20, r20, k20, d20⟩ := step_mov_at (code := code) (input := input)
        (s := u5) (d := dPS) (src := dB) (by rw [show u5.pc = 19 by omega]; rfl) (by omega)
      obtain ⟨u7, st20, pc21, r21, k21, d21⟩ := step_add15_at (code := code) (input := input)
        (s := u6) (d := dD) (lhs := dD) (rhs := dOne) (by rw [show u6.pc = 20 by omega]; rfl) (by omega)
      obtain ⟨u8, st21, pc22, r22, k22, d22⟩ := step_add15_at (code := code) (input := input)
        (s := u7) (d := dJ) (lhs := dJ) (rhs := dOne) (by rw [show u7.pc = 21 by omega]; rfl) (by omega)
      let t : State L := { u8 with pc := 4 }
      have st22 : step code input u8 = some (.next t) :=
        step_goto_at (code := code) (input := input) (s := u8) (target := 4)
          (by rw [show u8.pc = 22 by omega]; rfl) (by omega)
      have hkeepT (r : Fin 15) (hr : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict] : List (Fin 15))) :
          reg t r = reg s r := by
        have hneq : r ≠ dTmp ∧ r ≠ dPF ∧ r ≠ dPS ∧ r ≠ dD ∧ r ≠ dJ := by revert r hr; decide
        have hm9 : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dJ, dD, dPF, dPS] : List (Fin 15)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        have hmu : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dJ, dD, dA, dB] : List (Fin 15)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        exact ((k22 r hneq.2.2.2.2).trans ((k21 r hneq.2.2.2.1).trans ((k20 r hneq.2.2.1).trans
          ((k19 r hneq.2.1).trans ((k18 r hneq.1).trans ((k16 r hneq.1).trans (hukeep r hmu))))))).trans
          (keep9 r hm9)
      have hsds : s.data.size = workCap := s.data_size
      have hsdsU : u.data.size = workCap := u.data_size
      have hsdsU2 : u2.data.size = workCap := u2.data_size
      have h1 : (reg u dFstB).val + (reg u dD).val = candFstBBase H.vertexCount H.arcCount + acc.length := by
        rw [hukeep _ (by decide), hukeep _ (by decide), keep9 _ (by decide), keep9 _ (by decide), inv.fstBVal, inv.dVal]
      have h2 : (reg u2 dSndB).val + (reg u2 dD).val = candSndBBase H.vertexCount H.arcCount + acc.length := by
        rw [k16 _ (by decide), k16 _ (by decide), hukeep _ (by decide), hukeep _ (by decide),
            keep9 _ (by decide), keep9 _ (by decide), inv.sndBVal, inv.dVal]
      have hdst1 : candFstBBase H.vertexCount H.arcCount + acc.length < s.data.size := by
        rw [hsds, ← h1]; exact hbFB
      have hdst2 : candSndBBase H.vertexCount H.arcCount + acc.length <
          (s.data.set (candFstBBase H.vertexCount H.arcCount + acc.length) (reg u dA) hdst1).size := by
        rw [Array.size_set, hsds, ← h2]; exact hbSB
      have hd16' : u2.data = s.data.set (candFstBBase H.vertexCount H.arcCount + acc.length) (reg u dA) hdst1 := by
        rw [d16]; exact array_set_congr (v := reg u dA) (w := reg u dA)
          (by rw [hsdsU]; exact hbFB) hdst1 hudata h1 rfl
      have hA_eq : reg u2 dB = reg u dB := k16 _ (by decide)
      have htData : t.data =
          (s.data.set (candFstBBase H.vertexCount H.arcCount + acc.length) (reg u dA) hdst1).set
            (candSndBBase H.vertexCount H.arcCount + acc.length) (reg u dB) hdst2 := by
        change u8.data = _
        rw [d22, d21, d20, d19, d18]
        exact array_set_congr (v := reg u2 dB) (w := reg u dB)
          (by rw [hsdsU2]; exact hbSB) hdst2 hd16' h2 hA_eq
      have hIdxNe : candFstBBase H.vertexCount H.arcCount + acc.length ≠
          candSndBBase H.vertexCount H.arcCount + acc.length := by
        simp only [candSndBBase]; omega
      have hUAVal : (reg u dA).val = (cur[j]'hjlt).1 := by rw [hukeep _ (by decide), s9A]
      have hUBVal : (reg u dB).val = (cur[j]'hjlt).2 := by rw [hukeep _ (by decide), s9B]
      have hD6 : (reg u6 dD).val = acc.length := by
        rw [k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), k16 _ (by decide),
            hukeep _ (by decide), keep9 _ (by decide), inv.dVal]
      have hO6 : (reg u6 dOne).val = 1 := by
        rw [k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), k16 _ (by decide),
            hukeep _ (by decide), keep9 _ (by decide), inv.one]
      have hD7 : (reg u7 dD).val = acc.length + 1 := by
        rw [r21, PaperB.WordOps.add_no_wrap _ _ (by rw [hD6, hO6]; omega), hD6, hO6]
      have hJ7 : (reg u7 dJ).val = j := by
        rw [k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), k16 _ (by decide),
            hukeep _ (by decide), keep9 _ (by decide), inv.jVal]
      have hO7 : (reg u7 dOne).val = 1 := by
        rw [k21 _ (by decide), hO6]
      have hJ8 : (reg u8 dJ).val = j + 1 := by
        rw [r22, PaperB.WordOps.add_no_wrap _ _ (by rw [hJ7, hO7]; omega), hJ7, hO7]
      have hLastEq : (acc ++ [cur[j]'hjlt])[(acc ++ [cur[j]'hjlt]).length - 1]'(by simp) = cur[j]'hjlt := by
        simp [List.getElem_append_right]
      have hStrict' : PairLookup.StrictSorted (acc ++ [cur[j]'hjlt]).toArray := by
        intro p q hp hq hpq
        simp only [List.size_toArray, List.length_append, List.length_singleton] at hp hq
        simp only [List.getElem_toArray]
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hq' | rfl
        · have hp' : p < acc.length := Nat.lt_trans hpq hq'
          simp only [List.getElem_append_left hp', List.getElem_append_left hq']
          exact inv.strict p q (by simp; exact hp') (by simp; exact hq') hpq
        · simp only [List.getElem_append_left (by omega : p < acc.length),
            List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
          rcases hne with hzero | hpos
          · omega
          · have haccPos : 0 < acc.length := by omega
            have hneLast := hpos haccPos
            have hleLast : keyLe (acc[acc.length - 1]'(by omega)) (cur[j]'hjlt) := inv.lastLe haccPos hjlt
            have hltLast : PairLookup.lexLess (acc[acc.length - 1]'(by omega)) (cur[j]'hjlt) :=
              keyLe_and_ne_implies_lexLess hleLast hneLast
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : p < (acc.length - 1) + 1)) with hp' | hpEq
            · exact PairLookup.lexLess_trans (inv.strict p (acc.length - 1) (by simp; omega) (by simp; omega) hp') hltLast
            · subst hpEq; exact hltLast
      refine ⟨t, st14.append (st16.append (.cons st18 (.cons st19 (.cons st20 (.cons st21 (.cons st22 (.zero t))))))),
        rfl, by rw [hkeepT _ (by decide), inv.zero], by rw [hkeepT _ (by decide), inv.one],
        by rw [hkeepT _ (by decide), inv.kVal], by rw [hkeepT _ (by decide), inv.fstAVal],
        by rw [hkeepT _ (by decide), inv.sndAVal], by rw [hkeepT _ (by decide), inv.fstBVal],
        by rw [hkeepT _ (by decide), inv.sndBVal], by rw [hkeepT _ (by decide), inv.dictVal],
        hJ8, by change (reg u8 dD).val = _; rw [k22 _ (by decide), hD7]; simp,
        by omega, by simp only [List.length_append, List.length_singleton]; exact Nat.succ_le_succ inv.accLe,
        hStrict', ?_, ?_, ?_, ?_, ?_⟩
      · intro _ hj1
        rw [hLastEq]
        exact hSorted j (j + 1) hjlt hj1 (Nat.le_succ j)
      · intro _
        rw [hLastEq]
        constructor
        · change (reg u8 dPF).val = _; rw [k22 _ (by decide), k21 _ (by decide), k20 _ (by decide), r19,
            k18 _ (by decide), k16 _ (by decide), hUAVal]
        · change (reg u8 dPS).val = _; rw [k22 _ (by decide), k21 _ (by decide), r20,
            k19 _ (by decide), k18 _ (by decide), hA_eq, hUBVal]
      · intro z
        simp only [List.mem_append, List.mem_singleton, inv.memAcc]
        constructor
        · rintro (⟨t0, ht0, ht0lt, rfl⟩ | rfl)
          · exact ⟨t0, ht0, Nat.lt_succ_of_lt ht0lt, rfl⟩
          · exact ⟨j, hjlt, Nat.lt_succ_self j, rfl⟩
        · rintro ⟨t0, ht0, ht0lt, rfl⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht0lt) with hlt | rfl
          · exact Or.inl ⟨t0, ht0, hlt, rfl⟩
          · exact Or.inr rfl
      · intro idx
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa only [List.length_append, List.length_singleton] using idx.isLt)) with hlt | heq
        · have hne1 : candFstBBase H.vertexCount H.arcCount + acc.length ≠ candFstBBase H.vertexCount H.arcCount + idx.val := by omega
          have hne2 : candSndBBase H.vertexCount H.arcCount + acc.length ≠ candFstBBase H.vertexCount H.arcCount + idx.val := by
            simp only [candSndBBase]; omega
          have hne3 : candFstBBase H.vertexCount H.arcCount + acc.length ≠ candSndBBase H.vertexCount H.arcCount + idx.val := by
            simp only [candSndBBase]; omega
          have hne4 : candSndBBase H.vertexCount H.arcCount + acc.length ≠ candSndBBase H.vertexCount H.arcCount + idx.val := by omega
          have hprev := inv.inB ⟨idx.val, hlt⟩
          simp only [List.getElem_append_left hlt]
          exact ⟨by rw [htData, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]; exact hprev.1,
                 by rw [htData, Array.getElem?_set_ne _ hne4, Array.getElem?_set_ne _ hne3]; exact hprev.2⟩
        · have hget : (acc ++ [cur[j]'hjlt])[idx.val]'idx.isLt = cur[j]'hjlt := by
            simp only [heq, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
          rw [hget]
          exact ⟨by rw [htData, heq, Array.getElem?_set_ne _ (Ne.symm hIdxNe), Array.getElem?_set_self, Option.map_some, hUAVal],
                 by rw [htData, heq, Array.getElem?_set_self, Option.map_some, hUBVal]⟩
      · intro idx hidx
        have hne1 : candFstBBase H.vertexCount H.arcCount + acc.length ≠ idx := by
          rcases hidx with h | h
          · omega
          · simp only [dictBase, candSndBBase, candFstBBase] at h ⊢; omega
        have hne2 : candSndBBase H.vertexCount H.arcCount + acc.length ≠ idx := by
          rcases hidx with h | h
          · simp only [candSndBBase, candFstBBase] at h ⊢; omega
          · simp only [dictBase, candSndBBase] at h ⊢; omega
        rw [htData, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
        exact inv.frameDedup idx hidx
    -- Dispatch at pc = 9: branchLt dZero dD 10 14
    by_cases hd0 : acc.length = 0
    · have b9 : step code input s9 = some (.next { s9 with pc := 14 }) :=
        step_branchLt_false (by rw [pc9]; rfl) (by rw [keep9 _ (by decide), keep9 _ (by decide), inv.zero, inv.dVal, hd0]; exact Nat.le_refl _) (by omega)
      obtain ⟨t, stEmit, inv'⟩ := emitBlock { s9 with pc := 14 } rfl s9Data (fun _ _ => rfl) (Or.inl hd0)
      obtain ⟨acc', tFin, c2, hc2, st2, invFin⟩ := ih (j + 1) (acc ++ [cur[j]'hjlt]) t (by omega) inv'
      exact ⟨acc', tFin, 1 + 4 + 1 + 9 + c2, by omega,
        (Steps.cons b4 (st57.append (st79.append (Steps.cons b9 stEmit)))).append st2, invFin⟩
    · have hdPos : 0 < acc.length := Nat.pos_of_ne_zero hd0
      have b9 : step code input s9 = some (.next { s9 with pc := 10 }) :=
        step_branchLt_true (by rw [pc9]; rfl) (by rw [keep9 _ (by decide), keep9 _ (by decide), inv.zero, inv.dVal]; exact hdPos) (by omega)
      obtain ⟨hpf, hps⟩ := inv.pfSpec hdPos
      have hpf9 : (reg s9 dPF).val = (acc[acc.length - 1]'(by omega)).1 := by rw [keep9 _ (by decide), hpf]
      have hps9 : (reg s9 dPS).val = (acc[acc.length - 1]'(by omega)).2 := by rw [keep9 _ (by decide), hps]
      by_cases heqPair : acc[acc.length - 1]'(by omega) = cur[j]'hjlt
      · -- Duplicate: take false branches 10 -> 11 -> 12 -> 13 -> 21, then j++, goto 4 (total 12 steps after 9)
        have hpfEq : (reg s9 dPF).val = (reg s9 dA).val := by rw [hpf9, s9A, heqPair]
        have hpsEq : (reg s9 dPS).val = (reg s9 dB).val := by rw [hps9, s9B, heqPair]
        have b10 : step code input { s9 with pc := 10 } = some (.next { s9 with pc := 11 }) :=
          step_branchLt_false rfl (by change (reg s9 dA).val ≤ (reg s9 dPF).val; rw [hpfEq]; exact Nat.le_refl _) (by omega)
        have b11 : step code input { s9 with pc := 11 } = some (.next { s9 with pc := 12 }) :=
          step_branchLt_false rfl (by change (reg s9 dPF).val ≤ (reg s9 dA).val; rw [hpfEq]; exact Nat.le_refl _) (by omega)
        have b12 : step code input { s9 with pc := 12 } = some (.next { s9 with pc := 13 }) :=
          step_branchLt_false rfl (by change (reg s9 dB).val ≤ (reg s9 dPS).val; rw [hpsEq]; exact Nat.le_refl _) (by omega)
        have b13 : step code input { s9 with pc := 13 } = some (.next { s9 with pc := 21 }) :=
          step_branchLt_false rfl (by change (reg s9 dPS).val ≤ (reg s9 dB).val; rw [hpsEq]; exact Nat.le_refl _) (by omega)
        obtain ⟨u22, st21, pc22, r22, k22, d22⟩ := step_add15_at (code := code) (input := input)
          (s := { s9 with pc := 21 }) (d := dJ) (lhs := dJ) (rhs := dOne) rfl (by dsimp; omega)
        let t : State L := { u22 with pc := 4 }
        have st22 : step code input u22 = some (.next t) :=
          step_goto_at (code := code) (input := input) (s := u22) (target := 4)
            (by rw [show u22.pc = 22 by dsimp at pc22; omega]; rfl) (by omega)
        have hkeepT (r : Fin 15) (hr : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dD, dPF, dPS] : List (Fin 15))) :
            reg t r = reg s r := by
          have hneq : r ≠ dJ := by revert r hr; decide
          have hm9 : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB, dDict, dJ, dD, dPF, dPS] : List (Fin 15)) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
          exact (k22 r hneq).trans (keep9 r hm9)
        have htData : t.data = s.data := d22.trans s9Data
        have hJ9 : (reg s9 dJ).val = j := by rw [keep9 _ (by decide), inv.jVal]
        have hO9 : (reg s9 dOne).val = 1 := by rw [keep9 _ (by decide), inv.one]
        have htJ : (reg t dJ).val = j + 1 := by
          change (reg u22 dJ).val = _
          have hJ' : (reg { s9 with pc := 21 } dJ).val = j := hJ9
          have hO' : (reg { s9 with pc := 21 } dOne).val = 1 := hO9
          rw [r22, PaperB.WordOps.add_no_wrap _ _ (by rw [hJ', hO']; omega), hJ', hO']
        have hmem' : ∀ z : Key, z ∈ acc ↔ ∃ t0, ∃ ht0 : t0 < cur.length, t0 < j + 1 ∧ cur[t0]'ht0 = z := by
          intro z
          rw [inv.memAcc z]
          constructor
          · rintro ⟨t0, ht0, ht0lt, rfl⟩; exact ⟨t0, ht0, Nat.lt_succ_of_lt ht0lt, rfl⟩
          · rintro ⟨t0, ht0, ht0lt, rfl⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht0lt) with hlt | rfl
            · exact ⟨t0, ht0, hlt, rfl⟩
            · rw [← heqPair]; exact (inv.memAcc _).mp (List.getElem_mem (by omega))
        have inv' : DedupInv H cur origA (j + 1) acc t :=
          ⟨rfl, by rw [hkeepT _ (by decide), inv.zero], by rw [hkeepT _ (by decide), inv.one],
           by rw [hkeepT _ (by decide), inv.kVal], by rw [hkeepT _ (by decide), inv.fstAVal],
           by rw [hkeepT _ (by decide), inv.sndAVal], by rw [hkeepT _ (by decide), inv.fstBVal],
           by rw [hkeepT _ (by decide), inv.sndBVal], by rw [hkeepT _ (by decide), inv.dictVal],
           htJ, by rw [hkeepT _ (by decide), inv.dVal], hjlt, Nat.le_trans inv.accLe (Nat.le_succ j),
           inv.strict, fun hx hj1 => keyLe_trans (inv.lastLe hx hjlt) (hSorted j (j + 1) hjlt hj1 (Nat.le_succ j)),
           fun hx => ⟨by rw [hkeepT _ (by decide)]; exact (inv.pfSpec hx).1,
                      by rw [hkeepT _ (by decide)]; exact (inv.pfSpec hx).2⟩,
           hmem', fun idx => by rw [htData]; exact inv.inB idx, fun idx hidx => by rw [htData]; exact inv.frameDedup idx hidx⟩
        obtain ⟨acc', tFin, c2, hc2, st2, invFin⟩ := ih (j + 1) acc t (by omega) inv'
        exact ⟨acc', tFin, 1 + 4 + 5 + 2 + c2, by omega,
          (Steps.cons b4 (st57.append (st79.append (Steps.cons b9 (Steps.cons b10 (Steps.cons b11
            (Steps.cons b12 (Steps.cons b13 (Steps.cons st21 (Steps.cons st22 (.zero t))))))))))).append st2, invFin⟩
      · -- Distinct: branch to 14 in ≤ 4 steps from 10
        have hcheckNe : ∃ cChk, cChk ≤ 4 ∧ Steps code input cChk { s9 with pc := 10 } { s9 with pc := 14 } := by
          rcases Nat.lt_trichotomy (reg s9 dPF).val (reg s9 dA).val with h1 | h1 | h1
          · exact ⟨1, by omega, .cons (step_branchLt_true (code := code) (s := { s9 with pc := 10 }) rfl h1 (by omega)) (.zero _)⟩
          · have b10 : step code input { s9 with pc := 10 } = some (.next { s9 with pc := 11 }) :=
              step_branchLt_false (code := code) rfl (by omega : (reg s9 dA).val ≤ (reg s9 dPF).val) (by dsimp; omega)
            have b11 : step code input { s9 with pc := 11 } = some (.next { s9 with pc := 12 }) :=
              step_branchLt_false (code := code) rfl (by omega : (reg s9 dPF).val ≤ (reg s9 dA).val) (by dsimp; omega)
            have h2ne : (reg s9 dPS).val ≠ (reg s9 dB).val := by
              intro h2; exact heqPair (Prod.ext (by rw [← hpf9, h1, s9A]) (by rw [← hps9, h2, s9B]))
            rcases Nat.lt_or_gt_of_ne h2ne with h2lt | h2gt
            · exact ⟨3, by omega, .cons b10 (.cons b11 (.cons (step_branchLt_true (code := code) (s := { s9 with pc := 12 }) rfl h2lt (by omega)) (.zero _)))⟩
            · have b12 : step code input { s9 with pc := 12 } = some (.next { s9 with pc := 13 }) :=
                step_branchLt_false (code := code) rfl (by omega : (reg s9 dB).val ≤ (reg s9 dPS).val) (by dsimp; omega)
              exact ⟨4, by omega, .cons b10 (.cons b11 (.cons b12 (.cons (step_branchLt_true (code := code) (s := { s9 with pc := 13 }) rfl h2gt (by omega)) (.zero _))))⟩
          · have b10 : step code input { s9 with pc := 10 } = some (.next { s9 with pc := 11 }) :=
              step_branchLt_false (code := code) rfl (by omega : (reg s9 dA).val ≤ (reg s9 dPF).val) (by dsimp; omega)
            exact ⟨2, by omega, .cons b10 (.cons (step_branchLt_true (code := code) (s := { s9 with pc := 11 }) rfl h1 (by omega)) (.zero _))⟩
        obtain ⟨cChk, hcChk, stChk⟩ := hcheckNe
        obtain ⟨t, stEmit, inv'⟩ := emitBlock { s9 with pc := 14 } rfl s9Data (fun _ _ => rfl)
          (Or.inr (fun _ => heqPair))
        obtain ⟨acc', tFin, c2, hc2, st2, invFin⟩ := ih (j + 1) (acc ++ [cur[j]'hjlt]) t (by omega) inv'
        exact ⟨acc', tFin, _, by omega,
          (Steps.cons b4 (st57.append (st79.append (Steps.cons b9 (stChk.append stEmit))))).append st2, invFin⟩

private theorem ser_loop {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {acc : List Key} (hAccB : acc.length ≤ H.vertexCount)
    {origB : Array (Word bits)}
    (hInB : ∀ idx : Fin acc.length,
      MemPairAt origB (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx.val (acc[idx.val]'idx.isLt))
    (hCount : (origB[dictBase H.vertexCount H.arcCount]?).map Fin.val = some acc.length) :
    ∀ k (hk : k ≤ acc.length), ∀ s : State L,
      s.pc = 28 →
      (reg s dZero).val = 0 → (reg s dOne).val = 1 → (reg s dD).val = acc.length →
      (reg s dFstB).val = candFstBBase H.vertexCount H.arcCount →
      (reg s dSndB).val = candSndBBase H.vertexCount H.arcCount →
      (reg s dPF).val = dictBase H.vertexCount H.arcCount + 1 →
      (reg s dPS).val = dictBase H.vertexCount H.arcCount + 1 + acc.length →
      (reg s dK).val = dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length →
      (reg s dJ).val = k →
      (∀ i (hi : i < k),
        (s.data[dictBase H.vertexCount H.arcCount + 1 + i]?).map Fin.val = some (acc[i]'(by omega)).1 ∧
        (s.data[dictBase H.vertexCount H.arcCount + 1 + acc.length + i]?).map Fin.val = some (acc[i]'(by omega)).2 ∧
        (s.data[dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + i]?).map Fin.val = some 0) →
      (∀ idx,
        idx < dictBase H.vertexCount H.arcCount + 1 ∨
        (dictBase H.vertexCount H.arcCount + 1 + k ≤ idx ∧ idx < dictBase H.vertexCount H.arcCount + 1 + acc.length) ∨
        (dictBase H.vertexCount H.arcCount + 1 + acc.length + k ≤ idx ∧ idx < dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length) ∨
        dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k ≤ idx →
        s.data[idx]? = origB[idx]?) →
      ∃ t : State L, ∃ cost, cost ≤ 13 * (acc.length - k) + 1 ∧
        Steps (dedupPhase hi hw h8).code input cost s t ∧
        t.pc = (dedupPhase hi hw h8).code.size - 1 ∧
        (t.data[dictBase H.vertexCount H.arcCount]?).map Fin.val = some acc.length ∧
        (∀ i (hi : i < acc.length),
          (t.data[dictBase H.vertexCount H.arcCount + 1 + i]?).map Fin.val = some (acc[i]'hi).1 ∧
          (t.data[dictBase H.vertexCount H.arcCount + 1 + acc.length + i]?).map Fin.val = some (acc[i]'hi).2 ∧
          (t.data[dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + i]?).map Fin.val = some 0) ∧
        (∀ idx, idx < dictBase H.vertexCount H.arcCount ∨
          dictBase H.vertexCount H.arcCount + (1 + 3 * acc.length) ≤ idx →
          t.data[idx]? = origB[idx]?) := by
  let code := (dedupPhase hi hw h8).code
  have hSize : code.size = 42 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  intro k hk
  induction hd : acc.length - k generalizing k with
  | zero =>
    intro s hpc h0 h1 hD hFB hSB hPF hPS hK hJ hOut hFr
    have hkeq : k = acc.length := by omega
    subst hkeq
    have b28 : step code input s = some (.next { s with pc := 41 }) :=
      step_branchLt_false (by rw [hpc]; rfl) (by rw [hJ, hD]; exact Nat.le_refl _) (by omega)
    refine ⟨{ s with pc := 41 }, 1, by omega, .cons b28 (.zero _), by rw [hSize], ?_, hOut, ?_⟩
    · rw [hFr _ (Or.inl (by omega))]; exact hCount
    · intro idx hidx
      apply hFr
      rcases hidx with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inr (by omega)))
  | succ d ih =>
    intro s hpc h0 h1 hD hFB hSB hPF hPS hK hJ hOut hFr
    have hklt : k < acc.length := by omega
    have b28 : step code input s = some (.next { s with pc := 29 }) :=
      step_branchLt_true (by rw [hpc]; rfl) (by rw [hJ, hD]; exact hklt) (by omega)
    have hInBCur : MemPairAt s.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) k (acc[k]'hklt) := by
      have hf1 : candFstBBase H.vertexCount H.arcCount + k < dictBase H.vertexCount H.arcCount + 1 := by
        simp only [dictBase, candSndBBase]; omega
      have hf2 : candSndBBase H.vertexCount H.arcCount + k < dictBase H.vertexCount H.arcCount + 1 := by
        simp only [dictBase]; omega
      exact ⟨by rw [hFr _ (Or.inl hf1)]; exact (hInB ⟨k, hklt⟩).1,
             by rw [hFr _ (Or.inl hf2)]; exact (hInB ⟨k, hklt⟩).2⟩
    obtain ⟨⟨w1, hw1, hw1v⟩, ⟨w2, hw2, hw2v⟩⟩ := memPairAt_word hInBCur
    -- 29..30: load fstB[k] -> dA
    have hbFB : (reg { s with pc := 29 } dFstB).val + (reg { s with pc := 29 } dJ).val < workCap := by
      change (reg s dFstB).val + (reg s dJ).val < workCap
      rw [hFB, hJ]; simp only [candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase,
        rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    obtain ⟨s31, st29_31, pc31, r31, k31, d31⟩ := loadAtOffset_steps (code := code) (input := input)
      (s := { s with pc := 29 }) (entry := 29) (tmp := dTmp) (dst := dA) (base := dFstB) (idx := dJ)
      (w := w1) rfl rfl rfl (by omega) hbFB
      (by change s.data[(reg s dFstB).val + (reg s dJ).val]? = _; rw [hFB, hJ]; exact hw1)
    -- 31..32: store dPF[k] := dA
    have hb1 : (reg s31 dPF).val + (reg s31 dJ).val < workCap := by
      rw [k31 _ (by decide) (by decide), k31 _ (by decide) (by decide)]
      change (reg s dPF).val + (reg s dJ).val < workCap
      rw [hPF, hJ]; simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
      omega
    obtain ⟨s33, st31_33, pc33, d33, k33⟩ := storeAtOffset_steps (code := code) (input := input)
      (s := s31) (entry := 31) (tmp := dTmp) (base := dPF) (idx := dJ) (src := dA)
      rfl rfl pc31 (by omega) (by decide) hb1
    -- 33..34: load sndB[k] -> dA
    have hbSB : (reg s33 dSndB).val + (reg s33 dJ).val < workCap := by
      rw [k33 _ (by decide), k33 _ (by decide), k31 _ (by decide) (by decide), k31 _ (by decide) (by decide)]
      change (reg s dSndB).val + (reg s dJ).val < workCap
      rw [hSB, hJ]; simp only [candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
        rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    have hneqSB : (reg s31 dPF).val + (reg s31 dJ).val ≠ candSndBBase H.vertexCount H.arcCount + k := by
      rw [k31 _ (by decide) (by decide), k31 _ (by decide) (by decide)]
      change (reg s dPF).val + (reg s dJ).val ≠ _
      rw [hPF, hJ]; simp only [dictBase]; omega
    have hw2_33 : s33.data[(reg s33 dSndB).val + (reg s33 dJ).val]? = some w2 := by
      rw [k33 _ (by decide), k33 _ (by decide), k31 _ (by decide) (by decide), k31 _ (by decide) (by decide)]
      change s33.data[(reg s dSndB).val + (reg s dJ).val]? = _
      rw [d33, hSB, hJ, Array.getElem?_set_ne _ hneqSB, d31]; exact hw2
    obtain ⟨s35, st33_35, pc35, r35, k35, d35⟩ := loadAtOffset_steps (code := code) (input := input)
      (s := s33) (entry := 33) (tmp := dTmp) (dst := dA) (base := dSndB) (idx := dJ)
      (w := w2) rfl rfl pc33 (by omega) hbSB hw2_33
    -- 35..36: store dPS[k] := dA
    have hb2 : (reg s35 dPS).val + (reg s35 dJ).val < workCap := by
      rw [k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide),
          k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide)]
      change (reg s dPS).val + (reg s dJ).val < workCap
      rw [hPS, hJ]; simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
      omega
    obtain ⟨s37, st35_37, pc37, d37, k37⟩ := storeAtOffset_steps (code := code) (input := input)
      (s := s35) (entry := 35) (tmp := dTmp) (base := dPS) (idx := dJ) (src := dA)
      rfl rfl pc35 (by omega) (by decide) hb2
    -- 37..38: store dK[k] := dZero
    have hb3 : (reg s37 dK).val + (reg s37 dJ).val < workCap := by
      rw [k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide),
          k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide)]
      change (reg s dK).val + (reg s dJ).val < workCap
      rw [hK, hJ]; simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
      omega
    obtain ⟨s39, st37_39, pc39, d39, k39⟩ := storeAtOffset_steps (code := code) (input := input)
      (s := s37) (entry := 37) (tmp := dTmp) (base := dK) (idx := dJ) (src := dZero)
      rfl rfl pc37 (by omega) (by decide) hb3
    -- 39: add dJ dJ dOne; 40: goto 28
    obtain ⟨s40, st39, pc40, r40, k40, d40⟩ := step_add15_at (code := code) (input := input)
      (s := s39) (d := dJ) (lhs := dJ) (rhs := dOne) (by rw [pc39]; rfl) (by omega)
    let s' : State L := { s40 with pc := 28 }
    have st40 : step code input s40 = some (.next s') :=
      step_goto_at (code := code) (input := input) (s := s40) (target := 28)
        (by rw [show s40.pc = 40 by omega]; rfl) (by omega)
    have hkeep (r : Fin 15) (hr : r ∈ ([dZero, dOne, dD, dFstB, dSndB, dPF, dPS, dK] : List (Fin 15))) :
        reg s' r = reg s r := by
      have hneq : r ≠ dTmp ∧ r ≠ dA ∧ r ≠ dJ := by revert r hr; decide
      exact (k40 r hneq.2.2).trans ((k39 r hneq.1).trans ((k37 r hneq.1).trans
        ((k35 r hneq.1 hneq.2.1).trans ((k33 r hneq.1).trans (k31 r hneq.1 hneq.2.1)))))
    have hJ39 : (reg s39 dJ).val = k := by
      rw [k39 _ (by decide), k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide),
          k31 _ (by decide) (by decide)]; exact hJ
    have hO39 : (reg s39 dOne).val = 1 := by
      rw [k39 _ (by decide), k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide),
          k31 _ (by decide) (by decide)]; exact h1
    have hJ' : (reg s' dJ).val = k + 1 := by
      change (reg s40 dJ).val = _
      rw [r40, PaperB.WordOps.add_no_wrap _ _ (by rw [hJ39, hO39]; omega), hJ39, hO39]
    have hsds : s.data.size = workCap := s.data_size
    have hsds31 : s31.data.size = workCap := s31.data_size
    have hsds35 : s35.data.size = workCap := s35.data_size
    have hadr1 : (reg s31 dPF).val + (reg s31 dJ).val = dictBase H.vertexCount H.arcCount + 1 + k := by
      rw [k31 _ (by decide) (by decide), k31 _ (by decide) (by decide)]; change (reg s dPF).val + (reg s dJ).val = _; rw [hPF, hJ]
    have hadr2 : (reg s35 dPS).val + (reg s35 dJ).val = dictBase H.vertexCount H.arcCount + 1 + acc.length + k := by
      rw [k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide),
          k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide)]
      change (reg s dPS).val + (reg s dJ).val = _; rw [hPS, hJ]
    have hadr3 : (reg s37 dK).val + (reg s37 dJ).val = dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k := by
      rw [k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide),
          k37 _ (by decide), k35 _ (by decide) (by decide), k33 _ (by decide), k31 _ (by decide) (by decide)]
      change (reg s dK).val + (reg s dJ).val = _; rw [hK, hJ]
    have hd1lt : dictBase H.vertexCount H.arcCount + 1 + k < s.data.size := by rw [hsds, ← hadr1]; exact hb1
    have hd2lt : dictBase H.vertexCount H.arcCount + 1 + acc.length + k <
        (s.data.set (dictBase H.vertexCount H.arcCount + 1 + k) w1 hd1lt).size := by
      rw [Array.size_set, hsds, ← hadr2]; exact hb2
    have hd3lt : dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k <
        ((s.data.set (dictBase H.vertexCount H.arcCount + 1 + k) w1 hd1lt).set
          (dictBase H.vertexCount H.arcCount + 1 + acc.length + k) w2 hd2lt).size := by
      rw [Array.size_set, Array.size_set, hsds, ← hadr3]; exact hb3
    have hd33' : s33.data = s.data.set (dictBase H.vertexCount H.arcCount + 1 + k) w1 hd1lt := by
      rw [d33]; exact array_set_congr (v := reg s31 dA) (w := w1)
        (by rw [hsds31]; exact hb1) hd1lt d31 hadr1 r31
    have hd37' : s37.data = (s.data.set (dictBase H.vertexCount H.arcCount + 1 + k) w1 hd1lt).set
        (dictBase H.vertexCount H.arcCount + 1 + acc.length + k) w2 hd2lt := by
      rw [d37]; exact array_set_congr (v := reg s35 dA) (w := w2)
        (by rw [hsds35]; exact hb2) hd2lt (d35.trans hd33') hadr2 r35
    have hZero37 : reg s37 dZero = reg s dZero :=
      (k37 _ (by decide)).trans ((k35 _ (by decide) (by decide)).trans ((k33 _ (by decide)).trans (k31 _ (by decide) (by decide))))
    have hsData : s'.data =
        ((s.data.set (dictBase H.vertexCount H.arcCount + 1 + k) w1 hd1lt).set
          (dictBase H.vertexCount H.arcCount + 1 + acc.length + k) w2 hd2lt).set
          (dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k) (reg s dZero) hd3lt := by
      change s40.data = _
      rw [d40, d39]
      exact array_set_congr (v := reg s37 dZero) (w := reg s dZero)
        (by rw [hd37', Array.size_set, Array.size_set, hsds]; exact hb3) hd3lt hd37' hadr3 hZero37
    obtain ⟨t, c2, hc2, st2, hFin⟩ := ih (k + 1) (by omega) (by omega) s' rfl
      (by rw [hkeep _ (by decide), h0]) (by rw [hkeep _ (by decide), h1]) (by rw [hkeep _ (by decide), hD])
      (by rw [hkeep _ (by decide), hFB]) (by rw [hkeep _ (by decide), hSB])
      (by rw [hkeep _ (by decide), hPF]) (by rw [hkeep _ (by decide), hPS])
      (by rw [hkeep _ (by decide), hK]) hJ'
      (by intro idx hidx
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt' | rfl
          · have hprev := hOut idx hlt'
            have hne1a : dictBase H.vertexCount H.arcCount + 1 + k ≠ dictBase H.vertexCount H.arcCount + 1 + idx := by omega
            have hne2a : dictBase H.vertexCount H.arcCount + 1 + acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + idx := by omega
            have hne3a : dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + idx := by omega
            have hne1b : dictBase H.vertexCount H.arcCount + 1 + k ≠ dictBase H.vertexCount H.arcCount + 1 + acc.length + idx := by omega
            have hne2b : dictBase H.vertexCount H.arcCount + 1 + acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + acc.length + idx := by omega
            have hne3b : dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + acc.length + idx := by omega
            have hne1c : dictBase H.vertexCount H.arcCount + 1 + k ≠ dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + idx := by omega
            have hne2c : dictBase H.vertexCount H.arcCount + 1 + acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + idx := by omega
            have hne3c : dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k ≠ dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + idx := by omega
            refine ⟨?_, ?_, ?_⟩
            · rw [hsData, Array.getElem?_set_ne _ hne3a, Array.getElem?_set_ne _ hne2a, Array.getElem?_set_ne _ hne1a]; exact hprev.1
            · rw [hsData, Array.getElem?_set_ne _ hne3b, Array.getElem?_set_ne _ hne2b, Array.getElem?_set_ne _ hne1b]; exact hprev.2.1
            · rw [hsData, Array.getElem?_set_ne _ hne3c, Array.getElem?_set_ne _ hne2c, Array.getElem?_set_ne _ hne1c]; exact hprev.2.2
          · refine ⟨?_, ?_, ?_⟩
            · rw [hsData, Array.getElem?_set_ne _ (by omega), Array.getElem?_set_ne _ (by omega),
                  Array.getElem?_set_self, Option.map_some, hw1v]
            · rw [hsData, Array.getElem?_set_ne _ (by omega), Array.getElem?_set_self, Option.map_some, hw2v]
            · rw [hsData, Array.getElem?_set_self, Option.map_some, h0])
      (by intro idx hidx
          have hne1 : dictBase H.vertexCount H.arcCount + 1 + k ≠ idx := by
            rcases hidx with h | h | h | h <;> omega
          have hne2 : dictBase H.vertexCount H.arcCount + 1 + acc.length + k ≠ idx := by
            rcases hidx with h | h | h | h <;> omega
          have hne3 : dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + k ≠ idx := by
            rcases hidx with h | h | h | h <;> omega
          rw [hsData, Array.getElem?_set_ne _ hne3, Array.getElem?_set_ne _ hne2, Array.getElem?_set_ne _ hne1]
          exact hFr idx (by
            rcases hidx with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨by omega, h.2⟩))
            · exact Or.inr (Or.inr (Or.inr (by omega)))))
    refine ⟨t, 1 + (2 + (2 + (2 + (2 + (2 + 2))))) + c2, by omega, ?_, hFin⟩
    exact (Steps.cons b28 (st29_31.append (st31_33.append (st33_35.append (st35_37.append
      (st37_39.append (Steps.cons st39 (Steps.cons st40 (.zero s'))))))))).append st2

def zeroDictColumns (H : LabelledQuotient) (rows : PaperB.ForestDictionary.Rows H) :
    PaperB.RetainedProperLoss.Columns H where
  dict := packedDictionary rows orderedPairCode
  slots := Array.replicate (packedDictionary rows orderedPairCode).size 0
  back := #[]
  labels := #[]
  entry := #[]
  stop := #[]

theorem zeroDictFits {H : LabelledQuotient} (rows : PaperB.ForestDictionary.Rows H)
    (hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ 2 ^ bits) :
    FlatPairDictionary.Fits bits (zeroDictColumns H rows) := by
  have hspec := packedDictionary_spec rows orderedPairCode
  refine FlatPairDictionary.Fits.ofDenseIds (zeroDictColumns H rows) (by omega) ?_ ?_ ?_ ?_
  · intro i hi
    have hmem : (zeroDictColumns H rows).dict[i]'hi ∈ (packedDictionary rows orderedPairCode).toList := by
      have : (zeroDictColumns H rows).dict[i]'hi ∈ (zeroDictColumns H rows).dict.toList :=
        List.getElem_mem (by simpa using hi)
      exact this
    obtain ⟨y, q, _, hq⟩ := (hspec.2.1 _).mp hmem
    change ((zeroDictColumns H rows).dict[i]'hi).1 < H.vertexCount
    rw [← hq]
    unfold orderedPairCode
    split <;> exact Fin.isLt _
  · intro i hi
    have hmem : (zeroDictColumns H rows).dict[i]'hi ∈ (packedDictionary rows orderedPairCode).toList := by
      have : (zeroDictColumns H rows).dict[i]'hi ∈ (zeroDictColumns H rows).dict.toList :=
        List.getElem_mem (by simpa using hi)
      exact this
    obtain ⟨y, q, _, hq⟩ := (hspec.2.1 _).mp hmem
    change ((zeroDictColumns H rows).dict[i]'hi).2 < H.vertexCount
    rw [← hq]
    unfold orderedPairCode
    split <;> exact Fin.isLt _
  · intro i hi
    have : ((zeroDictColumns H rows).slots[i]?).getD 0 = 0 := by
      simp only [zeroDictColumns, Array.size_replicate] at hi
      simp [zeroDictColumns, hi]
    rw [this]; omega
  · unfold FlatPairDictionary.packedSize FlatPairDictionary.slotBase FlatPairDictionary.secondBase zeroDictColumns
    simp only [Array.size_replicate]
    have hsz : (packedDictionary rows orderedPairCode).size ≤ H.vertexCount := hspec.2.2
    omega

theorem run_dedupPhase {H : LabelledQuotient} (h8 : 8 ≤ 2 ^ bits)
    (input : Input L) (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {rows : Rows H} {cur : List Key}
    (hLen : cur.length ≤ H.vertexCount)
    (hSorted : ∀ i j (hi : i < cur.length) (hj : j < cur.length), i ≤ j → keyLe (cur[i]'hi) (cur[j]'hj))
    (hMem : ∀ z : Key, z ∈ cur ↔ z ∈ collectFrom rows orderedPairCode (List.finRange H.vertexCount))
    (s : State L)
    (h0 : (reg s dZero).val = 0) (h1 : (reg s dOne).val = 1) (hK : (reg s dK).val = cur.length)
    (hFA : (reg s dFstA).val = candFstABase H.vertexCount H.arcCount)
    (hSA : (reg s dSndA).val = candSndABase H.vertexCount H.arcCount)
    (hFB : (reg s dFstB).val = candFstBBase H.vertexCount H.arcCount)
    (hSB : (reg s dSndB).val = candSndBBase H.vertexCount H.arcCount)
    (hDictSlot : (s.data[slotDict]?).map Fin.val = some (dictBase H.vertexCount H.arcCount))
    (hInA : ∀ j : Fin cur.length,
      MemPairAt s.data (candFstABase H.vertexCount H.arcCount) (candSndABase H.vertexCount H.arcCount) j.val (cur[j.val]'j.isLt)) :
    let ph := dedupPhase hi hw h8
    let dictCols := zeroDictColumns H rows
    let fits := zeroDictFits rows (Nat.le_trans hCap hw)
    let serialized := FlatPairDictionary.serialize dictCols fits
    ∃ t : State L, ∃ cost, cost ≤ 32 * H.vertexCount + 11 ∧
      Steps ph.code input cost (Phase.initial s) t ∧
      t.pc = ph.code.size - 1 ∧
      (∀ j : Fin serialized.size, t.data[dictBase H.vertexCount H.arcCount + j.val]? = some (serialized[j.val]'j.isLt)) ∧
      (∀ idx, idx < candFstBBase H.vertexCount H.arcCount ∨
        dictBase H.vertexCount H.arcCount + (1 + 3 * dictCols.dict.size) ≤ idx →
        t.data[idx]? = s.data[idx]?) := by
  intro ph dictCols fits serialized
  have hSize : ph.code.size = 42 := rfl
  have hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  obtain ⟨wDict, hwDict, hwDictv⟩ := word_mem_eq_of_map_val hDictSlot
  let s0 := Phase.initial s
  -- 0..1: dDict := slotDict
  obtain ⟨s2, st02, pc2, r2, k2, d2⟩ := immLoad_steps (code := ph.code) (input := input)
    (s := s0) (entry := 0) (tmp := dTmp) (dst := dDict) (slot := ⟨5, by omega⟩) (w := wDict)
    rfl rfl rfl (by omega) hwDict
  -- 2: mov dJ dZero
  obtain ⟨s3, st2, pc3, r3, k3, d3⟩ := step_mov_at (code := ph.code) (input := input)
    (s := s2) (d := dJ) (src := dZero) (by rw [pc2]; rfl) (by omega)
  -- 3: mov dD dZero
  obtain ⟨s4, st3, pc4, r4, k4, d4⟩ := step_mov_at (code := ph.code) (input := input)
    (s := s3) (d := dD) (src := dZero) (by rw [show s3.pc = 3 by omega]; rfl) (by omega)
  have keep4 (r : Fin 15) (hr : r ∈ ([dZero, dOne, dK, dFstA, dSndA, dFstB, dSndB] : List (Fin 15))) :
      reg s4 r = reg s r := by
    have hneq : r ≠ dTmp ∧ r ≠ dDict ∧ r ≠ dJ ∧ r ≠ dD := by revert r hr; decide
    exact (k4 r hneq.2.2.2).trans ((k3 r hneq.2.2.1).trans (k2 r hneq.1 hneq.2.1))
  have hs4Data : s4.data = s.data := d4.trans (d3.trans d2)
  have invD0 : DedupInv H cur s.data 0 [] s4 :=
    ⟨by omega, by rw [keep4 _ (by decide), h0], by rw [keep4 _ (by decide), h1],
     by rw [keep4 _ (by decide), hK], by rw [keep4 _ (by decide), hFA],
     by rw [keep4 _ (by decide), hSA], by rw [keep4 _ (by decide), hFB],
     by rw [keep4 _ (by decide), hSB],
     by rw [k4 _ (by decide), k3 _ (by decide), r2, hwDictv],
     by rw [k4 _ (by decide), r3, k2 _ (by decide) (by decide)]; exact h0,
     by rw [r4, k3 _ (by decide), k2 _ (by decide) (by decide)]; exact h0,
     Nat.zero_le _, Nat.le_refl 0, fun _ _ h _ => by simp at h,
     fun hx => by simp at hx, fun hx => by simp at hx,
     fun _ => ⟨fun h => by simp at h, fun ⟨_, _, h, _⟩ => by omega⟩,
     fun idx => Fin.elim0 idx, fun _ _ => by rw [hs4Data]⟩
  obtain ⟨acc, sD, cDedup, hcDedup, stDedup, invD⟩ :=
    dedup_loop h8 input hCap hLen hSorted hInA cur.length 0 [] s4 (Nat.sub_zero _) invD0
  -- Identify acc = dictCols.dict.toList
  have hPackedSpec := packedDictionary_spec rows orderedPairCode
  have hMemPacked : ∀ z : Key, z ∈ acc ↔ z ∈ (packedDictionary rows orderedPairCode).toList := by
    intro z
    rw [invD.memAcc z]
    constructor
    · rintro ⟨t, ht, _, rfl⟩
      have h1 : cur[t] ∈ collect rows orderedPairCode := (hMem _).mp (List.getElem_mem ht)
      rw [mem_collect] at h1
      obtain ⟨y, q, hq1, hq2⟩ := h1
      exact (hPackedSpec.2.1 _).mpr ⟨y, q, hq1, hq2⟩
    · intro hz
      obtain ⟨y, q, hq1, hq2⟩ := (hPackedSpec.2.1 z).mp hz
      have h1 : z ∈ collect rows orderedPairCode := by
        rw [mem_collect]; exact ⟨y, q, hq1, hq2⟩
      obtain ⟨t, ht, htz⟩ := List.mem_iff_getElem.mp ((hMem z).mpr h1)
      exact ⟨t, ht, ht, htz⟩
  have hAccEq : acc = (packedDictionary rows orderedPairCode).toList :=
    strictSortedList_unique acc _ invD.strict hPackedSpec.1 hMemPacked
  have hAccLen : acc.length = dictCols.dict.size := by
    simp [dictCols, zeroDictColumns, hAccEq]
  have hAccB : acc.length ≤ H.vertexCount := by rw [hAccLen]; exact hPackedSpec.2.2
  -- 4 -> 23 -> 28 (6 steps)
  have b4 : step ph.code input sD = some (.next { sD with pc := 23 }) :=
    step_branchLt_false (by rw [invD.pc]; rfl) (by rw [invD.jVal, invD.kVal]; exact Nat.le_refl _) (by omega)
  have hDictBound : (reg { sD with pc := 23 } dDict).val < workCap := by
    change (reg sD dDict).val < workCap; rw [invD.dictVal]
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
      rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
  obtain ⟨s24, st23, pc24, d24, k24⟩ := step_storeData_at (code := ph.code) (input := input)
    (s := { sD with pc := 23 }) (addr := dDict) (src := dD) rfl (by dsimp; omega) hDictBound
  have hpc24 : s24.pc = 24 := by dsimp at pc24; exact pc24
  obtain ⟨s25, st24, pc25, r25, k25, d25⟩ := step_add15_at (code := ph.code) (input := input)
    (s := s24) (d := dPF) (lhs := dDict) (rhs := dOne) (by rw [hpc24]; rfl) (by rw [hpc24]; omega)
  have hpc25 : s25.pc = 25 := by omega
  obtain ⟨s26, st25, pc26, r26, k26, d26⟩ := step_add15_at (code := ph.code) (input := input)
    (s := s25) (d := dPS) (lhs := dPF) (rhs := dD) (by rw [hpc25]; rfl) (by rw [hpc25]; omega)
  have hpc26 : s26.pc = 26 := by omega
  obtain ⟨s27, st26, pc27, r27, k27, d27⟩ := step_add15_at (code := ph.code) (input := input)
    (s := s26) (d := dK) (lhs := dPS) (rhs := dD) (by rw [hpc26]; rfl) (by rw [hpc26]; omega)
  have hpc27 : s27.pc = 27 := by omega
  obtain ⟨s28, st27, pc28, r28, k28, d28⟩ := step_mov_at (code := ph.code) (input := input)
    (s := s27) (d := dJ) (src := dZero) (by rw [hpc27]; rfl) (by rw [hpc27]; omega)
  have hpc28 : s28.pc = 28 := by rw [pc28, hpc27]
  have hsD24_dict : (reg s24 dDict).val = dictBase H.vertexCount H.arcCount := by
    rw [k24]; exact invD.dictVal
  have hsD24_one : (reg s24 dOne).val = 1 := by rw [k24]; exact invD.one
  have hsD24_d : (reg s24 dD).val = acc.length := by rw [k24]; exact invD.dVal
  have hPF25 : (reg s25 dPF).val = dictBase H.vertexCount H.arcCount + 1 := by
    rw [r25, PaperB.WordOps.add_no_wrap _ _ (by rw [hsD24_dict, hsD24_one]; simp only [dictBase, candSndBBase,
      candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
      orderBase, stampsBase, indegBase, csrArenaWords]; omega), hsD24_dict, hsD24_one]
  have hPS26 : (reg s26 dPS).val = dictBase H.vertexCount H.arcCount + 1 + acc.length := by
    have h2' : (reg s25 dD).val = acc.length := by rw [k25 _ (by decide), hsD24_d]
    rw [r26, PaperB.WordOps.add_no_wrap _ _ (by rw [hPF25, h2']; simp only [dictBase, candSndBBase,
      candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
      orderBase, stampsBase, indegBase, csrArenaWords]; omega), hPF25, h2']
  have hK27 : (reg s27 dK).val = dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length := by
    have h2' : (reg s26 dD).val = acc.length := by rw [k26 _ (by decide), k25 _ (by decide), hsD24_d]
    rw [r27, PaperB.WordOps.add_no_wrap _ _ (by rw [hPS26, h2']; simp only [dictBase, candSndBBase,
      candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase,
      orderBase, stampsBase, indegBase, csrArenaWords]; omega), hPS26, h2']; omega
  have hsdsD : sD.data.size = workCap := sD.data_size
  have hDictLt : dictBase H.vertexCount H.arcCount < sD.data.size := by
    rw [hsdsD]; change (reg sD dDict).val < workCap at hDictBound; rw [← invD.dictVal]; exact hDictBound
  have hs28Data : s28.data = sD.data.set (dictBase H.vertexCount H.arcCount) (reg sD dD) hDictLt := by
    rw [d28, d27, d26, d25, d24]
    exact array_set_congr (a := sD.data) (b := sD.data) (v := reg sD dD) (w := reg sD dD)
      (by rw [sD.data_size]; exact hDictBound) hDictLt rfl invD.dictVal rfl
  have hInB28 : ∀ idx : Fin acc.length,
      MemPairAt s28.data (candFstBBase H.vertexCount H.arcCount) (candSndBBase H.vertexCount H.arcCount) idx.val (acc[idx.val]'idx.isLt) := by
    intro idx
    have hne1 : dictBase H.vertexCount H.arcCount ≠ candFstBBase H.vertexCount H.arcCount + idx.val := by
      simp only [dictBase, candSndBBase]; omega
    have hne2 : dictBase H.vertexCount H.arcCount ≠ candSndBBase H.vertexCount H.arcCount + idx.val := by
      simp only [dictBase]; omega
    exact ⟨by rw [hs28Data, Array.getElem?_set_ne _ hne1]; exact (invD.inB idx).1,
           by rw [hs28Data, Array.getElem?_set_ne _ hne2]; exact (invD.inB idx).2⟩
  have hCount28 : (s28.data[dictBase H.vertexCount H.arcCount]?).map Fin.val = some acc.length := by
    rw [hs28Data, Array.getElem?_set_self, Option.map_some, invD.dVal]
  obtain ⟨t, cSer, hcSer, stSer, hpcFin, hCountFin, hSerElems, hSerFr⟩ :=
    ser_loop h8 input hCap hAccB hInB28 hCount28 0 (Nat.zero_le _) s28 hpc28
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), k25 _ (by decide), k24]; exact invD.zero)
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), k25 _ (by decide), k24]; exact invD.one)
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), k25 _ (by decide)]; exact hsD24_d)
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), k25 _ (by decide), k24]; exact invD.fstBVal)
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), k25 _ (by decide), k24]; exact invD.sndBVal)
      (by rw [k28 _ (by decide), k27 _ (by decide), k26 _ (by decide)]; exact hPF25)
      (by rw [k28 _ (by decide), k27 _ (by decide)]; exact hPS26) (by rw [k28 _ (by decide)]; exact hK27)
      (by rw [r28, k27 _ (by decide), k26 _ (by decide), k25 _ (by decide), k24]; exact invD.zero)
      (fun _ hi => by omega) (fun _ _ => rfl)
  refine ⟨t, _, by rw [Nat.sub_zero] at hcSer; omega,
    (st02.append (.cons st2 (.cons st3 stDedup))).append
      (.cons b4 (.cons st23 (.cons st24 (.cons st25 (.cons st26 (.cons st27 stSer)))))),
    hpcFin, ?_, ?_⟩
  · intro j
    have hSerSize : serialized.size = 1 + 3 * dictCols.dict.size := by
      change (FlatPairDictionary.serialize dictCols fits).size = _
      rw [FlatPairDictionary.retained_words]
      simp [dictCols, zeroDictColumns]; omega
    have hjBound : j.val < 1 + dictCols.dict.size + dictCols.dict.size + dictCols.slots.size := by
      have : dictCols.slots.size = dictCols.dict.size := Array.size_replicate
      omega
    have hSerVal := serialize_val_eq dictCols fits j.val j.isLt hjBound
    have hAccIdx : ∀ idx (h1 : idx < acc.length) (h2 : idx < dictCols.dict.size),
        acc[idx]'h1 = dictCols.dict[idx]'h2 := by
      intro idx h1 h2
      have hopt : some (acc[idx]'h1) = some (dictCols.dict[idx]'h2) := by
        rw [← List.getElem?_eq_getElem h1, hAccEq]
        change (packedDictionary rows orderedPairCode).toList[idx]? = some (dictCols.dict[idx]'h2)
        rw [Array.getElem?_toList]
        rw [Array.getElem?_eq_getElem (show idx < (packedDictionary rows orderedPairCode).size from h2)]
        rfl
      exact Option.some.inj hopt
    have hvalMatch : ∃ w : Word bits, t.data[dictBase H.vertexCount H.arcCount + j.val]? = some w ∧
        w.val = (serialized[j.val]'j.isLt).val := by
      by_cases hj0 : j.val = 0
      · obtain ⟨w, hw, hwv⟩ := word_mem_eq_of_map_val hCountFin
        refine ⟨w, by rw [hj0]; exact hw, ?_⟩
        rw [hSerVal]; simp only [hj0, ↓reduceDIte]; rw [hwv, hAccLen]
      · by_cases hj1 : j.val < 1 + dictCols.dict.size
        · have hi : j.val - 1 < acc.length := by omega
          have hiD : j.val - 1 < dictCols.dict.size := by omega
          obtain ⟨w, hw, hwv⟩ := word_mem_eq_of_map_val (hSerElems (j.val - 1) hi).1
          refine ⟨w, by rw [show dictBase H.vertexCount H.arcCount + j.val = dictBase H.vertexCount H.arcCount + 1 + (j.val - 1) by omega]; exact hw, ?_⟩
          rw [hSerVal]; simp only [hj0, hj1, ↓reduceDIte]
          rw [hwv, hAccIdx (j.val - 1) hi hiD]
        · by_cases hj2 : j.val < 1 + 2 * dictCols.dict.size
          · have hi : j.val - (1 + dictCols.dict.size) < acc.length := by omega
            have hiD : j.val - (1 + dictCols.dict.size) < dictCols.dict.size := by omega
            obtain ⟨w, hw, hwv⟩ := word_mem_eq_of_map_val (hSerElems (j.val - (1 + dictCols.dict.size)) hi).2.1
            refine ⟨w, by rw [show dictBase H.vertexCount H.arcCount + j.val = dictBase H.vertexCount H.arcCount + 1 + acc.length + (j.val - (1 + dictCols.dict.size)) by omega]; exact hw, ?_⟩
            rw [hSerVal]; simp only [hj0, hj1, hj2, ↓reduceDIte]
            rw [hwv, hAccIdx (j.val - (1 + dictCols.dict.size)) hi hiD]
          · have hi : j.val - (1 + 2 * dictCols.dict.size) < acc.length := by omega
            obtain ⟨w, hw, hwv⟩ := word_mem_eq_of_map_val (hSerElems (j.val - (1 + 2 * dictCols.dict.size)) hi).2.2
            refine ⟨w, by rw [show dictBase H.vertexCount H.arcCount + j.val = dictBase H.vertexCount H.arcCount + 1 + 2 * acc.length + (j.val - (1 + 2 * dictCols.dict.size)) by omega]; exact hw, ?_⟩
            rw [hSerVal]; simp only [hj0, hj1, hj2, ↓reduceDIte]
            have hzeroSlot : (dictCols.slots[j.val - (1 + 2 * dictCols.dict.size)]?).getD 0 = 0 := by
              change ((Array.replicate dictCols.dict.size 0)[j.val - (1 + 2 * dictCols.dict.size)]?).getD 0 = 0
              by_cases hlt : j.val - (1 + 2 * dictCols.dict.size) < dictCols.dict.size
              · simp [hlt]
              · simp [hlt]
            rw [hwv, hzeroSlot]
    obtain ⟨w, hw, hwv⟩ := hvalMatch
    rw [hw]
    exact congrArg some (Fin.ext hwv)
  · intro idx hidx
    have hfr1 : idx < dictBase H.vertexCount H.arcCount ∨
        dictBase H.vertexCount H.arcCount + (1 + 3 * acc.length) ≤ idx := by
      rcases hidx with h | h
      · left; simp only [dictBase, candSndBBase]; omega
      · right; rw [hAccLen]; exact h
    rw [hSerFr idx hfr1, hs28Data, Array.getElem?_set_ne _ (by rcases hfr1 with h | h <;> omega)]
    have hfr2 : idx < candFstBBase H.vertexCount H.arcCount ∨ dictBase H.vertexCount H.arcCount ≤ idx := by
      rcases hidx with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    exact invD.frameDedup idx hfr2

end DedupPhase

/-! ### Combined Stage 2a pipeline: `dictSortPhase`, `dictSortProgram`, `DictSortOutput`, `run_dict_sort` -/

section DictSortPipeline

def dictSortPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  (collectPhase hi hw h8).link ((sortPhase hi hw h8).link (dedupPhase hi hw h8))

def dictSortProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  (dictSortPhase hi hw h8).code

structure DictSortOutput {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient)
    (s : State (layout bits inputCap workCap hi hw))
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (rank : Vertex H → Nat) (rows : Rows H)
    (hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ 2 ^ bits) : Prop where
  stage1 : Stage1Output H s order size_order rank rows
  dictAt : ∀ j : Fin (FlatPairDictionary.serialize (zeroDictColumns H rows) (zeroDictFits rows hBound)).size,
    s.data[dictBase H.vertexCount H.arcCount + j.val]? =
      some ((FlatPairDictionary.serialize (zeroDictColumns H rows) (zeroDictFits rows hBound))[j.val]'j.isLt)

theorem run_dict_sort {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State (layout bits inputCap workCap hi hw))
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    (hStage1 : Stage1Output H s order size_order rank rows) :
    ∃ t : State (layout bits inputCap workCap hi hw),
    ∃ states : List (State (layout bits inputCap workCap hi hw)),
    ∃ work : Nat,
      work ≤ 120 * (H.vertexCount + 1) * OracleContract.L H.vertexCount ∧
      run (dictSortProgram hi hw h8) input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace (dictSortProgram hi hw h8) input (Phase.initial s) states ⟨t, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      DictSortOutput H t order size_order rank rows (Nat.le_trans hCap hw) := by
  let p1 := collectPhase hi hw h8
  let p2 := sortPhase hi hw h8
  let p3 := dedupPhase hi hw h8
  let xs := collectFrom rows orderedPairCode (List.finRange H.vertexCount)
  have hxsLen : xs.length ≤ H.vertexCount := by
    simpa only [xs] using Nat.le_trans (collectFrom_length_le rows orderedPairCode _) (by simp)
  obtain ⟨t1, c1, hc1, st1, hpc1, z1, o1, n1, k1, fa1, sa1, sk1, sfa1, ssa1, sfb1, ssb1, sdict1, col1, fr1⟩ :=
    run_collectPhase h8 input hRaw hCap s hStage1.rows_mem
  have run1 : run p1.code input (c1 + 1) (Phase.initial s) = some ⟨t1, c1 + 1⟩ := by
    have hh : p1.code[t1.pc]? = some .halt := by
      have hhalt : t1.pc = p1.haltPC := hpc1
      rw [hhalt]; exact p1.haltAt
    exact st1.halts (step_halt_at hh)
  have hInA1 : ∀ j : Fin xs.length,
      (t1.data[candFstABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).1 ∧
      (t1.data[candSndABase H.vertexCount H.arcCount + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).2 := col1
  obtain ⟨cur, t2, c2, hc2, st2, hpc2, z2, o2, k2, fa2, sa2, fb2, sb2, curLen, curSorted, curMem, inA2, fr2⟩ :=
    run_sortPhase h8 input hCap hxsLen t1 z1 o1 k1 fa1 sa1 sfb1 ssb1 hInA1
  have run2 : run p2.code input (c2 + 1) (Phase.initial t1) = some ⟨t2, c2 + 1⟩ := by
    have hh : p2.code[t2.pc]? = some .halt := by
      have hhalt : t2.pc = p2.haltPC := hpc2
      rw [hhalt]; exact p2.haltAt
    exact st2.halts (step_halt_at hh)
  have hDictSlot2 : (t2.data[slotDict]?).map Fin.val = some (dictBase H.vertexCount H.arcCount) := by
    rw [fr2 _ (Or.inl (by decide))]
    exact sdict1
  obtain ⟨t3, c3, hc3, st3, hpc3, dictAt3, fr3⟩ :=
    run_dedupPhase h8 input hCap (by rw [curLen]; exact hxsLen) curSorted curMem t2
      z2 o2 (by rw [k2, curLen]) fa2 sa2 fb2 sb2 hDictSlot2 inA2
  have run3 : run p3.code input (c3 + 1) (Phase.initial t2) = some ⟨t3, c3 + 1⟩ := by
    have hh : p3.code[t3.pc]? = some .halt := by
      have hhalt : t3.pc = p3.haltPC := hpc3
      rw [hhalt]; exact p3.haltAt
    exact st3.halts (step_halt_at hh)
  have hp3Pos : 0 < p3.code.size := by have := p3.haltFits; omega
  obtain ⟨t23, st23, r23, d23, run23, chk23, peak23⟩ :=
    run_linked_pair p2 p3.code hp3Pos run2 run3
  have hp23Pos : 0 < (p2.link p3).code.size := by have := (p2.link p3).haltFits; omega
  obtain ⟨t, states, rt, dt, runAll, chkAll, peakAll⟩ :=
    run_linked_pair p1 (p2.link p3).code hp23Pos run1 run23
  have hDataEq : t.data = t3.data := dt.trans d23
  have hPresS1 : ∀ idx, orderBase H.vertexCount H.arcCount ≤ idx ∧ idx < candFstABase H.vertexCount H.arcCount →
      t.data[idx]? = s.data[idx]? := by
    intro idx hidx
    rw [hDataEq]
    have hltFB : idx < candFstBBase H.vertexCount H.arcCount := by
      simp only [candFstBBase, candSndABase]; omega
    rw [fr3 idx (Or.inl hltFB), fr2 idx (Or.inr (Or.inl hidx)), fr1 idx (Or.inl hidx)]
  have hLPos : 1 ≤ OracleContract.L H.vertexCount := by
    unfold OracleContract.L; omega
  have hCostTotal : (c1 + 1) + ((c2 + 1) + (c3 + 1)) ≤ 120 * (H.vertexCount + 1) * OracleContract.L H.vertexCount := by
    have hmul : (28 * H.vertexCount + 39) + (32 * H.vertexCount + 12) ≤ (60 * H.vertexCount + 51) * OracleContract.L H.vertexCount := by
      rw [show (28 * H.vertexCount + 39) + (32 * H.vertexCount + 12) = 60 * H.vertexCount + 51 by omega]
      exact Nat.le_mul_of_pos_right _ hLPos
    have hmul2 : (51 * H.vertexCount + 11) * OracleContract.L H.vertexCount + 9 ≤
        (51 * H.vertexCount + 20) * OracleContract.L H.vertexCount := by
      calc (51 * H.vertexCount + 11) * OracleContract.L H.vertexCount + 9
          ≤ (51 * H.vertexCount + 11) * OracleContract.L H.vertexCount + 9 * OracleContract.L H.vertexCount :=
            Nat.add_le_add_left (Nat.le_mul_of_pos_right 9 hLPos) _
        _ = (51 * H.vertexCount + 20) * OracleContract.L H.vertexCount := by rw [← Nat.add_mul]
    have hsum : (60 * H.vertexCount + 51) * OracleContract.L H.vertexCount +
        (51 * H.vertexCount + 20) * OracleContract.L H.vertexCount ≤
        120 * (H.vertexCount + 1) * OracleContract.L H.vertexCount := by
      rw [← Nat.add_mul]
      apply Nat.mul_le_mul_right
      omega
    omega
  refine ⟨t, states, (c1 + 1) + ((c2 + 1) + (c3 + 1)), hCostTotal, runAll, chkAll, ?_, ?_⟩
  · simpa only [footprint, layout] using peakAll
  · refine ⟨⟨hStage1.nodup, hStage1.covers, hStage1.topo, hStage1.rank_at, hStage1.rank_increasing, hStage1.rank_arc,
      ?_, ?_, ?_⟩, ?_⟩
    · intro i
      rw [hPresS1 _ ⟨by omega, by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase]; omega⟩]
      exact hStage1.order_mem i
    · intro v
      rw [hPresS1 _ ⟨by simp only [ranksBase]; omega, by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase]; omega⟩]
      exact hStage1.ranks_mem v
    · intro y
      obtain ⟨lo, hi', hlo, hhi, h1, h2, h3, h4⟩ := hStage1.rows_mem y
      refine ⟨lo, hi', ?_, ?_, h1, h2, h3, ?_⟩
      · rw [hPresS1 _ ⟨by simp only [rowStartBase, ranksBase]; omega, by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase]; omega⟩]; exact hlo
      · rw [hPresS1 _ ⟨by simp only [rowEndBase, rowStartBase, ranksBase]; omega, by simp only [candFstABase, predBufBase, rowEndBase]; omega⟩]; exact hhi
      · intro j
        rw [hPresS1 _ ⟨by simp only [predBufBase, rowEndBase, rowStartBase, ranksBase]; omega, by simp only [candFstABase]; have := j.isLt; omega⟩]
        exact h4 j
    · intro j
      rw [hDataEq]
      exact dictAt3 j

end DictSortPipeline

end PaperB.RamForestProgram.DictSort

