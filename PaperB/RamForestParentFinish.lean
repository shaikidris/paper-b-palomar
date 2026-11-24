module

public import PaperB.RamForestPhaseLink
public import PaperB.RamForestDegreeInit
public import PaperB.RamForestHistogram
public import PaperB.RamForestScatter
public import PaperB.RamForestWriteback

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram PaperB.RamProgram.FixedROM
open PaperB.ForestLayout (bucketChildLists)
open PaperB.LabelledQuotient (ValidDepthTree)
open PaperB.RamForestStack (commandWord)
open PaperB.Machine (Word)

variable {bits n inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def prepPhase : Phase L :=
  Phase.ofLast (prepareParentPhase hi hw) 3 rfl rfl rfl

private def clearPhase : Phase L :=
  Phase.ofLast (zeroDegreeProgram hi hw) 5 rfl rfl rfl

private def histogramPhase : Phase L :=
  Phase.ofLast (parentScanCode histogramBody) 13 rfl rfl rfl

private def offsetPhase : Phase L :=
  Phase.ofLast (offsetProgram hi hw) 10 rfl rfl rfl

private def scatterPhase : Phase L :=
  Phase.ofLast (parentScanCode scatterBody) 18 rfl rfl rfl

private def csrPhases : List (Phase L) :=
  [prepPhase, clearPhase, prepPhase, histogramPhase, prepPhase, offsetPhase,
    prepPhase, scatterPhase]

private def parentPhases : List (Phase L) :=
  csrPhases ++ [prepPhase, serializationPhase]

/-- Prepare the ordered CSR image without running the interval traversal. -/
def parentCsrProgram : Program L := pipeline csrPhases

/-- Prepares the child image and writes the intervals in one fixed program.
Its only tree input bank is the packed parent column. -/
def parentFinishProgram : Program L := pipeline parentPhases

private theorem onEntry {a : Arena bits workCap n} {root : Fin n} {i : Nat}
    {s : State L} (h : ParentCursor a root i s) : ParentCursor a root i (Phase.initial s) :=
  h.unchanged (fun _ _ => rfl)

private theorem offsetCursor {a : Arena bits workCap n} {s t : State L} {root : Fin n}
    (h : ParentCursor a root 0 s)
    (frame : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ clk → r ≠ registers.value →
      r ≠ registers.tmp → reg t r = reg s r)
    (ptr : (reg t registers.ptr).val = n) : ParentCursor a root n t := by
  have eq (r : Fin 15) (hp : r ≠ registers.ptr) (hc : r ≠ clk) (hv : r ≠ registers.value)
      (ht : r ≠ registers.tmp) : (reg t r).val = (reg s r).val :=
    congrArg Fin.val (frame r hp hc hv ht)
  refine ⟨⟨(eq count (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.count_eq,
      (eq registers.one (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.one,
      (eq registers.zero (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.zero,
      (eq registers.stackBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.stackBase_eq,
      (eq tinBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.tin_eq,
      (eq toutBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.tout_eq,
      (eq offsetBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.offset_eq,
      (eq childrenBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.child_eq⟩,
    (eq cmd (by decide) (by decide) (by decide) (by decide)).trans h.rootVal, ptr⟩

private theorem append_parent_csr (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n}
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) (s : State L)
    (ctrl : Control a s) (rootVal : (reg s cmd).val = root.val)
    (parents : ParentAt a parent s.data) :
    ∃ c work, work ≤ 42 * n + 26 ∧ ParentCursor a root n c ∧
      ChildImage a (bucketChildLists root parent) c.data ∧
      (∀ j < a.base, c.data[j]? = s.data[j]?) ∧
      (∀ (tail : List (Phase L)) (t : State L) (rest : Nat),
        PhasesRun input tail c t rest →
        PhasesRun input (csrPhases ++ tail) s t (work + rest)) := by
  have current : ParentCursor a root (reg s registers.ptr).val s := ⟨ctrl, rootVal, rfl⟩
  obtain ⟨z0, f0, zcur, _, _, zdat⟩ := run_prepare_parent_phase input _ rfl (onEntry current)
  obtain ⟨z, _, cz, zdone, zeroes, zkeep, _, _⟩ :=
    run_zero_degrees input _ rfl (onEntry zcur)
  obtain ⟨h0, f1, hcur, _, _, hdat⟩ := run_prepare_parent_phase input _ rfl (onEntry zdone)
  simp only [Phase.initial_data] at zdat zkeep hdat
  have hp : ParentAt a parent h0.data := by
    intro v
    have vlt := v.isLt
    rw [hdat, zkeep _ (Or.inl (by unfold Arena.tin; omega)), zdat]
    exact parents v
  have hz : ∀ p : Fin n, (h0.data[a.tin + p.val]?).map Fin.val = some 0 := by
    intro p
    rw [hdat]
    exact zeroes p
  obtain ⟨h, _, wh, bh, ch, hdone, hpar, hdeg, hkeep, _, _⟩ :=
    run_parent_histogram input root parent _ rfl (onEntry hcur) hp hz
  obtain ⟨o0, f2, ocur, clock, _, odat⟩ := run_prepare_parent_phase input _ rfl (onEntry hdone)
  simp only [Phase.initial_data] at hkeep odat
  have oi : OffsetInput a (parentDegree root parent) (Phase.initial o0) := by
    refine ⟨rfl, ocur.ptrVal, clock, (onEntry ocur).ctrl, ?_, mass⟩
    intro j hj
    change (o0.data[a.tin + j]?).map Fin.val = _
    rw [odat]
    exact hdeg ⟨j, hj⟩
  obtain ⟨o, _, co, off, okeep, _, _, oframe, optr⟩ :=
    run_csr_offsets_with_frame input _ oi
  have odone := offsetCursor (onEntry ocur) oframe optr
  obtain ⟨c0, f3, ccur, _, _, cdat⟩ := run_prepare_parent_phase input _ rfl (onEntry odone)
  simp only [Phase.initial_data] at okeep cdat
  have cp : ParentAt a parent c0.data := by
    intro v
    have vlt := v.isLt
    rw [cdat, okeep _ (Or.inl (by unfold Arena.offsets; omega)), odat]
    exact hpar v
  have cd : ∀ p : Fin n, (c0.data[a.tin + p.val]?).map Fin.val =
      some (parentDegree root parent p.val) := by
    intro p
    have plt := p.isLt
    rw [cdat, okeep _ (Or.inl (by unfold Arena.offsets Arena.tin; omega)), odat]
    exact hdeg p
  have cOff : OffsetAt a root parent c0.data := by
    intro j jle
    rw [cdat]
    exact off j jle
  obtain ⟨c, _, wc, bc, cc, cdone, rows, ckeep, _, _⟩ :=
    run_parent_scatter input root parent _ rfl (onEntry ccur) cp cOff cd mass
  let work := 4 + ((5 * n + 2) + (4 + (wh + (4 + ((8 * n + 4) + (4 + wc))))))
  refine ⟨c, work, by dsimp only [work]; omega, cdone, rows, ?_, ?_⟩
  · intro j hj
    have smallTin : j < a.tin := by unfold Arena.tin; omega
    have smallOffsets : j < a.offsets := by unfold Arena.offsets; omega
    simp only [Phase.initial_data] at ckeep
    rw [ckeep j hj, cdat, okeep j (Or.inl smallOffsets), odat,
      hkeep j (Or.inl smallTin), hdat, zkeep j (Or.inl smallTin), zdat]
  · intro tail t rest continuation
    have full : PhasesRun input (csrPhases ++ tail) s t
        (4 + ((5 * n + 2) + (4 + (wh + (4 + ((8 * n + 4) + (4 + (wc + rest)))))))) :=
      .cons f0 (.cons cz (.cons f1 (.cons ch (.cons f2 (.cons co (.cons f3 (.cons cc continuation)))))))
    simpa only [work, Nat.add_assoc] using full

/-- Run the CSR producer on any parent relation. Its bucket contract
does not require that the relation be a tree. -/
theorem run_parent_csr (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n}
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) (s : State L)
    (ctrl : Control a s) (rootVal : (reg s cmd).val = root.val)
    (parents : ParentAt a parent s.data) :
    ∃ t trace work, work ≤ 42 * n + 27 ∧
      ChildImage a (bucketChildLists root parent) t.data ∧
      (∀ j < a.base, t.data[j]? = s.data[j]?) ∧
      run parentCsrProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace parentCsrProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨c, w, bound, _, rows, kept, append⟩ :=
    append_parent_csr input mass s ctrl rootVal parents
  have record := append [] (Phase.initial c) 1 .nil
  rw [List.append_nil] at record
  obtain ⟨t, trace, _, eq, exec, success, peak⟩ := run_pipeline record
  simp only [Phase.initial_data] at eq
  exact ⟨t, trace, w + 1, by omega, eq.symm ▸ rows, eq.symm ▸ kept, exec, success, peak⟩

/-- Full machine-level finish from a physical parent column and arbitrary
scratch contents. Counter initialization, histogram, prefix offsets,
stable scatter, seeding, DFS, writeback, and every link are counted. -/
theorem run_parent_finish (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (tree : ValidDepthTree root parent depth)
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) (children : a.children ≤ n)
    (reserved : 2 * n ≤ a.base) (s : State L)
    (ctrl : Control a s) (rootVal : (reg s cmd).val = root.val)
    (parents : ParentAt a parent s.data) :
    let dst := a.base - 2 * n
    let final := PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)
    ∃ t trace work,
      ColumnAt (n := n) dst final.entries t.data ∧
      ColumnAt (n := n) (dst + n) final.ends t.data ∧
      (∀ j < dst, t.data[j]? = s.data[j]?) ∧ work ≤ 106 * n + 44 ∧
      run parentFinishProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace parentFinishProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨c, wc, bc, cdone, rows, ckeep, append⟩ :=
    append_parent_csr input mass s ctrl rootVal parents
  obtain ⟨p0, f4, pcur, _, words, pdat⟩ := run_prepare_parent_phase input _ rfl (onEntry cdone)
  simp only [Phase.initial_data] at ckeep pdat
  have ready : SeedInput a (bucketChildLists root parent) root (Phase.initial p0) :=
    ⟨rfl, (onEntry pcur).ctrl, words, pcur.ptrVal, Fin.ext pcur.rootVal, by
      change ChildImage a (bucketChildLists root parent) p0.data
      rwa [pdat]⟩
  obtain ⟨p, _, wp, pe, px, pkeep, bp, pc, _, _⟩ :=
    run_serialized_tree input tree rfl children reserved _ ready
  simp only [Phase.initial_data] at pkeep
  rw [← serializationPhase_code] at pc
  let w := wc + (4 + (wp + 1))
  have phases : PhasesRun input parentPhases s (Phase.initial p) w :=
    append [prepPhase, serializationPhase] _ _ (.cons f4 (.cons pc .nil))
  obtain ⟨t, trace, _, data, exec, success, peak⟩ := run_pipeline phases
  have qe : ColumnAt (n := n) (a.base - 2 * n)
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).entries t.data :=
    data.symm ▸ pe
  have qx : ColumnAt (n := n) (a.base - 2 * n + n)
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).ends t.data :=
    data.symm ▸ px
  refine ⟨t, trace, w, qe, qx, ?_, ?_, exec, success, peak⟩
  · intro j hj
    rw [data]
    change p.data[j]? = s.data[j]?
    have small : j < a.base := by omega
    rw [pkeep j hj, pdat, ckeep j small]
  · dsimp only [w]
    omega

private theorem parentPipeline_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    {h₁ : c₁ ≤ 2 ^ bits} {k₁ : d₁ ≤ 2 ^ bits}
    {h₂ : c₂ ≤ 2 ^ bits} {k₂ : d₂ ≤ 2 ^ bits}
    {p₁ : FixedROM.Phase (layout bits c₁ d₁ h₁ k₁)}
    {p₂ : FixedROM.Phase (layout bits c₂ d₂ h₂ k₂)}
    {ps₁ : List (FixedROM.Phase (layout bits c₁ d₁ h₁ k₁))}
    {ps₂ : List (FixedROM.Phase (layout bits c₂ d₂ h₂ k₂))}
    (hp : p₁.code = p₂.code ∧ p₁.haltPC = p₂.haltPC)
    (hps : FixedROM.pipeline ps₁ = FixedROM.pipeline ps₂) :
    FixedROM.pipeline (p₁ :: ps₁) = FixedROM.pipeline (p₂ :: ps₂) := by
  simp only [FixedROM.pipeline, FixedROM.join, hp.1, hp.2, hps]

theorem parentFinishProgram_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) :
    parentFinishProgram (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁) =
      parentFinishProgram (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂) := by
  unfold parentFinishProgram parentPhases csrPhases
  dsimp only [List.cons_append, List.nil_append]
  repeat' (refine parentPipeline_cap_indep ?_ ?_)
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact serializationPhase_cap_indep h₁ k₁ h₂ k₂
  · rfl

end PaperB.RamForestProgram.Finish
