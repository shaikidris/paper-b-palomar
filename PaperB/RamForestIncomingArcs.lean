module

public import PaperB.RamForestArcParents
public import PaperB.RamForestPackedFinish
public import PaperB.ForestIncomingRaw

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.ArcParents

open PaperB.RamProgram PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.Finish
open PaperB.ForestLayout (bucketChildLists bucketChildLists_get)
open PaperB.LabelledQuotient (mem_bucketChildren_iff nodup_bucketChildren)
open PaperB.Machine (Word)

variable {vertices arcs bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw
local notation "K" => (vertices + 1 + arcs)

/-- Read-only occurrence metadata. Rows group tokens by head; tail and
label information is still available at the token's original position. -/
def rowNodes (heads : Fin arcs → Fin vertices) (v : Fin vertices) : List (Fin K) :=
  (bucketChildLists (root vertices arcs) (parent heads)).get (headNode arcs v)

theorem arcNode_in_row (heads : Fin arcs → Fin vertices) (v : Fin vertices) (e : Fin arcs) :
    arcNode vertices e ∈ rowNodes heads v ↔ heads e = v := by
  unfold rowNodes
  rw [bucketChildLists_get, mem_bucketChildren_iff, parent_arcNode]
  constructor
  · intro h
    exact Fin.ext (by
      have eq := congrArg Fin.val h.2
      change (heads e).val + 1 = v.val + 1 at eq
      omega)
  · intro h
    refine ⟨?_, by rw [h]⟩
    intro eq
    have bad := congrArg Fin.val eq
    change vertices + 1 + e.val = 0 at bad
    omega

theorem rowNodes_are_arcs (heads : Fin arcs → Fin vertices) (v : Fin vertices)
    (u : Fin K) (m : u ∈ rowNodes heads v) :
    ∃ e : Fin arcs, u = arcNode vertices e ∧ heads e = v := by
  have target := m
  unfold rowNodes at target
  rw [bucketChildLists_get, mem_bucketChildren_iff] at target
  by_cases upper : vertices + 1 ≤ u.val
  · let e : Fin arcs := ⟨u.val - (vertices + 1), by have := u.isLt; omega⟩
    have equal : u = arcNode vertices e := by
      apply Fin.ext
      change u.val = vertices + 1 + (u.val - (vertices + 1))
      omega
    exact ⟨e, equal, (arcNode_in_row heads v e).mp (equal ▸ m)⟩
  · have wrong : parent heads u = root vertices arcs := dite_eq_right upper
    have eq := congrArg Fin.val (wrong.symm.trans target.2)
    change 0 = v.val + 1 at eq
    omega

theorem rowNodes_nodup (heads : Fin arcs → Fin vertices) (v : Fin vertices) :
    (rowNodes heads v).Nodup := by
  unfold rowNodes
  rw [bucketChildLists_get]
  exact nodup_bucketChildren _ _ _

private def parentPreparationPhase : Phase L :=
  Phase.ofLast (code hi hw) 12 rfl rfl rfl

/-- Group raw head words into CSR occurrence rows. No parent column,
degrees, offsets, sorted arcs, or scratch initialization is supplied. -/
def rawIncomingProgram : Program L :=
  join (parentPreparationPhase (hi := hi) (hw := hw)).code parentCsrProgram
    parentPreparationPhase.haltPC parentPreparationPhase.haltFits

private theorem arc_mass (heads : Fin arcs → Fin vertices) :
    rowPrefix (parentDegree (root vertices arcs) (parent heads)) K = K - 1 := by
  let x : PaperB.PackedStaticLayout.Input K :=
    ⟨root vertices arcs, PaperB.PackedStaticLayout.tabulate (parent heads),
      PaperB.PackedStaticLayout.tabulate (depth (vertices := vertices) (arcs := arcs))⟩
  have p : x.parent.read = parent heads := by
    funext u
    exact PaperB.PackedStaticLayout.read_tabulate _ u
  have d : x.depth.read = depth (vertices := vertices) (arcs := arcs) := by
    funext u
    exact PaperB.PackedStaticLayout.read_tabulate _ u
  have r : x.root = root vertices arcs := rfl
  have ht : PaperB.LabelledQuotient.ValidDepthTree x.root x.parent.read x.depth.read := by
    rw [r, p, d]
    exact parent_tree heads
  have total := packed_parent_mass x ht
  rw [r, p] at total
  exact total

/-- A physical occurrence row describes exactly the arcs with the given
head. IDs in the row are n+1 plus the original input arc positions. -/
def IncomingAt (a : Arena bits workCap K) (heads : Fin arcs → Fin vertices)
    (data : Array (Word bits)) : Prop :=
  ∀ v : Fin vertices, ∃ lo stop : Word bits,
    data[a.offsets + (headNode arcs v).val]? = some lo ∧
    data[a.offsets + (headNode arcs v).val + 1]? = some stop ∧
    stop.val = lo.val + (rowNodes heads v).length ∧ stop.val ≤ a.children ∧
    (∀ j : Fin (rowNodes heads v).length, ∃ e : Fin arcs,
      (rowNodes heads v)[j.val]'j.isLt = arcNode vertices e ∧ heads e = v ∧
      (data[a.payload + lo.val + j.val]?).map Fin.val = some (vertices + 1 + e.val))

private theorem incomingAt_of_childImage {a : Arena bits workCap K}
    {heads : Fin arcs → Fin vertices} {data : Array (Word bits)}
    (image : ChildImage a (bucketChildLists (root vertices arcs) (parent heads)) data) :
    IncomingAt a heads data := by
  intro v
  obtain ⟨lo, stop, l, r, eq, fit, cells⟩ := image (headNode arcs v)
  refine ⟨lo, stop, l, r, ?_, fit, ?_⟩
  · simpa only [childrenOf, List.length_map, rowNodes] using eq
  · intro j
    have hm : (rowNodes heads v)[j.val]'j.isLt ∈ rowNodes heads v := List.getElem_mem _
    obtain ⟨e, same, target⟩ := rowNodes_are_arcs heads v _ hm
    refine ⟨e, same, target, ?_⟩
    have read := cells j.val (by
      simp only [childrenOf, List.length_map]
      exact j.isLt)
    have elem : (rowNodes heads v)[j.val]? = some (arcNode vertices e) := by
      rw [getElem?_pos (rowNodes heads v) j.val j.isLt, same]
    simp only [childrenOf, List.getElem?_map] at read
    change data[a.payload + lo.val + j.val]? =
      ((rowNodes heads v)[j.val]?).map (fun u => PaperB.RamForestStack.commandWord a.tags
        (.enter u)) at read
    rw [read, elem, Option.map_some, Option.map_some]
    rfl

/-- The two passes are linked in a single instruction trace. The original
read-only arc words are never changed, including occurrence identifiers
used by the labelled-arc algorithms. -/
theorem run_raw_incoming (input : Input L) (a : Arena bits workCap K)
    (heads : Fin arcs → Fin vertices) (headAddr : Nat) (inputFit : headAddr + arcs ≤ inputCap)
    (raw : HeadsAt input headAddr heads) (space : K - 1 ≤ a.children) (s : State L)
    (cursor : ParentCursor a (root vertices arcs) 0 s)
    (split : (reg s clk).val = vertices + 1)
    (headBase : (reg s registers.childBase).val = headAddr) :
    ∃ t trace work, work ≤ 52 * K + 29 ∧ IncomingAt a heads t.data ∧
      run rawIncomingProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace rawIncomingProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨p, _, wp, pb, pr, state, parents, _, _, _⟩ :=
    run_arc_parents input heads headAddr inputFit raw (Phase.initial s) rfl
      (cursor.unchanged (fun _ _ => rfl)) split headBase
  have mass : rowPrefix (parentDegree (root vertices arcs) (parent heads)) K ≤ a.children := by
    rw [arc_mass]
    exact space
  obtain ⟨q, _, wq, qb, rows, _, qr, _, _⟩ :=
    run_parent_csr input mass p state.ctrl state.rootVal parents
  have full : 0 < (parentCsrProgram (hi := hi) (hw := hw)).size := by
    unfold parentCsrProgram
    exact pipeline_nonempty _
  obtain ⟨t, trace, _, data, run, traceRun, peak⟩ :=
    run_linked_pair parentPreparationPhase parentCsrProgram full pr qr
  have packed : IncomingAt a heads t.data := data.symm ▸ incomingAt_of_childImage rows
  exact ⟨t, trace, wp + wq, by omega, packed, run, traceRun, peak⟩

section Quotient

open PaperB (LabelledQuotient)
open PaperB.ForestIncomingRaw (Entry supplied length_supplied arcHead mem_supplied)
open PaperB.ForestPreparedBuild (arcTotal_eq_arcCount)

private theorem rawLength (H : LabelledQuotient) : (supplied H).reverse.length = H.arcCount :=
  List.length_reverse.trans ((length_supplied H).trans (arcTotal_eq_arcCount H))

/-- Read the source and label at an occurrence position in the flattened
quotient input. This definition is a specification used by the decoder. -/
def rawOccurrence (H : LabelledQuotient) (e : Fin H.arcCount) : Entry H :=
  (supplied H).reverse[e.val]'(by rw [rawLength H]; exact e.isLt)

def rawHead (H : LabelledQuotient) (e : Fin H.arcCount) : Fin H.vertexCount :=
  arcHead (rawOccurrence H e).2

theorem rawOccurrence_membership (H : LabelledQuotient)
    (u v : Fin H.vertexCount) :
    (∃ e : Fin H.arcCount, (rawOccurrence H e).1 = u ∧ rawHead H e = v) ↔
      H.HasQuotientArc u v := by
  constructor
  · rintro ⟨e, src, dst⟩
    have position : rawOccurrence H e ∈ (supplied H).reverse :=
      List.getElem_mem (by rw [rawLength H]; exact e.isLt)
    have inInput : ((rawOccurrence H e).1, (rawOccurrence H e).2) ∈ supplied H :=
      List.mem_reverse.mp position
    rw [src] at inInput
    exact ⟨(rawOccurrence H e).2, (mem_supplied H u _).mp inInput, dst⟩
  · rintro ⟨a, present, target⟩
    have inInput : (u, a) ∈ (supplied H).reverse :=
      List.mem_reverse.mpr ((mem_supplied H u a).mpr present)
    obtain ⟨j, hj, row⟩ := List.mem_iff_getElem.mp inInput
    let e : Fin H.arcCount := ⟨j, by rwa [rawLength H] at hj⟩
    have recordEq : rawOccurrence H e = (u, a) := row
    exact ⟨e, congrArg Prod.fst recordEq, (congrArg (fun z : Entry H => arcHead z.2) recordEq).trans target⟩

/-- A head row binds back to a real quotient arc using the original
input occurrence. Label identity is therefore independent of grouping. -/
theorem rawRow_source_iff (H : LabelledQuotient) (u v : Fin H.vertexCount) :
    (∃ e : Fin H.arcCount,
      arcNode H.vertexCount e ∈ rowNodes (rawHead H) v ∧ (rawOccurrence H e).1 = u) ↔
      H.HasQuotientArc u v := by
  constructor
  · rintro ⟨e, here, src⟩
    exact (rawOccurrence_membership H u v).mp
      ⟨e, src, (arcNode_in_row (rawHead H) v e).mp here⟩
  · intro arc
    obtain ⟨e, src, dst⟩ := (rawOccurrence_membership H u v).mpr arc
    exact ⟨e, (arcNode_in_row (rawHead H) v e).mpr dst, src⟩

end Quotient

end PaperB.RamForestProgram.ArcParents
