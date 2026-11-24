module

public import PaperB.DomFromOriginal
public import PaperB.StaticFromDominators
public import PaperB.StaticTreeReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.EX16Assembly

open EX15 EX15.WholeScan EX15.WholeScan.PackedInput
open JumpForestCommonAncestor
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath

universe u

-- Only the root and parent fields are used by EX16.Anc.
private def bridgeTables {N : Nat} (x : PackedStaticLayout.Input N) :
    EX16.Tables (Fin N) :=
  { root := x.root
    parent := x.parent.read
    depth := x.depth.read
    heavy := fun _ => none
    head := id
    size := fun _ => 0 }

/-- Iteration may take extra steps at the root; an EX16 path omits them. -/
theorem parentIter_iff_readerAncestor {N : Nat}
    (x : PackedStaticLayout.Input N)
    (hroot : x.parent.read x.root = x.root) (a v : Fin N) :
    EX15.WholeScan.PackedInput.SemanticAncestor x a v ↔
      StaticTreeReader.SemanticAncestor x a v := by
  change (∃ k, parentIter x k v = a) ↔ EX16.Anc (bridgeTables x) a v
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero =>
        change v = a at hk
        subst v
        exact EX16.Path.refl
    | succ k ih =>
        change parentIter x k (x.parent.read v) = a at hk
        by_cases hn : v = x.root
        · subst v
          rw [hroot] at hk
          exact ih x.root hk
        · exact EX16.Path.step (b := v) hn True.intro
            (ih (x.parent.read v) hk)
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @step b _ _ _ ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨k + 1, ?_⟩
        change parentIter x k (x.parent.read b) = a
        exact hk

section Scan

variable {α : Type u} {g : Digraph} {R : JumpWordRegion}
variable {r : Fin g.vertexCount} {s : ScanState}

private theorem scanRoot_fixed {S : Fin g.vertexCount → Prop}
    (C : Certified α R r S s) :
    (scanInput C).parent.read (scanInput C).root = (scanInput C).root := by
  have C' := C
  obtain ⟨F, I⟩ := C'
  have hLayout : JumpWordLayout R F s.words := I.layout
  have hExists : ∃ J, JumpWordLayout R J s.words := ⟨F, hLayout⟩
  have hp :
      ((scanInput C).parent.read (scanInput C).root).val =
        F.parentOf (scanInput C).root.val :=
    ofWords_parent hLayout hExists (scanInput C).root
  have hz : (scanInput C).root.val = 0 := rfl
  obtain ⟨_, inv⟩ := hLayout.valid.exists_forestInvariant
  apply Fin.ext
  simpa only [hp, hz] using inv.root_parent

/-- The scan's original-vertex map supplies the two indices into the reader. -/
theorem scan_dominates_iff_interval {S : Fin g.vertexCount → Prop}
    (C : Certified α R r S s) (q : StaticTreeReader.Reader (scanInput C))
    {a v : Fin g.vertexCount} (ha : S a) (hv : S v) :
    g.Dominates r a v ↔
      q.entry (scanSlot C a ha) ≤ q.entry (scanSlot C v hv) ∧
      q.entry (scanSlot C v hv) < q.stop (scanSlot C a ha) :=
  (dominates_iff_semanticAncestor C ha hv).trans
    ((parentIter_iff_readerAncestor (scanInput C) (scanRoot_fixed C)
      (scanSlot C a ha) (scanSlot C v hv)).trans
      (q.ancestor_iff_interval (scanSlot C a ha) (scanSlot C v hv)))

end Scan

private def readOriginalParent {g : Digraph} {r : Fin g.vertexCount}
    {n : Nat} (x : PackedStaticLayout.Input n) (ids : OriginalIds.Reader g r n)
    (v : Fin g.vertexCount) : Fin g.vertexCount :=
  match ids.find v with
  | none => v
  | some k => ids.originals.read (x.parent.read k)

private theorem readOriginalParent_hit {g : Digraph} {r : Fin g.vertexCount}
    {n : Nat} (x : PackedStaticLayout.Input n) (ids : OriginalIds.Reader g r n)
    {v : Fin g.vertexCount} {k : Fin n} (h : ids.find v = some k) :
    readOriginalParent x ids v = ids.originals.read (x.parent.read k) := by
  unfold readOriginalParent
  rw [h]

structure OriginalReader (g : Digraph) (r : Fin g.vertexCount) where
  count : Nat
  input : PackedStaticLayout.Input count
  reader : StaticTreeReader.Reader input
  slot : (v : Fin g.vertexCount) → g.InitiallyReachable r v → Fin count
  ids : OriginalIds.Reader g r count
  find_slot : ∀ (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v),
    ids.find v = some (slot v hv)
  parentSpec : PaperB.Digraph.ParentSpec g r (readOriginalParent input ids)
  dominates_iff_interval :
    ∀ (a v : Fin g.vertexCount)
      (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v),
      g.Dominates r a v ↔
        reader.entry (slot a ha) ≤ reader.entry (slot v hv) ∧
        reader.entry (slot v hv) < reader.stop (slot a ha)

private def ofScan {α : Type u} {g : Digraph} {R : JumpWordRegion}
    {r : Fin g.vertexCount} {s : ScanState}
    (H : ∃ F, Partial (WholeScan.packedJumpOps α R) r (g.InitiallyReachable r) F s ∧
      Parents r (g.InitiallyReachable r) F s.slots)
    (rootReach : g.InitiallyReachable r r) : OriginalReader g r :=
  let C : Certified α R r (g.InitiallyReachable r) s := by
    obtain ⟨F, I, _⟩ := H
    exact ⟨F, I⟩
  let x := scanInput C
  let hx := scanInput_ok C
  let q := PaperB.StaticTreeReader.build x hx
  let ids := OriginalIds.build C
  { count := occupied R s.words
    input := x
    reader := q
    slot := scanSlot C
    ids := ids
    find_slot := OriginalIds.toSlot_of_reachable C
    parentSpec := by
      obtain ⟨F, I, P⟩ := H
      have hLayout : JumpWordLayout R F s.words := I.layout
      have hExists : ∃ J, JumpWordLayout R J s.words := ⟨F, hLayout⟩
      have hword (k : Fin (occupied R s.words)) :
          (x.parent.read k).val = F.parentOf k.val :=
        ofWords_parent hLayout hExists k
      have hfind (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
          ids.find v = some (scanSlot C v hv) :=
        OriginalIds.toSlot_of_reachable C v hv
      constructor
      · have hslot : scanSlot C r rootReach = x.root := by
          apply Fin.ext
          change readSlot s.slots r = 0
          first
          | exact I.root_slot
          | exact I.slot_root
          | exact I.rootSlot
          | exact I.root
          | cases I <;> solve_by_elim
          | exact?
        have hr : ids.find r = some x.root := by
          rw [← hslot]
          exact hfind r rootReach
        have hp : x.parent.read x.root = x.root := by
          have hok := hx
          first
          | exact hok.root_parent
          | exact hok.parent_root
          | cases hok <;> assumption
          | exact scanRoot_fixed C
        rw [readOriginalParent_hit x ids hr, hp]
        exact ids.original_of_slot r x.root hr
      · intro v hvr
        by_cases hv : g.InitiallyReachable r v
        · obtain ⟨d, hd, hslot, hi⟩ := P v hv hvr
          have hp : x.parent.read (scanSlot C v hv) = scanSlot C d hd := by
            apply Fin.ext
            exact (hword (scanSlot C v hv)).trans hslot.symm
          have he : readOriginalParent x ids v = d :=
            (readOriginalParent_hit x ids (hfind v hv)).trans
              ((congrArg ids.originals.read hp).trans
                (ids.original_of_slot d (scanSlot C d hd) (hfind d hd)))
          exact Or.inl ⟨hv, he.symm ▸ hi⟩
        · have hm : ids.find v = none := (ids.miss_iff v).2 hv
          exact Or.inr ⟨hv, by simp only [readOriginalParent, hm]⟩
    dominates_iff_interval := fun _ _ ha hv =>
      scan_dominates_iff_interval C q ha hv }

/-- Run the original DAG scan once and build one reader from its word image.
The scan specification supplies one erased witness for both certificates. -/
def fromOriginal (g : Digraph) (r : Fin g.vertexCount)
    (hacyc : EX15.GraphAcyclic g) {L : Nat} (hL : g.vertexCount + 2 ≤ 2 ^ L)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r) : OriginalReader g r :=
  let out := EX15.runGraph g r hacyc
  ofScan (α := EX15.OriginalOccurrence g) (R := EX15.graphRegion g.vertexCount) (s := out.state)
    (by
      obtain ⟨F, I, P, _⟩ := EX15.runGraph_spec g r hacyc hL rootReach rootDom
      exact ⟨F, I, P⟩)
    rootReach

theorem fromOriginal_dominates_iff_interval
    (g : Digraph) (r : Fin g.vertexCount)
    (hacyc : EX15.GraphAcyclic g) {L : Nat} (hL : g.vertexCount + 2 ≤ 2 ^ L)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r)
    {a v : Fin g.vertexCount}
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) :
    let q := fromOriginal g r hacyc hL rootReach rootDom
    g.Dominates r a v ↔
      q.reader.entry (q.slot a ha) ≤ q.reader.entry (q.slot v hv) ∧
      q.reader.entry (q.slot v hv) < q.reader.stop (q.slot a ha) :=
  (fromOriginal g r hacyc hL rootReach rootDom).dominates_iff_interval a v ha hv

namespace OriginalReader

variable {g : Digraph} {r : Fin g.vertexCount}

/-- The original-ID parent callback, certified by `parentSpec`. -/
def parent (q : OriginalReader g r) (v : Fin g.vertexCount) :
    Fin g.vertexCount :=
  readOriginalParent q.input q.ids v

theorem find_eq_some_iff_original (q : OriginalReader g r)
    (i : Fin g.vertexCount) (x : Fin q.count) :
    q.ids.find i = some x ↔ q.ids.originals.read x = i := by
  constructor
  · intro h
    exact q.ids.original_of_slot i x h
  · intro h
    rw [← h]
    exact q.ids.slot_of_original x

theorem original_at_slot (q : OriginalReader g r)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
    q.ids.originals.read (q.slot v hv) = v :=
  (q.find_eq_some_iff_original v (q.slot v hv)).mp (q.find_slot v hv)

theorem slot_at_original (q : OriginalReader g r) (x : Fin q.count) :
    q.slot (q.ids.originals.read x) (q.ids.original_reachable x) = x := by
  apply Option.some.inj
  exact (q.find_slot _ (q.ids.original_reachable x)).symm.trans
    (q.ids.slot_of_original x)

theorem parent_at_slot (q : OriginalReader g r)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
    q.parent v = q.ids.originals.read (q.input.parent.read (q.slot v hv)) :=
  readOriginalParent_hit q.input q.ids (q.find_slot v hv)

theorem find_parent_at_slot (q : OriginalReader g r)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v) :
    q.ids.find (q.parent v) = some (q.input.parent.read (q.slot v hv)) := by
  rw [q.parent_at_slot v hv]
  exact q.ids.slot_of_original _

theorem parent_at_original (q : OriginalReader g r) (k : Fin q.count) :
    q.parent (q.ids.originals.read k) =
      q.ids.originals.read (q.input.parent.read k) :=
  readOriginalParent_hit q.input q.ids (q.ids.slot_of_original k)

theorem held_dominates_iff_interval (q : OriginalReader g r)
    (a x : Fin q.count) :
    g.Dominates r (q.ids.originals.read a) (q.ids.originals.read x) ↔
      q.reader.entry a ≤ q.reader.entry x ∧
      q.reader.entry x < q.reader.stop a := by
  simpa only [slot_at_original] using
    (q.dominates_iff_interval
      (q.ids.originals.read a) (q.ids.originals.read x)
      (q.ids.original_reachable a) (q.ids.original_reachable x))

/-- Query the stored reader directly on the two translated original IDs. -/
def dominates (q : OriginalReader g r) (a v : Fin g.vertexCount)
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) : Bool :=
  q.reader.isAncestor (q.slot a ha) (q.slot v hv)

theorem dominates_exact (q : OriginalReader g r) (a v : Fin g.vertexCount)
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) :
    g.Dominates r a v ↔ q.dominates a v ha hv = true :=
  (q.dominates_iff_interval a v ha hv).trans
    ((q.reader.ancestor_iff_interval (q.slot a ha) (q.slot v hv)).symm.trans
      (q.reader.isAncestor_exact (q.slot a ha) (q.slot v hv)).symm)

end OriginalReader
end PaperB.EX16Assembly
