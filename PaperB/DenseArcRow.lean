module

public import PaperB.DenseArcRecode
public import PaperB.ActualSiblingEmitter

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.PackedLocalArcs
open PaperB.DenseQuotientRows PaperB.DenseArcRecode PaperB.ForestLayout PaperB.LabelledQuotient

universe v
variable {N : Nat} {A : Type v}

private abbrev wire (n : Nat) : Wire n := by
  first | exact halves n | exact halves

structure Arc (n : Nat) (A : Type v) where
  tail : Fin n
  head : Fin n
  label : A

structure PhysicalRow (n : Nat) (A : Type v) where
  size : Nat
  read : Fin size → Arc n A

inductive Own (root : Fin N) (parent : Fin N → Fin N) (u : Fin N) :
    Fin (2 * N) → Prop where
  | self : Own root parent u ((wire N).pack (.inl u))
  | child (c : Fin N) : c ≠ root → parent c = u →
      Own root parent u ((wire N).pack (.inr c))

section
variable {g : ChildLists N} (rows : Layout (N := N) g)
variable {root : Fin N} {parent : Fin N → Fin N} (u : Fin N)

include rows in
theorem ordinaryChild (buckets : ∀ d : Fin N, g.get d = bucketChildren root parent d) (c : Fin N) :
    c ∈ g.get u ↔ c ≠ root ∧ parent c = u :=
  (rows.occurs_iff u (.inr c)).symm.trans
    (rows.ordinary_child_iff root parent buckets u c)

theorem packedOccurs
    (childOK : ∀ d c, c ∈ g.get d ↔ c ≠ root ∧ parent c = d)
    {b : Fin (2 * N)} (h : Own root parent u b) :
    Occurs g u ((wire N).unpack b) := by
  cases h with
  | self => rw [(wire N).unpack_pack] <;> rfl
  | child c hn hp =>
    rw [(wire N).unpack_pack]
    exact (childOK u c).2 ⟨hn, hp⟩

def translate (a : Arc (2 * N) A) : Option (Arc (rows.length u) A) :=
  match checkedSlot (wire N) rows u a.tail, checkedSlot (wire N) rows u a.head with
  | some t, some h => some ⟨t, h, a.label⟩
  | _, _ => none

def recode (r : PhysicalRow (2 * N) A) :
    Option (List (Arc (rows.length u) A)) :=
  (List.ofFn r.read).mapM (translate rows u)

abbrev Valid (r : PhysicalRow (2 * N) A) (root : Fin N)
    (parent : Fin N → Fin N) (u : Fin N) : Prop :=
  ∀ i : Fin r.size, Own root parent u (r.read i).tail ∧
    Own root parent u (r.read i).head

variable (childOK : ∀ d c, c ∈ g.get d ↔ c ≠ root ∧ parent c = d)
variable (r : PhysicalRow (2 * N) A) (own : Valid r root parent u)

def induced (i : Fin r.size) : Arc (rows.length u) A :=
  ⟨slot (wire N) rows u (r.read i).tail (packedOccurs u childOK (own i).1),
   slot (wire N) rows u (r.read i).head (packedOccurs u childOK (own i).2),
   (r.read i).label⟩

private theorem mapM_ofFn_some {X Y : Type v} (f : X → Option Y)
    {m : Nat} (p : Fin m → X) (q : Fin m → Y)
    (h : ∀ i, f (p i) = some (q i)) :
    (List.ofFn p).mapM f = some (List.ofFn q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := ih (fun i : Fin m => p i.succ) (fun i => q i.succ)
      (fun i => h i.succ)
    rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons, h 0, hs] <;> rfl

theorem recode_exact :
    recode rows u r = some (List.ofFn (induced rows u childOK r own)) := by
  unfold recode
  apply mapM_ofFn_some
  intro i
  have ht := packedOccurs u childOK (own i).1
  have hh := packedOccurs u childOK (own i).2
  simp [translate, induced, checkedSlot_valid _ _ _ _ ht,
    checkedSlot_valid _ _ _ _ hh]

theorem recode_labels (hValid : Valid r root parent u)
    (hChild : ∀ d c, c ∈ g.get d ↔ c ≠ root ∧ parent c = d) :
    (recode rows u r).map (List.map Arc.label) =
      some (List.ofFn fun i => (r.read i).label) := by
  rw [recode_exact rows u hChild r hValid]
  simp [List.map_ofFn, Function.comp_def, induced]

end

/-- Bind a typed emission fact to the packed endpoint equation. -/
theorem own_of_packed {root : Fin N} {parent : Fin N → Fin N} {u : Fin N}
    {k : Key N} {b : Fin (2 * N)} (eqCode : (wire N).pack k = b)
    (hk : match k with
      | .inl d => d = u
      | .inr c => c ≠ root ∧ parent c = u) :
    Own root parent u b := by
  rw [← eqCode]
  cases k with
  | inl d =>
    change d = u at hk
    subst d
    exact Own.self
  | inr c => exact Own.child c hk.1 hk.2

end PaperB.PackedLocalArcs
