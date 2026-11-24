module

public import PaperB.ExitInterleavedPacked

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option maxHeartbeats 2000000

namespace EX42.ArraySweep.Packed

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot

universe u v

variable {n m bits words slots : Nat} {M : Type u} {B : Type v}
variable {P : Plan n m}

structure DirectDepthInv (tags : TagsFit bits) (base : Word bits)
    (L : Layout base words slots) (S : Schedule P)
    (DepthOK : WriteResult bits words → Prop)
    (occ : Nat → Nat → Prop) (old : Nat → Store) (wb : Fin n → B)
    (k : Nat) (s : PhysicalState n bits words B) : Prop where
  inv : Inv tags base L S occ old wb k s
  depth : DepthOK s.bank

/-- `step_depth` is the frame obligation for the actual writer call. The
keep case needs no depth law: its output bank is the input bank. -/
structure DirectDepthContract (tags : TagsFit bits) (base : Word bits)
    (L : Layout base words slots) (K : Packing n m slots M) (S : Schedule P)
    (Q : DirectCallbacks n m bits words M B)
    (DepthOK : WriteResult bits words → Prop)
    (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wm : Fin m → M) (wb : Fin n → B) : Prop where
  install_refines : ∀ (a : Fin n) (i : Fin m),
    S.mapSlot.read (S.vertex a) = some i →
    ∀ s : PhysicalState n bits words B,
      OccupiedExact tags base L s.bank (occ a.val) (old a.val) →
      (∀ b : Fin n, Cell (b.val < a.val)
        (s.bases.read (S.vertex b)) (wb (S.vertex b))) →
      DepthOK s.bank →
      Q.install (S.vertex a) i s = wm i
  base_refines : ∀ (a : Fin n) (bank : WriteResult bits words) (bases : Slots B n),
    OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)) →
    (∀ b : Fin n, Cell (b.val < a.val)
      (bases.read (S.vertex b)) (wb (S.vertex b))) →
    DepthOK bank →
    Q.base (S.vertex a) bank bases = wb (S.vertex a)
  keep : ∀ a : Fin n, S.mapSlot.read (S.vertex a) = none →
    occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val
  put : ∀ (a : Fin n) (i : Fin m), S.mapSlot.read (S.vertex a) = some i →
    let j := K.jobAt (S.vertex a) i (wm i)
    PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) ∧
      occ (a.val + 1) = j.occupy (occ a.val) ∧
      old (a.val + 1) = j.overlay (old a.val)
  step_depth : ∀ (a : Fin n) (s : PhysicalState n bits words B)
      (h : Inv tags base L S occ old wb a.val s) (i : Fin m),
    S.mapSlot.read (S.vertex a) = some i →
    DepthOK s.bank →
    let j := K.jobAt (S.vertex a) i (Q.install (S.vertex a) i s)
    ∀ rj : PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val),
      let bank := PaperB.ExitPhysicalOneSlot.step tags base L s.bank j rj.bound
        (buildFromBank_fit tags base L s.bank j h.maps rj.deps rj.fit)
      OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)) →
      DepthOK bank

variable (tags : TagsFit bits) (base : Word bits) (L : Layout base words slots)
variable (K : Packing n m slots M) (S : Schedule P)
variable (Q : DirectCallbacks n m bits words M B)
variable (DepthOK : WriteResult bits words → Prop)
variable {occ : Nat → Nat → Prop} {old : Nat → Store}
variable {wm : Fin m → M} {wb : Fin n → B}

section
variable {tags base L K S Q DepthOK}

/-- Transport depth along the exact stage effect, without inspecting bank cells. -/
theorem DirectDepthContract.stage_preserves
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) (hd : DepthOK s.bank)
    {bank : WriteResult bits words}
    (hm : OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)))
    (he : DirectStageEffect tags base L K S Q a s h bank) :
    DepthOK bank := by
  cases ho : S.mapSlot.read (S.vertex a) with
  | none =>
    unfold DirectStageEffect at he
    rw [he.1 ho]
    exact hd
  | some i =>
    unfold DirectStageEffect at he
    obtain ⟨rj, rfl⟩ := he.2 i ho
    exact H.step_depth a s h i ho hd rj hm

end

/-- The imported `directStage` is private and requires unconditional callback
refinement. This stage uses the same routing and writer, with depth available
at the install call site. -/
private def directDepthStage
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) (hd : DepthOK s.bank) :
    {bank : WriteResult bits words //
      OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)) ∧
      DirectStageEffect tags base L K S Q a s h bank} := by
  cases ho : S.mapSlot.read (S.vertex a) with
  | none =>
    have t := H.keep a ho
    refine ⟨s.bank, ?_, ?_⟩
    · rw [t.1, t.2]
      exact h.maps
    · unfold DirectStageEffect
      refine ⟨fun _ => rfl, ?_⟩
      intro i hi
      have bad := ho.symm.trans hi
      cases bad
  | some i =>
    let j := K.jobAt (S.vertex a) i (Q.install (S.vertex a) i s)
    have hj : j = K.jobAt (S.vertex a) i (wm i) :=
      congrArg (K.jobAt (S.vertex a) i) (H.install_refines a i ho s h.maps h.bases hd)
    have t := H.put a i ho
    have rj : PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) := by
      rw [hj]
      exact t.1
    have fit := buildFromBank_fit tags base L s.bank j h.maps rj.deps rj.fit
    refine ⟨PaperB.ExitPhysicalOneSlot.step tags base L s.bank j rj.bound fit, ?_, ?_⟩
    · rw [t.2.1, t.2.2, ← hj]
      exact step_exact tags base L s.bank j rj.bound fit h.maps rj.fresh rj.deps
    · unfold DirectStageEffect
      refine ⟨?_, ?_⟩
      · intro hi
        have bad := ho.symm.trans hi
        cases bad
      · intro q hq
        have e : i = q := Option.some.inj (ho.symm.trans hq)
        subst q
        exact ⟨rj, rfl⟩

structure DirectDepthEventExact (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s)
    (t : PhysicalState n bits words B) : Prop where
  core : DirectEventExact tags base L K S Q a s h t
  depth : DepthOK t.bank

-- The corresponding base-column lemma in the imported module is private.
private theorem directDepth_read_write {α : Type v}
    (s : Slots α n) (a b : Fin n) (x : α) :
    (s.write a x).read b = if b = a then some x else s.read b := by
  by_cases h : b = a
  · subst b
    simp [Slots.read, Slots.write, Array.getElem_set]
  · have hv : b.val ≠ a.val := fun e => h (Fin.ext e)
    simp [Slots.read, Slots.write, Array.getElem_set, h, Ne.symm h, hv, Ne.symm hv]

/-- One stage, then one base write. The installer gets the original state;
the base callback gets the staged bank and the original base column. -/
def directDepthEvent
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : DirectDepthInv tags base L S DepthOK occ old wb a.val s) :
    {t : PhysicalState n bits words B //
      DirectDepthEventExact tags base L K S Q DepthOK a s h.inv t} :=
  let bases := s.bases
  let bank := directDepthStage tags base L K S Q DepthOK H a s h.inv h.depth
  let value := Q.base (S.vertex a) bank.val bases
  ⟨⟨bank.val, bases.write (S.vertex a) value⟩, by
    have hd : DepthOK bank.val :=
      H.stage_preserves a s h.inv h.depth bank.property.1 bank.property.2
    have hv : value = wb (S.vertex a) :=
      H.base_refines a bank.val bases bank.property.1 h.inv.bases hd
    refine ⟨⟨⟨bank.property.1, ?_⟩, bank.property.2, rfl⟩, hd⟩
    intro b
    change Cell (b.val < a.val + 1)
      ((bases.write (S.vertex a) value).read (S.vertex b)) (wb (S.vertex b))
    rw [directDepth_read_write]
    by_cases e : b = a
    · subst b
      simp [Cell, hv, Nat.lt_succ_self]
    · have hn : S.vertex b ≠ S.vertex a := fun eq => e (S.vertex_inj eq)
      have hne : b.val ≠ a.val := fun eq => e (Fin.ext eq)
      have hp : b.val < a.val + 1 ↔ b.val < a.val := by omega
      simpa only [if_neg hn, hp] using h.inv.bases b⟩

theorem directDepthEvent_read
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : DirectDepthInv tags base L S DepthOK occ old wb a.val s) (z : Fin n) :
    (directDepthEvent tags base L K S Q DepthOK H a s h).val.bases.read z =
      if z = S.vertex a then some (wb (S.vertex a)) else s.bases.read z := by
  let t := directDepthEvent tags base L K S Q DepthOK H a s h
  change t.val.bases.read z =
    (if z = S.vertex a then some (wb (S.vertex a)) else s.bases.read z)
  have hv : Q.base (S.vertex a) t.val.bank s.bases = wb (S.vertex a) :=
    H.base_refines a t.val.bank s.bases t.property.core.inv.maps
      h.inv.bases t.property.depth
  rw [t.property.core.bases_eq, directDepth_read_write, hv]

/-- One tail call per order-array entry. No depth predicate is evaluated. -/
def directDepthFoldTo
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) :
    (fuel start : Nat) → start + fuel = dst →
    (s : PhysicalState n bits words B) →
    DirectDepthInv tags base L S DepthOK occ old wb start s →
    {t : PhysicalState n bits words B //
      DirectDepthInv tags base L S DepthOK occ old wb dst t}
  | 0, start, hk, s, h => ⟨s, by rw [← hk, Nat.add_zero]; exact h⟩
  | fuel + 1, start, hk, s, h =>
    let a : Fin n := ⟨start, by omega⟩
    let t := directDepthEvent tags base L K S Q DepthOK H a s h
    directDepthFoldTo H dst hd fuel (start + 1) (by omega) t.val
      ⟨t.property.core.inv, t.property.depth⟩
termination_by structural fuel => fuel

theorem directDepthFoldTo_zero_val
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) (start : Nat) (hk : start + 0 = dst)
    (s : PhysicalState n bits words B)
    (h : DirectDepthInv tags base L S DepthOK occ old wb start s) :
    (directDepthFoldTo tags base L K S Q DepthOK H dst hd 0 start hk s h).val = s := by
  simp only [directDepthFoldTo]

theorem directDepthFoldTo_succ_val
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) (fuel start : Nat)
    (hk : start + (fuel + 1) = dst) (s : PhysicalState n bits words B)
    (h : DirectDepthInv tags base L S DepthOK occ old wb start s) :
    (directDepthFoldTo tags base L K S Q DepthOK H dst hd
      (fuel + 1) start hk s h).val =
      (let a : Fin n := ⟨start, by omega⟩
       let t := directDepthEvent tags base L K S Q DepthOK H a s h
       (directDepthFoldTo tags base L K S Q DepthOK H dst hd fuel (start + 1)
         (by omega) t.val ⟨t.property.core.inv, t.property.depth⟩).val) := by
  simp only [directDepthFoldTo]

/-- The caller supplies depth for the seed bank, including any seeded slots. -/
def directDepthRunPrefix
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (j : Nat) (hj : j ≤ n) (bank : WriteResult bits words)
    (hb : OccupiedExact tags base L bank (occ 0) (old 0))
    (hd : DepthOK bank) :
    {t : PhysicalState n bits words B //
      DirectDepthInv tags base L S DepthOK occ old wb j t} :=
  directDepthFoldTo tags base L K S Q DepthOK H j hj j 0 (Nat.zero_add j)
    ⟨bank, Slots.empty B n⟩
    ⟨⟨hb, fun a => ⟨fun ha => (Nat.not_lt_zero a.val ha).elim,
      fun _ => by simp [Slots.empty, Slots.read]⟩⟩, hd⟩

/-- When the old contract is also available, both events return the same
physical state. The comparison uses only their public exact effects. -/
theorem directDepthEvent_val_eq
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (H₀ : DirectContract tags base L K S Q occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : DirectDepthInv tags base L S DepthOK occ old wb a.val s) :
    (directDepthEvent tags base L K S Q DepthOK H a s h).val =
      (directEvent tags base L K S Q H₀ a s h.inv).val := by
  let t := directDepthEvent tags base L K S Q DepthOK H a s h
  let t₀ := directEvent tags base L K S Q H₀ a s h.inv
  change t.val = t₀.val
  have eb : t.val.bank = t₀.val.bank := by
    have e := t.property.core.stage_effect
    have e₀ := t₀.property.stage_effect
    cases ho : S.mapSlot.read (S.vertex a) with
    | none =>
      unfold DirectStageEffect at e e₀
      exact (e.1 ho).trans (e₀.1 ho).symm
    | some i =>
      unfold DirectStageEffect at e e₀
      obtain ⟨rj, ej⟩ := e.2 i ho
      obtain ⟨rj₀, ej₀⟩ := e₀.2 i ho
      exact ej.trans ej₀.symm
  have ec : t.val.bases = t₀.val.bases :=
    t.property.core.bases_eq.trans
      ((congrArg (fun bank =>
        s.bases.write (S.vertex a) (Q.base (S.vertex a) bank s.bases)) eb).trans
        t₀.property.bases_eq.symm)
  calc
    t.val = ⟨t.val.bank, t.val.bases⟩ := rfl
    _ = ⟨t₀.val.bank, t₀.val.bases⟩ := by simp only [eb, ec]
    _ = t₀.val := rfl

theorem directDepthFoldTo_val_eq
    (H : DirectDepthContract tags base L K S Q DepthOK occ old wm wb)
    (H₀ : DirectContract tags base L K S Q occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) (fuel : Nat) :
    ∀ (start : Nat) (hk : start + fuel = dst) (s : PhysicalState n bits words B)
      (h : DirectDepthInv tags base L S DepthOK occ old wb start s),
      (directDepthFoldTo tags base L K S Q DepthOK H dst hd fuel start hk s h).val =
        (directFoldTo tags base L K S Q H₀ dst hd fuel start hk s h.inv).val := by
  induction fuel with
  | zero =>
    intro start hk s h
    simp only [directDepthFoldTo_zero_val, directFoldTo_zero_val]
  | succ fuel ih =>
    intro start hk s h
    let a : Fin n := ⟨start, by omega⟩
    let t := directDepthEvent tags base L K S Q DepthOK H a s h
    let t₀ := directEvent tags base L K S Q H₀ a s h.inv
    have hn : start + 1 + fuel = dst := by omega
    have e : t.val = t₀.val :=
      directDepthEvent_val_eq tags base L K S Q DepthOK H H₀ a s h
    have align (x y : PhysicalState n bits words B)
        (hx : Inv tags base L S occ old wb (start + 1) x)
        (hy : Inv tags base L S occ old wb (start + 1) y) (he : x = y) :
        (directFoldTo tags base L K S Q H₀ dst hd fuel (start + 1) hn x hx).val =
          (directFoldTo tags base L K S Q H₀ dst hd fuel (start + 1) hn y hy).val := by
      subst y
      rfl
    have tail :
        (directDepthFoldTo tags base L K S Q DepthOK H dst hd fuel (start + 1)
          hn t.val ⟨t.property.core.inv, t.property.depth⟩).val =
        (directFoldTo tags base L K S Q H₀ dst hd fuel (start + 1)
          hn t₀.val t₀.property.inv).val :=
      (ih (start + 1) hn t.val ⟨t.property.core.inv, t.property.depth⟩).trans
        (align t.val t₀.val t.property.core.inv t₀.property.inv e)
    simpa only [directDepthFoldTo_succ_val, directFoldTo_succ_val] using tail

end EX42.ArraySweep.Packed
