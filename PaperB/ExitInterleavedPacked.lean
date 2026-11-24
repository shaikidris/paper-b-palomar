module

public import PaperB.ExitLinearSchedule
public import PaperB.ExitPhysicalPass

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option maxHeartbeats 2000000

namespace EX42.ArraySweep.Packed

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot

universe u v

structure Packing (n m slots : Nat) (M : Type u) where
  addr : Fin m → Fin slots
  view : Fin m → Stored → M
  job : Fin n → Fin m → M → Job

def Packing.jobAt {n m slots : Nat} {M : Type u}
    (K : Packing n m slots M) (y : Fin n) (i : Fin m) (x : M) : Job :=
  { K.job y i x with slot := (K.addr i).val }

structure PhysicalState (n bits words : Nat) (B : Type v) where
  bank : WriteResult bits words
  bases : Slots B n

variable {n m bits words slots : Nat} {M : Type u} {B : Type v}
variable {P : Plan n m} {D : Reads n m}

/-- Reference states are indexed by visits, not ranks. `occ 0` may contain
seeded records. The bridges translate logical read permissions to occupancy. -/
structure Contract (tags : TagsFit bits) (S : Schedule P) (C : Callbacks D M B)
    (K : Packing n m slots M) (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wm : Fin m → M) (wb : Fin n → B) : Prop where
  ready : Ready P D
  correct : Exact P C wm wb
  prior : ∀ (a : Fin n) (i : Fin m), P.mapBefore (P.rank (S.vertex a)) i →
    occ a.val (K.addr i).val
  staged : ∀ (a : Fin n) (i : Fin m),
    (P.mapBefore (P.rank (S.vertex a)) i ∨ P.observe (S.vertex a) i = true) →
    occ (a.val + 1) (K.addr i).val
  values : ∀ k i, occ k (K.addr i).val → K.view i (old k (K.addr i).val) = wm i
  keep : ∀ a : Fin n, S.mapSlot.read (S.vertex a) = none →
    occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val
  put : ∀ (a : Fin n) (i : Fin m), S.mapSlot.read (S.vertex a) = some i →
    let j := K.jobAt (S.vertex a) i (wm i)
    PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) ∧
      occ (a.val + 1) = j.occupy (occ a.val) ∧
      old (a.val + 1) = j.overlay (old a.val)

structure Inv (tags : TagsFit bits) (base : Word bits) (L : Layout base words slots)
    (S : Schedule P) (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wb : Fin n → B) (k : Nat) (s : PhysicalState n bits words B) : Prop where
  maps : OccupiedExact tags base L s.bank (occ k) (old k)
  bases : ∀ a : Fin n,
    Cell (a.val < k) (s.bases.read (S.vertex a)) (wb (S.vertex a))

variable (tags : TagsFit bits) (base : Word bits) (L : Layout base words slots)
variable (K : Packing n m slots M)

/-- A decoded callback value can retain the block, but not the bank via
the decoder's cell reader. -/
private def readMap (bank : WriteResult bits words) (i : Fin m) : M :=
  let k := K.addr i
  let cells := Array.ofFn (readStoredBlockAt bank.mem base k.val
    (L.addrAt k.isLt) (bank.le_size (L.memAt k.isLt)))
  K.view i ((storedCodec tags).decode (fun p : Fin 18 =>
    cells[p.val]'(by simpa [cells] using p.isLt)))

private theorem readMap_eq (bank : WriteResult bits words) (i : Fin m) :
    readMap tags base L K bank i =
      K.view i (readSlot tags base L bank (K.addr i).val (K.addr i).isLt) := by
  unfold readMap readSlot readStoredAt
  apply congrArg (K.view i)
  apply congrArg (storedCodec tags).decode
  funext p
  simp only [Array.getElem_ofFn]

variable (S : Schedule P) (C : Callbacks D M B)
variable {occ : Nat → Nat → Prop} {old : Nat → Store}
variable {wm : Fin m → M} {wb : Fin n → B}

section
variable {tags base L K S C}

private theorem base_ok {a : Fin n} {s : PhysicalState n bits words B}
    (h : Inv tags base L S occ old wb a.val s) (z : Fin n)
    (hz : P.rank z < P.rank (S.vertex a)) :
    s.bases.read z = some (wb z) := by
  obtain ⟨b, rfl⟩ := S.covers z
  exact (h.bases b).1 ((S.rank_lt_rank_iff b a).mp hz)

private theorem map_ok (H : Contract tags S C K occ old wm wb)
    {k : Nat} {bank : WriteResult bits words}
    (h : OccupiedExact tags base L bank (occ k) (old k))
    (i : Fin m) (hi : occ k (K.addr i).val) :
    some (readMap tags base L K bank i) = some (wm i) := by
  obtain ⟨_, he⟩ := h _ hi
  rw [readMap_eq, he, H.values k i hi]

end

private theorem read_write {α : Type v} (s : Slots α n) (a b : Fin n) (x : α) :
    (s.write a x).read b = if b = a then some x else s.read b := by
  by_cases h : b = a
  · subst b
    simp [Slots.read, Slots.write, Array.getElem_set]
  · have hv : b.val ≠ a.val := fun e => h (Fin.ext e)
    simp [Slots.read, Slots.write, Array.getElem_set, h, Ne.symm h, hv, Ne.symm hv]

private def stage (H : Contract tags S C K occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {bank : WriteResult bits words //
      OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1))} := by
  cases ho : S.mapSlot.read (S.vertex a) with
  | none =>
    have t := H.keep a ho
    exact ⟨s.bank, by rw [t.1, t.2]; exact h.maps⟩
  | some i =>
    let rb := fun (p : Fin n) (_ : D.installBase i p) => s.bases.read p
    let rm := fun (j : Fin m) (_ : D.installMap i j) =>
      some (readMap tags base L K s.bank j)
    let j := K.jobAt (S.vertex a) i (C.install (S.vertex a) i rb rm)
    have first := (S.slot_exact (S.vertex a) i).mp ho
    have r := H.ready.install (S.vertex a) i first
    have he : C.install (S.vertex a) i rb rm = wm i :=
      H.correct.install (S.vertex a) i rb rm first
        (fun p hp => base_ok h p (r.1 p hp))
        (fun q hq => map_ok H h.maps q (H.prior a q (r.2 q hq)))
    have hj : j = K.jobAt (S.vertex a) i (wm i) :=
      congrArg (K.jobAt (S.vertex a) i) he
    have t := H.put a i ho
    have rj : PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) := by
      rw [hj]
      exact t.1
    have fit := buildFromBank_fit tags base L s.bank j h.maps rj.deps rj.fit
    refine ⟨PaperB.ExitPhysicalOneSlot.step tags base L s.bank j rj.bound fit, ?_⟩
    rw [t.2.1, t.2.2, ← hj]
    exact step_exact tags base L s.bank j rj.bound fit h.maps rj.fresh rj.deps

/-- The installer sees the input bank; the base builder sees the staged bank.
Both read the same input base column. -/
def event (H : Contract tags S C K occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb (a.val + 1) t} :=
  let bank := stage tags base L K S C H a s h
  let rb := fun (z : Fin n) (_ : D.vertexBase (S.vertex a) z) => s.bases.read z
  let rm := fun (i : Fin m) (_ : D.vertexMap (S.vertex a) i) =>
    some (readMap tags base L K bank.val i)
  let value := C.base (S.vertex a) rb rm
  ⟨⟨bank.val, s.bases.write (S.vertex a) value⟩, by
    have r := H.ready.vertex (S.vertex a)
    have hv : value = wb (S.vertex a) :=
      H.correct.vertex (S.vertex a) rb rm
        (fun z hz => base_ok h z (r.1 z hz))
        (fun i hi => map_ok H bank.property i (H.staged a i (r.2 i hi)))
    refine ⟨bank.property, ?_⟩
    intro b
    change Cell (b.val < a.val + 1)
      ((s.bases.write (S.vertex a) value).read (S.vertex b)) (wb (S.vertex b))
    rw [read_write]
    by_cases e : b = a
    · subst b
      simp [Cell, hv, Nat.lt_succ_self]
    · have hn : S.vertex b ≠ S.vertex a := fun eq => e (S.vertex_inj eq)
      have hne : b.val ≠ a.val := fun eq => e (Fin.ext eq)
      have hp : b.val < a.val + 1 ↔ b.val < a.val := by omega
      simpa only [if_neg hn, hp] using h.bases b⟩

/-- One tail call per order-array entry. Contracts and prefix proofs erase. -/
def foldTo (H : Contract tags S C K occ old wm wb) (dst : Nat) (hd : dst ≤ n) :
    (fuel start : Nat) → start + fuel = dst → (s : PhysicalState n bits words B) →
    Inv tags base L S occ old wb start s →
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb dst t}
  | 0, start, hk, s, h => ⟨s, by rw [← hk, Nat.add_zero]; exact h⟩
  | fuel + 1, start, hk, s, h =>
    let a : Fin n := ⟨start, by omega⟩
    let t := event tags base L K S C H a s h
    foldTo H dst hd fuel (start + 1) (by omega) t.val t.property
termination_by structural fuel => fuel

def runPrefix (H : Contract tags S C K occ old wm wb) (j : Nat) (hj : j ≤ n)
    (bank : WriteResult bits words)
    (hb : OccupiedExact tags base L bank (occ 0) (old 0)) :
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb j t} :=
  foldTo tags base L K S C H j hj j 0 (Nat.zero_add j) ⟨bank, Slots.empty B n⟩
    ⟨hb, fun a => ⟨fun ha => (Nat.not_lt_zero a.val ha).elim,
      fun _ => by simp [Slots.empty, Slots.read]⟩⟩

-- Insert immediately before `end EX42.ArraySweep.Packed`.

section Direct

/-- The installer receives the pre-stage state. The base callback receives
the staged bank and the pre-stage base column. -/
structure DirectCallbacks (n m bits words : Nat) (M : Type u) (B : Type v) where
  install : Fin n → Fin m → PhysicalState n bits words B → M
  base : Fin n → WriteResult bits words → Slots B n → B

/-- The reference functions occur only in propositions. Callback refinement
uses the physical invariants at the call site, not an `Exact` graph build. -/
structure DirectContract (tags : TagsFit bits) (base : Word bits)
    (L : Layout base words slots) (K : Packing n m slots M) (S : Schedule P)
    (Q : DirectCallbacks n m bits words M B)
    (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wm : Fin m → M) (wb : Fin n → B) : Prop where
  install_refines : ∀ (a : Fin n) (i : Fin m),
    S.mapSlot.read (S.vertex a) = some i →
    ∀ s : PhysicalState n bits words B,
      OccupiedExact tags base L s.bank (occ a.val) (old a.val) →
      (∀ b : Fin n, Cell (b.val < a.val)
        (s.bases.read (S.vertex b)) (wb (S.vertex b))) →
      Q.install (S.vertex a) i s = wm i
  base_refines : ∀ (a : Fin n) (bank : WriteResult bits words) (bases : Slots B n),
    OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)) →
    (∀ b : Fin n, Cell (b.val < a.val)
      (bases.read (S.vertex b)) (wb (S.vertex b))) →
    Q.base (S.vertex a) bank bases = wb (S.vertex a)
  keep : ∀ a : Fin n, S.mapSlot.read (S.vertex a) = none →
    occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val
  put : ∀ (a : Fin n) (i : Fin m), S.mapSlot.read (S.vertex a) = some i →
    let j := K.jobAt (S.vertex a) i (wm i)
    PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) ∧
      occ (a.val + 1) = j.occupy (occ a.val) ∧
      old (a.val + 1) = j.overlay (old a.val)

variable (Q : DirectCallbacks n m bits words M B)

/-- A stage either preserves the bank or is one physical writer step on the
job constructed from the direct installer result. -/
def DirectStageEffect (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s)
    (bank : WriteResult bits words) : Prop :=
  (S.mapSlot.read (S.vertex a) = none → bank = s.bank) ∧
  ∀ i : Fin m, S.mapSlot.read (S.vertex a) = some i →
    let j := K.jobAt (S.vertex a) i (Q.install (S.vertex a) i s)
    ∃ rj : PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val),
      bank = PaperB.ExitPhysicalOneSlot.step tags base L s.bank j rj.bound
        (buildFromBank_fit tags base L s.bank j h.maps rj.deps rj.fit)

private def directStage (H : DirectContract tags base L K S Q occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {bank : WriteResult bits words //
      OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1)) ∧
      DirectStageEffect tags base L K S Q a s h bank} := by
  -- Only the existing schedule entry is read for routing.
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
    have he : Q.install (S.vertex a) i s = wm i :=
      H.install_refines a i ho s h.maps h.bases
    have hj : j = K.jobAt (S.vertex a) i (wm i) :=
      congrArg (K.jobAt (S.vertex a) i) he
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

structure DirectEventExact (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s)
    (t : PhysicalState n bits words B) : Prop where
  inv : Inv tags base L S occ old wb (a.val + 1) t
  stage_effect : DirectStageEffect tags base L K S Q a s h t.bank
  bases_eq : t.bases =
    s.bases.write (S.vertex a) (Q.base (S.vertex a) t.bank s.bases)

/-- One stage, followed by one base write. All certificates erase; the
executable path constructs neither reference columns nor point readers. -/
def directEvent (H : DirectContract tags base L K S Q occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {t : PhysicalState n bits words B //
      DirectEventExact tags base L K S Q a s h t} :=
  let bases := s.bases
  let bank := directStage tags base L K S Q H a s h
  let value := Q.base (S.vertex a) bank.val bases
  ⟨⟨bank.val, bases.write (S.vertex a) value⟩, by
    refine ⟨⟨bank.property.1, ?_⟩, bank.property.2, rfl⟩
    have hv : value = wb (S.vertex a) :=
      H.base_refines a bank.val bases bank.property.1 h.bases
    intro b
    change Cell (b.val < a.val + 1)
      ((bases.write (S.vertex a) value).read (S.vertex b)) (wb (S.vertex b))
    rw [read_write]
    by_cases e : b = a
    · subst b
      simp [Cell, hv, Nat.lt_succ_self]
    · have hn : S.vertex b ≠ S.vertex a := fun eq => e (S.vertex_inj eq)
      have hne : b.val ≠ a.val := fun eq => e (Fin.ext eq)
      have hp : b.val < a.val + 1 ↔ b.val < a.val := by omega
      simpa only [if_neg hn, hp] using h.bases b⟩

/-- The selected base is written exactly; every other base read is unchanged. -/
theorem directEvent_read (H : DirectContract tags base L K S Q occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) (z : Fin n) :
    (directEvent tags base L K S Q H a s h).val.bases.read z =
      if z = S.vertex a then some (wb (S.vertex a)) else s.bases.read z := by
  let t := directEvent tags base L K S Q H a s h
  change t.val.bases.read z =
    (if z = S.vertex a then some (wb (S.vertex a)) else s.bases.read z)
  have hv : Q.base (S.vertex a) t.val.bank s.bases = wb (S.vertex a) :=
    H.base_refines a t.val.bank s.bases t.property.inv.maps h.bases
  rw [t.property.bases_eq, read_write, hv]

def directFoldTo (H : DirectContract tags base L K S Q occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) :
    (fuel start : Nat) → start + fuel = dst →
    (s : PhysicalState n bits words B) →
    Inv tags base L S occ old wb start s →
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb dst t}
  | 0, start, hk, s, h => ⟨s, by rw [← hk, Nat.add_zero]; exact h⟩
  | fuel + 1, start, hk, s, h =>
    let a : Fin n := ⟨start, by omega⟩
    let t := directEvent tags base L K S Q H a s h
    directFoldTo H dst hd fuel (start + 1) (by omega) t.val t.property.inv
termination_by structural fuel => fuel

theorem directFoldTo_zero_val (H : DirectContract tags base L K S Q occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) (start : Nat) (hk : start + 0 = dst)
    (s : PhysicalState n bits words B) (h : Inv tags base L S occ old wb start s) :
    (directFoldTo tags base L K S Q H dst hd 0 start hk s h).val = s := by
  simp only [directFoldTo]

/-- Each successor visit consumes one schedule entry and performs one event. -/
theorem directFoldTo_succ_val (H : DirectContract tags base L K S Q occ old wm wb)
    (dst : Nat) (hd : dst ≤ n) (fuel start : Nat)
    (hk : start + (fuel + 1) = dst)
    (s : PhysicalState n bits words B) (h : Inv tags base L S occ old wb start s) :
    (directFoldTo tags base L K S Q H dst hd (fuel + 1) start hk s h).val =
      (let a : Fin n := ⟨start, by omega⟩
       let t := directEvent tags base L K S Q H a s h
       (directFoldTo tags base L K S Q H dst hd fuel (start + 1)
         (by omega) t.val t.property.inv).val) := by
  simp only [directFoldTo]

def directRunPrefix (H : DirectContract tags base L K S Q occ old wm wb)
    (j : Nat) (hj : j ≤ n) (bank : WriteResult bits words)
    (hb : OccupiedExact tags base L bank (occ 0) (old 0)) :
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb j t} :=
  directFoldTo tags base L K S Q H j hj j 0 (Nat.zero_add j)
    ⟨bank, Slots.empty B n⟩
    ⟨hb, fun a => ⟨fun ha => (Nat.not_lt_zero a.val ha).elim,
      fun _ => by simp [Slots.empty, Slots.read]⟩⟩

end Direct

end EX42.ArraySweep.Packed
