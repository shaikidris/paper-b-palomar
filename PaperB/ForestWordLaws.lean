module

public import PaperB.ForestReady

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-
Place after EX24.PreStep.WordLaws and the packed-word specifications.

Use c.usePackedWords as the fixed configuration of the topological loop.
The per-state input to the proof is just its JumpWordLayout, available as
Grounded.layout. No query-correctness hypotheses are added to the loop
invariant.
-/

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

namespace EX24

noncomputable section

set_option autoImplicit false

/-- Preserve the dictionary and indexing data; install the packed getters. -/
def Config.usePackedWords {H : LabelledQuotient} (c : Config H) : Config H :=
  { c with
    atDepth := fun R mem u d => (ancestorAtDepthWords R mem u d).1
    ancestor := fun R mem a u => (decideAncestorWords R mem a u).1 }

theorem Grounded.usePackedWords
    {H : LabelledQuotient} {c : Config H} {F : JumpForest} {t : Tables H}
    (g : Grounded c F t) : Grounded c.usePackedWords F t :=
  ⟨g.layout, g.size_eq, g.slot_size, g.back_size, g.zero,
    g.forward, g.backward⟩

namespace PreStep

/-- The forest's actual parent-array getter, restricted to occupied slots. -/
def boundedJumpParent {F : JumpForest} (hF : ValidJumpForest F)
    (a : Fin F.size) : Fin F.size :=
  ⟨F.parentOf a.val, hF.parentOf_lt_size a.isLt⟩

private theorem packedParentVal_eq
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) (a : Fin F.size) :
    (readRecordWords R mem a.val).1.parent = F.parentOf a.val :=
  congrArg JumpRecord.parent (readRecordWords_spec hLay a.isLt).1

/-- The same bounded function, expressed as a read from the packed memory. -/
def packedParentRead
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) (a : Fin F.size) : Fin F.size :=
  ⟨(readRecordWords R mem a.val).1.parent, by
    rw [packedParentVal_eq hLay a]
    exact hLay.valid.parentOf_lt_size a.isLt⟩

theorem packedParentRead_eq_boundedJumpParent
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) :
    packedParentRead hLay = boundedJumpParent hLay.valid := by
  funext a
  exact Fin.ext (packedParentVal_eq hLay a)

private theorem climb_parent_comm {α : Type} (up : α → α)
    (k : Nat) (a : α) :
    climb up k (up a) = up (climb up k a) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg up ih

private theorem climb_val_eq_iterParent
    {F : JumpForest} (hF : ValidJumpForest F) (k : Nat)
    (a : Fin F.size) :
    (climb (boundedJumpParent hF) k a).val = F.iterParent k a.val := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      calc
        (climb (boundedJumpParent hF) (k + 1) a).val =
            (climb (boundedJumpParent hF) k (boundedJumpParent hF a)).val :=
          congrArg (fun x : Fin F.size => x.val)
            (climb_parent_comm (boundedJumpParent hF) k a).symm
        _ = F.iterParent k (boundedJumpParent hF a).val :=
          ih (boundedJumpParent hF a)
        _ = F.iterParent (k + 1) a.val := rfl

theorem isAncestor_iff_exists_bounded_climb
    {F : JumpForest} (hF : ValidJumpForest F) (a b : Fin F.size) :
    IsAncestor F a.val b.val ↔ ∃ k : Nat, climb (boundedJumpParent hF) k b = a := by
  unfold IsAncestor
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Fin.ext ((climb_val_eq_iterParent hF k b).trans hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (climb_val_eq_iterParent hF k b).symm.trans
      (congrArg (fun x : Fin F.size => x.val) hk)⟩

private theorem depth_boundedJumpParent_pos
    {F : JumpForest} (hF : ValidJumpForest F) (a : Fin F.size)
    (hpos : 0 < F.depthOf a.val) :
    F.depthOf (boundedJumpParent hF a).val = F.depthOf a.val - 1 := by
  change F.depthOf (F.parentOf a.val) = F.depthOf a.val - 1
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  have ha : a.val < F.size := a.isLt
  have hne : a.val ≠ 0 := by
    intro hz
    have hd : F.depthOf a.val = 0 := by rw [hz, inv.root_depth]
    omega
  have haPos : 0 < a.val := by omega
  have hn := inv.nodes a.val ha
  first
  | cases hn <;> first | omega | (simp_all <;> omega) | grind
  | exact?
  | cases hn <;> cases inv <;> grind

private theorem depth_bounded_climb
    {F : JumpForest} (hF : ValidJumpForest F) (k : Nat) (a : Fin F.size)
    (hk : k ≤ F.depthOf a.val) :
    F.depthOf (climb (boundedJumpParent hF) k a).val = F.depthOf a.val - k := by
  induction k with
  | zero => simp [climb]
  | succ k ih =>
      have hprev := ih (by omega)
      have hpos : 0 < F.depthOf (climb (boundedJumpParent hF) k a).val := by
        omega
      change F.depthOf (boundedJumpParent hF
        (climb (boundedJumpParent hF) k a)).val = F.depthOf a.val - (k + 1)
      rw [depth_boundedJumpParent_pos hF _ hpos, hprev] <;> omega

theorem ancestorAtDepth_eq_bounded_climb
    {F : JumpForest} (hF : ValidJumpForest F) (a : Fin F.size)
    (d : Nat) (hd : d ≤ F.depthOf a.val) :
    F.ancestorAtDepth a.val d =
      (climb (boundedJumpParent hF) (F.depthOf a.val - d) a).val := by
  let k : Nat := F.depthOf a.val - d
  let w : Fin F.size := climb (boundedJumpParent hF) k a
  have hwAnc : IsAncestor F w.val a.val :=
    (isAncestor_iff_exists_bounded_climb hF w a).2 ⟨k, rfl⟩
  have hwDepth : F.depthOf w.val = d := by
    change F.depthOf (climb (boundedJumpParent hF) (F.depthOf a.val - d) a).val = d
    rw [depth_bounded_climb hF (F.depthOf a.val - d) a (Nat.sub_le _ _)]
    omega
  exact ((hF.ancestorAtDepth_unique a.isLt hd).mp ⟨hwAnc, hwDepth⟩).symm

/-- A uniform power witness for the word specs; their cost bounds are not needed here. -/
private theorem succ_le_two_pow (n : Nat) : n + 1 ≤ (2 : Nat) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

theorem packedSelector_depth
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (hLay : JumpWordLayout c.region F s.tables.mem) (a : Fin F.size) :
    (selectors c.usePackedWords s).depth a.val = F.depthOf a.val :=
  congrArg JumpRecord.depth (readRecordWords_spec hLay a.isLt).1

theorem packedSelector_atDepth
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (hLay : JumpWordLayout c.region F s.tables.mem) (a : Fin F.size)
    (d : Nat) :
    (selectors c.usePackedWords s).atDepth a.val d = F.ancestorAtDepth a.val d :=
  (ancestorAtDepthWords_spec hLay a.isLt (Nat.le_refl F.numInserted)
    (succ_le_two_pow (F.numInserted + 1)) d).1

theorem packedSelector_ancestor
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (hLay : JumpWordLayout c.region F s.tables.mem) (a b : Fin F.size) :
    (selectors c.usePackedWords s).ancestor a.val b.val = F.decideAncestor a.val b.val :=
  (decideAncestorWords_spec hLay a.isLt b.isLt (Nat.le_refl F.numInserted)
    (succ_le_two_pow (F.numInserted + 1))).1

/-- The binder is the bounded forest getter used by the embedding. -/
theorem wordLaws_packed
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (hLay : JumpWordLayout c.region F s.tables.mem) :
    WordLaws c.usePackedWords s F (boundedJumpParent hLay.valid) := by
  constructor
  · intro a d _ hd
    rw [packedSelector_depth c s hLay a] at hd
    rw [packedSelector_atDepth c s hLay a d, packedSelector_depth c s hLay a]
    exact ancestorAtDepth_eq_bounded_climb hLay.valid a d hd
  · intro a b _
    rw [packedSelector_ancestor c s hLay a b]
    exact (hLay.valid.decideAncestor_eq_true_iff a.isLt b.isLt).trans
      (isAncestor_iff_exists_bounded_climb hLay.valid a b)
  · intro a
    simp [nodeAt]
  · intro a d hd _
    simp [nodeAt, Nat.ne_of_gt hd]

/-- The same laws with the literal packed parent read as the binder. -/
theorem wordLaws_packedRead
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (hLay : JumpWordLayout c.region F s.tables.mem) :
    WordLaws c.usePackedWords s F (packedParentRead hLay) := by
  rw [packedParentRead_eq_boundedJumpParent hLay]
  exact wordLaws_packed c s hLay

/-- Per-head entry point for a loop already running with the packed config. -/
theorem wordLaws_of_packed_grounded
    {H : LabelledQuotient} {F : JumpForest} (c : Config H) (s : State H)
    (g : Grounded c.usePackedWords F s.tables) :
    WordLaws c.usePackedWords s F (boundedJumpParent g.layout.valid) :=
  wordLaws_packed c s g.layout

end PreStep

end

end EX24
