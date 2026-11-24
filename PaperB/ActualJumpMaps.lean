module

public import PaperB.JumpMapFold
public import PaperB.Jumps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute

open PaperB.ExitMap.CheckedFold
open JumpForest

/-- Use the existing tag directly. The source and destination carried by the
move are certified by `Follows`, not used as unchecked lookup indices. -/
def kind : JumpMove → Move
  | .parent _ _ => .parent
  | .jump _ _ => .jump

def selectMove (r : Stored) (mv : JumpMove) : Selected :=
  r.select (kind mv)

/-- The map store and the forest agree on both targets. The parent condition
is the strict-depth fact needed to certify a parent edge at a live vertex;
it does not require a root's self-parent to decrease. -/
structure StoreOK (F : JumpForest) (read : Store) : Prop where
  parent_eq : ∀ u, (read u).parent = F.parentOf u
  jump_eq : ∀ u, (read u).jump = F.jumpOf u
  parent_down : ∀ u, 0 < F.depthOf u →
    F.depthOf (F.parentOf u) < F.depthOf u
  jump_ok : ∀ u, JumpOK read F.depthOf u

/-- Checks the original list, including the source and destination fields
of every move. The tail always starts at the head move's destination. -/
inductive Follows (F : JumpForest) : Nat → List JumpMove → Nat → Prop where
  | nil (u : Nat) : Follows F u [] u
  | parent (u : Nat) {ms : List JumpMove} {a : Nat}
      (live : 0 < F.depthOf u)
      (tail : Follows F (F.parentOf u) ms a) :
      Follows F u (JumpMove.parent u (F.parentOf u) :: ms) a
  | jump (u : Nat) {ms : List JumpMove} {a : Nat}
      (tail : Follows F (F.jumpOf u) ms a) :
      Follows F u (JumpMove.jump u (F.jumpOf u) :: ms) a

theorem traceMovesAux_follows (F : JumpForest) (fuel u d : Nat) :
    Follows F u (F.traceMovesAux fuel u d) (F.ancestorAtDepthAux fuel u d) := by
  induction fuel generalizing u with
  | zero =>
    simpa [JumpForest.traceMovesAux_zero, JumpForest.ancestorAtDepthAux] using
      (Follows.nil (F := F) u)
  | succ fuel ih =>
    rw [JumpForest.traceMovesAux_succ]
    by_cases h : d < F.depthOf u
    · rw [if_pos h]
      have hnot : ¬ F.depthOf u ≤ d := Nat.not_le_of_lt h
      by_cases hj : d ≤ F.depthOf (F.jumpOf u)
      · simpa [JumpForest.stepMoveToDepth, JumpForest.stepToDepth,
          JumpForest.ancestorAtDepthAux, h, hnot, hj] using
          (Follows.jump (F := F) u (ih (F.jumpOf u)))
      · have live : 0 < F.depthOf u :=
          Nat.lt_of_le_of_lt (Nat.zero_le d) h
        simpa [JumpForest.stepMoveToDepth, JumpForest.stepToDepth,
          JumpForest.ancestorAtDepthAux, h, hnot, hj] using
          (Follows.parent (F := F) u live (ih (F.parentOf u)))
    · rw [if_neg h]
      have hle : F.depthOf u ≤ d := Nat.le_of_not_gt h
      simpa [JumpForest.ancestorAtDepthAux, h, hle] using
        (Follows.nil (F := F) u)

theorem traceMoves_follows (F : JumpForest) (u d : Nat) :
    Follows F u (F.traceMoves u d) (F.ancestorAtDepth u d) := by
  simpa only [JumpForest.traceMoves, JumpForest.ancestorAtDepth] using
    traceMovesAux_follows F (F.depthOf u - d) u d

theorem Follows.checked {F : JumpForest} {read : Store}
    (ok : StoreOK F read) {u a : Nat} {ms : List JumpMove}
    (h : Follows F u ms a) :
    Checked kind read F.depthOf u ms a := by
  induction h with
  | nil u =>
    exact Checked.nil u
  | @parent u ms a live tail ih =>
    have down : F.depthOf (read u).parent < F.depthOf u := by
      rw [ok.parent_eq u]
      exact ok.parent_down u live
    have dst :
        (selectMove (read u) (JumpMove.parent u (F.parentOf u))).dst =
          F.parentOf u :=
      ok.parent_eq u
    have ht : Checked kind read F.depthOf
        (selectMove (read u) (JumpMove.parent u (F.parentOf u))).dst ms a := by
      simpa only [dst] using ih
    exact Checked.cons u (JumpMove.parent u (F.parentOf u)) (parent_segment down) ht
  | @jump u ms a tail ih =>
    have dst :
        (selectMove (read u) (JumpMove.jump u (F.jumpOf u))).dst =
          F.jumpOf u :=
      ok.jump_eq u
    have ht : Checked kind read F.depthOf
        (selectMove (read u) (JumpMove.jump u (F.jumpOf u))).dst ms a := by
      simpa only [dst] using ih
    exact Checked.cons u (JumpMove.jump u (F.jumpOf u))
      (jump_segment (ok.jump_ok u)) ht

theorem traceMoves_checked {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (u d : Nat) :
    Checked kind read F.depthOf u (F.traceMoves u d) (F.ancestorAtDepth u d) :=
  Follows.checked ok (traceMoves_follows F u d)

/-- Consume the native trace directly. No converted move list, vertex list,
or expanded parent path is constructed. The endpoint is computed by the
fold itself; this definition does not call `ancestorAtDepth` separately. -/
def foldTrace (F : JumpForest) (read : Store) (u d : Nat) : Result :=
  fold kind read u (F.traceMoves u d)

theorem foldTrace_spec {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (u d : Nat) :
    let r := foldTrace F read u d
    r.stop = F.ancestorAtDepth u d ∧
      ParentPath read F.depthOf u (F.ancestorAtDepth u d) r.composed ∧
      r.steps = (F.traceMoves u d).length := by
  obtain ⟨hs, m, hp, hm⟩ :=
    foldAux_spec (traceMoves_checked ok u d) Map.identity 0
  have hc : (foldTrace F read u d).composed = m :=
    hm.trans (identity_compose m)
  refine ⟨hs, ?_, fold_steps kind read u (F.traceMoves u d)⟩
  simpa only [hc] using hp

/-- Equality of maps, not just equality on one input. The reference is
a proposition about consecutive parent edges and is erased at runtime. -/
theorem foldTrace_exact {F : JumpForest} {read : Store}
    (ok : StoreOK F read) {u d : Nat} {m : Map}
    (reference : ParentPath read F.depthOf u (F.ancestorAtDepth u d) m) :
    (foldTrace F read u d).stop = F.ancestorAtDepth u d ∧
      (foldTrace F read u d).composed = m :=
  fold_exact (traceMoves_checked ok u d) reference

theorem foldTrace_eval_exact {F : JumpForest} {read : Store}
    (ok : StoreOK F read) {u d : Nat} {m : Map}
    (reference : ParentPath read F.depthOf u (F.ancestorAtDepth u d) m)
    (xs : Values) :
    Map.eval (foldTrace F read u d).composed xs = Map.eval m xs := by
  rw [(foldTrace_exact ok reference).2]

/-- For `L` moves, the native trace allocates `L` list cells and `L` move
records, with at most `L + 1` trace recursion frames. The tail-recursive
fold needs only a fixed-size accumulator, cursor, and counter in addition
to that trace. All path and endpoint certificates are erased.

The fold makes `L` store reads and `L` compositions. Each composition
processes two coordinates and uses at most two interval joins; each join
uses at most one min and one max. With constant-cost record access and
word-sized indices and endpoints, both work and temporary storage are
`O(log (n + 2))`. A final map evaluation adds only constant work. -/
theorem foldTrace_cost {F : JumpForest} (read : Store)
    (hF : ValidJumpForest F) {u n : Nat}
    (hu : u < F.size) (hInserted : F.numInserted ≤ n) (d : Nat) :
    let L := (F.traceMoves u d).length
    let B := 3 * ceilLog2 (n + 2)
    (foldTrace F read u d).steps = L ∧ L ≤ B ∧
      2 * (foldTrace F read u d).steps ≤ 2 * B := by
  have hs : (foldTrace F read u d).steps = (F.traceMoves u d).length :=
    fold_steps kind read u (F.traceMoves u d)
  have hl : (F.traceMoves u d).length ≤ 3 * ceilLog2 (n + 2) :=
    traceMoves_length_le_ceilLog2 hF hu hInserted d
  refine ⟨hs, hl, ?_⟩
  rw [hs]
  exact Nat.mul_le_mul_left 2 hl

end PaperB.ExitMap.JumpMapRoute
