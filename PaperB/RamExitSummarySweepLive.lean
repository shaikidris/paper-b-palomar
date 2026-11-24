module

public import PaperB.RamExitSummarySweepAncestor

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (encodeBackPair encodeBackPair_eq_iff ofOrderedReader)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open PaperB.Exit.OrderedReaderResult
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

/-! The live sweep prefix is closed under parent and jump pointers. -/

def liveBefore {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (rankKahn : Vertex H → Nat)
    (idx u : Nat) : Prop :=
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  u < r.out.tables.next ∧
  (u = 0 ∨ B.F.parentOf u = 0 ∨
    ∃ P : CutPair H, r.out.tables.back[u]? = some (some P) ∧
      max (rankKahn P.fst) (rankKahn P.snd) < idx)

theorem liveBefore_parent_and_jump {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (rankKahn : Vertex H → Nat)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (idx : Nat) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ u, liveBefore flat increasing covers rankArc r rankKahn idx u →
      liveBefore flat increasing covers rankArc r rankKahn idx (B.F.parentOf u) ∧
      liveBefore flat increasing covers rankArc r rankKahn idx (B.F.jumpOf u) := by
  intro B
  have hParClosed : ∀ u, liveBefore flat increasing covers rankArc r rankKahn idx u →
      liveBefore flat increasing covers rankArc r rankKahn idx (B.F.parentOf u) := by
    intro u ⟨huLt, huCase⟩
    have huF : u < B.F.size := by rw [B.G.size_eq]; exact huLt
    have hpLt : B.F.parentOf u < r.out.tables.next := by
      rw [← B.G.size_eq]; exact B.G.layout.valid.parentOf_lt_size huF
    refine ⟨hpLt, ?_⟩
    rcases huCase with rfl | hp0 | ⟨P, hPu, hMax⟩
    · left; exact (validJumpForest_root_zero B.G.layout.valid).1
    · left; rw [hp0]
    · by_cases hpz : B.F.parentOf u = 0
      · left; exact hpz
      · by_cases hppz : B.F.parentOf (B.F.parentOf u) = 0
        · right; left; exact hppz
        · right; right
          have huPos : 0 < u := Nat.pos_of_ne_zero (fun hz => hpz (hz ▸ (validJumpForest_root_zero B.G.layout.valid).1))
          obtain ⟨Pu, Pp, hPu', hPp', hLtTr⟩ :=
            trigger_parent_lt_child flat increasing covers rankArc r rankKahn rankArcKahn huPos huLt (Nat.pos_of_ne_zero hpz)
          rw [hPu] at hPu'
          have hKey : P = Pu := Option.some.inj (Option.some.inj hPu')
          rw [hKey] at hMax
          exact ⟨Pp, hPp', Nat.lt_trans hLtTr hMax⟩
  have hIterClosed : ∀ k u, liveBefore flat increasing covers rankArc r rankKahn idx u →
      liveBefore flat increasing covers rankArc r rankKahn idx (B.F.iterParent k u) := by
    intro k
    induction k with
    | zero => intro u hu; exact hu
    | succ k ih =>
      intro u hu
      exact ih (B.F.parentOf u) (hParClosed u hu)
  intro u hu
  have huF : u < B.F.size := by
    rw [B.G.size_eq]
    exact hu.1
  obtain ⟨k, hk⟩ := B.G.layout.valid.jumpOf_isAncestor huF
  refine ⟨hParClosed u hu, ?_⟩
  rw [← hk]
  exact hIterClosed k u hu

theorem liveBefore_final_iff {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (rankKahn : Vertex H → Nat)
    (hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount)
    (u : Nat) :
    liveBefore flat increasing covers rankArc r rankKahn H.vertexCount u ↔
      u < r.out.tables.next := by
  constructor
  · exact fun h => h.1
  · intro huLt
    refine ⟨huLt, ?_⟩
    by_cases hu0 : u = 0
    · exact Or.inl hu0
    · let B := buildActualSweepBundle H flat increasing covers rankArc r
      by_cases hp0 : B.F.parentOf u = 0
      · exact Or.inr (Or.inl hp0)
      · right; right
        have huF : u < B.F.size := B.G.size_eq.symm ▸ huLt
        let uF : Fin B.F.size := ⟨u, huF⟩
        cases hk : (buildProperLossForest H rank).nodeKey? (B.E.image uF) with
        | some P =>
          exact ⟨P, (B.E.back_eq uF).trans (congrArg some hk),
            Nat.max_lt.mpr ⟨hRkLt P.fst, hRkLt P.snd⟩⟩
        | none =>
          exfalso
          have h0 : 0 < B.F.size := B.G.size_eq.symm ▸ (B_next_pos flat increasing covers rankArc r).1
          have hEq := buildProperLossForest_nodeKey?_inj H rank
            (hk.trans (buildProperLossForest_nodeKey?_root H rank).symm)
          rw [← B.E.root_eq h0] at hEq
          have huEq0 := congrArg Fin.val (B.E.injective hEq)
          change u = 0 at huEq0
          exact hu0 huEq0

theorem parentPath_transport {F : JumpForest} {ref₁ ref₂ : Store} {live : Nat → Prop}
    (hEq : ∀ w, live w → ref₁ w = ref₂ w)
    (hClosed : ∀ w, live w → live (F.parentOf w))
    (hPar1 : ∀ w, live w → (ref₁ w).parent = F.parentOf w)
    {u a : Nat} {m : Map} (hp : ParentPath ref₁ F.depthOf u a m) (hu : live u) :
    ParentPath ref₂ F.depthOf u a m := by
  have hParent : ∀ w, live w → live (ref₁ w).parent := by
    intro w hw
    rw [hPar1 w hw]
    exact hClosed w hw
  exact (parentPath_frame_on_live hParent (fun w hw => (hEq w hw).symm)
    (fun _ _ => rfl) hp hu).1

end PaperB.RamProgram.ExitSummaryBuild
