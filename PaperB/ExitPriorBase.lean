module

public import PaperB.ExitWordArrayQuery
public import PaperB.ExitKernels

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase

open PaperB.Machine (Word)
open PaperB.StoredPacking PaperB.BuiltExit
open PaperB.ExitMap.Retention
open CheckedFold

-- Name the worker's result type without depending on its field names.
-- The dummy call is a type argument, not another runtime fold.
private abbrev resultType {α : Type} (_ : α) : Type := α

private abbrev FoldResult :=
  resultType
    (foldFusedAux (fun _ => 0)
      (fun _ => ⟨0, 0, Map.identity, Map.identity⟩)
      0 0 0 Map.identity 0)

@[inline] def accumulated (r : FoldResult) : Map := by
  cases r <;> assumption

/-- Fused callback. `v` indexes the earlier vertex base; `u` is its
stored owner slot, and `d` is the requested ancestor depth. The caller
supplies these indices. There is no reference route or tail traversal. -/
@[inline] def run {bits : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (tags : TagsFit bits)
    (prior : Array (Option Values)) (v : Fin prior.size)
    (u d : Nat) : Values :=
  let folded := foldStored mem R tags u d
  let seed := (prior[v.val]'(v.isLt)).getD zero
  Map.eval (accumulated folded) seed

section Exact

variable {bits endpoints : Nat} {mem : Array (Word bits)}
  {R : Region bits mem.size} {F : JumpForest}
  {ref : Nat → CheckedFold.Stored}
  {w : Width bits (max R.slots endpoints)}

theorem run_exact_fold (ok : Occupied mem R F ref w)
    {u : Nat} (hu : u < F.size) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) :
    run mem R w.tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d))
        ((prior[v.val]'(v.isLt)).getD zero) := by
  simp only [run, foldStored_exact ok hu d]

/-- `c` charges the packed worker. The first `1` charges its initial
depth lookup; the last `1` charges the single earlier-base array cell.
That cell is not counted as a packed word. The indices are precomputed. -/
theorem run_read_charge (ok : Occupied mem R F ref w)
    (route : StoreOK F ref) {u n : Nat}
    (hu : u < F.size) (hn : F.numInserted ≤ n) (d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R w.tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R w.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3 := by
  obtain ⟨c, hc, hwords⟩ := foldStored_wordReads mem R w.tags u d
  have hsteps := foldStored_steps_le ok route hu hn d
  exact ⟨c, hc, hwords, by omega⟩

open PaperB.BuiltExit PaperB.LabelledQuotient PaperB.ExitSummary

/-- Proof-only bridge. The caller's representation invariant supplies
the base-cell and route-map agreements; neither reader runs in `run`. -/
theorem run_eq_query {H : LabelledQuotient} {m : Nat}
    {W : Model H m} {B : CutPair H} {z : Fin H.vertexCount}
    {P : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    (q : Query W P S B z) (rb : BaseReader P) (rm : MapReader S)
    (ok : Occupied mem R F ref w) {u : Nat} (hu : u < F.size) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size)
    (hbase : (prior[v.val]'(v.isLt)) = rb z q.readOK)
    (hmap : accumulated (foldFused F ref u d) = q.route.actual rm) :
    run mem R w.tags prior v u d = q.run rb rm := by
  simp only [run_exact_fold ok hu d prior v, hbase, hmap, Query.run]

end Exact

end PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
