module

public import PaperB.ExitPriorBase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase

open PaperB.Machine (Word)
open PaperB.StoredPacking PaperB.BuiltExit
open PaperB.ExitMap.Retention
open CheckedFold
open PaperB.LabelledQuotient PaperB.ExitSummary

structure RouteSlotEdges {H : LabelledQuotient} {m : Nat} (W : Model H m)
    {S : Fin m → Prop} (rm : MapReader S) (slot : CutPair H → Nat)
    (F : JumpForest) (ref : CheckedFold.Store) : Prop where
  parent : ∀ (i : Fin m), S i →
    (ref (slot (W.child i))).parent = slot (W.parent i)
  parentMap : ∀ (i : Fin m) (hi : S i),
    (ref (slot (W.child i))).parentMap = (rm i hi).getD Map.identity
  down : ∀ (i : Fin m), S i →
    F.depthOf (slot (W.parent i)) < F.depthOf (slot (W.child i))

variable {H : LabelledQuotient} {m : Nat} {W : Model H m}
  {S : Fin m → Prop} {z : Fin H.vertexCount} {A B : CutPair H}
  {F : JumpForest} {ref : CheckedFold.Store}

theorem route_parentPath (r : PaperB.BuiltExit.Route W S z B)
    {rm : MapReader S} {slot : CutPair H → Nat}
    (edges : RouteSlotEdges W rm slot F ref) (howner : W.owner z = some A) :
    ParentPath ref F.depthOf (slot A) (slot B) (r.actual rm) := by
  induction r with
  | seed ho =>
    simpa only [PaperB.BuiltExit.Route.actual,
      ← Option.some.inj (howner.symm.trans ho)] using
      (ParentPath.nil (read := ref) (rank := F.depthOf) (slot A))
  | step i hi _ inner ih =>
    have down :
        F.depthOf (ref (slot (W.child i))).parent < F.depthOf (slot (W.child i)) := by
      rw [edges.parent i hi]
      exact edges.down i hi
    have edge : ParentPath ref F.depthOf (slot (W.child i))
        (slot (W.parent i)) ((rm i hi).getD Map.identity) := by
      simpa only [compose_identity, edges.parent i hi, edges.parentMap i hi] using
        (ParentPath.cons (read := ref) (rank := F.depthOf)
          (slot (W.child i)) down (ParentPath.nil _))
    -- append uses compose_assoc to put this edge after the inner route.
    exact ParentPath.append ih edge

theorem parentPath_endpoint_of_depth {u a : Nat} {p : Map}
    (ha : ParentPath ref F.depthOf u a p) :
    ∀ {b : Nat} {q : Map}, ParentPath ref F.depthOf u b q →
      F.depthOf a = F.depthOf b → a = b := by
  induction ha with
  | nil u =>
    intro b q hb hd
    cases hb with
    | nil => rfl
    | cons =>
      rename_i down tail
      have hle := ParentPath.rank_le tail
      omega
  | @cons u a p down tail ih =>
    intro b q hb hd
    cases hb with
    | nil =>
      have hle := ParentPath.rank_le tail
      omega
    | cons =>
      rename_i tail'
      exact ih tail' hd

theorem accumulated_foldFused_of_path (ok : StoreOK F ref)
    {u a d : Nat} {p : Map} (hp : ParentPath ref F.depthOf u a p)
    (hd : F.depthOf (F.ancestorAtDepth u d) = F.depthOf a) :
    accumulated (foldFused F ref u d) = p := by
  have hstop := parentPath_endpoint_of_depth (foldTrace_spec ok u d).2.1 hp hd
  have hp' : ParentPath ref F.depthOf u (F.ancestorAtDepth u d) p := by
    rw [hstop]
    exact hp
  rw [foldFused_eq_foldTrace ok u d, ← (foldTrace_exact ok (d := d) hp').2]
  cases foldTrace F ref u d <;> rfl

theorem run_eq_query_of_route
    {bits endpoints : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {w : Width bits (max R.slots endpoints)}
    {P : Fin H.vertexCount → Prop}
    (q : Query W P S B z) (rb : BaseReader P) (rm : MapReader S)
    (slot : CutPair H → Nat) (howner : W.owner z = some A)
    (edges : RouteSlotEdges W rm slot F ref)
    (ok : Occupied mem R F ref w) (storeOK : StoreOK F ref)
    (hu : slot A < F.size) (d : Nat)
    (hdepth : F.depthOf (F.ancestorAtDepth (slot A) d) = d)
    (hend : F.depthOf (slot B) = d)
    (prior : Array (Option Values)) (v : Fin prior.size)
    (hbase : (prior[v.val]'(v.isLt)) = rb z q.readOK) :
    run mem R w.tags prior v (slot A) d = q.run rb rm := by
  exact run_eq_query q rb rm ok hu d prior v hbase
    (accumulated_foldFused_of_path storeOK (d := d)
      (route_parentPath q.route edges howner) (hdepth.trans hend.symm))

end PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
