module

public import PaperB.ExitActualCompactSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

section

variable {H : PaperB.LabelledQuotient}
  {p : PaperB.ForestDictionary.Rows H}
  {data : Array (PaperB.ForestHead.Vertex H)}
  {size_data : data.size = H.vertexCount}
  {rank : PaperB.ForestHead.Vertex H → Nat}
  {large : 3 ≤ H.vertexCount}
  [DecidableEq H.CutPair]
  (r : PaperB.OrderedReaderResult p data size_data rank large)

abbrev actualDriverAddress (i : Fin (exitTransferDrivers r).size) :
    Fin r.out.tables.next :=
  ⟨(exitTransferDrivers r)[i.val].address, exitTransferDrivers_address_lt r i⟩

variable
  (increasing : ∀ (i j : Fin H.vertexCount), (↑i : Nat) < ↑j →
    (actualP r).rank ((actualP r).orderAt i) <
      (actualP r).rank ((actualP r).orderAt j))
  (covers : ∀ (y : PaperB.ForestHead.Vertex H), ∃ j, (actualP r).orderAt j = y)

abbrev actualCompactPlan :=
  (driverPlan r increasing covers).compactSites (actualDriverAddress r)

theorem actualCompactPlan_mapBefore_of_actualSlot
    {F : PaperB.JumpForest}
    {g : _root_.EX24.Grounded (_root_.EX24.PreparedSweep.orderedConfig p large) F
      (_root_.EX24.initial (_root_.EX24.PreparedSweep.orderedConfig p large)
        (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).fst
        H.vertexCount).tables}
    (fullRows : _root_.EX24.PreparedSweep.FullRows p rank
      (_root_.EX24.PreparedSweep.orderedRows p data size_data))
    (chronology : _root_.EX24.PreparedSweep.ChronologicalIndex.Chronology
      (_root_.EX24.PreparedSweep.orderedConfig p large) g r.out r.log)
    (i : Fin (exitTransferDrivers r).size)
    {z : PaperB.ForestHead.Vertex H} {k : Nat}
    (hslot : actualSlot r z = some (actualDriverAddress r i))
    (hz : rank z < k) :
    (actualCompactPlan r increasing covers).mapBefore k i := by
  have hfirst : (driverPlan r increasing covers).firstAt z (actualDriverAddress r i) :=
    (driverPlan_firstAt_iff (r := r) (increasing := increasing) (covers := covers)
      z (actualDriverAddress r i)).mpr
      ((actualSlot_exact (r := r) (g := g) fullRows chronology
        z (actualDriverAddress r i)).mp hslot)
  change ((driverPlan r increasing covers).compactSites
    (actualDriverAddress r)).mapBefore k i
  apply (_root_.EX42.ArraySweep.Plan.compactSites_mapBefore ..).mpr
  exact ⟨z, hz, hfirst.1⟩

end

end PaperB.Exit.OrderedReaderResult
