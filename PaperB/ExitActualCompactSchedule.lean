module

public import PaperB.ExitCompactDriverIndex
public import PaperB.ExitCompactSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

def actualCompactArraySchedule
    {H : PaperB.LabelledQuotient}
    {p : PaperB.ForestDictionary.Rows H}
    {data : Array (PaperB.ForestHead.Vertex H)}
    {size_data : data.size = H.vertexCount}
    {rank : PaperB.ForestHead.Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    [inst : DecidableEq H.CutPair]
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (increasing : ∀ (i j : Fin H.vertexCount),
      (↑i : Nat) < ↑j →
        (actualP r).rank ((actualP r).orderAt i) <
          (actualP r).rank ((actualP r).orderAt j))
    (covers : ∀ (y : PaperB.ForestHead.Vertex H),
      ∃ j, (actualP r).orderAt j = y)
    {F : PaperB.JumpForest}
    {g : _root_.EX24.Grounded (_root_.EX24.PreparedSweep.orderedConfig p large) F
      (_root_.EX24.initial (_root_.EX24.PreparedSweep.orderedConfig p large)
        (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).fst
        H.vertexCount).tables}
    (fullRows : _root_.EX24.PreparedSweep.FullRows p rank
      (_root_.EX24.PreparedSweep.orderedRows p data size_data))
    (chronology : _root_.EX24.PreparedSweep.ChronologicalIndex.Chronology
      (_root_.EX24.PreparedSweep.orderedConfig p large) g r.out r.log) :
    EX42.ArraySweep.Schedule ((driverPlan r increasing covers).compactSites
      (fun j : Fin (exitTransferDrivers r).size =>
        ⟨(exitTransferDrivers r)[j.val].address, exitTransferDrivers_address_lt r j⟩)) :=
  let drivers := exitTransferDrivers r
  let h : PaperB.ExitSlotIndex.InRange r.out.tables.next
      drivers (fun d => d.address) :=
    fun j => exitTransferDrivers_address_lt r j
  let addr : Fin drivers.size → Fin r.out.tables.next :=
    fun j => ⟨drivers[j.val].address, exitTransferDrivers_address_lt r j⟩
  let inv : EX42.ArraySweep.Slots (Fin drivers.size) r.out.tables.next :=
    ⟨PaperB.ExitSlotIndex.build r.out.tables.next drivers
        (fun d => d.address) h,
      PaperB.ExitSlotIndex.size_build h⟩
  have hinj : Function.Injective
      (PaperB.ExitSlotIndex.addressAt drivers (fun d => d.address)) := by
    intro i j hij
    exact exitTransferDrivers_address_injective r (g := g)
      increasing covers fullRows chronology hij
  have roundTrip : ∀ (s : Fin r.out.tables.next) (j : Fin drivers.size),
      inv.read s = some j ↔ addr j = s := by
    intro s j
    have hread : inv.read s = some j ↔
        PaperB.ExitSlotIndex.addressAt drivers (fun d => d.address) j = s.val :=
      PaperB.ExitSlotIndex.lookup_build_eq_some_iff (h := h) hinj s j
    exact hread.trans ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
  EX42.ArraySweep.Schedule.compactSites
    (actualArraySchedule r increasing covers (g := g) fullRows chronology)
    addr inv roundTrip

end PaperB.Exit.OrderedReaderResult
