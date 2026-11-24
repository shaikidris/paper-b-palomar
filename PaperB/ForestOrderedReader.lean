module

public import PaperB.ForestActualFull
public import PaperB.ForestPhysicalIntervals
public import PaperB.ForestPhysicalReflection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

structure OrderedReaderResult {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    [DecidableEq (CutPair H)] where
  out : State H
  log : Log H
  index : Index (orderedConfig p large) rank out
  dictionary : Array PaperB.PairLookup.Key
  dictionary_eq : dictionary = (orderedConfig p large).dict
  ran : runOrdered p data size_data rank large = some (out, log)
  trace :
    Trace (orderedConfig p large) rank
      (initial (orderedConfig p large)
        (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount)
      (orderedRows p data size_data) out log
  logHeads : log.map Event.head = (orderedRows p data size_data).map Row.head
  logLength : log.length = (orderedRows p data size_data).length
  logLabels : ∀ e ∈ log, (selectors (orderedConfig p large) out).label e.head = e.node
  contains_true_iff : ∀ (q : CutPair H) (y : Vertex H),
    index.contains q y = true ↔ q.fst < q.snd ∧ H.ProperLoss q y

private theorem orderedReader_iterParent_parentOf (F : JumpForest)
    (k u : Nat) :
    F.iterParent k (F.parentOf u) = F.parentOf (F.iterParent k u) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    change F.iterParent k (F.parentOf (F.parentOf u)) =
      F.parentOf (F.iterParent k (F.parentOf u))
    exact ih (F.parentOf u)

private theorem orderedReader_climb_eq_iterParent (F : JumpForest)
    (k u : Nat) :
    climb F.parentOf k u = F.iterParent k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change F.parentOf (climb F.parentOf k u) =
      F.iterParent k (F.parentOf u)
    exact (congrArg F.parentOf ih).trans
      (orderedReader_iterParent_parentOf F k u).symm

private theorem orderedReader_contains_true_iff {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {out : State H}
    [DecidableEq (CutPair H)] (I : Index c rank out)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v)
    (flat : H.IsFlat) (q : CutPair H) (y : Vertex H) :
    I.contains q y = true ↔ q.fst < q.snd ∧ H.ProperLoss q y := by
  obtain ⟨F, up, G, hUp, E, hRoot, hSurj, hSlot, hLoss⟩ :=
    OutputOK.physicalReflection I.ok rankArc distinctRanks flat
  rw [I.contains_exact G q y, hLoss q y]
  constructor
  · rintro ⟨n, hb, k, hk⟩
    refine ⟨n, (physicalPairSlot?_eq_some_iff G q n).2 hb, k, ?_⟩
    simpa only [orderedReader_climb_eq_iterParent] using hk
  · rintro ⟨n, hs, k, hk⟩
    refine ⟨n, (physicalPairSlot?_eq_some_iff G q n).1 hs, k, ?_⟩
    simpa only [orderedReader_climb_eq_iterParent] using hk

/-- Build the reader from the state and log returned by the actual ordered run. -/
def runOrderedReader {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    OrderedReaderResult p data size_data rank large :=
  let c := orderedConfig p large
  let rows := orderedRows p data size_data
  have total :=
    runOrdered_total p data size_data rank large increasing covers rankArc flat
  have distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v := by
    intro u v huv
    obtain ⟨i, hi⟩ := covers u
    obtain ⟨j, hj⟩ := covers v
    have hr : rank (orderedVertexAt data size_data i) =
        rank (orderedVertexAt data size_data j) := by
      simpa only [hi, hj] using huv
    have hval : i.val = j.val := by
      rcases Nat.lt_trichotomy i.val j.val with hij | hij | hji
      · exact False.elim ((Nat.ne_of_lt (increasing i j hij)) hr)
      · exact hij
      · exact False.elim ((Nat.ne_of_lt (increasing j i hji)) hr.symm)
    have hij : i = j := Fin.ext hval
    exact hi.symm.trans ((congrArg (orderedVertexAt data size_data) hij).trans hj)
  match hRun : fromRoot c rank
      (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount rows with
  | none => False.elim (by
      obtain ⟨out, log, hSome, _⟩ := total
      have hBad : (none : Option (State H × Log H)) = some (out, log) :=
        hRun.symm.trans hSome
      cases hBad)
  | some (out, log) =>
      have cert :
          Trace c rank
            (initial c (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount)
            rows out log ∧
          log.map Event.head = rows.map Row.head ∧
          log.length = rows.length ∧
          (∀ e ∈ log, (selectors c out).label e.head = e.node) ∧
          OutputOK c rank out := by
        obtain ⟨out', log', hSome, hCert⟩ := total
        have hPair : (out, log) = (out', log') :=
          Option.some.inj (hRun.symm.trans hSome)
        have hOut : out = out' := congrArg Prod.fst hPair
        have hLog : log = log' := congrArg Prod.snd hPair
        simpa only [hOut, hLog] using hCert
      let I := PaperB.EX24.FinalDFS.build cert.2.2.2.2
      { out := out
        log := log
        index := I
        dictionary := c.dict
        dictionary_eq := rfl
        ran := hRun
        trace := cert.1
        logHeads := cert.2.1
        logLength := cert.2.2.1
        logLabels := cert.2.2.2.1
        contains_true_iff :=
          orderedReader_contains_true_iff I rankArc distinctRanks flat }

end PaperB
