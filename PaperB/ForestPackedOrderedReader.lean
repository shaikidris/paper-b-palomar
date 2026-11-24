module

-- Save the supplied reader and packed-dictionary units under these module names.
public import PaperB.ForestOrderedReader
public import PaperB.ForestPackedOrderedSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

private def PackedReaderBuilt {H : LabelledQuotient}
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount} [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large) : Prop :=
  r.index = PaperB.EX24.FinalDFS.build r.index.ok

private structure PackedReaderCertificate {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) [DecidableEq (CutPair H)]
    (out : State H) (log : Log H) : Prop where
  ok : OutputOK (orderedConfig p large) rank out
  trace : Trace (orderedConfig p large) rank
    (initial (orderedConfig p large)
      (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount)
    (orderedRows p data size_data) out log
  logHeads : log.map Event.head = (orderedRows p data size_data).map Row.head
  logLength : log.length = (orderedRows p data size_data).length
  logLabels : ∀ e ∈ log, (selectors (orderedConfig p large) out).label e.head = e.node
  containsBuilt : ∀ (h : OutputOK (orderedConfig p large) rank out)
    (q : CutPair H) (y : Vertex H),
    (PaperB.EX24.FinalDFS.build h).contains q y = true ↔
      q.fst < q.snd ∧ H.ProperLoss q y

private theorem packedReaderCertificate {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (ans : Option (State H × Log H))
    (hAns : ans = runOrdered p data size_data rank large) :
    match ans with
    | none => False
    | some (out, log) => PackedReaderCertificate p data size_data rank large out log := by
  let old := runOrderedReader p data size_data rank large increasing covers rankArc flat
  cases ans with
  | none =>
      have bad : (none : Option (State H × Log H)) = some (old.out, old.log) :=
        hAns.trans old.ran
      cases bad
  | some pair =>
      have hp : pair = (old.out, old.log) :=
        Option.some.inj (hAns.trans old.ran)
      subst pair
      have hb : PackedReaderBuilt old := by
        dsimp only [old]
        unfold runOrderedReader
        dsimp only
        split
        · have hn : runOrdered p data size_data rank large = none := by assumption
          have bad := hn.symm.trans old.ran
          cases bad
        · unfold PackedReaderBuilt
          rfl
      have hi : old.index = PaperB.EX24.FinalDFS.build old.index.ok := hb
      refine ⟨old.index.ok, old.trace, old.logHeads, old.logLength, old.logLabels, ?_⟩
      intro h q y
      have he : PaperB.EX24.FinalDFS.build h = old.index := hi.symm
      rw [he]
      exact old.contains_true_iff q y

private theorem castFinalBuild {H : LabelledQuotient} {c d : Config H}
    {rank : Vertex H → Nat} {out : State H} (e : c = d)
    (hc : OutputOK c rank out) (hd : OutputOK d rank out) :
    cast (congrArg (fun k => Index k rank out) e)
      (PaperB.EX24.FinalDFS.build hc) = PaperB.EX24.FinalDFS.build hd := by
  cases e
  rfl

/-- Run with one packed config and finish with the supplied constructor. -/
def runOrderedReaderPacked {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (finish : ∀ {c : Config H} {out : State H}, OutputOK c rank out → Index c rank out)
    (finish_eq : ∀ {c : Config H} {out : State H} (h : OutputOK c rank out),
      finish h = PaperB.EX24.FinalDFS.build h) :
    OrderedReaderResult p data size_data rank large :=
  let c := packedOrderedConfig p large
  let root := (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
  let rows := orderedRows p data size_data
  let ans := fromRoot c rank root H.vertexCount rows
  have hc : c = orderedConfig p large := packedOrderedConfig_eq p large
  have hAns : ans = runOrdered p data size_data rank large :=
    congrArg (fun k => fromRoot k rank root H.vertexCount rows) hc
  match hRun : ans with
  | none =>
      False.elim (packedReaderCertificate p data size_data rank large
        increasing covers rankArc flat none hAns)
  | some (out, log) =>
      have ran := hAns.symm
      have cert : PackedReaderCertificate p data size_data rank large out log :=
        packedReaderCertificate p data size_data rank large
          increasing covers rankArc flat (some (out, log)) ran.symm
      have ok : OutputOK c rank out :=
        cast (congrArg (fun k => OutputOK k rank out) hc.symm) cert.ok
      let transport : Index c rank out → Index (orderedConfig p large) rank out :=
        cast (congrArg (fun k => Index k rank out) hc)
      let I := transport (finish ok)
      have hI : I = PaperB.EX24.FinalDFS.build cert.ok :=
        (congrArg transport (finish_eq ok)).trans (castFinalBuild hc ok cert.ok)
      { out := out
        log := log
        index := I
        dictionary := c.dict
        dictionary_eq := congrArg Config.dict hc
        ran := ran
        trace := cert.trace
        logHeads := cert.logHeads
        logLength := cert.logLength
        logLabels := cert.logLabels
        contains_true_iff := fun q y => by
          rw [hI]
          exact cert.containsBuilt cert.ok q y }

end PaperB
