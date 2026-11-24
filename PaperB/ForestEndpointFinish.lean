module

public import PaperB.ForestBuildPackedWords
public import PaperB.StaticDfsLiveSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace StaticGroupedTreeReader

open ForestLayout ForestHeavyPath LabelledQuotient
open PackedStaticLayout (Input InputOK Endpoints)

variable {N : Nat}

/-- Only the child buckets and the two interval columns are needed by
the proper-loss query. This finish skips heavy paths and child searches. -/
def endpointsOnly (x : Input N) : Endpoints N :=
  let g := (groupedChildLists x.root x.parent.read).1
  let s := layout g x.root (2 * N)
  { entry := ⟨s.entries, s.entries_size⟩
    stop := ⟨s.ends, s.ends_size⟩ }

theorem endpointsOnly_eq (x : Input N) :
    endpointsOnly x = (PackedStaticLayout.build x).endpoints := by
  rw [← buildLayout_eq]
  rfl

/-- The exact grouping work and every DFS fuel prefix of the compact finish.
The prefix bound includes the live child fold as well as command boundaries. -/
theorem endpointsOnly_resources (x : Input N)
    (tree : ValidDepthTree x.root x.parent.read x.depth.read) :
    let grouped := groupedChildLists x.root x.parent.read
    let g := grouped.1
    let childMass := childScanLength g
    grouped.2 = ⟨N, ⟨N, N - 1, N - 1, N - 1, N⟩⟩ ∧
      childMass = N - 1 ∧
      (layout g x.root (2 * N)).processed = 2 * N ∧
      (endpointsOnly x).entry.data = (layout g x.root (2 * N)).entries ∧
      (endpointsOnly x).stop.data = (layout g x.root (2 * N)).ends ∧
      ∀ k : Nat, k ≤ 2 * N → LiveCells.PrefixLive g x.root childMass k := by
  intro grouped g childMass
  have hg : g = bucketChildLists x.root x.parent.read :=
    groupedChildLists_eq_bucketChildLists x.root x.parent.read
  have hm : childMass = N - 1 := buildLayout_childScanLength x
  refine ⟨groupedChildLists_work x.root x.parent.read, hm, ?_, rfl, rfl, ?_⟩
  · rw [hg]
    exact (layout_bucketChildren_exact tree).2
  · intro k hk
    exact LiveCells.validTree_prefix tree g hg childMass (hm ▸ Nat.sub_le N 1) k hk

end StaticGroupedTreeReader

namespace ForestPreparedBuild

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.RetainedProperLoss PaperB.ForestSlimIndex
open PaperB.Jumps

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]

private def finishColumns {c : Config H} {rank : Vertex H → Nat}
    (out : State H) (ok : OutputOK c rank out) : Columns H :=
  let e := StaticGroupedTreeReader.endpointsOnly (packedInput ok)
  { dict := c.dict
    slots := out.tables.slots
    back := out.tables.back
    labels := out.labels
    entry := e.entry.data
    stop := e.stop.data }

section Reference

variable {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
variable {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
variable {large : 3 ≤ H.vertexCount}

private theorem finishColumns_eq {c : Config H} (hc : c = orderedConfig p large)
    (r : OrderedReaderResult p data size_data rank large) :
    finishColumns (c := c) r.out (hc.symm ▸ r.index.ok) = ofOrderedReader r := by
  subst c
  unfold finishColumns ofOrderedReader
  rw [StaticGroupedTreeReader.endpointsOnly_eq, ← r.index.reader.layout_exact]

private def compactColumns {c : Config H} {rank : Vertex H → Nat}
    (ans : Option (State H × Log H))
    (ok : ∀ s log, ans = some (s, log) → OutputOK c rank s)
    (ready : ans.isSome = true) : Columns H :=
  match ans with
  | none => False.elim (by simp at ready)
  | some (s, log) => finishColumns s (ok s log rfl)

private theorem compactColumns_eq (r : OrderedReaderResult p data size_data rank large)
    {c : Config H} (hc : c = orderedConfig p large)
    (ans : Option (State H × Log H)) (hrun : ans = some (r.out, r.log))
    (ok : ∀ s log, ans = some (s, log) → OutputOK c rank s)
    (ready : ans.isSome = true) :
    compactColumns ans ok ready = ofOrderedReader r := by
  subst ans
  exact finishColumns_eq hc r

private def packColumns {bits : Nat} (s : Columns H)
    (dict : FlatPairDictionary.Fits bits s) (back : H.vertexCount < 2 ^ bits)
    (labels : ∀ i : Fin s.labels.size, s.labels[i.val]'i.isLt < 2 ^ bits)
    (entry : ∀ i : Fin s.entry.size, s.entry[i.val]'i.isLt < 2 ^ bits)
    (stop : ∀ i : Fin s.stop.size, s.stop[i.val]'i.isLt < 2 ^ bits) : WordColumns bits :=
  { dictionary := FlatPairDictionary.serialize s dict
    back := packBackWords s back
    labels := BoundedScalarArray.pack s.labels _ labels
    entry := BoundedScalarArray.pack s.entry _ entry
    stop := BoundedScalarArray.pack s.stop _ stop }

private theorem packColumns_eq {bits : Nat}
    (r : OrderedReaderResult p data size_data rank large)
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s : Columns H) (he : s = ofOrderedReader r)
    (dict : FlatPairDictionary.Fits bits s) (back : H.vertexCount < 2 ^ bits)
    (labels : ∀ i : Fin s.labels.size, s.labels[i.val]'i.isLt < 2 ^ bits)
    (entry : ∀ i : Fin s.entry.size, s.entry[i.val]'i.isLt < 2 ^ bits)
    (stop : ∀ i : Fin s.stop.size, s.stop[i.val]'i.isLt < 2 ^ bits) :
    packColumns s dict back labels entry stop = packWordColumns r cap := by
  subst s
  rfl

end Reference

section Runner

variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

/-- Build the packed proper-loss image without constructing the full static
tree reader. The reference reader appears only in erased proof terms. -/
def buildWordsCompact : Option (WordColumns (OracleContract.wordBits 5 H.vertexCount 0)) :=
  if large : 3 ≤ H.vertexCount then
    let p := (ForestIncomingPrep.build H (by intro u y; rfl)).tests
    let c := packedOrderedConfig p large
    let ans := fromRoot c rank (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
      (orderedRows p data size_data)
    let r := readerForWords data size_data rank increasing covers rankArc flat large
    have hc : c = orderedConfig p large := packedOrderedConfig_eq p large
    have hrun : ans = some (r.out, r.log) :=
      (runOrderedPacked_eq p data size_data rank large).trans r.ran
    have oks : ∀ s log, ans = some (s, log) → OutputOK c rank s := by
      intro s log hs
      have e : s = r.out := congrArg Prod.fst (Option.some.inj (hs.symm.trans hrun))
      subst s
      exact hc.symm ▸ r.index.ok
    have ready : ans.isSome = true := by simp [hrun]
    let s := compactColumns ans oks ready
    have he : s = ofOrderedReader r := compactColumns_eq r hc ans hrun oks ready
    have cap := local_word_columns_fit H.vertexCount
    have fit : H.vertexCount + 1 < 2 ^ OracleContract.wordBits 5 H.vertexCount 0 := by omega
    some (packColumns s (he.symm ▸ dictionary_fits r cap) (by omega)
      (he.symm ▸ fun i => Nat.lt_of_le_of_lt (label_field_bound r i) fit)
      (he.symm ▸ fun i => Nat.lt_of_le_of_lt (entry_field_bound r i) fit)
      (he.symm ▸ fun i => Nat.lt_of_le_of_lt (stop_field_bound r i) fit))
  else
    none

theorem buildWordsCompact_eq :
    buildWordsCompact data size_data rank increasing covers rankArc flat =
      buildWords data size_data rank increasing covers rankArc flat := by
  by_cases large : 3 ≤ H.vertexCount
  · simp only [buildWordsCompact, buildWords, dite_eq_left large]
    apply congrArg some
    apply packColumns_eq
    apply compactColumns_eq
    · exact packedOrderedConfig_eq _ _
    · exact (runOrderedPacked_eq _ _ _ _ _).trans
        (readerForWords data size_data rank increasing covers rankArc flat large).ran
  · simp only [buildWordsCompact, buildWords, dite_eq_right large]

end Runner

end ForestPreparedBuild

end PaperB
