module

public import PaperB.ForestBuildPackedWords

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PackingVisits

variable {α β : Type}

def tick (x : α) : StateM Nat α := fun visits => (x, visits + 1)

theorem ofFnM_tick {n : Nat} (f : Fin n → α) (visits : Nat) :
    (Array.ofFnM (fun i => tick (f i))).run visits = (Array.ofFn f, visits + n) := by
  induction n generalizing visits with
  | zero => simp [StateT.run, Array.ofFn_zero]; rfl
  | succ n ih =>
    rw [Array.ofFnM_succ, Array.ofFn_succ]
    change (let (xs, c) := (Array.ofFnM (fun i => tick (f i.castSucc))).run visits
      (xs.push (f (Fin.last n)), c + 1)) = _
    rw [ih]
    rfl

theorem list_mapM_tick (xs : List α) (f : α → β) (visits : Nat) :
    (xs.mapM (fun x => tick (f x))).run visits = (xs.map f, visits + xs.length) := by
  induction xs generalizing visits with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    change (let (ys, c) := (xs.mapM (fun y => tick (f y))).run (visits + 1)
      (f x :: ys, c)) = _
    rw [ih]
    simp only [List.map_cons, List.length_cons]
    congr 1
    omega

theorem mapM_tick (xs : Array α) (f : α → β) (visits : Nat) :
    (xs.mapM (fun x => tick (f x))).run visits = (xs.map f, visits + xs.size) := by
  rcases xs with ⟨xs⟩
  rw [List.mapM_toArray]
  change (let (ys, c) := (xs.mapM (fun x => tick (f x))).run visits
    (ys.toArray, c)) = _
  rw [list_mapM_tick]
  simp

theorem ofFn_pass {n : Nat} (f : Fin n → α) :
    ∃ pass : StateM Nat (Array α), ∀ c,
      pass.run c = (Array.ofFn f, c + (Array.ofFn f).size) := by
  exact ⟨Array.ofFnM (fun i => tick (f i)), fun c => by
    rw [ofFnM_tick, Array.size_ofFn]⟩

theorem generated_map_passes {γ : Type} (xs : Array α)
    (f : Fin xs.size → β) (g : α → γ) :
    ∃ first : StateM Nat (Array β), ∃ second : StateM Nat (Array γ), ∀ c,
      first.run c = (Array.ofFn f, c + (Array.ofFn f).size) ∧
      second.run c = (xs.map g, c + (xs.map g).size) := by
  obtain ⟨first, exactFirst⟩ := ofFn_pass f
  exact ⟨first, xs.mapM (fun x => tick (g x)), fun c =>
    ⟨exactFirst c, by rw [mapM_tick, Array.size_map]⟩⟩

end PackingVisits

namespace PaperB.RetainedProperLoss

open _root_.EX24.PreparedSweep PackingVisits
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex

variable {H : LabelledQuotient} {bits : Nat}

private theorem dictionary_pass (s : Columns H) (f : FlatPairDictionary.Fits bits s) :
    ∃ pass : StateM Nat (Array (Fin (2 ^ bits))), ∀ c,
      pass.run c = (FlatPairDictionary.serialize s f, c + (FlatPairDictionary.serialize s f).size) := by
  unfold FlatPairDictionary.serialize
  exact ofFn_pass _

private theorem back_passes (s : Columns H) (h : H.vertexCount < 2 ^ bits) :
    ∃ first second : StateM Nat (Array (Fin (2 ^ bits))), ∀ c,
      first.run c = ((packBackWords s h).tagAndFirst, c + (packBackWords s h).tagAndFirst.size) ∧
      second.run c = ((packBackWords s h).second, c + (packBackWords s h).second.size) := by
  unfold packBackWords PairColumns.left PairColumns.right
  dsimp only
  exact generated_map_passes _ _ _

private theorem scalar_pass (xs : Array Nat) (lim : Nat)
    (fits : ∀ i : Fin xs.size, xs[i.val]'(i.isLt) < lim) :
    ∃ pass : StateM Nat (Array (Fin lim)), ∀ c,
      pass.run c = (BoundedScalarArray.pack xs lim fits, c + (BoundedScalarArray.pack xs lim fits).size) := by
  unfold BoundedScalarArray.pack
  exact ofFn_pass _

variable {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]

/-- A metered replay of the six packing passes charges each generator invocation
or map visit once and returns the same columns as the executable packer. -/
theorem packWordColumns_visits (r : OrderedReaderResult p data size_data rank large)
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) :
    ∃ pass : StateM Nat (WordColumns bits), ∀ c,
      pass.run c = (packWordColumns r cap, c + (packWordColumns r cap).wordCount) := by
  unfold packWordColumns
  dsimp only
  obtain ⟨dict, hDict⟩ := dictionary_pass _ (dictionary_fits r cap)
  obtain ⟨first, second, hBack⟩ :=
    back_passes (bits := bits) (ofOrderedReader r) (by omega)
  have fit : H.vertexCount + 1 < 2 ^ bits := by omega
  obtain ⟨labels, hLabels⟩ := scalar_pass (ofOrderedReader r).labels _
    (fun i => Nat.lt_of_le_of_lt (label_field_bound r i) fit)
  obtain ⟨entry, hEntry⟩ := scalar_pass (ofOrderedReader r).entry _
    (fun i => Nat.lt_of_le_of_lt (entry_field_bound r i) fit)
  obtain ⟨stop, hStop⟩ := scalar_pass (ofOrderedReader r).stop _
    (fun i => Nat.lt_of_le_of_lt (stop_field_bound r i) fit)
  refine ⟨(do
    let d ← dict
    let a ← first
    let b ← second
    let l ← labels
    let e ← entry
    let s ← stop
    pure ⟨d, ⟨a, b⟩, l, e, s⟩), ?_⟩
  intro c
  simp only [StateT.run_bind, hDict, (hBack _).1, (hBack _).2,
    hLabels, hEntry, hStop, StateT.run_pure, WordColumns.wordCount]
  dsimp only [Bind.bind, Pure.pure, Id.instMonad]
  congr 1
  omega

end PaperB.RetainedProperLoss

namespace PaperB.ForestPreparedBuild

open _root_.EX24.PreparedSweep

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

/-- Only word-packing visits are counted here. The preceding reader is supplied
by the same expression as in the executable builder. -/
theorem buildWords_packing_visits :
    let result := buildWords data size_data rank increasing covers rankArc flat
    let visits := (result.map WordColumns.wordCount).getD 0
    visits ≤ 19 * H.vertexCount ∧
    ∃ pass : StateM Nat (Option (WordColumns (OracleContract.wordBits 5 H.vertexCount 0))),
      ∀ c, pass.run c = (result, c + visits) := by
  refine ⟨buildWords_retained data size_data rank increasing covers rankArc flat, ?_⟩
  by_cases large : 3 ≤ H.vertexCount
  · rw [buildWords_of_large data size_data rank increasing covers rankArc flat large]
    obtain ⟨pass, hexact⟩ := packWordColumns_visits
      (readerForWords data size_data rank increasing covers rankArc flat large)
      (local_word_columns_fit H.vertexCount)
    refine ⟨(do return some (← pass)), ?_⟩
    intro c
    change (let (w, n) := pass.run c; (some w, n)) = _
    rw [hexact]
    rfl
  · rw [show buildWords data size_data rank increasing covers rankArc flat = none by
      simp only [buildWords, dite_eq_right large]]
    exact ⟨pure none, fun _ => rfl⟩

end PaperB.ForestPreparedBuild
