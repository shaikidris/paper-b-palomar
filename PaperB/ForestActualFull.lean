module

public import PaperB.ForestTopologicalTotal
public import PaperB.JumpRegionInit
public import PaperB.SmallQuotient

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep

open PaperB EX24.PreStep PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps

set_option autoImplicit false

universe u

private theorem memOrderedOfFn {α : Type u} {n : Nat}
    (f : Fin n → α) (x : α) :
    x ∈ List.ofFn f ↔ ∃ i : Fin n, f i = x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨i, hi⟩)
        · exact ⟨0, h.symm⟩
        · exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.cases ?_ ?_ i
        · intro h
          exact Or.inl h.symm
        · intro j h
          exact Or.inr ⟨j, h⟩

private theorem pairwiseOrderedOfFn {α : Type u} {n : Nat}
    (R : α → α → Prop) (f : Fin n → α)
    (increasing : ∀ i j : Fin n, i.val < j.val → R (f i) (f j)) :
    (List.ofFn f).Pairwise R := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ]
      apply List.Pairwise.cons
      · intro x hx
        obtain ⟨j, rfl⟩ := (memOrderedOfFn (fun i : Fin n => f i.succ) x).mp hx
        exact increasing 0 j.succ (Nat.zero_lt_succ j.val)
      · exact ih _ (fun i j hij =>
          increasing i.succ j.succ (Nat.succ_lt_succ hij))

/-- `data` and `size_data` are the projections of the supplied `OrderArray`.
    No new order array is allocated. -/
def orderedVertexAt {H : LabelledQuotient}
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (i : Fin H.vertexCount) : Vertex H :=
  data[i.val]'(by simpa only [size_data] using i.isLt)

private def readOrderedRow {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (i : Fin H.vertexCount) : Row H :=
  let v := orderedVertexAt data size_data i
  { head := v, tests := p.row v }

/-- Materialize the exact rows in the supplied array order. -/
def orderedRows {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount) :
    List (Row H) :=
  List.ofFn (readOrderedRow p data size_data)

theorem orderedRows_full {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v) :
    FullRows p rank (orderedRows p data size_data) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pairwiseOrderedOfFn
      (fun a b : Row H => rank a.head < rank b.head)
      (readOrderedRow p data size_data) increasing
  · intro v
    obtain ⟨i, hi⟩ := covers v
    exact ⟨readOrderedRow p data size_data i,
      (memOrderedOfFn (readOrderedRow p data size_data) _).mpr ⟨i, rfl⟩,
      hi⟩
  · intro row hr
    obtain ⟨i, rfl⟩ :=
      (memOrderedOfFn (readOrderedRow p data size_data) row).mp hr
    rfl
  · simp [orderedRows]

/-- Keep the coordinate order of the cut pair. -/
def orderedPairCode {H : LabelledQuotient} :
    CutPair H → PaperB.PairLookup.Key
  | ⟨a, b, _, _, _⟩ => (a.val, b.val)

private theorem orderedPairCode_inj {H : LabelledQuotient}
    {a b : CutPair H} (h : orderedPairCode a = orderedPairCode b) :
    a = b := by
  rcases a with ⟨a₁, a₂, ha₁, ha₂, ha₁₂⟩
  rcases b with ⟨b₁, b₂, hb₁, hb₂, hb₁₂⟩
  have h₁ : a₁ = b₁ := Fin.ext (congrArg Prod.fst h)
  have h₂ : a₂ = b₂ := Fin.ext (congrArg Prod.snd h)
  subst b₁
  subst b₂
  rfl

/-- This constructor is only for quotients with at least three vertices.
    Quotients of size at most two use the existing small root-only path. -/
def orderedConfig {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) : Config H :=
  let base : Config H :=
    { region := ConcreteInit.region H.vertexCount
      dict := ForestDictionary.dictionary p orderedPairCode
      sorted := (ForestDictionary.dictionary_spec p orderedPairCode).1
      code := orderedPairCode
      code_inj := by
        intro a b h
        exact orderedPairCode_inj h
      vertexIndex := Fin.val
      vertexIndex_inj := by
        intro a b h
        exact Fin.ext h
      zeroKey := SmallQuotient.sentinelDefaultCutPair H large
      -- Both fields are replaced by usePackedWords before the config is used.
      atDepth := fun _ _ _ _ => 0
      ancestor := fun _ _ _ _ => false }
  base.usePackedWords

/-- The executable path is the compact fold on the materialized row list.
    No proof or timing witness is evaluated by this wrapper. -/
def runOrdered {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount) :
    Option (State H × Log H) :=
  fromRoot (orderedConfig p large) rank
    (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    (orderedRows p data size_data)

theorem runOrdered_total {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    ∃ (out : State H) (log : Log H),
      runOrdered p data size_data rank large = some (out, log) ∧
      Trace c rank
        (initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount)
        rows out log ∧
      log.map Event.head = rows.map Row.head ∧
      log.length = rows.length ∧
      (∀ e ∈ log, (selectors c out).label e.head = e.node) ∧
      OutputOK c rank out := by
  let c := orderedConfig p large
  let rows := orderedRows p data size_data
  have full : FullRows p rank rows :=
    orderedRows_full p data size_data rank increasing covers
  have distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b := by
    intro a b hab
    obtain ⟨i, hi⟩ := covers a
    obtain ⟨j, hj⟩ := covers b
    have hij : i.val = j.val := by
      by_cases hlt : i.val < j.val
      · have h := increasing i j hlt
        rw [hi, hj] at h
        omega
      · by_cases hgt : j.val < i.val
        · have h := increasing j i hgt
          rw [hj, hi] at h
          omega
        · omega
    exact hi.symm.trans
      ((congrArg (orderedVertexAt data size_data) (Fin.ext hij)).trans hj)
  have layout : JumpWordLayout c.region JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1 := by
    change JumpWordLayout (ConcreteInit.region H.vertexCount) JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1
    exact?
  have hc : c.usePackedWords = c := by
    rfl
  have parents : ∀ row ∈ rows, ParentAt c rank row := by
    intro row hr s F up g _hup E
    have T : TestSpec row.head row.tests := by
      rw [full.tests_eq row hr]
      exact p.spec row.head
    exact EX24.PreparedSweep.runPrepared_parent_occupied
      (c := c) (s := s) (F := F) (rank := rank) (up := up) (row := row)
      hc E g T rankArc
  exact fromRoot_total p c rank layout hc rfl rfl (fun _ => rfl)
    rankArc distinctRanks flat full parents

end EX24.PreparedSweep
