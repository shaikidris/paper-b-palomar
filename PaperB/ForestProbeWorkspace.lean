module

public import PaperB.ForestScanPrefixSpace
public import PaperB.OracleContract
public import PaperB.Jumps
public import PaperB.ForestNumericSweepSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.ForestHead

/-- A descent in the actual measured prefix search. A suspended caller
retains its one probe result until its selected child returns. -/
inductive SearchAt (p : Nat → Probe) (fuel lo hi : Nat) :
    Nat → Nat → Nat → Nat → Prop where
  | start : SearchAt p fuel lo hi fuel lo hi 0
  | pass {k a b frames : Nat}
      (parent : SearchAt p fuel lo hi (k + 1) a b frames)
      (continues : ¬ b ≤ a + 1) (ok : (p (a + (b - a) / 2)).ok = true) :
      SearchAt p fuel lo hi k (a + (b - a) / 2) b (frames + 1)
  | fail {k a b frames : Nat}
      (parent : SearchAt p fuel lo hi (k + 1) a b frames)
      (continues : ¬ b ≤ a + 1) (ok : (p (a + (b - a) / 2)).ok = false) :
      SearchAt p fuel lo hi k a (a + (b - a) / 2) (frames + 1)

theorem SearchAt.accounting {p : Nat → Probe} {fuel lo hi k a b frames : Nat}
    (cursor : SearchAt p fuel lo hi k a b frames) :
    frames + k = fuel ∧
      frames + (measuredSearch p k a b).comparisons =
        (measuredSearch p fuel lo hi).comparisons := by
  induction cursor with
  | start => simp
  | pass parent continues ok ih =>
    obtain ⟨hFuel, hCalls⟩ := ih
    simp only [measuredSearch, ite_eq_right continues, ok, ite_true, addProbe] at hCalls
    omega
  | fail parent continues ok ih =>
    obtain ⟨hFuel, hCalls⟩ := ih
    simp only [measuredSearch, ite_eq_right continues, ok, Bool.false_eq_true,
      ite_false, addProbe] at hCalls
    omega

theorem SearchAt.frames_le {p : Nat → Probe} {fuel lo hi k a b frames : Nat}
    (cursor : SearchAt p fuel lo hi k a b frames) :
    frames ≤ fuel := by
  have fuelEq := cursor.accounting.1
  omega

open PaperB.LabelledQuotient

/-- The search holds only its ancestor probe results while the current
predecessor scan runs. Every reached scan cursor partitions that one row
between its suspended test frames and its unread suffix. -/
theorem probe_search_cursor_cells {H : LabelledQuotient}
    (S : Selectors H) (xs : List (Vertex H)) (m : Vertex H)
    {k a b searchFrames : Nat}
    (cursor : SearchAt (probe S xs m) (Nat.log2 (S.depth (S.label m) + 1) + 1)
      0 (S.depth (S.label m) + 1) (k + 1) a b searchFrames)
    (depthFits : S.depth (S.label m) + 1 ≤ H.vertexCount + 1)
    {scanFrames : Nat} {todo : List (Vertex H)}
    (scanCursor :
      let d := a + (b - a) / 2
      let u := S.atDepth (S.label m) d
      ShortCircuitSpace.At (fun x => (raw S u (S.key u) x).1) xs todo scanFrames) :
    (searchFrames + 1) + (scanFrames + todo.length) ≤
      OracleContract.L H.vertexCount + xs.length := by
  have fuelEq := cursor.accounting.1
  have hlog : Nat.log2 (S.depth (S.label m) + 1) ≤ Nat.log2 (H.vertexCount + 1) :=
    (Nat.le_log2 (by omega : H.vertexCount + 1 ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le (by omega)) depthFits)
  have hscan := ShortCircuitSpace.at_length scanCursor
  unfold OracleContract.L
  omega

end PaperB.ForestHead

namespace PaperB.Jumps

/-- A prefix of the read-logging jump traversal. The suspended frames each
retain one loaded record trace on a jump, or two on a parent step. -/
inductive ReadCursor (R : JumpWordRegion) (mem : Array Nat)
    (target fuel origin : Nat) (rec : JumpRecord) :
    Nat → Nat → JumpRecord → Nat → Nat → Prop where
  | start : ReadCursor R mem target fuel origin rec fuel origin rec 0 0
  | jump {k w : Nat} {here : JumpRecord} {frames saved : Nat}
      (prev : ReadCursor R mem target fuel origin rec (k + 1) w here frames saved)
      (descend : target < here.depth)
      (fits : target ≤ (readRecordWords R mem here.jump).1.depth) :
      ReadCursor R mem target fuel origin rec k here.jump
        (readRecordWords R mem here.jump).1 (frames + 1) (saved + 3)
  | parent {k w : Nat} {here : JumpRecord} {frames saved : Nat}
      (prev : ReadCursor R mem target fuel origin rec (k + 1) w here frames saved)
      (descend : target < here.depth)
      (fits : ¬ target ≤ (readRecordWords R mem here.jump).1.depth) :
      ReadCursor R mem target fuel origin rec k here.parent
        (readRecordWords R mem here.parent).1 (frames + 1) (saved + 6)

private theorem read_length (R : JumpWordRegion) (mem : Array Nat) (u : Nat) :
    (readRecordWords R mem u).2.length = 3 := rfl

theorem ReadCursor.accounting {R : JumpWordRegion} {mem : Array Nat}
    {target fuel origin k w frames saved : Nat} {rec here : JumpRecord}
    (cursor : ReadCursor R mem target fuel origin rec k w here frames saved) :
    frames + k = fuel ∧ 3 * frames ≤ saved ∧
      saved + (ancestorAtDepthWordsAux R mem k w here target).2.length =
        (ancestorAtDepthWordsAux R mem fuel origin rec target).2.length := by
  induction cursor with
  | start => simp
  | jump prev descend fits ih =>
    obtain ⟨hFuel, hFrames, hReads⟩ := ih
    simp only [ancestorAtDepthWordsAux_succ, ite_eq_left descend, ite_eq_left fits,
      List.length_append, read_length] at hReads
    omega
  | parent prev descend fits ih =>
    obtain ⟨hFuel, hFrames, hReads⟩ := ih
    simp only [ancestorAtDepthWordsAux_succ, ite_eq_left descend, ite_eq_right fits,
      List.length_append, read_length] at hReads
    omega

/-- Each active ancestor-depth cursor is charged for the suspended frames,
their saved trace cells, and the suffix trace. The initial record load is
charged separately by the returned trace of the outer worker. -/
theorem ancestor_read_prefix_cells {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} (layout : JumpWordLayout R F mem) {u n L : Nat}
    (within : u < F.size) (inserted : F.numInserted ≤ n) (budget : n + 2 ≤ 2 ^ L)
    {target k w frames saved : Nat} {here : JumpRecord}
    (cursor : ReadCursor R mem target
      ((readRecordWords R mem u).1.depth - target) u (readRecordWords R mem u).1
      k w here frames saved) :
    frames + saved + (ancestorAtDepthWordsAux R mem k w here target).2.length ≤
      2 * (1 + 3 * (6 * L + 1)) := by
  obtain ⟨_, hFrames, hReads⟩ := cursor.accounting
  have hTotal := (ancestorAtDepthWords_spec layout within inserted budget target).2.2.1
  unfold ancestorAtDepthWords at hTotal
  simp only [List.length_append, read_length] at hTotal
  omega

/-- The membership selector calls the same worker when the candidate
ancestor is shallow enough. Its extra depth read is in the outer log. -/
theorem ancestor_test_prefix_cells {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} (layout : JumpWordLayout R F mem) {u a n L : Nat}
    (within : u < F.size) (ancestorWithin : a < F.size)
    (inserted : F.numInserted ≤ n) (budget : n + 2 ≤ 2 ^ L)
    {k w frames saved : Nat} {here : JumpRecord}
    (shallow : readWord mem (R.depthAddr a) ≤ (readRecordWords R mem u).1.depth)
    (cursor : ReadCursor R mem (readWord mem (R.depthAddr a))
      ((readRecordWords R mem u).1.depth - readWord mem (R.depthAddr a))
      u (readRecordWords R mem u).1 k w here frames saved) :
    frames + saved + (ancestorAtDepthWordsAux R mem k w here
      (readWord mem (R.depthAddr a))).2.length ≤
        2 * (1 + 3 * (6 * L + 1)) := by
  obtain ⟨_, hFrames, hReads⟩ := cursor.accounting
  have hTotal := (decideAncestorWords_spec layout ancestorWithin within inserted budget).2.1
  unfold decideAncestorWords at hTotal
  simp only [ite_eq_left shallow, List.length_cons, List.length_append, read_length] at hTotal
  omega

end PaperB.Jumps

namespace EX24.PreparedSweep

open PaperB PaperB.LabelledQuotient PaperB.ForestHead
open EX24.PreStep Storage

/-- Recover the certified local predicate at the exact nonempty suffix
reached by the executable fold. Both derivations consume the same step. -/
theorem LocalTrace.site_at_visit {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {P : State H → Row H → Prop}
    {s out t : State H} {rows rest : List (Row H)} {row : Row H}
    {log rev acc : Log H} {visited : Nat}
    (trace : LocalTrace c rank P s rows out log)
    (visit : Visit c rank rows s rev (row :: rest) t acc visited) :
    P t row := by
  induction trace generalizing rest t rev acc visited with
  | nil => cases visit
  | cons hs site _ ih =>
    cases visit with
    | here => exact site
    | more hs' tail =>
      have he := Option.some.inj (hs.symm.trans hs')
      cases he
      exact ih tail

private theorem row_cells_le {H : LabelledQuotient} {row : Row H}
    {rows : List (Row H)} (mem : row ∈ rows) : row.tests.length ≤ testCells rows := by
  induction rows with
  | nil => simp at mem
  | cons a xs ih =>
    cases List.mem_cons.mp mem with
    | inl e =>
      subst a
      simp only [testCells]
      omega
    | inr m =>
      have h := ih m
      simp only [testCells]
      omega

/-- Combine the sweep's persistent roots with the current scan, binary
search, and jump worker. The jump term may use either checked read-cursor
bound, and is zero at cursors without a nested jump call. Each unit is
one array/list cell or one fixed-size suspended frame. -/
theorem probe_workspace_at_visit {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out t : State H}
    {rows rest : List (Row H)} {row : Row H}
    {log acc : Log H} {visited : Nat}
    (trace : LocalTrace c rank (AggregateEX24.SiteOK c rank) s rows out log)
    (visit : Visit c rank rows s [] (row :: rest) t acc visited)
    (data : Array (Vertex H))
    (base : checkpointCells c data rows t acc ≤ 10 * H.vertexCount + H.arcCount + 5)
    (entries : testCells rows ≤ H.arcCount)
    (capacity : c.region.maxNodes = H.vertexCount)
    {m : Vertex H} {key : Option (CutPair H)}
    (active : planPrepared rank row.head row.tests = some (m, key))
    {k a b searchFrames scanFrames : Nat} {todo : List (Vertex H)}
    (searchCursor : SearchAt (probe (selectors c t) row.tests m)
      (Nat.log2 ((selectors c t).depth ((selectors c t).label m) + 1) + 1)
      0 ((selectors c t).depth ((selectors c t).label m) + 1) (k + 1) a b searchFrames)
    (scanCursor :
      let d := a + (b - a) / 2
      let u := (selectors c t).atDepth ((selectors c t).label m) d
      ShortCircuitSpace.At
        (fun x => (raw (selectors c t) u ((selectors c t).key u) x).1)
        row.tests todo scanFrames)
    (jumpCells : Nat)
    (jumpBound : jumpCells ≤ 2 * (1 + 3 * (6 * OracleContract.L H.vertexCount + 1))) :
    checkpointCells c data rows t acc + H.vertexCount +
      ((searchFrames + 1) + (scanFrames + todo.length)) + jumpCells ≤
      11 * H.vertexCount + 2 * H.arcCount + 37 * OracleContract.L H.vertexCount + 13 := by
  have site := trace.site_at_visit visit
  obtain ⟨_, ⟨F, grounded⟩, limits⟩ := site
  have hsize := grounded.size_eq
  have hinsert := grounded.layout.inserted_le
  rw [capacity] at hinsert
  change F.size - 1 ≤ H.vertexCount at hinsert
  have hd := limits m key active
  have htest := probe_search_cursor_cells (selectors c t) row.tests m searchCursor (by omega)
    scanCursor
  obtain ⟨done, hr, _, _⟩ := visit.actualPrefix
  have hrow : row ∈ rows := by rw [hr]; simp
  have hmass := row_cells_le hrow
  omega

end EX24.PreparedSweep
