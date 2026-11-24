module

public import PaperB.ReachScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace Digraph

/-- Count every occurrence of `v`, including repeated parallel arcs. -/
def countOccurrence {n : Nat} (v : Fin n) : List (Fin n) → Nat
  | [] => 0
  | w :: ws => (if w = v then 1 else 0) + countOccurrence v ws

private abbrev ScanState := Array Nat × Nat

private def bump {n : Nat} (a : Array Nat) (w : Fin n) : Array Nat :=
  a.setIfInBounds w.val ((a[w.val]?).getD 0 + 1)

private def step {n : Nat} (s : ScanState) (w : Fin n) : ScanState :=
  (bump s.1 w, s.2 + 1)

private def scanRow {n : Nat} : List (Fin n) → ScanState → ScanState
  | [], s => s
  | w :: ws, s => scanRow ws (step s w)

private def scanRows {n : Nat} : List (List (Fin n)) → ScanState → ScanState
  | [], s => s
  | row :: rows, s => scanRows rows (scanRow row s)

private theorem bump_read {n : Nat} {a : Array Nat} (hs : a.size = n)
    (w v : Fin n) :
    ((bump a w)[v.val]?).getD 0 =
      (a[v.val]?).getD 0 + (if w = v then 1 else 0) := by
  by_cases h : w = v
  · subst w
    have hv : v.val < a.size := by rw [hs]; exact v.isLt
    simp [bump, Array.getElem?_setIfInBounds_self_of_lt hv]
  · have hv : w.val ≠ v.val := fun he => h (Fin.ext he)
    simp [bump, h, hv]

private theorem scanRow_spec {n : Nat} (row : List (Fin n)) (s : ScanState)
    (hs : s.1.size = n) :
    (scanRow row s).1.size = n ∧
    (scanRow row s).2 = s.2 + row.length ∧
    ∀ v : Fin n, ((scanRow row s).1[v.val]?).getD 0 =
      (s.1[v.val]?).getD 0 + countOccurrence v row := by
  induction row generalizing s with
  | nil => simp [scanRow, countOccurrence, hs]
  | cons w ws ih =>
    have hs' : (step s w).1.size = n := by simpa [step, bump] using hs
    obtain ⟨ha, hc, hv⟩ := ih (step s w) hs'
    simp only [scanRow]
    refine ⟨ha, ?_, ?_⟩
    · rw [hc]
      simp only [step, List.length_cons] <;> omega
    · intro v
      rw [hv v]
      change ((bump s.1 w)[v.val]?).getD 0 + countOccurrence v ws = _
      rw [bump_read hs]
      simp only [countOccurrence, Nat.add_assoc]

private theorem scanRows_spec {n : Nat} (rows : List (List (Fin n)))
    (s : ScanState) (hs : s.1.size = n) :
    (scanRows rows s).1.size = n ∧
    (scanRows rows s).2 = s.2 + (rows.map List.length).sum ∧
    ∀ v : Fin n, ((scanRows rows s).1[v.val]?).getD 0 =
      (s.1[v.val]?).getD 0 + (rows.map (countOccurrence v)).sum := by
  induction rows generalizing s with
  | nil => simp [scanRows, hs]
  | cons row rows ih =>
    obtain ⟨hr, hrc, hrv⟩ := scanRow_spec row s hs
    obtain ⟨ha, hc, hv⟩ := ih (scanRow row s) hr
    simp only [scanRows, List.map_cons, List.sum_cons]
    refine ⟨ha, ?_, ?_⟩
    · rw [hc, hrc, Nat.add_assoc]
    · intro v
      rw [hv v, hrv v, Nat.add_assoc]

private def indegreeRows (g : Digraph) : List (List (Fin g.vertexCount)) :=
  List.ofFn g.outArcs

/-- Kahn's first stage: the indegree array and the number of examined arcs. -/
def indegreeScan (g : Digraph) : Array Nat × Nat :=
  scanRows (indegreeRows g) (Array.replicate g.vertexCount 0, 0)

def indegrees (g : Digraph) : Array Nat := (indegreeScan g).1

def indegreeScanCount (g : Digraph) : Nat := (indegreeScan g).2

private theorem indegreeScan_spec (g : Digraph) :
    (indegrees g).size = g.vertexCount ∧
    indegreeScanCount g = ((indegreeRows g).map List.length).sum ∧
    ∀ v : Fin g.vertexCount, ((indegrees g)[v.val]?).getD 0 =
      ((indegreeRows g).map (countOccurrence v)).sum := by
  have h := scanRows_spec (indegreeRows g)
    (Array.replicate g.vertexCount 0, 0) (by simp)
  refine ⟨h.1, ?_, ?_⟩
  · simpa [indegreeScanCount, indegreeScan] using h.2.1
  · intro v
    have hv : v.val < (Array.replicate g.vertexCount (0 : Nat)).size := by
      simp
    simpa [indegrees, indegreeScan, getElem?_pos, hv] using h.2.2 v

@[simp] theorem indegrees_size (g : Digraph) :
    (indegrees g).size = g.vertexCount :=
  (indegreeScan_spec g).1

/-- Reading the computed array gives the sum of the occurrences over all tails. -/
theorem indegrees_getElem (g : Digraph) (v : Fin g.vertexCount) :
    (indegrees g)[v.val]'(by rw [indegrees_size]; exact v.isLt) =
      ((List.ofFn g.outArcs).map (countOccurrence v)).sum := by
  have hv : v.val < (indegrees g).size := by
    rw [indegrees_size]
    exact v.isLt
  simpa [indegreeRows, getElem?_pos, hv] using (indegreeScan_spec g).2.2 v

private theorem indegreeRows_eq (g : Digraph) :
    indegreeRows g = g.adj.toList := by
  apply List.ext_getElem
  · simp [indegreeRows, g.adj_size]
  · intro i hi hj
    simp [indegreeRows, List.getElem_ofFn, Digraph.outArcs]

private theorem lengthFoldl {α : Type} (rows : List (List α)) (k : Nat) :
    rows.foldl (fun acc row => acc + row.length) k =
      k + (rows.map List.length).sum := by
  induction rows generalizing k with
  | nil => simp
  | cons row rows ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Nat.add_assoc]

/-- Each original adjacency-list entry is examined exactly once. -/
theorem indegreeScanCount_eq_arcCount (g : Digraph) :
    indegreeScanCount g = g.arcCount := by
  rw [(indegreeScan_spec g).2.1, indegreeRows_eq]
  unfold Digraph.arcCount
  generalize g.adj.toList = rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    first
    | rfl
    | exact congrArg (fun k : Nat => row.length + k) ih
    | simp [listLengthSum, lengthFoldl, List.foldr] at ih ⊢ <;> omega

theorem arcCount_le_indegreeScanCount (g : Digraph) :
    g.arcCount ≤ indegreeScanCount g :=
  Nat.le_of_eq (indegreeScanCount_eq_arcCount g).symm

theorem indegreeScanCount_le_arcCount (g : Digraph) :
    indegreeScanCount g ≤ g.arcCount :=
  Nat.le_of_eq (indegreeScanCount_eq_arcCount g)

end Digraph
end PaperB
