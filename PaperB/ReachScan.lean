module

public import PaperB.Graph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Append after the supplied Digraph definitions.
namespace PaperB.Digraph

/-- Every vertex occurs once, and every arc points into the suffix after its tail. -/
def IsTopologicalList (g : Digraph) (order : List (Fin g.vertexCount)) : Prop :=
  order.Nodup ∧
  (∀ u : Fin g.vertexCount, u ∈ order) ∧
  (∀ (pre : List (Fin g.vertexCount)) (u : Fin g.vertexCount)
     (post : List (Fin g.vertexCount)),
    order = pre ++ (u :: post) →
      ∀ v : Fin g.vertexCount, g.HasArc u v → v ∈ post)

structure ReachScanResult where
  marked : Array Bool
  vertexVisits : Nat
  adjacencyOccurrences : Nat
  deriving Repr

/-- Semantic traversal count, not a count of word-RAM operations. -/
def ReachScanResult.probes (r : ReachScanResult) : Nat :=
  r.vertexVisits + r.adjacencyOccurrences

/-- The adjacency budget for the supplied list. This is not computed by the scan. -/
def suppliedAdjacencyLength (g : Digraph) : List (Fin g.vertexCount) → Nat
  | [] => 0
  | u :: us => (g.outArcs u).length + suppliedAdjacencyLength g us

/-- Mark and count each list cell, including repeated heads and already marked heads. -/
private def markReachHeads {n : Nat} (marked : Array Bool) :
    List (Fin n) → Array Bool × Nat
  | [] => (marked, 0)
  | v :: vs =>
      let rest := markReachHeads (marked.setIfInBounds v.val true) vs
      (rest.1, rest.2 + 1)

private def visitReachVertex (g : Digraph) (marked : Array Bool)
    (u : Fin g.vertexCount) : Array Bool × Nat :=
  if (marked[u.val]?).getD false then
    markReachHeads marked (g.outArcs u)
  else
    (marked, 0)

private def scanReachVertices (g : Digraph) (marked : Array Bool) :
    List (Fin g.vertexCount) → ReachScanResult
  | [] => ⟨marked, 0, 0⟩
  | u :: us =>
      let step := visitReachVertex g marked u
      let rest := scanReachVertices g step.1 us
      ⟨rest.marked, rest.vertexVisits + 1,
        step.2 + rest.adjacencyOccurrences⟩

private def seedReachMarks (g : Digraph) (source : Fin g.vertexCount) :
    Array Bool :=
  (Array.replicate g.vertexCount false).setIfInBounds source.val true

/-- Scan an already verified order. The order proof is not used at runtime. -/
def scanReachability (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (_verified : g.IsTopologicalList order) :
    ReachScanResult :=
  scanReachVertices g (seedReachMarks g source) order

private theorem markReachHeads_spec {n : Nat} (heads : List (Fin n))
    (marked : Array Bool) :
    (markReachHeads marked heads).1.size = marked.size ∧
    (markReachHeads marked heads).2 = heads.length := by
  induction heads generalizing marked with
  | nil => exact ⟨rfl, rfl⟩
  | cons v vs ih =>
      rcases ih (marked.setIfInBounds v.val true) with ⟨hs, hc⟩
      constructor
      · simp [markReachHeads, hs]
      · simp only [markReachHeads, List.length_cons, hc]

private theorem visitReachVertex_spec (g : Digraph) (marked : Array Bool)
    (u : Fin g.vertexCount) :
    (visitReachVertex g marked u).1.size = marked.size ∧
    (visitReachVertex g marked u).2 ≤ (g.outArcs u).length := by
  unfold visitReachVertex
  split
  · rcases markReachHeads_spec (g.outArcs u) marked with ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    simpa only [hc] using Nat.le_refl (g.outArcs u).length
  · exact ⟨rfl, Nat.zero_le _⟩

/-- Size and counting invariants hold even for lists that are not topological. -/
private theorem scanReachVertices_spec (g : Digraph)
    (order : List (Fin g.vertexCount)) (marked : Array Bool) :
    (scanReachVertices g marked order).marked.size = marked.size ∧
    (scanReachVertices g marked order).vertexVisits = order.length ∧
    (scanReachVertices g marked order).adjacencyOccurrences ≤
      g.suppliedAdjacencyLength order := by
  induction order generalizing marked with
  | nil => exact ⟨rfl, rfl, Nat.le_refl 0⟩
  | cons u us ih =>
      rcases visitReachVertex_spec g marked u with ⟨hsize, hcount⟩
      rcases ih (visitReachVertex g marked u).1 with ⟨hs, hv, hc⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [scanReachVertices] using hs.trans hsize
      · simp only [scanReachVertices, List.length_cons, hv]
      · simpa only [scanReachVertices, suppliedAdjacencyLength] using
          Nat.add_le_add hcount hc

theorem scanReachability_size (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).marked.size = g.vertexCount := by
  simpa [scanReachability, seedReachMarks] using
    (scanReachVertices_spec g order (seedReachMarks g source)).1

theorem scanReachability_vertexVisits (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).vertexVisits = order.length :=
  (scanReachVertices_spec g order (seedReachMarks g source)).2.1

theorem scanReachability_adjacencyOccurrences_le (g : Digraph)
    (source : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).adjacencyOccurrences ≤
      g.suppliedAdjacencyLength order :=
  (scanReachVertices_spec g order (seedReachMarks g source)).2.2

theorem scanReachability_probes_le (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).probes ≤
      order.length + g.suppliedAdjacencyLength order := by
  unfold ReachScanResult.probes
  rw [scanReachability_vertexVisits]
  exact Nat.add_le_add (Nat.le_refl _)
    (scanReachability_adjacencyOccurrences_le g source order verified)

private theorem markReachHeads_query {n : Nat} (heads : List (Fin n))
    (marked : Array Bool) (hsize : marked.size = n) (u : Fin n) :
    ((markReachHeads marked heads).1[u.val]?).getD false = true ↔
      (marked[u.val]?).getD false = true ∨ u ∈ heads := by
  induction heads generalizing marked with
  | nil =>
      simp [markReachHeads]
  | cons v vs ih =>
      have hv : v.val < marked.size := by
        simpa only [hsize] using v.isLt
      have hs : (marked.setIfInBounds v.val true).size = n := by
        simpa using hsize
      simp only [markReachHeads]
      rw [ih (marked.setIfInBounds v.val true) hs]
      by_cases h : v.val = u.val
      · have he : v = u := Fin.ext h
        subst v
        rw [Array.getElem?_setIfInBounds_self_of_lt hv]
        simp
      · have hne : u ≠ v := fun he => h (congrArg Fin.val he.symm)
        rw [Array.getElem?_setIfInBounds_ne h]
        simp [List.mem_cons, hne]

private theorem seedReachMarks_query (g : Digraph)
    (source u : Fin g.vertexCount) :
    ((seedReachMarks g source)[u.val]?).getD false = true ↔ u = source := by
  unfold seedReachMarks
  have hu : u.val < (Array.replicate g.vertexCount false).size := by
    simp
  by_cases h : source.val = u.val
  · have he : source = u := Fin.ext h
    subst source
    rw [Array.getElem?_setIfInBounds_self_of_lt hu]
    simp
  · have hne : u ≠ source := fun he => h (congrArg Fin.val he.symm)
    rw [Array.getElem?_setIfInBounds_ne h]
    simp [u.isLt, hne]

private theorem visitReachVertex_sound (g : Digraph)
    (source u : Fin g.vertexCount) (marked : Array Bool)
    (hsize : marked.size = g.vertexCount)
    (hsound : ∀ v : Fin g.vertexCount,
      (marked[v.val]?).getD false = true → g.InitiallyReachable source v)
    (v : Fin g.vertexCount)
    (hv : ((visitReachVertex g marked u).1[v.val]?).getD false = true) :
    g.InitiallyReachable source v := by
  unfold visitReachVertex at hv
  split at hv
  · rename_i hu
    rcases (markReachHeads_query (g.outArcs u) marked hsize v).mp hv with
      hmarked | hhead
    · exact hsound v hmarked
    · exact initiallyReachable_extend (hsound u hu) (show g.HasArc u v from hhead)
  · exact hsound v hv

/-- Every scan preserves soundness of its input marks, regardless of order. -/
private theorem scanReachVertices_sound (g : Digraph)
    (source : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (marked : Array Bool) (hsize : marked.size = g.vertexCount)
    (hsound : ∀ v : Fin g.vertexCount,
      (marked[v.val]?).getD false = true → g.InitiallyReachable source v) :
    ∀ v : Fin g.vertexCount,
      ((scanReachVertices g marked order).marked[v.val]?).getD false = true →
        g.InitiallyReachable source v := by
  induction order generalizing marked with
  | nil =>
      simpa only [scanReachVertices] using hsound
  | cons u us ih =>
      have hstepSize : (visitReachVertex g marked u).1.size = g.vertexCount :=
        (visitReachVertex_spec g marked u).1.trans hsize
      simpa only [scanReachVertices] using
        (ih (visitReachVertex g marked u).1 hstepSize
          (visitReachVertex_sound g source u marked hsize hsound))

/-- Every marked vertex is reachable from the original source. -/
theorem scanReachability_sound (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order)
    (u : Fin g.vertexCount)
    (hu : ((g.scanReachability source order verified).marked[u.val]?).getD false =
      true) :
    g.InitiallyReachable source u := by
  have hsize : (seedReachMarks g source).size = g.vertexCount := by
    simp [seedReachMarks]
  have hseed : ∀ v : Fin g.vertexCount,
      ((seedReachMarks g source)[v.val]?).getD false = true →
        g.InitiallyReachable source v := by
    intro v hv
    have he : v = source := (seedReachMarks_query g source v).mp hv
    subst v
    exact initiallyReachable_source g source
  exact scanReachVertices_sound g source order (seedReachMarks g source) hsize
    hseed u (by simpa only [scanReachability] using hu)

private def reachScanMarked {n : Nat} (marked : Array Bool) (u : Fin n) : Prop :=
  (marked[u.val]?).getD false = true

private theorem visitReachVertex_query (g : Digraph) (marked : Array Bool)
    (u : Fin g.vertexCount) (hsize : marked.size = g.vertexCount)
    (v : Fin g.vertexCount) :
    reachScanMarked (visitReachVertex g marked u).1 v ↔
      reachScanMarked marked v ∨ (reachScanMarked marked u ∧ g.HasArc u v) := by
  unfold reachScanMarked visitReachVertex
  split
  · rename_i hu
    refine (markReachHeads_query (g.outArcs u) marked hsize v).trans ?_
    constructor
    · intro hv
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr ⟨hu, hv⟩
    · intro hv
      rcases hv with hv | ⟨_, hv⟩
      · exact Or.inl hv
      · exact Or.inr hv
  · rename_i hu
    constructor
    · exact Or.inl
    · intro hv
      rcases hv with hv | ⟨hmarked, _⟩
      · exact hv
      · exact (hu hmarked).elim

private theorem reachScan_arc_tail_mem_prefix (g : Digraph)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order)
    (pre rest : List (Fin g.vertexCount)) (p u : Fin g.vertexCount)
    (horder : order = pre ++ (u :: rest)) (hpu : g.HasArc p u) :
    p ∈ pre := by
  have hpAll : p ∈ pre ++ (u :: rest) := by
    rw [← horder]
    exact verified.2.1 p
  rcases List.mem_append.mp hpAll with hp | hp
  · exact hp
  · exfalso
    have suffixNodup : ∀ (xs ys : List (Fin g.vertexCount)),
        (xs ++ ys).Nodup → ys.Nodup := by
      intro xs ys
      induction xs with
      | nil =>
          intro h
          exact h
      | cons x xs ih =>
          intro h
          change (x :: (xs ++ ys)).Nodup at h
          exact ih (List.nodup_cons.mp h).2
    have hn : (pre ++ (u :: rest)).Nodup := by
      rw [← horder]
      exact verified.1
    have huNot : u ∉ rest :=
      (List.nodup_cons.mp (suffixNodup pre (u :: rest) hn)).1
    have splitMem : ∀ xs : List (Fin g.vertexCount), p ∈ xs →
        ∃ a b : List (Fin g.vertexCount), xs = a ++ (p :: b) := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih =>
          intro hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst x
            exact ⟨[], xs, rfl⟩
          · rcases ih hx with ⟨a, b, hab⟩
            exact ⟨x :: a, b, congrArg (List.cons x) hab⟩
    rcases splitMem (u :: rest) hp with ⟨a, b, hab⟩
    have hpOrder : order = (pre ++ a) ++ (p :: b) := by
      rw [List.append_assoc, ← hab]
      exact horder
    have huIn : u ∈ b := verified.2.2 (pre ++ a) p b hpOrder u hpu
    apply huNot
    cases a with
    | nil =>
        have he : u :: rest = p :: b := hab
        rw [(List.cons.inj he).2]
        exact huIn
    | cons x xs =>
        have he : u :: rest = x :: (xs ++ (p :: b)) := hab
        rw [(List.cons.inj he).2]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr huIn)))

/-- The source, every processed reachable vertex, and all of their arc heads
remain marked as the scan advances. -/
private theorem scanReachVertices_complete (g : Digraph)
    (source : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (verified : g.IsTopologicalList order)
    (rest pre : List (Fin g.vertexCount)) (marked : Array Bool)
    (horder : order = pre ++ rest) (hsize : marked.size = g.vertexCount)
    (hsource : reachScanMarked marked source)
    (hpre : ∀ p : Fin g.vertexCount, p ∈ pre → g.InitiallyReachable source p →
      reachScanMarked marked p ∧
        (∀ v : Fin g.vertexCount, g.HasArc p v → reachScanMarked marked v)) :
    ∀ v : Fin g.vertexCount, g.InitiallyReachable source v →
      reachScanMarked (scanReachVertices g marked rest).marked v := by
  induction rest generalizing pre marked with
  | nil =>
      intro v hv
      have hmem : v ∈ pre := by
        simpa only [horder, List.append_nil] using (verified.2.1 v)
      simpa only [scanReachVertices] using (hpre v hmem hv).1
  | cons u us ih =>
      have huMarked : g.InitiallyReachable source u → reachScanMarked marked u := by
        intro hu
        have hlast : source = u ∨
            ∃ p : Fin g.vertexCount, g.InitiallyReachable source p ∧ g.HasArc p u := by
          first
          | exact eq_or_exists_last_arc hu
          | exact AvoidPath.eq_or_exists_last_arc hu
        rcases hlast with h | ⟨p, hp, hpu⟩
        · exact h ▸ hsource
        · have hpPre : p ∈ pre :=
            reachScan_arc_tail_mem_prefix g order verified pre us p u horder hpu
          exact (hpre p hpPre hp).2 u hpu
      let next := (visitReachVertex g marked u).1
      have hpreserve : ∀ v : Fin g.vertexCount, reachScanMarked marked v →
          reachScanMarked next v := by
        intro v hv
        exact (visitReachVertex_query g marked u hsize v).mpr (Or.inl hv)
      have hpre' : ∀ p : Fin g.vertexCount, p ∈ pre ++ [u] →
          g.InitiallyReachable source p → reachScanMarked next p ∧
            (∀ v : Fin g.vertexCount, g.HasArc p v → reachScanMarked next v) := by
        intro p hp hreach
        rcases List.mem_append.mp hp with hp | hp
        · rcases hpre p hp hreach with ⟨hmarked, hheads⟩
          exact ⟨hpreserve p hmarked, fun v hv => hpreserve v (hheads v hv)⟩
        · have he : p = u := by simpa using hp
          subst p
          have hm := huMarked hreach
          refine ⟨hpreserve u hm, ?_⟩
          intro v hv
          exact (visitReachVertex_query g marked u hsize v).mpr (Or.inr ⟨hm, hv⟩)
      have horder' : order = (pre ++ [u]) ++ us := by
        rw [List.append_assoc]
        exact horder
      have hsize' : next.size = g.vertexCount :=
        (visitReachVertex_spec g marked u).1.trans hsize
      simpa only [scanReachVertices] using
        (ih (pre ++ [u]) next horder' hsize' (hpreserve source hsource) hpre')

/-- Scanning a topological list marks every vertex reachable from the source. -/
theorem scanReachability_complete (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order)
    (u : Fin g.vertexCount) (hu : g.InitiallyReachable source u) :
    ((g.scanReachability source order verified).marked[u.val]?).getD false = true := by
  have hsize : (seedReachMarks g source).size = g.vertexCount := by
    simp [seedReachMarks]
  have hsource : reachScanMarked (seedReachMarks g source) source :=
    (seedReachMarks_query g source source).mpr rfl
  exact scanReachVertices_complete g source order verified order []
    (seedReachMarks g source) rfl hsize hsource
    (by
      intro p hp
      simp at hp) u hu

/-- The scan marks exactly the vertices reachable from the source. -/
theorem scanReachability_iff (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order)
    (u : Fin g.vertexCount) :
    ((g.scanReachability source order verified).marked[u.val]?).getD false = true ↔
      g.InitiallyReachable source u :=
  ⟨scanReachability_sound g source order verified u,
    scanReachability_complete g source order verified u⟩

end PaperB.Digraph
