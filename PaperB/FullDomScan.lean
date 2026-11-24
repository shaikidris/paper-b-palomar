module

public import PaperB.ConcreteDomOps

public import PaperB.DomBuildStep
public import PaperB.DomPredecessorFold
public import PaperB.ReachScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace EX15
namespace WholeScan

open JumpForestCommonAncestor

universe u

variable {α : Type u} {g : Digraph}

private theorem ancestor_append_new {F : JumpForest} (hF : ValidJumpForest F)
    {p a : Nat} (hp : p < F.size) :
    IsAncestor (F.appendLeaf p) a F.size ↔ a = F.size ∨ IsAncestor F a p := by
  have hParent : (F.appendLeaf p).parentOf F.size = p := by
    change ((F.appendLeaf p).recordAt F.size).parent = p
    rw [recordAt_appendLeaf_new F p] <;> rfl
  have hStep (j : Nat) :
      (F.appendLeaf p).iterParent (j + 1) F.size = F.iterParent j p := by
    change (F.appendLeaf p).iterParent j ((F.appendLeaf p).parentOf F.size) =
      F.iterParent j p
    rw [hParent]
    exact (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).iterParent_eq
      hF hp j
  constructor
  · intro ⟨j, hj⟩
    cases j with
    | zero => exact Or.inl hj.symm
    | succ j => exact Or.inr ⟨j, (hStep j).symm.trans hj⟩
  · rintro (ha | ⟨j, hj⟩)
    · exact ⟨0, ha.symm⟩
    · exact ⟨j + 1, (hStep j).trans hj⟩

/-- The executable fold is the packed predecessor fold, not an oracle on forests. -/
def packedJumpOps (α : Type u) (R : JumpWordRegion) :=
  ({ wordFold := JumpForestPredecessorFold.wordFold R
     appendLeafWords := appendLeafWords R
     occurrence := JumpForestPredecessorFold.Step.occurrence
     size := JumpForest.size
     appendLeaf := JumpForest.appendLeaf
     ancestor := IsAncestor
     layout := JumpWordLayout R
     maxNodes := R.maxNodes
     foldExact := by
       intro F mem n L hLay hn hL slot head tail hslots
       change F.numInserted ≤ n at hn
       exact JumpForestPredecessorFold.wordFold_exact hLay hn hL slot head tail hslots
     foldOccurrences := by
       intro mem slot head tail
       exact JumpForestPredecessorFold.wordFold_occurrences R mem slot head tail
     appendExact := by
       intro F mem p hLay hRoom hp
       change F.numInserted < R.maxNodes at hRoom
       have h := appendLeafWords_spec hLay hRoom hp
       exact ⟨h.1, h.2.2.1⟩
     appendSize := by
       intro F mem p hLay hp
       exact JumpForest.size_appendLeaf F p
     ancestorOld := by
       intro F mem p k x hLay hp hx
       exact isAncestor_appendLeaf_old hLay.valid hp hx
     ancestorNew := by
       intro F mem p k hLay hp
       exact ancestor_append_new hLay.valid hp
     ancestorBound := by
       intro F mem k x hLay hx ha
       obtain ⟨j, hj⟩ := ha
       rw [← hj]
       exact hLay.valid.iterParent_lt_size hx j }
    : JumpOps α JumpForest (JumpForestPredecessorFold.Step α) _)

abbrev Active (r : Vertex g) (marked : Vertex g → Bool) (v : Vertex g) : Prop :=
  v ≠ r ∧ marked v = true

def Prefix (r : Vertex g) (marked : Vertex g → Bool)
    (pre : List (Vertex g)) (v : Vertex g) : Prop :=
  v = r ∨ (v ∈ pre ∧ marked v = true)

def insertions (r : Vertex g) (marked : Vertex g → Bool) :
    List (Vertex g) → Nat
  | [] => 0
  | v :: vs => (if Active r marked v then 1 else 0) + insertions r marked vs

def rawRows (r : Vertex g) (marked : Vertex g → Bool)
    (incoming : Vertex g → List α) : List (Vertex g) → Nat
  | [] => 0
  | v :: vs =>
      (if Active r marked v then (incoming v).length else 0) +
        rawRows r marked incoming vs

/-- The actual parent field, decoded through the forward slot map. -/
def Parents (r : Vertex g) (S : Vertex g → Prop)
    (F : JumpForest) (slots : Array Nat) : Prop :=
  ∀ v, S v → v ≠ r →
    ∃ d, S d ∧ readSlot slots d = F.parentOf (readSlot slots v) ∧
      g.IsImmediateDominator r d v

theorem parentSlot_sound {R : JumpWordRegion} {r : Vertex g}
    {S : Vertex g → Prop} {F : JumpForest} {s : ScanState}
    (I : Partial (packedJumpOps α R) r S F s)
    (P : Parents r S F s.slots)
    {v d : Vertex g} (hv : S v) (hvr : v ≠ r) (hd : S d)
    (h : readSlot s.slots d = F.parentOf (readSlot s.slots v)) :
    g.IsImmediateDominator r d v := by
  obtain ⟨e, he, hslot, hi⟩ := P v hv hvr
  have hde := I.injective hd he (h.trans hslot.symm)
  exact hde.symm ▸ hi

private theorem read_put (m : Array Nat) (v x : Vertex g) (k : Nat)
    (hm : m.size = g.vertexCount) :
    readSlot (putSlot m v k hm) x =
      if x = v then k else readSlot m x := by
  have hx : x.val < m.size := by rw [hm]; exact x.isLt
  by_cases h : x = v
  · subst x
    simp [readSlot, putSlot, hx, Array.getElem_set]
  · have h₁ : x.val ≠ v.val := fun e => h (Fin.ext e)
    have h₂ : v.val ≠ x.val := Ne.symm h₁
    simp [readSlot, putSlot, hx, h, h₁, h₂, Array.getElem_set]

private theorem parents_append {R : JumpWordRegion} {r v : Vertex g}
    {S : Vertex g → Prop} {F : JumpForest} {s : ScanState}
    (I : Partial (packedJumpOps α R) r S F s)
    (P : Parents r S F s.slots) (fresh : ¬ S v) {p : Nat}
    (hParent : ∃ d, S d ∧ readSlot s.slots d = p ∧
      g.IsImmediateDominator r d v) :
    Parents r (fun x => S x ∨ x = v) (F.appendLeaf p)
      (putSlot s.slots v s.next I.mapSize) := by
  obtain ⟨d, hd, hdSlot, hdIdom⟩ := hParent
  have hw : p < F.size := by
    rw [← hdSlot]
    exact I.bounded hd
  have hLayout : JumpWordLayout R F s.words := I.layout
  have keep (x : Vertex g) (hx : S x) :
      readSlot (putSlot s.slots v s.next I.mapSize) x = readSlot s.slots x := by
    rw [read_put, if_neg (fun (e : x = v) => fresh (e ▸ hx))]
  have newSlot : readSlot (putSlot s.slots v s.next I.mapSize) v = F.size := by
    rw [read_put, if_pos rfl]
    exact I.nextEq
  have parentNew : (F.appendLeaf p).parentOf F.size = p := by
    change ((F.appendLeaf p).recordAt F.size).parent = p
    rw [recordAt_appendLeaf_new F p] <;> rfl
  have parentOld {k : Nat} (hk : k < F.size) :
      (F.appendLeaf p).parentOf k = F.parentOf k := by
    exact (JumpForest.Extends.step (JumpForest.Extends.refl F) hw).iterParent_eq
      hLayout.valid hk 1
  intro x hx hxr
  rcases hx with hx | hx
  · obtain ⟨e, he, heSlot, heIdom⟩ := P x hx hxr
    refine ⟨e, Or.inl he, ?_, heIdom⟩
    rw [keep e he, keep x hx, parentOld (I.bounded hx)]
    exact heSlot
  · subst x
    refine ⟨d, Or.inl hd, ?_, hdIdom⟩
    rw [keep d hd, newSlot, parentNew]
    exact hdSlot

private theorem step_mapSize (R : JumpWordRegion) (s : ScanState)
    (v : Vertex g) (hm : s.slots.size = g.vertexCount)
    (source : α → Vertex g) (head : α) (tail : List α) :
    (step (packedJumpOps α R) s v hm source head tail).state.slots.size =
      g.vertexCount := by
  change (putSlot s.slots v s.next hm).size = g.vertexCount
  simpa [putSlot] using hm

structure Result where
  state : ScanState
  rowOccurrences : Nat
  foldInputs : Nat
  lcaQueries : Nat
  appendAccesses : Nat

private def Result.charge (out : Result) (raw inputs queries accesses : Nat) : Result :=
  ⟨out.state, raw + out.rowOccurrences, inputs + out.foldInputs,
    queries + out.lcaQueries, accesses + out.appendAccesses⟩

/--
Each active row is filtered once. The seed is a fold input but not an LCA query.
Only the new arrays and scalar counts survive a head; the per-head traces do not.
The counters count occurrences, queries, and append accesses, not the individual
packed accesses inside an LCA query.
-/
def scan (R : JumpWordRegion) (r : Vertex g) (marked : Vertex g → Bool)
    (source : α → Vertex g) (incoming : Vertex g → List α) :
    (todo : List (Vertex g)) → (s : ScanState) →
      s.slots.size = g.vertexCount → Result
  | [], s, _ => ⟨s, 0, 0, 0, 0⟩
  | v :: vs, s, hm =>
      if Active r marked v then
        let raw := (incoming v).length
        match reachableOccurrences s r source (incoming v) with
        | [] =>
            (scan R r marked source incoming vs s hm).charge raw 0 0 0
        | head :: tail =>
            let out := step (packedJumpOps α R) s v hm source head tail
            let inputs := tail.length + 1
            let queries := out.queries.length
            let accesses := out.appendAccesses.length
            (scan R r marked source incoming vs out.state
              (step_mapSize R s v hm source head tail)).charge
                raw inputs queries accesses
      else
        scan R r marked source incoming vs s hm

private theorem split_mem {β : Type u} {x : β} {xs : List β} (hx : x ∈ xs) :
    ∃ pre post, xs = pre ++ (x :: post) := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with e | hy
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨pre, post, h⟩ := ih hy
        exact ⟨y :: pre, post, congrArg (List.cons y) h⟩

private theorem nodup_split {β : Type u} (pre : List β) (x : β)
    (post : List β) (h : (pre ++ (x :: post)).Nodup) :
    x ∉ pre ∧ x ∉ post := by
  induction pre with
  | nil =>
      exact ⟨by simp, (List.nodup_cons.mp h).1⟩
  | cons y pre ih =>
      change (y :: (pre ++ (x :: post))).Nodup at h
      obtain ⟨hy, ht⟩ := List.nodup_cons.mp h
      obtain ⟨hp, hs⟩ := ih ht
      refine ⟨?_, hs⟩
      intro hx
      rcases List.mem_cons.mp hx with e | hx
      · subst y
        exact hy (List.mem_append.mpr (Or.inr (by simp)))
      · exact hp hx

/-- The exact predecessor fact needed by the next reachable, non-root head. -/
theorem predecessor_before_head {order pre post : List (Vertex g)}
    (topo : g.IsTopologicalList order) {u v : Vertex g}
    (hsplit : order = pre ++ (v :: post)) (he : g.HasArc u v) :
    u ∈ pre := by
  have hn := topo.1
  rw [hsplit] at hn
  have hout := (nodup_split pre v post hn).2
  have hu := topo.2.1 u
  rw [hsplit] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hu
  · rcases List.mem_cons.mp hu with e | hu
    · subst u
      exact False.elim (hout (topo.2.2 pre v post hsplit v he))
    · obtain ⟨mid, suffix, hm⟩ := split_mem hu
      have hs : order = (pre ++ (v :: mid)) ++ (u :: suffix) := by
        simp [hsplit, hm, List.append_assoc]
      have hv := topo.2.2 (pre ++ (v :: mid)) u suffix hs v he
      apply False.elim
      apply hout
      rw [hm]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hv)))

private def orderRank (x : Vertex g) : List (Vertex g) → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else orderRank x ys + 1

private theorem orderRank_split (x : Vertex g) (pre post : List (Vertex g))
    (hx : x ∉ pre) : orderRank x (pre ++ (x :: post)) = pre.length := by
  induction pre with
  | nil => simp [orderRank]
  | cons y pre ih =>
      have hxy : x ≠ y := fun e => hx (List.mem_cons.mpr (Or.inl e))
      have hxp : x ∉ pre := fun h => hx (List.mem_cons.mpr (Or.inr h))
      change orderRank x (y :: (pre ++ (x :: post))) = (y :: pre).length
      simp [orderRank, hxy, ih hxp]

private theorem orderRank_progress {order : List (Vertex g)}
    (topo : g.IsTopologicalList order) :
    ∀ u v, g.HasArc u v → orderRank u order < orderRank v order := by
  intro u v he
  obtain ⟨pre, post, hu⟩ := split_mem (topo.2.1 u)
  obtain ⟨mid, suffix, hm⟩ :=
    split_mem (topo.2.2 pre u post hu v he)
  have hv : order = (pre ++ (u :: mid)) ++ (v :: suffix) := by
    simp [hu, hm, List.append_assoc]
  have hnu := topo.1
  have hnv := topo.1
  rw [hu] at hnu
  rw [hv] at hnv
  have hru : orderRank u order = pre.length := by
    rw [hu]
    exact orderRank_split u pre post (nodup_split pre u post hnu).1
  have hrv : orderRank v order = (pre ++ (u :: mid)).length := by
    rw [hv]
    exact orderRank_split v (pre ++ (u :: mid)) suffix
      (nodup_split (pre ++ (u :: mid)) v suffix hnv).1
  rw [hru, hrv, List.length_append, List.length_cons]
  omega

private theorem prefix_snoc {r v x : Vertex g} {marked : Vertex g → Bool}
    (pre : List (Vertex g)) :
    Prefix r marked (pre ++ [v]) x ↔
      Prefix r marked pre x ∨ (x = v ∧ marked v = true) := by
  simp only [Prefix, List.mem_append, List.mem_singleton]
  constructor
  · rintro (hr | ⟨hp, hb⟩)
    · exact Or.inl (Or.inl hr)
    · rcases hp with hp | e
      · exact Or.inl (Or.inr ⟨hp, hb⟩)
      · exact Or.inr ⟨e, e ▸ hb⟩
  · rintro ((hr | ⟨hp, hb⟩) | ⟨e, hb⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨Or.inl hp, hb⟩
    · exact Or.inr ⟨Or.inr e, e.symm ▸ hb⟩

private theorem prefix_add {r v : Vertex g} {marked : Vertex g → Bool}
    (pre : List (Vertex g)) (h : Active r marked v) :
    (fun x => Prefix r marked pre x ∨ x = v) = Prefix r marked (pre ++ [v]) := by
  funext x
  apply propext
  rw [prefix_snoc]
  constructor
  · rintro (hp | e)
    · exact Or.inl hp
    · exact Or.inr ⟨e, h.2⟩
  · rintro (hp | ⟨e, _⟩)
    · exact Or.inl hp
    · exact Or.inr e

private theorem prefix_skip {r v : Vertex g} {marked : Vertex g → Bool}
    (pre : List (Vertex g)) (h : ¬ Active r marked v) :
    Prefix r marked pre = Prefix r marked (pre ++ [v]) := by
  funext x
  apply propext
  rw [prefix_snoc]
  constructor
  · exact Or.inl
  · rintro (hp | ⟨e, hm⟩)
    · exact hp
    · subst x
      by_cases hr : v = r
      · exact Or.inl hr
      · exact False.elim (h ⟨hr, hm⟩)

private theorem filter_length_le {β : Type u} (p : β → Bool) (xs : List β) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases h : p x <;> simp [List.filter, h] <;> omega

set_option maxHeartbeats 1000000 in
/--
Reusable suffix induction. The two capacity bounds include the insertions
still to come, so neither the root nor an unmarked vertex consumes room.
-/
theorem scan_suffix (R : JumpWordRegion) (r : Vertex g)
    (order : List (Vertex g)) (topo : g.IsTopologicalList order)
    (marked : Vertex g → Bool)
    (markOK : ∀ x, marked x = true ↔ g.InitiallyReachable r x)
    (source : α → Vertex g) (incoming : Vertex g → List α)
    (incomingCover : ∀ v u, g.HasArc u v ↔ ∃ a ∈ incoming v, source a = u)
    (selfDom : ∀ x, g.InitiallyReachable r x → g.Dominates r x x)
    {n L : Nat} (hL : n + 2 ≤ 2 ^ L) :
    ∀ (todo pre : List (Vertex g)) {F : JumpForest} {s : ScanState},
      order = pre ++ todo →
      (I : Partial (packedJumpOps α R) r (Prefix r marked pre) F s) →
      Parents r (Prefix r marked pre) F s.slots →
      F.size - 1 + insertions r marked todo ≤ n →
      F.size - 1 + insertions r marked todo ≤ R.maxNodes →
      let out := scan R r marked source incoming todo s I.mapSize
      ∃ G, Partial (packedJumpOps α R) r (Prefix r marked (pre ++ todo)) G out.state ∧
        Parents r (Prefix r marked (pre ++ todo)) G out.state.slots ∧
        out.rowOccurrences = rawRows r marked incoming todo ∧
        out.foldInputs ≤ out.rowOccurrences ∧
        out.lcaQueries + insertions r marked todo = out.foldInputs ∧
        out.appendAccesses = 14 * insertions r marked todo := by
  intro todo
  induction todo with
  | nil =>
      intro pre F s hsplit I P hn hcap
      simp only [List.append_nil, scan, rawRows, insertions, Nat.mul_zero]
      exact ⟨F, I, P, True.intro, Nat.le_refl _, True.intro, True.intro⟩
  | cons v vs ih =>
      intro pre F s hsplit I P hn hcap
      have hjoin : pre ++ (v :: vs) = (pre ++ [v]) ++ vs := by
        simp [List.append_assoc]
      have hsplit' : order = (pre ++ [v]) ++ vs := hsplit.trans hjoin
      by_cases hon : Active r marked v
      · have hv := (markOK v).mp hon.2
        have fresh : ¬ Prefix r marked pre v := by
          have hn' := topo.1
          rw [hsplit] at hn'
          rintro (e | ⟨hm, _⟩)
          · exact hon.1 e
          · exact (nodup_split pre v vs hn').1 hm
        have predSeen :
            ∀ u, g.HasArc u v → g.InitiallyReachable r u → Prefix r marked pre u :=
          fun u he hr =>
            Or.inr ⟨predecessor_before_head topo hsplit he, (markOK u).mpr hr⟩
        obtain ⟨head, tail, hrow, cover⟩ :=
          prepare (packedJumpOps α R) I hv hon.1 predSeen source (incoming v)
            (incomingCover v)
        simp only [insertions, if_pos hon] at hn hcap
        have hn' : F.size - 1 ≤ n := by omega
        have hroom : F.size - 1 < R.maxNodes := by omega
        let out := step (packedJumpOps α R) s v I.mapSize source head tail
        let p := ((packedJumpOps α R).wordFold s.words
          (fun a => readSlot s.slots (source a)) head tail).1
        obtain ⟨I', hp, _, hq, ha⟩ :=
          step_spec (packedJumpOps α R) I (orderRank_progress topo)
            hv fresh (selfDom v hv) predSeen source head tail cover hn' hL hroom
        have P' : Parents r (fun x => Prefix r marked pre x ∨ x = v)
            (F.appendLeaf p) out.state.slots :=
          parents_append I P fresh hp
        have hset := prefix_add pre hon
        rw [hset] at I' P'
        have hsize : (F.appendLeaf p).size = F.size + 1 :=
          JumpForest.size_appendLeaf F p
        have hpos : 0 < F.size := by
          have h := I.bounded I.rootMem
          rw [I.rootSlot] at h
          exact h
        have hnNext : (F.appendLeaf p).size - 1 + insertions r marked vs ≤ n := by
          rw [hsize]
          omega
        have hcapNext :
            (F.appendLeaf p).size - 1 + insertions r marked vs ≤ R.maxNodes := by
          rw [hsize]
          omega
        obtain ⟨G, IG, PG, hraw, hused, hqueries, happend⟩ :=
          ih (pre ++ [v]) hsplit' I' P' hnNext hcapNext
        have hfiltered : tail.length + 1 ≤ (incoming v).length := by
          have h := filter_length_le
            (fun a => decide (source a = r ∨ readSlot s.slots (source a) ≠ 0))
            (incoming v)
          change (reachableOccurrences s r source (incoming v)).length ≤
            (incoming v).length at h
          simpa only [hrow, List.length_cons] using h
        simp only [scan, if_pos hon, hrow, Result.charge, rawRows, insertions, hjoin]
        refine ⟨G, IG, PG, ?_, ?_, ?_, ?_⟩
        · rw [hraw]
        · exact Nat.add_le_add hfiltered hused
        · rw [hq]
          omega
        · rw [ha]
          omega
      · have hset := prefix_skip pre hon
        have I' : Partial (packedJumpOps α R) r (Prefix r marked (pre ++ [v])) F s := by
          rw [← hset]
          exact I
        have P' : Parents r (Prefix r marked (pre ++ [v])) F s.slots := by
          rw [← hset]
          exact P
        simp only [insertions, if_neg hon, Nat.zero_add] at hn hcap
        obtain ⟨G, IG, PG, hraw, hused, hqueries, happend⟩ :=
          ih (pre ++ [v]) hsplit' I' P' hn hcap
        simpa only [scan, if_neg hon, rawRows, insertions, Nat.zero_add, hjoin] using
          (show ∃ G',
              Partial (packedJumpOps α R) r (Prefix r marked ((pre ++ [v]) ++ vs))
                G' (scan R r marked source incoming vs s I'.mapSize).state ∧
              Parents r (Prefix r marked ((pre ++ [v]) ++ vs))
                G' (scan R r marked source incoming vs s I'.mapSize).state.slots ∧
              (scan R r marked source incoming vs s I'.mapSize).rowOccurrences =
                rawRows r marked incoming vs ∧
              (scan R r marked source incoming vs s I'.mapSize).foldInputs ≤
                (scan R r marked source incoming vs s I'.mapSize).rowOccurrences ∧
              (scan R r marked source incoming vs s I'.mapSize).lcaQueries +
                insertions r marked vs =
                (scan R r marked source incoming vs s I'.mapSize).foldInputs ∧
              (scan R r marked source incoming vs s I'.mapSize).appendAccesses =
                14 * insertions r marked vs from
            ⟨G, IG, PG, hraw, hused, hqueries, happend⟩)

def topologicalMark (r : Vertex g) (order : List (Vertex g))
    (topo : g.IsTopologicalList order) (x : Vertex g) : Bool :=
  ((g.scanReachability r order topo).marked[x.val]?).getD false

/--
Run on a full certified order, in particular the order returned by Kahn with
`run_isTopologicalList`. Bind the reachability array once before the scan.
-/
def run (R : JumpWordRegion) (r : Vertex g) (order : List (Vertex g))
    (topo : g.IsTopologicalList order)
    (source : α → Vertex g) (incoming : Vertex g → List α)
    (rootWords : Array Nat) : Result :=
  let marks := (g.scanReachability r order topo).marked
  scan R r (fun x => (marks[x.val]?).getD false) source incoming order
    (initialState g rootWords) (by simp [initialState])

/--
At completion the slot map is exact on all reachable vertices. Every reachable
non-root vertex has its immediate dominator in its packed parent field. The raw
charge is the sum of the active incoming row lengths; the order's `Nodup`
ensures a row is charged at most once, without deduplicating parallel occurrences.
-/
theorem run_spec (R : JumpWordRegion) (r : Vertex g) (order : List (Vertex g))
    (topo : g.IsTopologicalList order)
    (source : α → Vertex g) (incoming : Vertex g → List α)
    (incomingCover : ∀ v u, g.HasArc u v ↔ ∃ a ∈ incoming v, source a = u)
    (selfDom : ∀ x, g.InitiallyReachable r x → g.Dominates r x x)
    {rootF : JumpForest} {rootWords : Array Nat}
    (rootLayout : JumpWordLayout R rootF rootWords)
    (rootSize : rootF.size = 1) (rootAncestor : IsAncestor rootF 0 0)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r)
    {n L : Nat} (hL : n + 2 ≤ 2 ^ L)
    (hn : insertions r (topologicalMark r order topo) order ≤ n)
    (hcap : insertions r (topologicalMark r order topo) order ≤ R.maxNodes) :
    let out := run R r order topo source incoming rootWords
    ∃ F, Partial (packedJumpOps α R) r (g.InitiallyReachable r) F out.state ∧
      Parents r (g.InitiallyReachable r) F out.state.slots ∧
      out.rowOccurrences = rawRows r (topologicalMark r order topo) incoming order ∧
      out.foldInputs ≤ out.rowOccurrences ∧
      out.lcaQueries + insertions r (topologicalMark r order topo) order =
        out.foldInputs ∧
      out.appendAccesses = 14 * insertions r (topologicalMark r order topo) order := by
  let marked := topologicalMark r order topo
  have markOK (x : Vertex g) : marked x = true ↔ g.InitiallyReachable r x :=
    g.scanReachability_iff r order topo x
  have hempty : Prefix r marked [] = (fun x => x = r) := by
    funext x
    simp [Prefix]
  have I₀ : Partial (packedJumpOps α R) r (Prefix r marked []) rootF
      (initialState g rootWords) := by
    rw [hempty]
    exact initialState_partial (packedJumpOps α R) rootLayout rootSize
      rootAncestor rootReach rootDom
  have P₀ : Parents r (Prefix r marked []) rootF (initialState g rootWords).slots := by
    rw [hempty]
    intro v hv hvr
    exact False.elim (hvr hv)
  have hn₀ : rootF.size - 1 + insertions r marked order ≤ n := by
    simpa only [rootSize, Nat.reduceSub, Nat.zero_add] using hn
  have hcap₀ : rootF.size - 1 + insertions r marked order ≤ R.maxNodes := by
    simpa only [rootSize, Nat.reduceSub, Nat.zero_add] using hcap
  obtain ⟨F, IF, PF, hraw, hused, hqueries, happend⟩ :=
    scan_suffix R r order topo marked markOK source incoming incomingCover
      selfDom hL order [] (by simp) I₀ P₀ hn₀ hcap₀
  have hfull : Prefix r marked ([] ++ order) = g.InitiallyReachable r := by
    funext x
    apply propext
    constructor
    · rintro (e | ⟨_, hm⟩)
      · exact e.symm ▸ rootReach
      · exact (markOK x).mp hm
    · intro hx
      exact Or.inr ⟨by simpa using topo.2.1 x, (markOK x).mpr hx⟩
  rw [hfull] at IF PF
  exact ⟨F, IF, PF, hraw, hused, hqueries, happend⟩

end WholeScan
end EX15
end PaperB
