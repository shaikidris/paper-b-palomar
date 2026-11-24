module

public import PaperB.TopologicalRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX15

open Digraph

universe u f q a

abbrev Vertex (g : Digraph) := Fin g.vertexCount

/-
The word backend is an explicit import boundary: the graph module above does
not need to import the files containing JumpForest and its word layout.
For the concrete backend, use wordFold_exact, wordFold_occurrences, and
appendLeafWords_spec for the three word-operation laws below. The remaining
laws concern only the forest model, not the graph or its dominators.

In particular, ancestorNew is the leaf law: an ancestor of the fresh slot
is either that slot itself or an old ancestor of its attachment point.
-/
structure JumpOps (α : Type u) (Forest : Type f)
    (QueryStep : Type q) (Access : Type a) where
  wordFold :
    Array Nat → (α → Nat) → α → List α → Nat × List QueryStep
  appendLeafWords : Array Nat → Nat → Array Nat × List Access
  occurrence : QueryStep → α

  size : Forest → Nat
  appendLeaf : Forest → Nat → Forest
  ancestor : Forest → Nat → Nat → Prop
  layout : Forest → Array Nat → Prop
  maxNodes : Nat

  foldExact :
    ∀ {F mem n L}, layout F mem → size F - 1 ≤ n → n + 2 ≤ 2 ^ L →
      ∀ (slot : α → Nat) (head : α) (tail : List α),
        (∀ x ∈ head :: tail, slot x < size F) →
        let w := (wordFold mem slot head tail).1
        w < size F ∧
          (∀ x ∈ head :: tail, ancestor F w (slot x)) ∧
          ∀ k, (∀ x ∈ head :: tail, ancestor F k (slot x)) ↔ ancestor F k w
  foldOccurrences :
    ∀ mem slot head tail, (wordFold mem slot head tail).2.map occurrence = tail
  appendExact :
    ∀ {F mem p}, layout F mem → size F - 1 < maxNodes → p < size F →
      layout (appendLeaf F p) (appendLeafWords mem p).1 ∧
        (appendLeafWords mem p).2.length = 14

  appendSize :
    ∀ {F mem p}, layout F mem → p < size F →
      size (appendLeaf F p) = size F + 1
  ancestorOld :
    ∀ {F mem p k x}, layout F mem → p < size F → x < size F →
      (ancestor (appendLeaf F p) k x ↔ ancestor F k x)
  ancestorNew :
    ∀ {F mem p k}, layout F mem → p < size F →
      (ancestor (appendLeaf F p) k (size F) ↔ k = size F ∨ ancestor F k p)
  ancestorBound :
    ∀ {F mem k x}, layout F mem → x < size F → ancestor F k x → k < size F

structure ScanState where
  slots : Array Nat
  words : Array Nat
  next : Nat

def readSlot {g : Digraph} (m : Array Nat) (x : Vertex g) : Nat :=
  if h : x.val < m.size then m[x.val]'h else 0

def putSlot {g : Digraph} (m : Array Nat) (v : Vertex g) (k : Nat)
    (hm : m.size = g.vertexCount) : Array Nat :=
  m.set v.val k (by rw [hm]; exact v.isLt)

private theorem readSlot_putSlot {g : Digraph} (m : Array Nat)
    (v x : Vertex g) (k : Nat) (hm : m.size = g.vertexCount) :
    readSlot (putSlot m v k hm) x =
      if x = v then k else readSlot m x := by
  have hx : x.val < m.size := by rw [hm]; exact x.isLt
  by_cases h : x = v
  · subst x
    simp [readSlot, putSlot, hx, Array.getElem_set]
  · have h₁ : x.val ≠ v.val := fun e => h (Fin.ext e)
    have h₂ : v.val ≠ x.val := Ne.symm h₁
    simp [readSlot, putSlot, hx, h, h₁, h₂, Array.getElem_set]

variable {α : Type u} {Forest : Type f} {QueryStep : Type q} {Access : Type a}
variable {g : Digraph} {r v : Vertex g}

/--
`S` and `F` are proof data. In particular there is no executable reverse
map: `onto` is used only to name the original vertex at the returned slot.
The slot value zero doubles as the unmapped value, with the root distinguished
by its original vertex number.
-/
structure Partial (J : JumpOps α Forest QueryStep Access) (r : Vertex g)
    (S : Vertex g → Prop) (F : Forest) (s : ScanState) : Prop where
  layout : J.layout F s.words
  mapSize : s.slots.size = g.vertexCount
  nextEq : s.next = J.size F
  rootMem : S r
  rootSlot : readSlot s.slots r = 0
  reachable : ∀ {x}, S x → g.InitiallyReachable r x
  bounded : ∀ {x}, S x → readSlot s.slots x < J.size F
  injective :
    ∀ {x y}, S x → S y → readSlot s.slots x = readSlot s.slots y → x = y
  onto : ∀ k, k < J.size F → ∃ x, S x ∧ readSlot s.slots x = k
  unmapped : ∀ x, ¬ S x → readSlot s.slots x = 0
  semantic :
    ∀ {x}, S x → ∀ d, g.Dominates r d x ↔
      S d ∧ J.ancestor F (readSlot s.slots d) (readSlot s.slots x)

def initialState (g : Digraph) (rootWords : Array Nat) : ScanState :=
  ⟨Array.replicate g.vertexCount 0, rootWords, 1⟩

theorem initialState_partial (J : JumpOps α Forest QueryStep Access)
    {F : Forest} {rootWords : Array Nat}
    (hLayout : J.layout F rootWords) (hSize : J.size F = 1)
    (hAncestor : J.ancestor F 0 0) (hReach : g.InitiallyReachable r r)
    (hDom : ∀ d, g.Dominates r d r ↔ d = r) :
    Partial J r (fun x => x = r) F (initialState g rootWords) := by
  have hz (x : Vertex g) :
      readSlot (initialState g rootWords).slots x = 0 := by
    simp [initialState, readSlot, x.isLt]
  refine
    { layout := hLayout
      mapSize := by simp [initialState]
      nextEq := hSize.symm
      rootMem := rfl
      rootSlot := hz r
      reachable := ?_
      bounded := ?_
      injective := ?_
      onto := ?_
      unmapped := fun x _ => hz x
      semantic := ?_ }
  · intro x hx
    subst x
    exact hReach
  · intro x _
    rw [hz x, hSize]
    exact Nat.zero_lt_succ 0
  · intro x y hx hy _
    exact hx.trans hy.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    exact ⟨r, rfl, (hz r).trans hk0.symm⟩
  · intro x hx d
    subst x
    rw [hDom d, hz d, hz r]
    exact ⟨fun h => ⟨h, hAncestor⟩, And.left⟩

private theorem reachablePredecessor
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    ∃ u, g.HasArc u v ∧ g.InitiallyReachable r u := by
  rcases AvoidPath.eq_or_exists_last_arc hv with he | ⟨u, hpre, huv⟩
  · exact False.elim (hvr he.symm)
  · exact ⟨u, huv, initiallyReachable_of_survivingPath (g := g) hpre⟩

theorem predecessorsInPrefix {rank : Vertex g → Nat} {S : Vertex g → Prop}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hasEarlier : ∀ x, rank x < rank v → g.InitiallyReachable r x → S x) :
    ∀ u, g.HasArc u v → g.InitiallyReachable r u → S u :=
  fun u huv hu => hasEarlier u (progress u v huv) hu

/--
The partial form of `immediateDominator_iff_predecessor_lca`.
Only the ancestry columns of the reachable predecessors and of `d` are
needed. There is no `ParentSpec` for the tree being constructed.
-/
theorem immediateDominator_iff_predecessor_lca_partial
    {rank : Vertex g → Nat} {d : Vertex g}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r)
    (rel : Vertex g → Vertex g → Prop)
    (predSem : ∀ a u, g.HasArc u v → g.InitiallyReachable r u →
      (rel a u ↔ g.Dominates r a u))
    (parentSem : ∀ a, rel a d ↔ g.Dominates r a d) :
    g.IsImmediateDominator r d v ↔
      (∀ u, g.HasArc u v → g.InitiallyReachable r u → rel d u) ∧
        ∀ a, (∀ u, g.HasArc u v → g.InitiallyReachable r u → rel a u) →
          rel a d := by
  have recurrence (b : Vertex g) (hb : b ≠ v) :
      g.Dominates r b v ↔
        ∀ u, g.HasArc u v → g.InitiallyReachable r u → rel b u := by
    constructor
    · intro hd u huv hu
      exact (predSem b u huv hu).mpr
        ((dominates_iff_reachable_predecessors hvr hb).mp hd u huv hu)
    · intro hp
      exact (dominates_iff_reachable_predecessors hvr hb).mpr
        (fun u huv hu => (predSem b u huv hu).mp (hp u huv hu))
  have notCurrent (b : Vertex g)
      (hb : ∀ u, g.HasArc u v → g.InitiallyReachable r u → rel b u) : b ≠ v := by
    obtain ⟨u, huv, hu⟩ := reachablePredecessor hv hvr
    have hlt := progress u v huv
    have hvu : v ≠ u := fun e => (Nat.ne_of_lt hlt) (congrArg rank e.symm)
    intro e
    subst b
    have hback := rank_lt_of_strict_dominator progress hu
      ((predSem v u huv hu).mp (hb u huv hu)) hvu
    exact (Nat.lt_irrefl _) (Nat.lt_trans hlt hback)
  constructor
  · rintro ⟨hdv, hd, hdeep⟩
    exact ⟨(recurrence d hdv).mp hd, fun b hb =>
      (parentSem b).mpr (hdeep b (notCurrent b hb)
        ((recurrence b (notCurrent b hb)).mpr hb))⟩
  · rintro ⟨hd, hdeep⟩
    have hdv := notCurrent d hd
    exact ⟨hdv, (recurrence d hdv).mpr hd,
      fun b hb hdom => (parentSem b).mp (hdeep b ((recurrence b hb).mp hdom))⟩

/-- Stable filtering of original incoming occurrences, not of distinct sources. -/
def reachableOccurrences (s : ScanState) (r : Vertex g)
    (source : α → Vertex g) (incoming : List α) : List α :=
  incoming.filter (fun x => decide (source x = r ∨ readSlot s.slots (source x) ≠ 0))

theorem prepare (J : JumpOps α Forest QueryStep Access)
    {S : Vertex g → Prop} {F : Forest} {s : ScanState}
    (I : Partial J r S F s)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r)
    (predSeen : ∀ u, g.HasArc u v → g.InitiallyReachable r u → S u)
    (source : α → Vertex g) (incoming : List α)
    (incomingCover : ∀ u, g.HasArc u v ↔ ∃ x ∈ incoming, source x = u) :
    ∃ head tail, reachableOccurrences s r source incoming = head :: tail ∧
      ∀ u, (g.HasArc u v ∧ g.InitiallyReachable r u) ↔
        ∃ x ∈ head :: tail, source x = u := by
  have assigned (u : Vertex g) :
      (u = r ∨ readSlot s.slots u ≠ 0) ↔ S u := by
    constructor
    · rintro (e | h)
      · subst u
        exact I.rootMem
      · classical
        by_cases hs : S u
        · exact hs
        · exact False.elim (h (I.unmapped u hs))
    · intro hu
      by_cases e : u = r
      · exact Or.inl e
      · exact Or.inr (fun he => e
          (I.injective hu I.rootMem (he.trans I.rootSlot.symm)))
  have mem (x : α) :
      x ∈ reachableOccurrences s r source incoming ↔ x ∈ incoming ∧ S (source x) := by
    simp [reachableOccurrences, assigned]
  have cover (u : Vertex g) :
      (g.HasArc u v ∧ g.InitiallyReachable r u) ↔
        ∃ x ∈ reachableOccurrences s r source incoming, source x = u := by
    constructor
    · rintro ⟨he, hu⟩
      obtain ⟨x, hx, e⟩ := (incomingCover u).mp he
      refine ⟨x, (mem x).mpr ⟨hx, ?_⟩, e⟩
      rw [e]
      exact predSeen u he hu
    · rintro ⟨x, hx, e⟩
      obtain ⟨hin, hseen⟩ := (mem x).mp hx
      exact ⟨(incomingCover u).mpr ⟨x, hin, e⟩,
        e ▸ I.reachable hseen⟩
  cases he : reachableOccurrences s r source incoming with
  | nil =>
      obtain ⟨u, huv, hu⟩ := reachablePredecessor hv hvr
      obtain ⟨x, hx, _⟩ := (cover u).mp ⟨huv, hu⟩
      simp [he] at hx
  | cons head tail =>
      exact ⟨head, tail, rfl, fun u => by simpa only [he] using cover u⟩

structure StepResult (QueryStep : Type q) (Access : Type a) where
  state : ScanState
  queries : List QueryStep
  appendAccesses : List Access

/--
The executable step. It queries the old word region, appends under the slot
returned by the fold, and writes one original-vertex map entry. The next
slot is a counter; evaluating this function never traverses the ghost forest.
-/
def step (J : JumpOps α Forest QueryStep Access) (s : ScanState)
    (v : Vertex g) (hm : s.slots.size = g.vertexCount)
    (source : α → Vertex g) (head : α) (tail : List α) :
    StepResult QueryStep Access :=
  let folded := J.wordFold s.words (fun x => readSlot s.slots (source x)) head tail
  let appended := J.appendLeafWords s.words folded.1
  ⟨⟨putSlot s.slots v s.next hm, appended.1, s.next + 1⟩, folded.2, appended.2⟩

theorem step_spec (J : JumpOps α Forest QueryStep Access)
    {S : Vertex g → Prop} {F : Forest} {s : ScanState}
    (I : Partial J r S F s)
    {rank : Vertex g → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (fresh : ¬ S v)
    (selfDom : g.Dominates r v v)
    (predSeen : ∀ u, g.HasArc u v → g.InitiallyReachable r u → S u)
    (source : α → Vertex g) (head : α) (tail : List α)
    (cover : ∀ u, (g.HasArc u v ∧ g.InitiallyReachable r u) ↔
      ∃ x ∈ head :: tail, source x = u)
    {n L : Nat} (hn : J.size F - 1 ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (room : J.size F - 1 < J.maxNodes) :
    let out := step J s v I.mapSize source head tail
    let w := (J.wordFold s.words (fun x => readSlot s.slots (source x)) head tail).1
    Partial J r (fun x => S x ∨ x = v) (J.appendLeaf F w) out.state ∧
      (∃ d, S d ∧ readSlot s.slots d = w ∧ g.IsImmediateDominator r d v) ∧
      out.queries.map J.occurrence = tail ∧
      out.queries.length = tail.length ∧ out.appendAccesses.length = 14 := by
  let slot := fun x => readSlot s.slots (source x)
  let w := (J.wordFold s.words slot head tail).1
  let out := step J s v I.mapSize source head tail
  change Partial J r (fun x => S x ∨ x = v) (J.appendLeaf F w) out.state ∧
    (∃ d, S d ∧ readSlot s.slots d = w ∧ g.IsImmediateDominator r d v) ∧
    out.queries.map J.occurrence = tail ∧
    out.queries.length = tail.length ∧ out.appendAccesses.length = 14
  have hvr : v ≠ r := fun e => fresh (e.symm ▸ I.rootMem)
  have slotsOK : ∀ x ∈ head :: tail, slot x < J.size F := by
    intro x hx
    obtain ⟨he, hr⟩ := (cover (source x)).mpr ⟨x, hx, rfl⟩
    exact I.bounded (predSeen (source x) he hr)
  obtain ⟨hw, hAll, hClass⟩ :=
    J.foldExact I.layout hn hL slot head tail slotsOK
  have collect (k : Nat) :
      (∀ u, g.HasArc u v → g.InitiallyReachable r u →
        J.ancestor F k (readSlot s.slots u)) ↔
      (∀ x ∈ head :: tail, J.ancestor F k (slot x)) := by
    constructor
    · intro h x hx
      obtain ⟨he, hr⟩ := (cover (source x)).mpr ⟨x, hx, rfl⟩
      exact h (source x) he hr
    · intro h u he hr
      obtain ⟨x, hx, e⟩ := (cover u).mp ⟨he, hr⟩
      rw [← e]
      exact h x hx
  have classPred (k : Nat) :
      (∀ u, g.HasArc u v → g.InitiallyReachable r u →
        J.ancestor F k (readSlot s.slots u)) ↔ J.ancestor F k w :=
    (collect k).trans (hClass k)
  obtain ⟨d, hd, hdSlot⟩ := I.onto w hw
  let rel := fun b u : Vertex g =>
    S b ∧ J.ancestor F (readSlot s.slots b) (readSlot s.slots u)
  have hi : g.IsImmediateDominator r d v := by
    apply (immediateDominator_iff_predecessor_lca_partial
      (d := d) progress hv hvr rel
      (fun b u he hr => (I.semantic (predSeen u he hr) b).symm)
      (fun b => (I.semantic hd b).symm)).mpr
    constructor
    · intro u he hr
      exact ⟨hd, by rw [hdSlot]; exact (collect w).mpr hAll u he hr⟩
    · intro b hb
      obtain ⟨u, he, hr⟩ := reachablePredecessor hv hvr
      exact ⟨(hb u he hr).1, by
        rw [hdSlot]
        exact (classPred _).mp (fun x hx hxr => (hb x hx hxr).2)⟩
  have proper (b : Vertex g) (hb : b ≠ v) :
      g.Dominates r b v ↔ g.Dominates r b d := by
    constructor
    · exact hi.2.2 b hb
    · intro h
      obtain ⟨hs, ha⟩ := (I.semantic hd b).mp h
      have haw : J.ancestor F (readSlot s.slots b) w := by
        simpa only [hdSlot] using ha
      apply (dominates_iff_reachable_predecessors hvr hb).mpr
      intro u he hr
      exact (I.semantic (predSeen u he hr) b).mpr
        ⟨hs, (classPred _).mpr haw u he hr⟩
  have hAppend := J.appendExact I.layout room hw
  have hSize := J.appendSize I.layout hw
  have hRead (x : Vertex g) :
      readSlot out.state.slots x =
        if x = v then s.next else readSlot s.slots x :=
    readSlot_putSlot s.slots v x s.next I.mapSize
  have hNew : readSlot out.state.slots v = J.size F := by
    rw [hRead, if_pos rfl, I.nextEq]
  have hKeep {x : Vertex g} (hx : x ≠ v) :
      readSlot out.state.slots x = readSlot s.slots x := by
    rw [hRead, if_neg hx]
  have hOld {x : Vertex g} (hx : S x) :
      readSlot out.state.slots x = readSlot s.slots x :=
    hKeep (fun e => fresh (e ▸ hx))
  have hOccurrences : out.queries.map J.occurrence = tail :=
    J.foldOccurrences s.words slot head tail
  refine ⟨?_, ⟨d, hd, hdSlot, hi⟩, hOccurrences, ?_, hAppend.2⟩
  · refine
      { layout := hAppend.1
        mapSize := ?_
        nextEq := ?_
        rootMem := Or.inl I.rootMem
        rootSlot := (hOld I.rootMem).trans I.rootSlot
        reachable := ?_
        bounded := ?_
        injective := ?_
        onto := ?_
        unmapped := ?_
        semantic := ?_ }
    · change (putSlot s.slots v s.next I.mapSize).size = g.vertexCount
      simpa [putSlot] using I.mapSize
    · change s.next + 1 = J.size (J.appendLeaf F w)
      rw [I.nextEq, hSize]
    · intro x hx
      rcases hx with hx | hx
      · exact I.reachable hx
      · subst x
        exact hv
    · intro x hx
      rcases hx with hx | hx
      · rw [hOld hx, hSize]
        exact Nat.lt_trans (I.bounded hx) (Nat.lt_succ_self _)
      · subst x
        rw [hNew, hSize]
        exact Nat.lt_succ_self _
    · intro x y hx hy he
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hOld hx, hOld hy] at he
        exact I.injective hx hy he
      · subst y
        rw [hOld hx, hNew] at he
        exact False.elim ((Nat.ne_of_lt (I.bounded hx)) he)
      · subst x
        rw [hNew, hOld hy] at he
        exact False.elim ((Nat.ne_of_lt (I.bounded hy)) he.symm)
      · exact hx.trans hy.symm
    · refine fun (k : Nat) (hk : k < J.size (J.appendLeaf F w)) => ?_
      rw [hSize] at hk
      by_cases h : k < J.size F
      · obtain ⟨x, hx, e⟩ := I.onto k h
        exact ⟨x, Or.inl hx, (hOld hx).trans e⟩
      · have e : k = J.size F := by omega
        exact ⟨v, Or.inr rfl, hNew.trans e.symm⟩
    · intro x hx
      exact (hKeep (fun e => hx (Or.inr e))).trans
        (I.unmapped x (fun hs => hx (Or.inl hs)))
    · intro x hx b
      rcases hx with hx | hx
      · rw [hOld hx, J.ancestorOld I.layout hw (I.bounded hx)]
        by_cases hb : b = v
        · subst b
          rw [hNew]
          constructor
          · intro h
            exact False.elim (fresh ((I.semantic hx v).mp h).1)
          · intro h
            exact False.elim ((Nat.lt_irrefl _)
              (J.ancestorBound I.layout (I.bounded hx) h.2))
        · rw [hKeep hb, I.semantic hx b]
          simp only [hb, or_false]
      · subst x
        rw [hNew, J.ancestorNew I.layout hw]
        by_cases hb : b = v
        · subst b
          rw [hNew]
          exact ⟨fun _ => ⟨Or.inr rfl, Or.inl rfl⟩, fun _ => selfDom⟩
        · rw [hKeep hb, proper b hb]
          simp only [hb, or_false]
          constructor
          · intro h
            obtain ⟨hs, ha⟩ := (I.semantic hd b).mp h
            exact ⟨hs, Or.inr (by simpa only [hdSlot] using ha)⟩
          · rintro ⟨hs, he | ha⟩
            · exact False.elim ((Nat.ne_of_lt (I.bounded hs)) he)
            · exact (I.semantic hd b).mpr ⟨hs, by simpa only [hdSlot] using ha⟩
  · simpa only [List.length_map] using congrArg List.length hOccurrences

end PaperB.EX15
