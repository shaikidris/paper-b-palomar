module

public import PaperB.BothReachableRoute

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.EX44

open PaperB
open PaperB.Digraph
open PaperB.Digraph.EX44
open PaperB.LabelledQuotient

noncomputable section

variable {g : PaperB.Digraph} {n k B E : Nat}
variable {R : Runtime g.vertexCount n k B E} {W : World g n}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

variable (progress : ∀ i j, g.HasArc i j → rank i < rank j)
variable (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
variable (spec : ParentSpec g (W.vertex R.source) parent)

private abbrev ThirdVertex
    (R : Runtime g.vertexCount n k B E) (W : World g n) (d : Fin n) :=
  SiblingVertex g (W.vertex R.source) (W.vertex d)

private abbrev thirdQ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)) :=
  finiteSiblingQuotient progress injRank spec hd

private abbrev thirdIndex (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (Z : ThirdVertex R W d) :
    Fin (thirdQ (R := R) (W := W) progress injRank spec d hd).vertexCount :=
  encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) parent
    ((siblingBlockSystem progress injRank spec hd).block Z)

private def ThirdChild
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (d x u : Fin n) (Z : ThirdVertex R W d) : Prop :=
  Z.val = W.vertex x ∧ (R.fetch (.child d x)).value = some u

private def ThirdEnds {Q : LabelledQuotient}
    (J : CutPair Q) (s t : Fin Q.vertexCount) : Prop :=
  (J.fst = s ∧ J.snd = t) ∨ (J.fst = t ∧ J.snd = s)

private def ThirdMapped (W : World g n)
    (xs : List (Fin g.vertexCount)) (x : Fin n) : Prop :=
  W.vertex x ∈ xs

/-- Mathematical inputs to the canonical forest, not table contracts. -/
structure ThirdForestGeometry
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g (W.vertex R.source) parent) where
  qRank : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)),
    Fin (thirdQ progress injRank spec d hd).vertexCount → Nat
  rankArc : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (i j : Fin (thirdQ progress injRank spec d hd).vertexCount),
    (thirdQ progress injRank spec d hd).HasQuotientArc i j →
      qRank d hd i < qRank d hd j
  rankInj : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (i j : Fin (thirdQ progress injRank spec d hd).vertexCount),
    qRank d hd i = qRank d hd j → i = j
  flat : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)),
    (thirdQ progress injRank spec d hd).IsFlat
  rooted : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (i : Fin (thirdQ progress injRank spec d hd).vertexCount),
    let Q := thirdQ progress injRank spec d hd
    AvoidPath Q.HasQuotientArc (fun _ => False) Q.root i

private abbrev thirdForest
    (G : ThirdForestGeometry R W progress injRank spec) (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)) :=
  buildProperLossForest (thirdQ progress injRank spec d hd) (G.qRank d hd)

/-- A physical key decodes to a node of the canonical forest. Storage order
is the node's cut order; the hit specifies how to put it in query order.
The extrema law names the exact paper exit lists, allowing either naming
of the same two cut endpoints. It says nothing about the answer bit. -/
structure ThirdForestTables
    (G : ThirdForestGeometry R W progress injRank spec) where
  decode : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)),
    Fin k → Option (Fin ((thirdForest progress injRank spec G d hd).realNodeCount + 1))
  dictionary : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (a b u v : Fin n) (U V : ThirdVertex R W d)
    (K : CutPair (thirdQ progress injRank spec d hd)),
    ThirdChild R W d a u U → ThirdChild R W d b v V →
    K.fst < K.snd →
    ThirdEnds K (thirdIndex progress injRank spec d hd U)
      (thirdIndex progress injRank spec d hd V) →
    let H := thirdForest progress injRank spec G d hd
    match (R.pairKey d u v).value with
    | none => ∀ i, H.nodeKey? i ≠ some K
    | some hit =>
      ∃ i, decode d hd hit.key = some i ∧ H.nodeKey? i = some K ∧
        ∀ s : Span n × Span n,
          hit.orientation.order s =
            if thirdIndex progress injRank spec d hd U = K.fst then s
            else (s.2, s.1)
  member : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (key : Fin k) (x y : Fin n) (Z : ThirdVertex R W d)
    (i : Fin ((thirdForest progress injRank spec G d hd).realNodeCount + 1)),
    decode d hd key = some i → ThirdChild R W d x y Z →
    let H := thirdForest progress injRank spec G d hd
    (R.pairMember key y).value = true ↔
      IsForestAncestor H.parent i
        (H.label (thirdIndex progress injRank spec d hd Z))
  extrema : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (key : Fin k) (x y : Fin n) (Z : ThirdVertex R W d)
    (i : Fin ((thirdForest progress injRank spec G d hd).realNodeCount + 1))
    (K J : CutPair (thirdQ progress injRank spec d hd)),
    decode d hd key = some i →
    (thirdForest progress injRank spec G d hd).nodeKey? i = some K →
    ThirdEnds K J.fst J.snd →
    ThirdChild R W d x y Z → (R.pairMember key y).value = true →
    let Q := thirdQ progress injRank spec d hd
    let z := thirdIndex progress injRank spec d hd Z
    let s := (R.exitExtrema key y).value
    SpanExact W.entry (ThirdMapped W (lemma22ExitTails Q J K.fst z)) s.1 ∧
    SpanExact W.entry (ThirdMapped W (lemma22ExitTails Q J K.snd z)) s.2

/-- The last-exit witness names two endpoints. Only the ascending
representative can be used with the canonical forest's existence theorem. -/
private theorem thirdAscending {Q : LabelledQuotient} (J : CutPair Q) :
    ∃ K : CutPair Q, K.fst < K.snd ∧ ThirdEnds K J.fst J.snd := by
  classical
  by_cases h : J.fst < J.snd
  · exact ⟨J, h, Or.inl ⟨rfl, rfl⟩⟩
  · have hn : J.fst ≠ J.snd := by
      first
      | exact J.ne
      | exact J.fst_ne_snd
      | exact J.distinct
      | cases J <;> assumption
      | cases J <;> omega
      | cases J <;> grind
    have hr : J.snd < J.fst := by omega
    have sw : ∃ K : CutPair Q, K.fst = J.snd ∧ K.snd = J.fst := by
      exact ⟨{ fst := J.snd, snd := J.fst,
               fst_ne_root := J.snd_ne_root,
               snd_ne_root := J.fst_ne_root,
               ne := Ne.symm J.ne }, rfl, rfl⟩
    obtain ⟨K, h₁, h₂⟩ := sw
    exact ⟨K, by simpa only [h₁, h₂] using hr, Or.inr ⟨h₁, h₂⟩⟩

private theorem thirdLossCongr {Q : LabelledQuotient} {K J : CutPair Q}
    (ends : ThirdEnds K J.fst J.snd) (z : Fin Q.vertexCount) :
    Q.ProperLoss K z ↔ Q.ProperLoss J z := by
  have hm : K.Mem = J.Mem := by
    funext v
    apply propext
    rcases ends with h | h
    · simp only [CutPair.Mem, h.1, h.2]
    · simp only [CutPair.Mem, h.1, h.2, or_comm]
  unfold LabelledQuotient.ProperLoss LabelledQuotient.Lost
  rw [hm] <;>
    (rcases ends with h | h <;>
      simp [CutPair.Mem, h.1, h.2, and_comm, or_comm])

private theorem thirdClean {Q : LabelledQuotient} (J : CutPair Q)
    (z : Fin Q.vertexCount)
    (rooted : AvoidPath Q.HasQuotientArc (fun _ => False) Q.root z)
    (h₁ : z ≠ J.fst) (h₂ : z ≠ J.snd)
    (hl : ¬ Q.ProperLoss J z) :
    AvoidPath Q.HasQuotientArc J.Mem Q.root z := by
  apply Classical.byContradiction
  intro blocked
  apply hl
  have notMem : ¬ J.Mem z := by
    intro hz
    exact hz.elim h₁ h₂
  unfold LabelledQuotient.ProperLoss
  first
  | solve_by_elim [And.intro]
  | simpa [CutPair.Mem, h₁, h₂, rooted, blocked]
  | grind [CutPair.Mem]

private theorem thirdReachOfNotDom {r f z : Fin g.vertexCount}
    (h : ¬ g.Dominates r f z) : g.InitiallyReachable r z := by
  apply Classical.byContradiction
  intro hu
  apply h
  first
  | intro p
    exact hu (AvoidPath.mono p (fun _ hfalse => False.elim hfalse))
  | intro p
    exfalso
    apply hu
    exact?
  | exact?

/-- Only tails witnessing non-dominance need a retained index. Such a tail
is initially reachable, so exact translation supplies that index. -/
private theorem thirdMapped_iff
    (T : BothTables R W progress injRank spec)
    (a : Fin n) (xs : List (Fin g.vertexCount)) :
    (¬ g.CommonDominator (W.vertex R.source) xs (W.vertex a)) ↔
      ∃ i, ThirdMapped W xs i ∧ ¬ W.Inside a i := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro noWitness
    apply h
    intro z hz
    apply Classical.byContradiction
    intro nd
    have reachable := thirdReachOfNotDom nd
    cases tr : (R.fetch (.translate z)).value with
    | none => exact (T.translateNone z).1 tr reachable
    | some i =>
      have iz := (T.translateSome z i).1 tr
      apply noWitness
      refine ⟨i, ?_, ?_⟩
      · change W.vertex i ∈ xs
        rwa [iz]
      · intro inside
        apply nd
        simpa only [iz] using (T.domInterval a i).1 inside
  · rintro ⟨i, hi, outside⟩ common
    exact outside ((T.domInterval a i).2 (common (W.vertex i) hi))

theorem third_route_leaf_contract
    {G : ThirdForestGeometry R W progress injRank spec}
    (D : ThirdForestTables progress injRank spec G)
    (T : BothTables R W progress injRank spec)
    {d u v a b x y : Fin n}
    (input : BothThirdInput (R := R) (W := W)
      progress injRank spec d u v a b x y) :
    LeafContract R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x)
      ((routeThird d u v a b y).run R).value := by
  classical
  obtain ⟨hd, A, C, Z, J, order, eqZ, keyA, keyC, noA, noC, branches⟩ :=
    input.paper
  let Q := thirdQ (R := R) (W := W) progress injRank spec d hd
  let ix := thirdIndex (R := R) (W := W) progress injRank spec d hd
  let S := siblingBlockSystem progress injRank spec hd
  let F : Fin g.vertexCount → Prop := fun z => z = W.vertex a ∨ z = W.vertex b
  let r := W.vertex R.source
  have ka : J.fst = ix A := keyA
  have kc : J.snd = ix C := keyC
  have nA : ix Z ≠ J.fst := noA
  have nC : ix Z ≠ J.snd := noC
  have blockA : S.block Z ≠ S.block A := by
    intro h
    apply nA
    rw [ka]
    exact congrArg
      (encodeSiblingBlockKey g r (W.vertex d) parent) h
  have blockC : S.block Z ≠ S.block C := by
    intro h
    apply nC
    rw [kc]
    exact congrArg
      (encodeSiblingBlockKey g r (W.vertex d) parent) h
  unfold LastExitTestBranches at branches
  have third := branches.2.2.2.2 Z blockA blockC
  have goalZ :
      Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) ↔
        g.SurvivingPath F r Z.val := by
    have hf : Fails (some (W.vertex a)) (some (W.vertex b)) = F := by
      funext z
      apply propext
      simp [Fails, F]
    change g.SurvivingPath (Fails (some (W.vertex a)) (some (W.vertex b)))
      r (W.vertex x) ↔ _
    rw [hf, eqZ]

  obtain ⟨U, V, valU, valV, perm⟩ :
      ∃ U V : ThirdVertex R W d,
        U.val = W.vertex a ∧ V.val = W.vertex b ∧
        ((U = A ∧ V = C) ∨ (U = C ∧ V = A)) := by
    rcases order with h | h
    · exact ⟨A, C, h.1, h.2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨C, A, h.2, h.1, Or.inr ⟨rfl, rfl⟩⟩
  have repU : ThirdChild R W d a u U := ⟨valU, input.firstChild⟩
  have repV : ThirdChild R W d b v V := ⟨valV, input.secondChild⟩
  have repZ : ThirdChild R W d x y Z := ⟨eqZ, input.targetChild⟩
  have jEnds : ThirdEnds J (ix U) (ix V) := by
    rcases perm with h | h
    · exact Or.inl
        ⟨ka.trans (congrArg ix h.1).symm, kc.trans (congrArg ix h.2).symm⟩
    · exact Or.inr
        ⟨ka.trans (congrArg ix h.2).symm, kc.trans (congrArg ix h.1).symm⟩
  obtain ⟨K, asc, sameEnds⟩ := thirdAscending J
  have kEnds : ThirdEnds K (ix U) (ix V) := by
    rcases sameEnds with h | h <;> rcases jEnds with j | j
    · exact Or.inl ⟨h.1.trans j.1, h.2.trans j.2⟩
    · exact Or.inr ⟨h.1.trans j.1, h.2.trans j.2⟩
    · exact Or.inr ⟨h.1.trans j.2, h.2.trans j.1⟩
    · exact Or.inl ⟨h.1.trans j.2, h.2.trans j.1⟩
  have lossEq : Q.ProperLoss K (ix Z) ↔ Q.ProperLoss J (ix Z) :=
    thirdLossCongr sameEnds (ix Z)
  have liveOfNoLoss (h : ¬ Q.ProperLoss K (ix Z)) :
      Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) := by
    apply goalZ.mpr
    apply third.2.1
    exact thirdClean J (ix Z) (G.rooted d hd (ix Z)) nA nC
      (fun loss => h (lossEq.mpr loss))

  have dict := D.dictionary d hd a b u v U V K repU repV asc kEnds
  cases hk : (R.pairKey d u v).value with
  | none =>
    simp only [hk] at dict
    have hk' : (R.fetch (.key d u v)).value = none := hk
    have tag : ((routeThird d u v a b y).run R).value = .thirdMissing := by
      simp [routeThird, Plan.run, hk', hk]
    rw [tag]
    apply liveOfNoLoss
    intro loss
    obtain ⟨i, hi, _⟩ :=
      (buildProperLossForest_properLoss_iff_ancestor
        (G.rankArc d hd) (G.rankInj d hd) (G.flat d hd) asc (ix Z)).mp loss
    exact dict i hi
  | some hit =>
    simp only [hk] at dict
    obtain ⟨i, dec, node, orient⟩ := dict
    have hk' : (R.fetch (.key d u v)).value = some hit := hk
    have member := D.member d hd hit.key x y Z i dec repZ
    have ancestry :=
      buildProperLossForest_properLoss_iff_of_node
        (G.rankArc d hd) (G.rankInj d hd) (G.flat d hd) node (ix Z)
    cases hm : (R.pairMember hit.key y).value with
    | false =>
      have hm' : (R.fetch (.member hit.key y)).value = false := hm
      have tag : ((routeThird d u v a b y).run R).value = .thirdNonmember := by
        simp [routeThird, Plan.run, hk', hk, hm', hm]
      rw [tag]
      apply liveOfNoLoss
      intro loss
      have marked := member.mpr (ancestry.mp loss)
      rw [hm] at marked
      cases marked
    | true =>
      have hm' : (R.fetch (.member hit.key y)).value = true := hm
      have tag :
          ((routeThird d u v a b y).run R).value = .thirdExits d u v a b y hit := by
        simp [routeThird, Plan.run, hk', hk, hm', hm]
      have loss : Q.ProperLoss J (ix Z) :=
        lossEq.mp (ancestry.mpr (member.mp hm))
      let tails : Fin Q.vertexCount → List (Fin g.vertexCount) :=
        fun s => lemma22ExitTails Q J s (ix Z)
      let X : Fin n → Prop := ThirdMapped W (tails (ix U))
      let Y : Fin n → Prop := ThirdMapped W (tails (ix V))

      -- Read the two tests in paper order, then transport them to query order.
      obtain ⟨_, _, l₁, l₂, _, _, commonA, commonC, survives, _⟩ :=
        third.2.2 loss
      have paper :
          Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) ↔
            (¬ g.CommonDominator r (tails J.fst) A.val) ∨
            (¬ g.CommonDominator r (tails J.snd) C.val) :=
        goalZ.trans (survives.trans
          (or_congr (commonA A.val).symm (commonC C.val).symm))
      have mapU :
          (¬ g.CommonDominator r (tails (ix U)) (W.vertex a)) ↔
            ∃ j, X j ∧ ¬ W.Inside a j :=
        thirdMapped_iff progress injRank spec T a (tails (ix U))
      have mapV :
          (¬ g.CommonDominator r (tails (ix V)) (W.vertex b)) ↔
            ∃ j, Y j ∧ ¬ W.Inside b j :=
        thirdMapped_iff progress injRank spec T b (tails (ix V))
      have sem :
          Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) ↔
            (∃ j, X j ∧ ¬ W.Inside a j) ∨ (∃ j, Y j ∧ ¬ W.Inside b j) := by
        rcases perm with h | h
        · have jf : J.fst = ix U := ka.trans (congrArg ix h.1).symm
          have js : J.snd = ix V := kc.trans (congrArg ix h.2).symm
          have av : A.val = W.vertex a := (congrArg Subtype.val h.1).symm.trans valU
          have cv : C.val = W.vertex b := (congrArg Subtype.val h.2).symm.trans valV
          rw [jf, js, av, cv] at paper
          exact paper.trans (or_congr mapU mapV)
        · have jf : J.fst = ix V := ka.trans (congrArg ix h.2).symm
          have js : J.snd = ix U := kc.trans (congrArg ix h.1).symm
          have av : A.val = W.vertex b := (congrArg Subtype.val h.2).symm.trans valV
          have cv : C.val = W.vertex a := (congrArg Subtype.val h.1).symm.trans valU
          rw [jf, js, av, cv] at paper
          exact paper.trans ((or_congr mapV mapU).trans or_comm)

      -- This is the orientation of the actual physical extrema read.
      let s := (R.exitExtrema hit.key y).value
      have raw :
          SpanExact W.entry (ThirdMapped W (tails K.fst)) s.1 ∧
          SpanExact W.entry (ThirdMapped W (tails K.snd)) s.2 :=
        D.extrema d hd hit.key x y Z i K J dec node sameEnds repZ hm
      have spans :
          SpanExact W.entry X (requested R y hit).1 ∧
          SpanExact W.entry Y (requested R y hit).2 := by
        change SpanExact W.entry X (hit.orientation.order s).1 ∧
          SpanExact W.entry Y (hit.orientation.order s).2
        rw [orient s]
        rcases kEnds with h | h
        · rw [if_pos h.1.symm]
          simpa only [h.1, h.2] using raw
        · have notFirst : ix U ≠ K.fst := by
            intro e
            have eq : K.snd = K.fst := h.2.trans e
            have selfLt : K.fst < K.fst := by
              simpa only [eq] using asc
            exact Nat.lt_irrefl K.fst.val selfLt
          rw [if_neg notFirst]
          exact ⟨by simpa only [h.2] using raw.2,
                 by simpa only [h.1] using raw.1⟩
      rw [tag]
      exact ⟨hk, hm, X, Y, spans.1, spans.2, sem⟩

/-- Conditional correctness for every leaf actually selected for the two
incomparable retained failures. No contract is granted to `.malformed`. -/
theorem both_route_leaf_contract
    {G : ThirdForestGeometry R W progress injRank spec}
    (D : ThirdForestTables progress injRank spec G)
    (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic) (a b : Fin n)
    (ab : ¬ Ancestor parent (W.vertex a) (W.vertex b))
    (ba : ¬ Ancestor parent (W.vertex b) (W.vertex a))
    (t : Fin g.vertexCount) :
    LeafContract R W (some (W.vertex a)) (some (W.vertex b)) t
      ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value := by
  have split := bothReachable_split progress injRank spec T acyclic a b ab ba t
  cases split with
  | no tag dead =>
    rcases tag with h | h | h <;> rw [h] <;> exact dead
  | yes tag live =>
    rw [tag]
    exact live
  | withinFirst x target tag criterion =>
    rw [tag]
    exact criterion
  | withinSecond x target tag criterion =>
    rw [tag]
    exact criterion
  | third d u v x y target tag input =>
    rw [tag, ← target]
    exact third_route_leaf_contract progress injRank spec D T input

theorem both_routed_answer_correct
    {G : ThirdForestGeometry R W progress injRank spec}
    (D : ThirdForestTables progress injRank spec G)
    (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic) (a b : Fin n)
    (ab : ¬ Ancestor parent (W.vertex a) (W.vertex b))
    (ba : ¬ Ancestor parent (W.vertex b) (W.vertex a))
    (t : Fin g.vertexCount) :
    ((answer
      ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value).run R).value
        = true ↔ Goal R W (some (W.vertex a)) (some (W.vertex b)) t :=
  answer_correct T.intervals _
    (both_route_leaf_contract progress injRank spec D T acyclic a b ab ba t)

end

end PaperB.EX44

namespace PaperB.EX44

open PaperB PaperB.Digraph PaperB.Digraph.EX44 PaperB.LabelledQuotient

noncomputable section

variable {g : PaperB.Digraph} {n k B E : Nat}
variable {R : Runtime g.vertexCount n k B E} {W : World g n}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ i j, g.HasArc i j → rank i < rank j)
variable (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
variable (spec : ParentSpec g (W.vertex R.source) parent)

private theorem thirdMapCast_rfl {m : Nat} (xs : List (Fin m)) :
    xs.map (Fin.cast (rfl : m = m)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : Fin.cast (rfl : m = m) x = x := by
      cases x
      rfl
    simp only [List.map_cons, hx, ih]

/-- The facts consumed by the third leaf proof, in query order. -/
structure DirectThirdFacts
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (d u v y : Fin n) (Q : LabelledQuotient) (J : CutPair Q)
    (hOrig : Q.origVertexCount = g.vertexCount)
    (s t z : Fin Q.vertexCount) : Prop where
  missing : (R.pairKey d u v).value = none → ¬ Q.ProperLoss J z
  member : ∀ hit, (R.pairKey d u v).value = some hit →
    ((R.pairMember hit.key y).value = true ↔ Q.ProperLoss J z)
  extrema : ∀ hit, (R.pairKey d u v).value = some hit →
    (R.pairMember hit.key y).value = true →
    SpanExact W.entry (ThirdMapped W ((lemma22ExitTails Q J s z).map (Fin.cast hOrig)))
        (requested R y hit).1 ∧
      SpanExact W.entry (ThirdMapped W ((lemma22ExitTails Q J t z).map (Fin.cast hOrig)))
        (requested R y hit).2

/-- Rootedness is geometric. The table laws relate the actual reads to
the structural sibling quotient without decoding any forest node. -/
structure DirectThirdTables : Prop where
  rooted : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d)),
    let Q := thirdQ progress injRank spec d hd
    ∀ z : Fin Q.vertexCount, AvoidPath Q.HasQuotientArc (fun _ => False) Q.root z
  laws : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (a b u v x y : Fin n) (U V Z : ThirdVertex R W d)
    (J : CutPair (thirdQ progress injRank spec d hd)),
    ThirdChild R W d a u U → ThirdChild R W d b v V → ThirdChild R W d x y Z →
    ThirdEnds J (thirdIndex progress injRank spec d hd U)
      (thirdIndex progress injRank spec d hd V) →
    DirectThirdFacts R W d u v y (thirdQ progress injRank spec d hd) J rfl
      (thirdIndex progress injRank spec d hd U)
      (thirdIndex progress injRank spec d hd V)
      (thirdIndex progress injRank spec d hd Z)

/-- The legacy dictionary and ancestry bookkeeping is one way to prove
the direct laws; it is not needed by the leaf proof. -/
theorem ThirdForestTables.toDirect
    {G : ThirdForestGeometry R W progress injRank spec}
    (D : ThirdForestTables progress injRank spec G) :
    DirectThirdTables progress injRank spec := by
  refine ⟨G.rooted, ?_⟩
  intro d hd a b u v x y U V Z J repU repV repZ jEnds
  let ix := thirdIndex (R := R) (W := W) progress injRank spec d hd
  obtain ⟨K, asc, sameEnds⟩ := thirdAscending J
  have kEnds : ThirdEnds K (ix U) (ix V) := by
    rcases sameEnds with h | h <;> rcases jEnds with j | j
    · exact Or.inl ⟨h.1.trans j.1, h.2.trans j.2⟩
    · exact Or.inr ⟨h.1.trans j.1, h.2.trans j.2⟩
    · exact Or.inr ⟨h.1.trans j.2, h.2.trans j.1⟩
    · exact Or.inl ⟨h.1.trans j.2, h.2.trans j.1⟩
  have lossEq := thirdLossCongr sameEnds (ix Z)
  have dict := D.dictionary d hd a b u v U V K repU repV asc kEnds
  constructor
  · intro hk loss
    simp only [hk] at dict
    obtain ⟨i, hi, _⟩ :=
      (buildProperLossForest_properLoss_iff_ancestor
        (G.rankArc d hd) (G.rankInj d hd) (G.flat d hd) asc (ix Z)).mp
        (lossEq.mpr loss)
    exact dict i hi
  · intro hit hk
    simp only [hk] at dict
    obtain ⟨i, dec, node, _⟩ := dict
    have ancestry := buildProperLossForest_properLoss_iff_of_node
      (G.rankArc d hd) (G.rankInj d hd) (G.flat d hd) node (ix Z)
    exact (D.member d hd hit.key x y Z i dec repZ).trans (ancestry.symm.trans lossEq)
  · intro hit hk hm
    simp only [hk] at dict
    obtain ⟨i, dec, node, orient⟩ := dict
    let s := (R.exitExtrema hit.key y).value
    let tails : Fin (thirdQ progress injRank spec d hd).vertexCount → List (Fin g.vertexCount) :=
      fun p => lemma22ExitTails (thirdQ progress injRank spec d hd) J p (ix Z)
    have raw : SpanExact W.entry (ThirdMapped W (tails K.fst)) s.1 ∧
        SpanExact W.entry (ThirdMapped W (tails K.snd)) s.2 :=
      D.extrema d hd hit.key x y Z i K J dec node sameEnds repZ hm
    change SpanExact W.entry
        (ThirdMapped W ((tails (ix U)).map (Fin.cast (rfl : g.vertexCount = g.vertexCount))))
          (requested R y hit).1 ∧
      SpanExact W.entry
        (ThirdMapped W ((tails (ix V)).map (Fin.cast (rfl : g.vertexCount = g.vertexCount))))
          (requested R y hit).2
    simp only [thirdMapCast_rfl]
    change SpanExact W.entry (ThirdMapped W (tails (ix U))) (hit.orientation.order s).1 ∧
      SpanExact W.entry (ThirdMapped W (tails (ix V))) (hit.orientation.order s).2
    rw [orient s]
    rcases kEnds with h | h
    · rw [if_pos h.1.symm]
      simpa only [h.1, h.2] using raw
    · rw [if_neg (show ix U ≠ K.fst from fun e => K.ne (h.2.trans e).symm)]
      exact ⟨by simpa only [h.2] using raw.2, by simpa only [h.1] using raw.1⟩

theorem third_route_leaf_contract_direct
    (D : DirectThirdTables progress injRank spec)
    (T : BothTables R W progress injRank spec) {d u v a b x y : Fin n}
    (input : BothThirdInput (R := R) (W := W) progress injRank spec d u v a b x y) :
    LeafContract R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x)
      ((routeThird d u v a b y).run R).value := by
  classical
  obtain ⟨hd, A, C, Z, J, order, eqZ, keyA, keyC, noA, noC, branches⟩ := input.paper
  let Q := thirdQ (R := R) (W := W) progress injRank spec d hd
  let ix := thirdIndex (R := R) (W := W) progress injRank spec d hd
  let S := siblingBlockSystem progress injRank spec hd
  let r := W.vertex R.source
  let F : Fin g.vertexCount → Prop := fun z => z = W.vertex a ∨ z = W.vertex b
  have ka : J.fst = ix A := keyA
  have kc : J.snd = ix C := keyC
  have nA : ix Z ≠ J.fst := noA
  have nC : ix Z ≠ J.snd := noC
  have blockA : S.block Z ≠ S.block A := by
    intro h
    exact nA ((congrArg (encodeSiblingBlockKey g r (W.vertex d) parent) h).trans ka.symm)
  have blockC : S.block Z ≠ S.block C := by
    intro h
    exact nC ((congrArg (encodeSiblingBlockKey g r (W.vertex d) parent) h).trans kc.symm)
  unfold LastExitTestBranches at branches
  have third := branches.2.2.2.2 Z blockA blockC
  have goalZ : Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) ↔
      g.SurvivingPath F r Z.val := by
    have hf : Fails (some (W.vertex a)) (some (W.vertex b)) = F := by
      funext z
      apply propext
      simp [Fails, F]
    change g.SurvivingPath (Fails (some (W.vertex a)) (some (W.vertex b))) r (W.vertex x) ↔ _
    rw [hf, eqZ]
  have live (h : ¬ Q.ProperLoss J (ix Z)) :
      Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) :=
    goalZ.mpr (third.2.1 (thirdClean J (ix Z) (D.rooted d hd (ix Z)) nA nC h))
  obtain ⟨U, V, valU, valV, perm⟩ :
      ∃ U V : ThirdVertex R W d, U.val = W.vertex a ∧ V.val = W.vertex b ∧
        ((U = A ∧ V = C) ∨ (U = C ∧ V = A)) := by
    rcases order with h | h
    · exact ⟨A, C, h.1, h.2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨C, A, h.2, h.1, Or.inr ⟨rfl, rfl⟩⟩
  have ends : ThirdEnds J (ix U) (ix V) := by
    rcases perm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ka, kc⟩
    · exact Or.inr ⟨ka, kc⟩
  have laws := D.laws d hd a b u v x y U V Z J
    ⟨valU, input.firstChild⟩ ⟨valV, input.secondChild⟩ ⟨eqZ, input.targetChild⟩ ends
  cases hk : (R.pairKey d u v).value with
  | none =>
    have hk' : (R.fetch (.key d u v)).value = none := hk
    rw [show ((routeThird d u v a b y).run R).value = .thirdMissing by
      simp [routeThird, Plan.run, hk', hk]]
    exact live (laws.missing hk)
  | some hit =>
    have hk' : (R.fetch (.key d u v)).value = some hit := hk
    cases hm : (R.pairMember hit.key y).value with
    | false =>
      have hm' : (R.fetch (.member hit.key y)).value = false := hm
      rw [show ((routeThird d u v a b y).run R).value = .thirdNonmember by
        simp [routeThird, Plan.run, hk', hk, hm', hm]]
      apply live
      intro loss
      have marked := (laws.member hit hk).mpr loss
      rw [hm] at marked
      cases marked
    | true =>
      have hm' : (R.fetch (.member hit.key y)).value = true := hm
      rw [show ((routeThird d u v a b y).run R).value = .thirdExits d u v a b y hit by
        simp [routeThird, Plan.run, hk', hk, hm', hm]]
      let tails : Fin Q.vertexCount → List (Fin g.vertexCount) :=
        fun s => lemma22ExitTails Q J s (ix Z)
      obtain ⟨_, _, _, _, _, _, commonA, commonC, survives, _⟩ :=
        third.2.2 ((laws.member hit hk).mp hm)
      have paper : Goal R W (some (W.vertex a)) (some (W.vertex b)) (W.vertex x) ↔
          (¬ g.CommonDominator r (tails J.fst) A.val) ∨
          (¬ g.CommonDominator r (tails J.snd) C.val) :=
        goalZ.trans (survives.trans (or_congr (commonA A.val).symm (commonC C.val).symm))
      have mapU := thirdMapped_iff progress injRank spec T a (tails (ix U))
      have mapV := thirdMapped_iff progress injRank spec T b (tails (ix V))
      have spans := laws.extrema hit hk hm
      change SpanExact W.entry
          (ThirdMapped W ((tails (ix U)).map (Fin.cast (rfl : g.vertexCount = g.vertexCount))))
            (requested R y hit).1 ∧
        SpanExact W.entry
          (ThirdMapped W ((tails (ix V)).map (Fin.cast (rfl : g.vertexCount = g.vertexCount))))
            (requested R y hit).2 at spans
      simp only [thirdMapCast_rfl] at spans
      refine ⟨hk, hm, ThirdMapped W (tails (ix U)), ThirdMapped W (tails (ix V)),
        spans.1, spans.2, ?_⟩
      rcases perm with h | h
      · rw [ka, kc, ← h.1, ← h.2, valU, valV] at paper
        exact paper.trans (or_congr mapU mapV)
      · rw [ka, kc, ← h.2, ← h.1, valV, valU] at paper
        exact paper.trans ((or_congr mapV mapU).trans or_comm)

theorem both_route_leaf_contract_direct
    (D : DirectThirdTables progress injRank spec) (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic) (a b : Fin n)
    (ab : ¬ Ancestor parent (W.vertex a) (W.vertex b))
    (ba : ¬ Ancestor parent (W.vertex b) (W.vertex a)) (t : Fin g.vertexCount) :
    LeafContract R W (some (W.vertex a)) (some (W.vertex b)) t
      ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value := by
  cases bothReachable_split progress injRank spec T acyclic a b ab ba t with
  | no tag dead => rcases tag with h | h | h <;> rw [h] <;> exact dead
  | yes tag live => rw [tag]; exact live
  | withinFirst x target tag criterion => rw [tag]; exact criterion
  | withinSecond x target tag criterion => rw [tag]; exact criterion
  | third d u v x y target tag input =>
    rw [tag, ← target]
    exact third_route_leaf_contract_direct progress injRank spec D T input

theorem both_routed_answer_correct_direct
    (D : DirectThirdTables progress injRank spec) (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic) (a b : Fin n)
    (ab : ¬ Ancestor parent (W.vertex a) (W.vertex b))
    (ba : ¬ Ancestor parent (W.vertex b) (W.vertex a)) (t : Fin g.vertexCount) :
    ((answer
      ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value).run R).value
        = true ↔ Goal R W (some (W.vertex a)) (some (W.vertex b)) t :=
  answer_correct T.intervals _
    (both_route_leaf_contract_direct progress injRank spec D T acyclic a b ab ba t)

end

end PaperB.EX44
