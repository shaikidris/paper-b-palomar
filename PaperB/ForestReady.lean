module

public import PaperB.ForestKeyInstall

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-
Append this fragment immediately after the supplied `end EX24`.

This is the conditional pre-step bridge. The excerpt does not give the
JumpForest parent getter, the word-query correctness theorems, or the
canonical nodeChain recursion lemmas. Consequently `WordLaws` and
`CanonicalLaws` below are explicit input contracts, not claimed
instantiations of those APIs. In particular, `Grounded` alone cannot imply
`WordLaws`: it places no correctness condition on Config.atDepth or
Config.ancestor.

The embedding and view are proof-side objects. Nothing is added to State,
Tables, or the installer, and no path is stored at runtime.
-/

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

namespace EX24
namespace PreStep

noncomputable section

variable {H : LabelledQuotient}
variable {c : Config H} {s : State H} {F : JumpForest}
variable {rank : Vertex H → Nat}

abbrev CanonNode (H : LabelledQuotient) (rank : Vertex H → Nat) :=
  Fin ((buildProperLossForest H rank).realNodeCount + 1)

/-- Apply one parent function `k` times, without constructing a path list. -/
def climb {α : Type} (parent : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => parent (climb parent k a)

/--
`up` is the existing forest's parent getter restricted to occupied slots.
`Grounded.size_eq` identifies `Fin F.size` with the allocated slot interval.
The label condition applies only to vertices processed before this head.
-/
structure Embedding (c : Config H) (s : State H) (F : JumpForest)
    (rank : Vertex H → Nat) (up : Fin F.size → Fin F.size)
    (processed : Vertex H → Prop) where
  image : Fin F.size → CanonNode H rank
  injective : Function.Injective image
  root_eq : ∀ h : 0 < F.size,
    image ⟨0, h⟩ = (buildProperLossForest H rank).rootNode
  label_lt : ∀ v, processed v → (selectors c s).label v < F.size
  label_eq : ∀ v (hv : processed v),
    image ⟨(selectors c s).label v, label_lt v hv⟩ =
      (buildProperLossForest H rank).label v
  depth_eq : ∀ a,
    (selectors c s).depth a.val =
      (buildProperLossForest H rank).depth (image a)
  parent_eq : ∀ a,
    image (up a) = (buildProperLossForest H rank).parent (image a)
  back_eq : ∀ a,
    s.tables.back[a.val]? =
      some ((buildProperLossForest H rank).nodeKey? (image a))

/-- Query contracts to be discharged using the actual getter specifications. -/
structure WordLaws (c : Config H) (s : State H) (F : JumpForest)
    (up : Fin F.size → Fin F.size) : Prop where
  at_depth : ∀ (a : Fin F.size) (d : Nat), 0 < d →
    d ≤ (selectors c s).depth a.val →
    (selectors c s).atDepth a.val d =
      (climb up ((selectors c s).depth a.val - d) a).val
  ancestor : ∀ (a b : Fin F.size), 0 < (selectors c s).depth a.val →
    ((selectors c s).ancestor a.val b.val = true ↔
      ∃ k, climb up k b = a)
  node_zero : ∀ a, nodeAt (selectors c s) a 0 = 0
  node_pos : ∀ a d, 0 < d → d ≤ (selectors c s).depth a →
    nodeAt (selectors c s) a d = (selectors c s).atDepth a d

/--
These laws refer to the actual canonical proper-loss forest, not a second
forest model. `parent_take` is a one-edge law; the prefix theorem below
derives its iterated form.
-/
structure CanonicalLaws (H : LabelledQuotient) (rank : Vertex H → Nat) :
    Prop where
  root_nil :
    (buildProperLossForest H rank).nodeChain
      (buildProperLossForest H rank).rootNode = []
  depth_length : ∀ a : CanonNode H rank,
    (buildProperLossForest H rank).depth a =
      ((buildProperLossForest H rank).nodeChain a).length
  parent_take : ∀ a : CanonNode H rank,
    (buildProperLossForest H rank).nodeChain
        ((buildProperLossForest H rank).parent a) =
      ((buildProperLossForest H rank).nodeChain a).take
        (((buildProperLossForest H rank).nodeChain a).length - 1)
  last_key : ∀ (a : CanonNode H rank) (k : Nat),
    ((buildProperLossForest H rank).nodeChain a).length = k + 1 →
    (buildProperLossForest H rank).nodeKey? a =
      ((buildProperLossForest H rank).nodeChain a)[k]?
  ancestor : ∀ (a b : CanonNode H rank),
    0 < (buildProperLossForest H rank).depth a →
    (IsForestAncestor (buildProperLossForest H rank).parent a b ↔
      ∃ k, climb (buildProperLossForest H rank).parent k b = a)
  lost_cases : ∀ (B : CutPair H) (u : Vertex H),
    (B.Mem u ∨ H.ProperLoss B u) ↔ H.Lost B u
  nested : ∀ m : Vertex H,
    (sweepChain H rank m).Pairwise
      (fun B P => ∀ v, P.Mem v → H.Lost B v)
  legacy : ∀ (y m : Vertex H) (k : Nat)
      (hk : k < (sweepChain H rank m).length),
    sweepPasses H rank y (sweepChain H rank m)[k] = true ↔
      ∀ u, H.HasQuotientArc u y → H.Lost (sweepChain H rank m)[k] u

variable {up : Fin F.size → Fin F.size} {processed : Vertex H → Prop}
variable (E : Embedding c s F rank up processed)

theorem image_climb (k : Nat) (a : Fin F.size) :
    E.image (climb up k a) =
      climb (buildProperLossForest H rank).parent k (E.image a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [climb, E.parent_eq, ih]

/-- Reflection preserves the exact step count, not just reachability. -/
theorem path_iff (k : Nat) (a b : Fin F.size) :
    climb up k b = a ↔
      climb (buildProperLossForest H rank).parent k (E.image b) =
        E.image a := by
  rw [← image_climb E k b]
  exact ⟨congrArg E.image, fun h => E.injective h⟩

theorem real_ancestor (W : WordLaws c s F up) (L : CanonicalLaws H rank)
    (a b : Fin F.size) (ha : 0 < (selectors c s).depth a.val) :
    (selectors c s).ancestor a.val b.val = true ↔
      IsForestAncestor (buildProperLossForest H rank).parent
        (E.image a) (E.image b) := by
  have hda : 0 < (buildProperLossForest H rank).depth (E.image a) :=
    E.depth_eq a ▸ ha
  rw [W.ancestor a b ha, L.ancestor (E.image a) (E.image b) hda]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, (path_iff E k a b).mp hk⟩,
         fun ⟨k, hk⟩ => ⟨k, (path_iff E k a b).mpr hk⟩⟩

def view (n : Nat) : List (CutPair H) :=
  if h : n < F.size then
    (buildProperLossForest H rank).nodeChain (E.image ⟨n, h⟩)
  else []

theorem view_slot (a : Fin F.size) :
    view E a.val = (buildProperLossForest H rank).nodeChain (E.image a) := by
  cases a with
  | mk n hn => simp [view, hn]

theorem view_root (L : CanonicalLaws H rank) (h0 : 0 < F.size) :
    view E 0 = [] := by
  simpa only [view, dite_eq_left h0, E.root_eq h0] using L.root_nil

private theorem chain_climb (L : CanonicalLaws H rank)
    (a : CanonNode H rank) (k : Nat) :
    (buildProperLossForest H rank).nodeChain
        (climb (buildProperLossForest H rank).parent k a) =
      ((buildProperLossForest H rank).nodeChain a).take
        (((buildProperLossForest H rank).nodeChain a).length - k) := by
  induction k with
  | zero => simp [climb]
  | succ k ih =>
    let n := ((buildProperLossForest H rank).nodeChain a).length
    have h₁ : n - k ≤ n := Nat.sub_le n k
    have h₂ : n - k - 1 ≤ n - k := Nat.sub_le (n - k) 1
    have h₃ : n - k - 1 = n - (k + 1) := by omega
    simp only [climb, L.parent_take, ih, List.length_take, List.take_take]
    change ((buildProperLossForest H rank).nodeChain a).take
      (min (min (n - k) n - 1) (n - k)) =
        ((buildProperLossForest H rank).nodeChain a).take (n - (k + 1))
    rw [Nat.min_eq_left h₁, Nat.min_eq_left h₂, h₃]

variable
  (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
  (distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v)
  (flat : H.IsFlat)

include rankArc distinctRanks flat

/-- The positive-depth word query selects the slot for exactly this prefix. -/
theorem selected_prefix (W : WordLaws c s F up) (L : CanonicalLaws H rank)
    (m : Vertex H) (hm : processed m) (d : Nat) (hd₀ : 0 < d)
    (hd : d ≤ (selectors c s).depth ((selectors c s).label m)) :
    ∃ p : Fin F.size,
      (selectors c s).atDepth ((selectors c s).label m) d = p.val ∧
      (buildProperLossForest H rank).nodeChain (E.image p) =
        (sweepChain H rank m).take d := by
  let a : Fin F.size := ⟨(selectors c s).label m, E.label_lt m hm⟩
  let n := (selectors c s).depth a.val
  have hdn : d ≤ n := hd
  refine ⟨climb up (n - d) a, W.at_depth a d hd₀ hd, ?_⟩
  rw [image_climb E, chain_climb L, ← L.depth_length (E.image a),
    ← E.depth_eq a]
  change ((buildProperLossForest H rank).nodeChain (E.image a)).take
      (n - (n - d)) = _
  rw [show n - (n - d) = d by omega]
  have ha : E.image a = (buildProperLossForest H rank).label m :=
    E.label_eq m hm
  rw [ha, ← buildProperLossForest_sweepChain_eq_nodeChain
    rankArc distinctRanks flat m]

theorem ready (W : WordLaws c s F up) (L : CanonicalLaws H rank)
    (h0 : 0 < F.size) {y m : Vertex H} {xs : List (Vertex H)}
    (hm : processed m) (hxs : ∀ u ∈ xs, processed u) :
    Ready (selectors c s) (view E) rank y m xs := by
  have hmdepth :
      (selectors c s).depth ((selectors c s).label m) =
        (sweepChain H rank m).length := by
    let a : Fin F.size := ⟨(selectors c s).label m, E.label_lt m hm⟩
    change (selectors c s).depth a.val = _
    have ha : E.image a = (buildProperLossForest H rank).label m :=
      E.label_eq m hm
    rw [E.depth_eq a, ha, L.depth_length,
      ← buildProperLossForest_sweepChain_eq_nodeChain
        rankArc distinctRanks flat m]
  have probeSlot (k : Nat) (hk : k < (sweepChain H rank m).length) :
      ∃ p : Fin F.size,
        (selectors c s).atDepth ((selectors c s).label m) (k + 1) = p.val ∧
        (buildProperLossForest H rank).nodeKey? (E.image p) =
          some ((sweepChain H rank m)[k]'hk) ∧
        0 < (selectors c s).depth p.val := by
    have hk₁ : k + 1 ≤ (sweepChain H rank m).length := Nat.succ_le_of_lt hk
    have hd : k + 1 ≤ (selectors c s).depth ((selectors c s).label m) := by
      rw [hmdepth]
      exact hk₁
    obtain ⟨p, hp, hc⟩ := selected_prefix E rankArc distinctRanks flat W L
      m hm (k + 1) (Nat.zero_lt_succ k) hd
    have htlen : ((sweepChain H rank m).take (k + 1)).length = k + 1 := by
      rw [List.length_take, Nat.min_eq_left hk₁]
    have hl : ((buildProperLossForest H rank).nodeChain (E.image p)).length =
        k + 1 := by
      rw [hc, htlen]
    have htake : k < ((sweepChain H rank m).take (k + 1)).length := by
      rw [htlen]
      exact Nat.lt_succ_self k
    refine ⟨p, hp, ?_, ?_⟩
    · rw [L.last_key (E.image p) k hl, hc]
      simp only [getElem?_def, dite_eq_left htake, List.getElem_take]
    · rw [E.depth_eq p, L.depth_length, hl]
      exact Nat.zero_lt_succ k
  refine ⟨hmdepth, ?_, ?_, ?_, L.nested m, L.legacy y m⟩
  · intro d hd
    by_cases hz : d = 0
    · subst d
      calc
        view E (nodeAt (selectors c s) ((selectors c s).label m) 0) =
            view E 0 := congrArg (view E) (W.node_zero _)
        _ = [] := view_root E L h0
        _ = (sweepChain H rank m).take 0 := rfl
    · have hd₀ : 0 < d := Nat.pos_of_ne_zero hz
      obtain ⟨p, hp, hc⟩ :=
        selected_prefix E rankArc distinctRanks flat W L m hm d hd₀ hd
      rw [W.node_pos _ _ hd₀ hd, hp]
      change view E p.val = (sweepChain H rank m).take d
      exact (view_slot E p).trans hc
  · intro k hk
    obtain ⟨p, hp, hkey, _⟩ := probeSlot k hk
    rw [hp]
    change (match s.tables.back[p.val]? with
      | some (some q) => q
      | _ => c.zeroKey) = (sweepChain H rank m)[k]'hk
    rw [E.back_eq p, hkey]
  · intro k hk u hu
    obtain ⟨p, hp, hkey, hdepth⟩ := probeSlot k hk
    let b : Fin F.size := ⟨(selectors c s).label u, E.label_lt u (hxs u hu)⟩
    have hb : E.image b = (buildProperLossForest H rank).label u :=
      E.label_eq u (hxs u hu)
    have htest : (selectors c s).ancestor p.val b.val = true ↔
        H.ProperLoss ((sweepChain H rank m)[k]'hk) u := by
      rw [real_ancestor E W L p b hdepth, hb]
      exact (buildProperLossForest_properLoss_iff_of_node
        rankArc distinctRanks flat hkey u).symm
    rw [hp]
    change (((sweepChain H rank m)[k]'hk).Mem u ∨
      (selectors c s).ancestor p.val b.val = true) ↔
        H.Lost ((sweepChain H rank m)[k]'hk) u
    rw [htest]
    exact L.lost_cases _ _

/--
For a later head, instantiate `processed` with `fun v => rank v < rank y`.
`max_arc` and `tests_arc` are the predecessor facts needed from `preds`
and `TestSpec`; rank monotonicity then supplies both processed-label facts.
-/
theorem later_head_semantics {y : Vertex H} {xs : List (Vertex H)}
    {r : HeadResult H}
    (Ey : Embedding c s F rank up (fun v => rank v < rank y))
    (W : WordLaws c s F up) (L : CanonicalLaws H rank)
    (h0 : 0 < F.size) (T : TestSpec y xs)
    (tests_arc : ∀ u ∈ xs, H.HasQuotientArc u y)
    (max_arc : ∀ m, maxByRank rank (preds H y) = some m →
      H.HasQuotientArc m y)
    (hstep : step c s rank y xs = some r) :
    decode (view Ey) r.measured.step = sweepChain H rank y := by
  apply step_request_semantics hstep (view Ey) T (view_root Ey L h0) rankArc
  intro m _ _ hm
  have hmy := max_arc m hm
  exact ⟨hmy, ready Ey rankArc distinctRanks flat W L h0
    (rankArc m y hmy) (fun u hu => rankArc u y (tests_arc u hu))⟩

end

end PreStep
end EX24
