module

public import PaperB.ExitSummary
public import PaperB.SemanticLCA

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.Digraph.ExitLCABridge

open PaperB.ExitMap PaperB.ExitSummary

abbrev Vertex (g : Digraph) := Fin g.vertexCount

def AllReach {g : Digraph} (r : Vertex g) (vs : List (Vertex g)) : Prop :=
  ∀ v ∈ vs, g.InitiallyReachable r v

/-- Certificate for ordinary DFS of the dominator tree. The entry coordinate
is the preorder rank; `tout` is the exclusive cutoff in preorder coordinates,
not a timestamp from a clock that also counts exit events. -/
structure DFSIndex (g : Digraph) (r : Vertex g) where
  rank : Vertex g → Fin g.vertexCount
  unrank : Fin g.vertexCount → Vertex g
  unrank_rank : ∀ v, unrank (rank v) = v
  rank_unrank : ∀ i, rank (unrank i) = i
  tout : Vertex g → Nat
  dominates_iff_interval :
    ∀ d v, g.InitiallyReachable r v →
      (g.Dominates r d v ↔ (rank d).val ≤ (rank v).val ∧ (rank v).val < tout d)

variable {g : Digraph} {r : Vertex g}

theorem pairReach {a b : Vertex g} (ha : g.InitiallyReachable r a)
    (hb : g.InitiallyReachable r b) : AllReach r [a, b] := by
  intro v hv
  have h : v = a ∨ v = b := by simpa using hv
  rcases h with rfl | rfl
  · exact ha
  · exact hb

theorem appendReach {xs ys : List (Vertex g)} (hx : AllReach r xs)
    (hy : AllReach r ys) : AllReach r (xs ++ ys) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hx v hv
  · exact hy v hv

theorem common_pair_iff (a b d : Vertex g) :
    g.CommonDominator r [a, b] d ↔ g.Dominates r d a ∧ g.Dominates r d b := by
  constructor
  · intro h
    exact ⟨h a (by simp), h b (by simp)⟩
  · rintro ⟨ha, hb⟩ v hv
    have h : v = a ∨ v = b := by simpa using hv
    rcases h with rfl | rfl
    · exact ha
    · exact hb

private theorem summary_has_extrema (xs : List Nat) (hne : xs ≠ []) :
    ∃ lo hi, summary xs = .span lo hi ∧ lo ∈ xs ∧ hi ∈ xs ∧
      ∀ k ∈ xs, lo ≤ k ∧ k ≤ hi := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    by_cases h : xs = []
    · subst xs
      refine ⟨x, x, by simp [ExitSummary.singleton], by simp, by simp, ?_⟩
      intro k hk
      have he : k = x := by simpa using hk
      subst k
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨a, b, hab, ha, hb, hbounds⟩ := ih h
      refine ⟨min x a, max x b, ?_, ?_, ?_, ?_⟩
      · simp [hab, ExitSummary.singleton, Interval.join]
      · rw [Nat.min_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr ha)
      · rw [Nat.max_def]
        split <;> first
          | exact List.mem_cons.mpr (Or.inl rfl)
          | exact List.mem_cons.mpr (Or.inr hb)
      · intro k hk
        rcases List.mem_cons.mp hk with he | hk
        · subst k
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega
        · obtain ⟨hl, hh⟩ := hbounds k hk
          simp only [Nat.min_def, Nat.max_def]
          split <;> split <;> omega

namespace DFSIndex

variable (I : DFSIndex g r)

def record (vs : List (Vertex g)) : Interval :=
  summary (vs.map fun v => (I.rank v).val)

theorem record_append (xs ys : List (Vertex g)) :
    I.record (xs ++ ys) = Interval.join (I.record xs) (I.record ys) := by
  simp only [record, List.map_append, summary_append]

theorem record_extrema {vs : List (Vertex g)} (hne : vs ≠ []) :
    ∃ a b, a ∈ vs ∧ b ∈ vs ∧
      I.record vs = .span (I.rank a).val (I.rank b).val ∧
      ∀ v ∈ vs, (I.rank a).val ≤ (I.rank v).val ∧
        (I.rank v).val ≤ (I.rank b).val := by
  have hm : (vs.map fun v => (I.rank v).val) ≠ [] := by
    cases vs with
    | nil => exact False.elim (hne rfl)
    | cons v vs => simp
  obtain ⟨lo, hi, hs, hlo, hhi, hbounds⟩ := summary_has_extrema _ hm
  obtain ⟨a, ha, ea⟩ := List.mem_map.mp hlo
  obtain ⟨b, hb, eb⟩ := List.mem_map.mp hhi
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [ea, eb]
    exact hs
  · intro v hv
    rw [ea, eb]
    exact hbounds _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

@[simp] theorem record_eq_empty_iff (vs : List (Vertex g)) :
    I.record vs = .empty ↔ vs = [] := by
  constructor
  · intro hs
    by_cases h : vs = []
    · exact h
    · obtain ⟨a, b, _, _, hab, _⟩ := I.record_extrema h
      have bad := hab.symm.trans hs
      cases bad
  · rintro rfl
    rfl

theorem endpointsInside_record_iff {vs : List (Vertex g)}
    (hr : AllReach r vs) (d : Vertex g) :
    endpointsInside (I.rank d).val (I.tout d) (I.record vs) = true ↔
      g.CommonDominator r vs d := by
  rw [record, endpointsInside_summary_iff]
  constructor
  · intro h v hv
    exact (I.dominates_iff_interval d v (hr v hv)).mpr
      (h _ (List.mem_map.mpr ⟨v, hv, rfl⟩))
  · intro h k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
    exact (I.dominates_iff_interval d v (hr v hv)).mp (h v hv)

/-- The two endpoints and the entire physical-tail list have the same
common-dominator predicate, including when the two endpoints coincide. -/
theorem commonDominator_eq_extrema {vs : List (Vertex g)} {a b : Vertex g}
    (hr : AllReach r vs) (ha : a ∈ vs) (hb : b ∈ vs)
    (hord : (I.rank a).val ≤ (I.rank b).val)
    (hs : I.record vs = .span (I.rank a).val (I.rank b).val) :
    g.CommonDominator r vs = g.CommonDominator r [a, b] := by
  funext d
  apply propext
  rw [← I.endpointsInside_record_iff hr d, hs, endpointsInside_span_iff,
    common_pair_iff a b d,
    I.dominates_iff_interval d a (hr a ha),
    I.dominates_iff_interval d b (hr b hb)]
  constructor
  · rintro ⟨hl, hh⟩
    exact ⟨⟨hl, Nat.lt_of_le_of_lt hord hh⟩, ⟨Nat.le_trans hl hord, hh⟩⟩
  · rintro ⟨⟨hl, _⟩, ⟨_, hh⟩⟩
    exact ⟨hl, hh⟩

theorem dominatorLCA_eq_extrema (hacyc : g.IsAcyclic)
    {vs : List (Vertex g)} {a b : Vertex g}
    (hne : vs ≠ []) (hr : AllReach r vs) (ha : a ∈ vs) (hb : b ∈ vs)
    (hord : (I.rank a).val ≤ (I.rank b).val)
    (hs : I.record vs = .span (I.rank a).val (I.rank b).val) :
    g.dominatorLCA r vs hacyc hne hr =
      g.dominatorLCA r [a, b] hacyc (by simp) (pairReach (hr a ha) (hr b hb)) := by
  have hCD := I.commonDominator_eq_extrema hr ha hb hord hs
  have hl := dominatorLCA_spec hacyc hne hr
  have hp : g.IsDominatorLCA r [a, b] (g.dominatorLCA r vs hacyc hne hr) := by
    unfold IsDominatorLCA at hl ⊢
    rw [← hCD]
    exact hl
  exact eq_dominatorLCA_of_isDominatorLCA hacyc (by simp)
    (pairReach (hr a ha) (hr b hb)) hp

/-- Decode endpoints in minimum-then-maximum order. The out-of-range
branches cannot occur on a recorded span. -/
def read : Interval → List (Vertex g)
  | .empty => []
  | .span lo hi =>
    if hl : lo < g.vertexCount then
      if hh : hi < g.vertexCount then [I.unrank ⟨lo, hl⟩, I.unrank ⟨hi, hh⟩]
      else []
    else []

theorem read_span_of_ranks (a b : Vertex g) :
    I.read (.span (I.rank a).val (I.rank b).val) = [a, b] := by
  simp only [read, dif_pos (I.rank a).isLt, dif_pos (I.rank b).isLt]
  change [I.unrank (I.rank a), I.unrank (I.rank b)] = [a, b]
  simp only [I.unrank_rank]

theorem read_record_spec {vs : List (Vertex g)} (hr : AllReach r vs) :
    AllReach r (I.read (I.record vs)) ∧
      (I.read (I.record vs) = [] ↔ vs = []) ∧
      ∀ d, g.CommonDominator r (I.read (I.record vs)) d ↔
        g.CommonDominator r vs d := by
  by_cases hne : vs = []
  · subst vs
    simp [record, read, AllReach]
  · obtain ⟨a, b, ha, hb, hs, hbounds⟩ := I.record_extrema hne
    have hread := (congrArg I.read hs).trans (I.read_span_of_ranks a b)
    have hCD := I.commonDominator_eq_extrema hr ha hb (hbounds b hb).1 hs
    rw [hread]
    refine ⟨pairReach (hr a ha) (hr b hb), by simp [hne], ?_⟩
    intro d
    rw [hCD]

end DFSIndex

abbrev Result (g : Digraph) (r : Vertex g) :=
  Option {v : Vertex g // g.InitiallyReachable r v}

def Holds (d : Vertex g) : Result g r → Prop
  | none => True
  | some v => g.Dominates r d v.val

noncomputable def reachedLCA (hacyc : g.IsAcyclic)
    (vs : List (Vertex g)) (hne : vs ≠ []) (hr : AllReach r vs) :
    {v : Vertex g // g.InitiallyReachable r v} :=
  ⟨g.dominatorLCA r vs hacyc hne hr, by
    cases vs with
    | nil => exact False.elim (hne rfl)
    | cons v vs =>
      have hm : v ∈ v :: vs := List.mem_cons.mpr (Or.inl rfl)
      exact initiallyReachable_of_dominates (hr v hm)
        ((dominatorLCA_spec hacyc hne hr).1 v hm)⟩

noncomputable def listLCA (hacyc : g.IsAcyclic) :
    (vs : List (Vertex g)) → AllReach r vs → Result g r
  | [], _ => none
  | v :: vs, hr => some (reachedLCA hacyc (v :: vs) (by simp) hr)

@[simp] theorem listLCA_eq_none (hacyc : g.IsAcyclic)
    (vs : List (Vertex g)) (hr : AllReach r vs) :
    listLCA hacyc vs hr = none ↔ vs = [] := by
  cases vs <;> simp [listLCA]

theorem listLCA_spec (hacyc : g.IsAcyclic) (vs : List (Vertex g))
    (hr : AllReach r vs) (d : Vertex g) :
    Holds d (listLCA hacyc vs hr) ↔ g.CommonDominator r vs d := by
  cases vs with
  | nil => simp [listLCA, Holds, CommonDominator]
  | cons v vs =>
    exact (all_tail_dominates_iff_dominates_lca (d := d)
      hacyc (vs := v :: vs) (by simp) hr).symm

/-- The empty tag is tested separately: domination tests alone need not
distinguish `none` from a vertex dominated by every vertex. -/
theorem result_eq_of_tests (hacyc : g.IsAcyclic) {x y : Result g r}
    (he : x = none ↔ y = none) (hd : ∀ d, Holds d x ↔ Holds d y) : x = y := by
  cases x with
  | none => exact (he.mp rfl).symm
  | some a =>
    cases y with
    | none => exact he.mpr rfl
    | some b =>
      have hb : g.IsDominatorLCA r [a.val] b.val := by
        constructor
        · intro v hv
          have hv' : v = a.val := by simpa using hv
          subst v
          exact (hd b.val).mpr dominates_refl
        · intro d hc
          exact (hd d).mp (hc a.val (by simp))
      have hr : AllReach r [a.val] := by
        intro v hv
        have hv' : v = a.val := by simpa using hv
        subst v
        exact a.property
      have hba : b.val = a.val :=
        (eq_dominatorLCA_of_isDominatorLCA hacyc (by simp) hr hb).trans
          (dominatorLCA_singleton hacyc a.val (by simp) hr)
      have hab : a = b := Subtype.ext hba.symm
      exact congrArg some hab

noncomputable def lcaJoin (hacyc : g.IsAcyclic) :
    Result g r → Result g r → Result g r
  | none, y => y
  | x, none => x
  | some a, some b => listLCA hacyc [a.val, b.val] (pairReach a.property b.property)

@[simp] theorem lcaJoin_eq_none (hacyc : g.IsAcyclic) (x y : Result g r) :
    lcaJoin hacyc x y = none ↔ x = none ∧ y = none := by
  cases x <;> cases y <;> simp [lcaJoin, listLCA]

theorem holds_lcaJoin (hacyc : g.IsAcyclic) (d : Vertex g) (x y : Result g r) :
    Holds d (lcaJoin hacyc x y) ↔ Holds d x ∧ Holds d y := by
  cases x with
  | none => simp [lcaJoin, Holds]
  | some a =>
    cases y with
    | none => simp [lcaJoin, Holds]
    | some b =>
      change Holds d (listLCA hacyc [a.val, b.val] (pairReach a.property b.property)) ↔
        g.Dominates r d a.val ∧ g.Dominates r d b.val
      exact (listLCA_spec hacyc _ _ d).trans (common_pair_iff a.val b.val d)

theorem lcaJoin_assoc (hacyc : g.IsAcyclic) (x y z : Result g r) :
    lcaJoin hacyc (lcaJoin hacyc x y) z = lcaJoin hacyc x (lcaJoin hacyc y z) := by
  apply result_eq_of_tests hacyc
  · simp only [lcaJoin_eq_none, and_assoc]
  · intro d
    simp only [holds_lcaJoin, and_assoc]

theorem lcaJoin_comm (hacyc : g.IsAcyclic) (x y : Result g r) :
    lcaJoin hacyc x y = lcaJoin hacyc y x := by
  apply result_eq_of_tests hacyc
  · simpa only [lcaJoin_eq_none] using
      (and_comm : (x = none ∧ y = none) ↔ (y = none ∧ x = none))
  · intro d
    simpa only [holds_lcaJoin] using
      (and_comm : (Holds d x ∧ Holds d y) ↔ (Holds d y ∧ Holds d x))

theorem listLCA_append (hacyc : g.IsAcyclic) (xs ys : List (Vertex g))
    (hx : AllReach r xs) (hy : AllReach r ys) :
    listLCA hacyc (xs ++ ys) (appendReach hx hy) =
      lcaJoin hacyc (listLCA hacyc xs hx) (listLCA hacyc ys hy) := by
  apply result_eq_of_tests hacyc
  · simp only [listLCA_eq_none, lcaJoin_eq_none]
    cases xs <;> simp
  · intro d
    simp only [holds_lcaJoin, listLCA_spec]
    constructor
    · intro h
      exact ⟨fun v hv => h v (List.mem_append.mpr (Or.inl hv)),
        fun v hv => h v (List.mem_append.mpr (Or.inr hv))⟩
    · rintro ⟨hx', hy'⟩ v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hx' v hv
      · exact hy' v hv

namespace DFSIndex

variable (I : DFSIndex g r)

/-- Only intervals actually recorded from reachable physical tails are
admitted to the refinement. In particular, a malformed span is not empty. -/
def Valid (s : Interval) : Prop :=
  ∃ vs : List (Vertex g), AllReach r vs ∧ I.record vs = s

theorem valid_record {vs : List (Vertex g)} (hr : AllReach r vs) :
    I.Valid (I.record vs) :=
  ⟨vs, hr, rfl⟩

theorem valid_empty : I.Valid .empty :=
  ⟨[], by simp [AllReach], rfl⟩

theorem valid_join {a b : Interval} (ha : I.Valid a) (hb : I.Valid b) :
    I.Valid (Interval.join a b) := by
  obtain ⟨xs, hx, hxs⟩ := ha
  obtain ⟨ys, hy, hys⟩ := hb
  subst a
  subst b
  exact ⟨xs ++ ys, appendReach hx hy, I.record_append xs ys⟩

theorem read_reachable {s : Interval} (hs : I.Valid s) :
    AllReach r (I.read s) := by
  obtain ⟨vs, hr, he⟩ := hs
  subst s
  exact (I.read_record_spec hr).1

noncomputable def decode (hacyc : g.IsAcyclic) (s : Interval) (hs : I.Valid s) :
    Result g r :=
  listLCA hacyc (I.read s) (I.read_reachable hs)

theorem decode_congr (hacyc : g.IsAcyclic) {s t : Interval}
    (h : s = t) (hs : I.Valid s) (ht : I.Valid t) :
    I.decode hacyc s hs = I.decode hacyc t ht := by
  subst t
  rfl

theorem decode_record (hacyc : g.IsAcyclic) {vs : List (Vertex g)}
    (hr : AllReach r vs) (hs : I.Valid (I.record vs)) :
    I.decode hacyc (I.record vs) hs = listLCA hacyc vs hr := by
  have h := I.read_record_spec hr
  apply result_eq_of_tests hacyc
  · simpa only [decode, listLCA_eq_none] using h.2.1
  · intro d
    simpa only [decode, listLCA_spec] using h.2.2 d

@[simp] theorem decode_eq_none (hacyc : g.IsAcyclic) (s : Interval)
    (hs : I.Valid s) : I.decode hacyc s hs = none ↔ s = .empty := by
  have hs' := hs
  obtain ⟨vs, hr, he⟩ := hs'
  subst s
  rw [I.decode_record hacyc hr hs, listLCA_eq_none, I.record_eq_empty_iff]

/-- Merging recorded min-max intervals refines the semantic LCA join. -/
theorem decode_join (hacyc : g.IsAcyclic) {a b : Interval}
    (ha : I.Valid a) (hb : I.Valid b) (hj : I.Valid (Interval.join a b)) :
    I.decode hacyc (Interval.join a b) hj =
      lcaJoin hacyc (I.decode hacyc a ha) (I.decode hacyc b hb) := by
  have ha' := ha
  have hb' := hb
  obtain ⟨xs, hx, hxs⟩ := ha'
  obtain ⟨ys, hy, hys⟩ := hb'
  subst a
  subst b
  have hxy := appendReach hx hy
  calc
    _ = I.decode hacyc (I.record (xs ++ ys)) (I.valid_record hxy) :=
      I.decode_congr hacyc (I.record_append xs ys).symm hj _
    _ = listLCA hacyc (xs ++ ys) hxy :=
      I.decode_record hacyc hxy _
    _ = lcaJoin hacyc (listLCA hacyc xs hx) (listLCA hacyc ys hy) :=
      listLCA_append hacyc xs ys hx hy
    _ = _ := by rw [I.decode_record hacyc hx ha, I.decode_record hacyc hy hb]

def ValidValues (xs : Values) : Prop :=
  ∀ i : Fin 2, I.Valid (Two.get xs i)

def ValidMap (m : Map) : Prop :=
  ∀ i : Fin 2, I.Valid (Two.get m i).base

theorem valid_coord_eval {c : Coord} {xs : Values} (hc : I.Valid c.base)
    (hx : I.ValidValues xs) : I.Valid (Coord.eval c xs) := by
  cases c with
  | mk base slot =>
    cases slot with
    | none => exact hc
    | some j => exact I.valid_join hc (hx j)

theorem valid_eval {m : Map} {xs : Values} (hm : I.ValidMap m)
    (hx : I.ValidValues xs) : I.ValidValues (Map.eval m xs) := by
  intro i
  simpa only [Map.eval, Two.get_map] using I.valid_coord_eval (hm i) hx

theorem valid_compose {inner outer : Map} (hi : I.ValidMap inner)
    (ho : I.ValidMap outer) : I.ValidMap (Map.compose inner outer) := by
  intro i
  rw [Map.compose, Two.get_map]
  cases hslot : (Two.get outer i).slot with
  | none => simpa only [Coord.compose, hslot] using ho i
  | some j =>
    simpa only [Coord.compose, hslot] using I.valid_join (ho i) (hi j)

noncomputable def evalLcaCoord (hacyc : g.IsAcyclic) (c : Coord)
    (hc : I.Valid c.base) (xs : Fin 2 → Result g r) : Result g r :=
  match c.slot with
  | none => I.decode hacyc c.base hc
  | some j => lcaJoin hacyc (I.decode hacyc c.base hc) (xs j)

noncomputable def evalLcaMap (hacyc : g.IsAcyclic) (m : Map)
    (hm : I.ValidMap m) (xs : Fin 2 → Result g r) (i : Fin 2) : Result g r :=
  I.evalLcaCoord hacyc (Two.get m i) (hm i) xs

theorem eval_coord_refines (hacyc : g.IsAcyclic) {c : Coord} {xs : Values}
    (hc : I.Valid c.base) (hx : I.ValidValues xs)
    (he : I.Valid (Coord.eval c xs)) :
    I.decode hacyc (Coord.eval c xs) he =
      I.evalLcaCoord hacyc c hc (fun j => I.decode hacyc (Two.get xs j) (hx j)) := by
  cases c with
  | mk base slot =>
    cases slot with
    | none => rfl
    | some j => exact I.decode_join hacyc hc (hx j) he

/-- The output coordinate is `i` on both sides; a copied input coordinate
is selected by its slot `j`, independently of `i`. -/
theorem eval_refines (hacyc : g.IsAcyclic) {m : Map} {xs : Values}
    (hm : I.ValidMap m) (hx : I.ValidValues xs) (i : Fin 2)
    (he : I.Valid (Two.get (Map.eval m xs) i)) :
    I.decode hacyc (Two.get (Map.eval m xs) i) he =
      I.evalLcaMap hacyc m hm (fun j => I.decode hacyc (Two.get xs j) (hx j)) i := by
  have hget : Two.get (Map.eval m xs) i = Coord.eval (Two.get m i) xs := by
    simp only [Map.eval, Two.get_map]
  calc
    _ = I.decode hacyc (Coord.eval (Two.get m i) xs) (I.valid_coord_eval (hm i) hx) :=
      I.decode_congr hacyc hget he _
    _ = _ := I.eval_coord_refines hacyc (hm i) hx _

/-- Composition runs inner first, then outer, at both ordered coordinates. -/
theorem eval_compose_refines (hacyc : g.IsAcyclic) {inner outer : Map}
    {xs : Values} (hi : I.ValidMap inner) (ho : I.ValidMap outer)
    (hx : I.ValidValues xs) (i : Fin 2) :
    I.decode hacyc (Two.get (Map.eval (Map.compose inner outer) xs) i)
        (I.valid_eval (I.valid_compose hi ho) hx i) =
      I.evalLcaMap hacyc outer ho
        (I.evalLcaMap hacyc inner hi (fun j => I.decode hacyc (Two.get xs j) (hx j))) i := by
  have hm := I.valid_eval hi hx
  calc
    _ = I.decode hacyc (Two.get (Map.eval outer (Map.eval inner xs)) i)
          (I.valid_eval ho hm i) :=
      I.decode_congr hacyc (Map.eval_compose_get inner outer xs i) _ _
    _ = I.evalLcaMap hacyc outer ho
          (fun j => I.decode hacyc (Two.get (Map.eval inner xs) j) (hm j)) i :=
      I.eval_refines hacyc ho hm i _
    _ = _ := by
      have hinner :
          (fun j => I.decode hacyc (Two.get (Map.eval inner xs) j) (hm j)) =
            I.evalLcaMap hacyc inner hi (fun j => I.decode hacyc (Two.get xs j) (hx j)) := by
        funext j
        exact I.eval_refines hacyc hi hx j (hm j)
      rw [hinner]

theorem evalLcaMap_compose (hacyc : g.IsAcyclic) {inner outer : Map}
    {xs : Values} (hi : I.ValidMap inner) (ho : I.ValidMap outer)
    (hx : I.ValidValues xs) :
    I.evalLcaMap hacyc (Map.compose inner outer) (I.valid_compose hi ho)
        (fun j => I.decode hacyc (Two.get xs j) (hx j)) =
      I.evalLcaMap hacyc outer ho
        (I.evalLcaMap hacyc inner hi (fun j => I.decode hacyc (Two.get xs j) (hx j))) := by
  funext i
  exact (I.eval_refines hacyc (I.valid_compose hi ho) hx i
    (I.valid_eval (I.valid_compose hi ho) hx i)).symm.trans
      (I.eval_compose_refines hacyc hi ho hx i)

end DFSIndex
end PaperB.Digraph.ExitLCABridge
