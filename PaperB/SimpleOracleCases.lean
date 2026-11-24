module

public import PaperB.Dom

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph.EX44

/-- An absent failure coordinate fails no vertex. A present coordinate
uses the original vertex ID. -/
def hit {V : Type} (p : Option V) (x : V) : Prop :=
  match p with
  | none => False
  | some a => x = a

private instance hitDecidable {V : Type} [DecidableEq V]
    (p : Option V) (x : V) : Decidable (hit p x) :=
  match p with
  | none => inferInstanceAs (Decidable False)
  | some a => inferInstanceAs (Decidable (x = a))

abbrev fails {V : Type} (p q : Option V) (x : V) : Prop :=
  hit p x ∨ hit q x

section Paths

variable {g : Digraph} {r v : Fin g.vertexCount}

theorem failed_source {failed : Fin g.vertexCount → Prop}
    (hr : failed r) : ¬ g.SurvivingPath failed r v :=
  fun path => AvoidPath.source_alive path hr

theorem initially_unreachable_target {failed : Fin g.vertexCount → Prop}
    (hv : ¬ g.InitiallyReachable r v) : ¬ g.SurvivingPath failed r v :=
  fun path => hv (initiallyReachable_of_survivingPath (g := g) path)

theorem failed_target {failed : Fin g.vertexCount → Prop}
    (hv : failed v) : ¬ g.SurvivingPath failed r v :=
  fun path => AvoidPath.target_alive path hv

theorem zero_failures :
    g.SurvivingPath (fails none none) r v ↔ g.InitiallyReachable r v := by
  change g.SurvivingPath (fun _ => False ∨ False) r v ↔
    g.SurvivingPath (fun _ => False) r v
  simp only [false_or]

theorem delete_one_iff_not_dominates (a : Fin g.vertexCount) :
    g.SurvivingPath (fun x => x = a) r v ↔ ¬ g.Dominates r a v := by
  change g.SurvivingPath (fun x => x = a) r v ↔
    ¬ ¬ g.SurvivingPath (fun x => x = a) r v
  exact ⟨fun path h => h path, fun h => Classical.byContradiction h⟩

theorem one_failure_left (a : Fin g.vertexCount) :
    g.SurvivingPath (fails (some a) none) r v ↔ ¬ g.Dominates r a v := by
  change g.SurvivingPath (fun x => x = a ∨ False) r v ↔ ¬ g.Dominates r a v
  simpa only [or_false] using delete_one_iff_not_dominates (g := g) (r := r) (v := v) a

theorem one_failure_right (a : Fin g.vertexCount) :
    g.SurvivingPath (fails none (some a)) r v ↔ ¬ g.Dominates r a v := by
  change g.SurvivingPath (fun x => False ∨ x = a) r v ↔ ¬ g.Dominates r a v
  simpa only [false_or] using delete_one_iff_not_dominates (g := g) (r := r) (v := v) a

/-- Carry a surviving source prefix to the head of each suffix. If that
head were `b`, the prefix itself would contradict `noPrefix`. -/
private theorem avoid_without_prefix {failed : Fin g.vertexCount → Prop}
    {u b : Fin g.vertexCount} (noPrefix : ¬ g.SurvivingPath failed r b)
    (path : g.SurvivingPath failed u v) :
    g.SurvivingPath failed r u →
      g.SurvivingPath (fun x => failed x ∨ x = b) u v := by
  induction path with
  | refl x alive =>
      intro hpre
      have hxb : x ≠ b := by
        intro he
        exact noPrefix (he ▸ hpre)
      exact AvoidPath.refl x (fun h => h.elim alive hxb)
  | step x y z alive arc tail ih =>
      intro hpre
      have hxb : x ≠ b := by
        intro he
        exact noPrefix (he ▸ hpre)
      have hy : ¬ failed y := AvoidPath.source_alive tail
      have last : g.SurvivingPath failed x y :=
        AvoidPath.step x y y alive arc (AvoidPath.refl y hy)
      have hpre' : g.SurvivingPath failed r y := AvoidPath.trans hpre last
      exact AvoidPath.step x y z (fun h => h.elim alive hxb) arc (ih hpre')

/-- The same source path can be certified to avoid `b` as well as `a`. -/
theorem avoids_dominated {a b : Fin g.vertexCount}
    (hab : g.Dominates r a b) (path : g.SurvivingPath (fun x => x = a) r v) :
    g.SurvivingPath (fails (some a) (some b)) r v := by
  have hr : ¬ (r = a) := by
    have sourceAlive {edge : Fin g.vertexCount → Fin g.vertexCount → Prop}
        (p : AvoidPath edge (fun x => x = a) r v) : ¬ (r = a) :=
      @AvoidPath.source_alive (Fin g.vertexCount) edge (fun x => x = a) r v p
    exact sourceAlive path
  have hpre : g.SurvivingPath (fun x => x = a) r r :=
    AvoidPath.refl r hr
  change g.SurvivingPath (fun x => x = a ∨ x = b) r v
  exact avoid_without_prefix (g := g) (r := r) (v := v) (b := b)
    (failed := fun x => x = a) hab path hpre

theorem pair_iff_delete_left {a b : Fin g.vertexCount} (hab : g.Dominates r a b) :
    g.SurvivingPath (fails (some a) (some b)) r v ↔
      g.SurvivingPath (fun x => x = a) r v := by
  constructor
  · intro path
    exact AvoidPath.mono path (fun _ h => Or.inl h)
  · exact avoids_dominated hab

theorem pair_iff_delete_right {a b : Fin g.vertexCount} (hba : g.Dominates r b a) :
    g.SurvivingPath (fails (some a) (some b)) r v ↔
      g.SurvivingPath (fun x => x = b) r v := by
  constructor
  · intro path
    exact AvoidPath.mono path (fun _ h => Or.inr h)
  · intro path
    have swapped := avoids_dominated hba path
    exact AvoidPath.mono swapped (fun _ h => h.elim Or.inr Or.inl)

/-- Neither ordering requires the original target to be retained, or the
two retained failures to be distinct. -/
theorem retained_comparable {a b : g.ReachableVertex r}
    (hab : g.Dominates r a.val b.val) :
    (g.SurvivingPath (fails (some a.val) (some b.val)) r v ↔
      g.SurvivingPath (fun x => x = a.val) r v) ∧
    (g.SurvivingPath (fails (some b.val) (some a.val)) r v ↔
      g.SurvivingPath (fun x => x = a.val) r v) :=
  ⟨pair_iff_delete_left hab, pair_iff_delete_right hab⟩

theorem duplicate_failure (a : Fin g.vertexCount) :
    g.SurvivingPath (fails (some a) (some a)) r v ↔
      g.SurvivingPath (fun x => x = a) r v :=
  pair_iff_delete_left (dominates_refl (g := g))

/-- Failure tests only need to agree, in the required direction, at vertices
that can be visited from the source. -/
private theorem mono_on_reachable {f₁ f₂ : Fin g.vertexCount → Prop}
    {u : Fin g.vertexCount}
    (imp : ∀ x, g.InitiallyReachable r x → f₂ x → f₁ x)
    (path : g.SurvivingPath f₁ u v) :
    g.InitiallyReachable r u → g.SurvivingPath f₂ u v := by
  induction path with
  | refl x alive =>
      intro hx
      exact AvoidPath.refl x (fun h => alive (imp x hx h))
  | step x y z alive arc _ ih =>
      intro hx
      have hy := initiallyReachable_extend (g := g) (r := r) hx arc
      exact AvoidPath.step x y z (fun h => alive (imp x hx h)) arc (ih hy)

end Paths

section Filter

variable (g : Digraph) (r : Fin g.vertexCount)
variable [∀ x, Decidable (g.InitiallyReachable r x)]

/-- Discard an initially unreachable failure, without renumbering vertices. -/
def keep : Option (Fin g.vertexCount) → Option (Fin g.vertexCount)
  | none => none
  | some a => if g.InitiallyReachable r a then some a else none

private theorem hit_keep_iff (p : Option (Fin g.vertexCount))
    {x : Fin g.vertexCount} (hx : g.InitiallyReachable r x) :
    hit (keep g r p) x ↔ hit p x := by
  cases p with
  | none => exact Iff.rfl
  | some a =>
      by_cases ha : g.InitiallyReachable r a
      · simp only [keep, ite_eq_left ha]
      · have hxa : x ≠ a := fun he => ha (he ▸ hx)
        simpa only [keep, ite_eq_right ha, hit] using
          (show False ↔ x = a from ⟨False.elim, hxa⟩)

theorem keep_path_iff (v : Fin g.vertexCount) (p q : Option (Fin g.vertexCount)) :
    g.SurvivingPath (fails (keep g r p) (keep g r q)) r v ↔
      g.SurvivingPath (fails p q) r v := by
  have agree (x : Fin g.vertexCount) (hx : g.InitiallyReachable r x) :
      fails (keep g r p) (keep g r q) x ↔ fails p q x :=
    or_congr (hit_keep_iff g r p hx) (hit_keep_iff g r q hx)
  exact ⟨fun path => mono_on_reachable (fun x hx => (agree x hx).mpr)
      path (initiallyReachable_source g r),
    fun path => mono_on_reachable (fun x hx => (agree x hx).mp)
      path (initiallyReachable_source g r)⟩

end Filter

/-- `none` makes no claim; a Boolean answer must agree with the query. -/
def Checked (P : Prop) : Option Bool → Prop
  | none => True
  | some answer => answer = true ↔ P

private theorem checked_false {P : Prop} (h : ¬ P) : Checked P (some false) := by
  simp [Checked, h]

private theorem checked_decide {P Q : Prop} [Decidable P] (h : P ↔ Q) :
    Checked Q (some (decide P)) := by
  change (decide P = true) ↔ Q
  exact ⟨fun ht => h.mp (of_decide_eq_true ht), fun hq => decide_eq_true (h.mpr hq)⟩

private theorem checked_congr {P Q : Prop} {o : Option Bool} (h : P ↔ Q) :
    Checked P o → Checked Q o := by
  cases o with
  | none => exact id
  | some answer =>
      intro hp
      exact hp.trans h

section Decisions

variable (g : Digraph) (r v : Fin g.vertexCount)
variable [∀ x, Decidable (g.InitiallyReachable r x)]
variable [∀ a b, Decidable (g.Dominates r a b)]

/-- The target has already passed the initial reachability test. -/
private def reducedDecision : Option (Fin g.vertexCount) →
    Option (Fin g.vertexCount) → Option Bool
  | none, none => some true
  | some a, none => some (decide (¬ g.Dominates r a v))
  | none, some b => some (decide (¬ g.Dominates r b v))
  | some a, some b =>
      if g.Dominates r a b then some (decide (¬ g.Dominates r a v))
      else if g.Dominates r b a then some (decide (¬ g.Dominates r b v))
      else none

omit [∀ x, Decidable (g.InitiallyReachable r x)] in
private theorem reducedDecision_checked (hv : g.InitiallyReachable r v)
    (p q : Option (Fin g.vertexCount)) :
    Checked (g.SurvivingPath (fails p q) r v) (reducedDecision g r v p q) := by
  cases p with
  | none =>
      cases q with
      | none =>
          exact ⟨fun _ => (zero_failures (g := g)).mpr hv, fun _ => rfl⟩
      | some b =>
          exact checked_decide (one_failure_right (g := g) (r := r) (v := v) b).symm
  | some a =>
      cases q with
      | none =>
          exact checked_decide (one_failure_left (g := g) (r := r) (v := v) a).symm
      | some b =>
          by_cases hab : g.Dominates r a b
          · have h := (pair_iff_delete_left (v := v) hab).trans
                (delete_one_iff_not_dominates (g := g) (r := r) (v := v) a)
            simpa only [reducedDecision, ite_eq_left hab] using checked_decide h.symm
          · by_cases hba : g.Dominates r b a
            · have h := (pair_iff_delete_right (v := v) hba).trans
                  (delete_one_iff_not_dominates (g := g) (r := r) (v := v) b)
              simpa only [reducedDecision, ite_eq_right hab, ite_eq_left hba] using checked_decide h.symm
            · simp only [reducedDecision, ite_eq_right hab, ite_eq_right hba, Checked]

/-- Run the endpoint and initial-reachability checks, then discard
unreachable failures and try the zero-, one-, or comparable-failure case. -/
def earlyDecision (p q : Option (Fin g.vertexCount)) : Option Bool :=
  if fails p q r then some false
  else if g.InitiallyReachable r v then
    if fails p q v then some false
    else reducedDecision g r v (keep g r p) (keep g r q)
  else some false

theorem earlyDecision_checked (p q : Option (Fin g.vertexCount)) :
    Checked (g.SurvivingPath (fails p q) r v) (earlyDecision g r v p q) := by
  by_cases hs : fails p q r
  · simpa only [earlyDecision, ite_eq_left hs] using
      checked_false (failed_source (g := g) (v := v) hs)
  · by_cases hv : g.InitiallyReachable r v
    · by_cases ht : fails p q v
      · simpa only [earlyDecision, ite_eq_right hs, ite_eq_left hv, ite_eq_left ht] using
          checked_false (failed_target (g := g) (r := r) ht)
      · simpa only [earlyDecision, ite_eq_right hs, ite_eq_left hv, ite_eq_right ht] using
          checked_congr (keep_path_iff g r v p q)
            (reducedDecision_checked g r v hv (keep g r p) (keep g r q))
    · simpa only [earlyDecision, ite_eq_right hs, ite_eq_right hv] using
        checked_false (initially_unreachable_target (failed := fails p q) hv)

theorem earlyDecision_correct (p q : Option (Fin g.vertexCount)) {answer : Bool}
    (h : earlyDecision g r v p q = some answer) :
    answer = true ↔ g.SurvivingPath (fails p q) r v := by
  have hc := earlyDecision_checked g r v p q
  rw [h] at hc
  exact hc

end Decisions

end PaperB.Digraph.EX44
