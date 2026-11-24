module

public import PaperB.OracleRuntime
public import PaperB.LastExitPaper
public import PaperB.SimpleOracleCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Append this block after the supplied runtime.
namespace PaperB.EX44

open PaperB.Digraph PaperB.Digraph.EX44

variable {N n k B E : Nat} {g : PaperB.Digraph}

theorem work_append (xs ys : List Event) :
    work (xs ++ ys) = work xs + work ys := by
  induction xs with
  | nil => simp [work]
  | cons x xs ih => simp [work, ih, Nat.add_assoc]

theorem slowCalls_append (xs ys : List Event) :
    slowCalls (xs ++ ys) = slowCalls xs + slowCalls ys := by
  induction xs with
  | nil => simp [slowCalls]
  | cons x xs ih => simp [slowCalls, ih, Nat.add_assoc]

theorem Plan.bounds_then {α β : Type} {f s f' s' : Nat}
    (R : Runtime N n k B E) (p : Plan N n k α f s)
    (next : α → Plan N n k β f' s') :
    let r := p.run R
    let z := (next r.value).run R
    let es := r.events ++ z.events
    es.length ≤ (f + f') + (s + s') ∧
    slowCalls es ≤ s + s' ∧
    work es ≤ (f + f') * B + (s + s') * E := by
  dsimp only
  obtain ⟨h₁, h₂, h₃⟩ := Plan.bounds R p
  obtain ⟨j₁, j₂, j₃⟩ := Plan.bounds R (next (p.run R).value)
  simp only [List.length_append, slowCalls_append, work_append, Nat.add_mul]
  exact ⟨by omega, by omega, by omega⟩

theorem query_bounds (R : Runtime N n k B E) (p q : Option (Fin N))
    (t : Fin N) :
    (query R p q t).events.length ≤ 16 ∧
    slowCalls (query R p q t).events ≤ 1 ∧
    work (query R p q t).events ≤ 15 * B + E := by
  have h := Plan.bounds_then R (route R.source p q t) answer
  change (query R p q t).events.length ≤ 16 ∧
    slowCalls (query R p q t).events ≤ 1 ∧
    work (query R p q t).events ≤ 15 * B + 1 * E at h
  simpa only [Nat.one_mul] using h

structure World (g : PaperB.Digraph) (n : Nat) where
  vertex : Fin n → Fin g.vertexCount
  entry : Fin n → Nat
  last : Fin n → Nat

def World.Inside (W : World g n) (a x : Fin n) : Prop :=
  W.entry a ≤ W.entry x ∧ W.entry x ≤ W.last a

structure Contracts (R : Runtime N n k B E) (W : World g n) : Prop where
  ancestor : ∀ a x, (R.ancestor a x).value = true ↔ W.Inside a x

def SpanExact (entry : Fin n → Nat) (X : Fin n → Prop) : Span n → Prop
  | none => ∀ x, ¬ X x
  | some (lo, hi) =>
      X lo ∧ X hi ∧ ∀ x, X x → entry lo ≤ entry x ∧ entry x ≤ entry hi

abbrev Goal (R : Runtime g.vertexCount n k B E) (W : World g n)
    (p q : Option (Fin g.vertexCount)) (t : Fin g.vertexCount) : Prop :=
  g.SurvivingPath (Fails p q) (W.vertex R.source) t

abbrev requested (R : Runtime N n k B E) (y : Fin n) (hit : Hit k) :
    Span n × Span n :=
  hit.orientation.order (R.exitExtrema hit.key y).value

/-- The builder grants the last-exit reduction and exact summaries of its
two witness sets, in requested rather than storage order. -/
def ExitGrant (R : Runtime N n k B E) (W : World g n) (P : Prop)
    (d u v a b y : Fin n) (hit : Hit k) : Prop :=
  (R.pairKey d u v).value = some hit ∧
  (R.pairMember hit.key y).value = true ∧
  ∃ X Y : Fin n → Prop,
    SpanExact W.entry X (requested R y hit).1 ∧
    SpanExact W.entry Y (requested R y hit).2 ∧
    (P ↔ (∃ x, X x ∧ ¬ W.Inside a x) ∨
         (∃ x, Y x ∧ ¬ W.Inside b x))

def LeafContract (R : Runtime g.vertexCount n k B E) (W : World g n)
    (p q : Option (Fin g.vertexCount)) (t : Fin g.vertexCount) :
    Leaf n k → Prop
  | .failedSource | .unreachableTarget | .failedTarget => ¬ Goal R W p q t
  | .zero | .outside | .thirdMissing | .thirdNonmember => Goal R W p q t
  | .malformed => False
  | .oneFirst a x | .oneSecond a x
  | .comparableLeft a x | .comparableRight a x
  | .withinLeft a x | .withinRight a x =>
      Goal R W p q t ↔ ¬ W.Inside a x
  | .thirdExits d u v a b y hit =>
      ExitGrant R W (Goal R W p q t) d u v a b y hit

/-- The one-unreachable projection of `LastExitPaper.last_exit_test`,
transported to the retained interval lookup. -/
theorem oneFirst_contract_of_last_exit
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (a x : Fin n) (z : Fin g.vertexCount)
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (acyclic : g.IsAcyclic)
    (progress : ∀ u v, g.HasArc u v → rank u < rank v)
    (injective : ∀ ⦃u v⦄, rank u = rank v → u = v)
    (spec : ParentSpec g (W.vertex R.source) parent)
    (haz : ¬ Ancestor parent (W.vertex a) z)
    (hza : ¬ Ancestor parent z (W.vertex a))
    (hz : ¬ g.InitiallyReachable (W.vertex R.source) z)
    (dom : g.Dominates (W.vertex R.source) (W.vertex a) (W.vertex x) ↔
      W.Inside a x) :
    LeafContract R W (some (W.vertex a)) (some z) (W.vertex x)
      (.oneFirst a x) := by
  have h := (last_exit_test (rank := rank) acyclic progress injective
    spec haz hza).2.1 hz (W.vertex x)
  have hFails : Fails (some (W.vertex a)) (some z) =
      (fun v : Fin g.vertexCount => v = W.vertex a ∨ v = z) := by
    funext v
    apply propext
    simp [Fails, eq_comm]
  change g.SurvivingPath (Fails (some (W.vertex a)) (some z))
      (W.vertex R.source) (W.vertex x) ↔ ¬ W.Inside a x
  rw [hFails]
  simpa only [Fails, Option.some.injEq, dom] using h

private theorem negBit {b : Bool} {P : Prop} (h : b = true ↔ P) :
    (!b) = true ↔ ¬ P := by
  cases b <;> simp_all

private theorem orBit (a b : Bool) :
    (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

def spanBit (R : Runtime N n k B E) (a : Fin n) : Span n → Bool
  | none => false
  | some (lo, hi) => !(R.ancestor a lo).value || !(R.ancestor a hi).value

theorem testSpan_run {α : Type} {f s : Nat}
    (R : Runtime N n k B E) (a : Fin n) (span : Span n)
    (next : Bool → Plan N n k α f s) :
    ((testSpan a span next).run R).value =
      ((next (spanBit R a span)).run R).value := by
  cases span with
  | none => rfl
  | some ends => cases ends <;> rfl

theorem spanBit_correct {R : Runtime N n k B E} {W : World g n}
    (C : Contracts R W) (a : Fin n) (span : Span n) (X : Fin n → Prop)
    (h : SpanExact W.entry X span) :
    spanBit R a span = true ↔ ∃ x, X x ∧ ¬ W.Inside a x := by
  cases span with
  | none =>
    change (∀ x, ¬ X x) at h
    change false = true ↔ _
    constructor
    · intro bad
      cases bad
    · rintro ⟨x, hx, _⟩
      exact (h x hx).elim
  | some ends =>
    rcases ends with ⟨lo, hi⟩
    change X lo ∧ X hi ∧
      (∀ x, X x → W.entry lo ≤ W.entry x ∧ W.entry x ≤ W.entry hi) at h
    obtain ⟨hlo, hhi, bounds⟩ := h
    change (!(R.ancestor a lo).value || !(R.ancestor a hi).value) = true ↔ _
    rw [orBit, negBit (C.ancestor a lo), negBit (C.ancestor a hi)]
    constructor
    · rintro (hl | hh)
      · exact ⟨lo, hlo, hl⟩
      · exact ⟨hi, hhi, hh⟩
    · rintro ⟨x, hx, hout⟩
      by_cases hl : W.Inside a lo
      · right
        intro hh
        exact hout ⟨Nat.le_trans hl.1 (bounds x hx).1,
          Nat.le_trans (bounds x hx).2 hh.2⟩
      · exact Or.inl hl

private theorem testOne_correct {R : Runtime N n k B E} {W : World g n}
    (C : Contracts R W) (a x : Fin n) :
    ((testOne a x).run R).value = true ↔ ¬ W.Inside a x :=
  negBit (C.ancestor a x)

private theorem stopFalse_correct (R : Runtime N n k B E) {P : Prop}
    (h : ¬ P) :
    ((Plan.stop false : Plan N n k Bool 4 1).run R).value = true ↔ P := by
  simp [h]

private theorem stopTrue_correct (R : Runtime N n k B E) {P : Prop}
    (h : P) :
    ((Plan.stop true : Plan N n k Bool 4 1).run R).value = true ↔ P := by
  simp [h]

/-- Local to a granted leaf. Neither selection nor construction of the
last-exit witness sets is a premise proved by the answer stage. -/
theorem answer_correct {R : Runtime g.vertexCount n k B E} {W : World g n}
    (C : Contracts R W) {p q : Option (Fin g.vertexCount)}
    {t : Fin g.vertexCount} (l : Leaf n k) (h : LeafContract R W p q t l) :
    ((answer l).run R).value = true ↔ Goal R W p q t := by
  cases l with
  | malformed => exact False.elim (show False from h)
  | thirdExits d u v a b y hit =>
    change ExitGrant R W (Goal R W p q t) d u v a b y hit at h
    rcases h with ⟨_, _, X, Y, hX, hY, sem⟩
    let s := requested R y hit
    change ((testSpan a s.1 fun left => testSpan b s.2 fun right =>
      .done (left || right)).run R).value = true ↔ _
    rw [testSpan_run, testSpan_run]
    change (spanBit R a s.1 || spanBit R b s.2) = true ↔ _
    rw [orBit, spanBit_correct C a s.1 X hX, spanBit_correct C b s.2 Y hY]
    exact sem.symm
  | _ =>
    first
    | exact stopFalse_correct R h
    | exact stopTrue_correct R h
    | exact (testOne_correct C _ _).trans (Iff.symm h)

end PaperB.EX44
