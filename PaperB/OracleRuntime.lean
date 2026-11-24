module

public import Std
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.EX44

/-!
The query program takes retained index reads and the original query slots.

A debit in `Sample` is a primitive's work charge. A compiled implementation
must justify that charge in its machine model. The query has at most 15
ordinary calls and one extrema call. Thus logarithmic primitive bounds give
a logarithmic query bound. With the paper's cubic-logarithmic bound for the
extrema call, the corresponding bound for this query is cubic-logarithmic.
-/

variable {N n k B E : Nat}

inductive Orientation where
  | direct
  | reversed
  deriving DecidableEq, Repr

def Orientation.order {α : Type} (o : Orientation) (p : α × α) : α × α :=
  match o with
  | .direct => p
  | .reversed => (p.2, p.1)

structure Hit (k : Nat) where
  key : Fin k
  orientation : Orientation
  deriving DecidableEq, Repr

/-- The first and last DFS-entry witnesses for one exit coordinate. -/
abbrev Span (n : Nat) := Option (Fin n × Fin n)

structure Sample (cap : Nat) (α : Type) where
  value : α
  debit : Nat
  bounded : debit ≤ cap

structure Runtime (N n k B E : Nat) where
  source : Fin n
  translate : Fin N → Sample B (Option (Fin n))
  ancestor : Fin n → Fin n → Sample B Bool
  lca : Fin n → Fin n → Sample B (Fin n)
  childBelow : Fin n → Fin n → Sample B (Option (Fin n))
  pairKey : Fin n → Fin n → Fin n → Sample B (Option (Hit k))
  pairMember : Fin k → Fin n → Sample B Bool
  exitExtrema : Fin k → Fin n → Sample E (Span n × Span n)

inductive Kind where
  | translate | ancestor | lca | child | key | member | extrema
  deriving DecidableEq, Repr

inductive Fast (N n k : Nat) : Type → Type where
  | translate (i : Fin N) : Fast N n k (Option (Fin n))
  | ancestor (a t : Fin n) : Fast N n k Bool
  | lca (a b : Fin n) : Fast N n k (Fin n)
  | child (d t : Fin n) : Fast N n k (Option (Fin n))
  | key (d u v : Fin n) : Fast N n k (Option (Hit k))
  | member (p : Fin k) (y : Fin n) : Fast N n k Bool

def Fast.kind {α : Type} : Fast N n k α → Kind
  | .translate _ => .translate
  | .ancestor _ _ => .ancestor
  | .lca _ _ => .lca
  | .child _ _ => .child
  | .key _ _ _ => .key
  | .member _ _ => .member

def Runtime.fetch (R : Runtime N n k B E) {α : Type} :
    Fast N n k α → Sample B α
  | .translate i => R.translate i
  | .ancestor a t => R.ancestor a t
  | .lca a b => R.lca a b
  | .child d t => R.childBelow d t
  | .key d u v => R.pairKey d u v
  | .member p y => R.pairMember p y

/-- Grades bound ordinary calls and extrema calls separately. -/
inductive Plan (N n k : Nat) (α : Type) : Nat → Nat → Type 1 where
  | done (x : α) : Plan N n k α 0 0
  | widen {f s f' s' : Nat} (hf : f ≤ f') (hs : s ≤ s')
      (p : Plan N n k α f s) : Plan N n k α f' s'
  | fast {β : Type} {f s : Nat} (op : Fast N n k β)
      (next : β → Plan N n k α f s) : Plan N n k α (f + 1) s
  | extrema {f s : Nat} (p : Fin k) (y : Fin n)
      (next : (Span n × Span n) → Plan N n k α f s) :
      Plan N n k α f (s + 1)

def Plan.stop {α : Type} {f s : Nat} (x : α) : Plan N n k α f s :=
  .widen (Nat.zero_le f) (Nat.zero_le s) (.done x)

structure Event where
  kind : Kind
  debit : Nat
  deriving Repr

def work : List Event → Nat
  | [] => 0
  | e :: es => e.debit + work es

def Kind.slow : Kind → Nat
  | .extrema => 1
  | _ => 0

def slowCalls : List Event → Nat
  | [] => 0
  | e :: es => e.kind.slow + slowCalls es

@[simp] theorem Fast.kind_slow {α : Type} (op : Fast N n k α) :
    op.kind.slow = 0 := by
  cases op <;> rfl

structure Run (α : Type) where
  value : α
  events : List Event

def Plan.run {α : Type} (R : Runtime N n k B E) {f s : Nat} :
    Plan N n k α f s → Run α
  | .done x => ⟨x, []⟩
  | .widen _ _ p => p.run R
  | .fast op next =>
      let a := R.fetch op
      let r := (next a.value).run R
      ⟨r.value, ⟨op.kind, a.debit⟩ :: r.events⟩
  | .extrema p y next =>
      let a := R.exitExtrema p y
      let r := (next a.value).run R
      ⟨r.value, ⟨.extrema, a.debit⟩ :: r.events⟩

@[simp] theorem Plan.stop_value {α : Type} {f s : Nat}
    (R : Runtime N n k B E) (x : α) :
    ((Plan.stop x : Plan N n k α f s).run R).value = x := rfl

@[simp] theorem Plan.fast_value {α β : Type} {f s : Nat}
    (R : Runtime N n k B E) (op : Fast N n k β)
    (next : β → Plan N n k α f s) :
    ((Plan.fast op next).run R).value =
      ((next (R.fetch op).value).run R).value := rfl

@[simp] theorem Plan.extrema_value {α : Type} {f s : Nat}
    (R : Runtime N n k B E) (p : Fin k) (y : Fin n)
    (next : (Span n × Span n) → Plan N n k α f s) :
    ((Plan.extrema p y next).run R).value =
      ((next (R.exitExtrema p y).value).run R).value := rfl

theorem Plan.bounds {α : Type} {f s : Nat} (R : Runtime N n k B E)
    (p : Plan N n k α f s) :
    (p.run R).events.length ≤ f + s ∧
    slowCalls (p.run R).events ≤ s ∧
    work (p.run R).events ≤ f * B + s * E := by
  induction p with
  | done x => simp [Plan.run, slowCalls, work]
  | widen hf hs p ih =>
      exact ⟨Nat.le_trans ih.1 (Nat.add_le_add hf hs),
        Nat.le_trans ih.2.1 hs,
        Nat.le_trans ih.2.2
          (Nat.add_le_add (Nat.mul_le_mul_right B hf)
            (Nat.mul_le_mul_right E hs))⟩
  | fast op next ih =>
      obtain ⟨hl, hc, hw⟩ := ih (R.fetch op).value
      have hd := (R.fetch op).bounded
      simp only [Plan.run, List.length_cons, slowCalls, Fast.kind_slow,
        Nat.zero_add, work, Nat.add_mul, Nat.one_mul]
      exact ⟨by omega, hc, by omega⟩
  | extrema p y next ih =>
      obtain ⟨hl, hc, hw⟩ := ih (R.exitExtrema p y).value
      have hd := (R.exitExtrema p y).bounded
      simp only [Plan.run, List.length_cons, slowCalls, Kind.slow,
        work, Nat.add_mul, Nat.one_mul]
      exact ⟨by omega, by omega, by omega⟩

/-- An operational branch partition: follow exactly the result of each read. -/
def Plan.Select {α : Type} (R : Runtime N n k B E) {f s : Nat} :
    Plan N n k α f s → α → Prop
  | .done x, z => z = x
  | .widen _ _ p, z => p.Select R z
  | .fast op next, z =>
      ∃ w, w = (R.fetch op).value ∧ (next w).Select R z
  | .extrema p y next, z =>
      ∃ w, w = (R.exitExtrema p y).value ∧ (next w).Select R z

theorem Plan.select_iff {α : Type} {f s : Nat} (R : Runtime N n k B E)
    (p : Plan N n k α f s) (z : α) :
    p.Select R z ↔ z = (p.run R).value := by
  induction p with
  | done x => rfl
  | widen hf hs p ih => exact ih
  | fast op next ih =>
      change (∃ w, w = (R.fetch op).value ∧ (next w).Select R z) ↔ _
      constructor
      · rintro ⟨w, rfl, hw⟩
        exact (ih _).1 hw
      · intro h
        exact ⟨_, rfl, (ih _).2 h⟩
  | extrema p y next ih =>
      change (∃ w, w = (R.exitExtrema p y).value ∧ (next w).Select R z) ↔ _
      constructor
      · rintro ⟨w, rfl, hw⟩
        exact (ih _).1 hw
      · intro h
        exact ⟨_, rfl, (ih _).2 h⟩

/-! Executable routing and answer stages. -/

abbrev Fails {α : Type} (a b : Option α) (x : α) :=
  some x = a ∨ some x = b

inductive Leaf (n k : Nat) where
  | failedSource | unreachableTarget | failedTarget | zero
  | oneFirst (a t : Fin n)
  | oneSecond (b t : Fin n)
  | comparableLeft (a t : Fin n)
  | comparableRight (b t : Fin n)
  | outside
  | withinLeft (a t : Fin n)
  | withinRight (b t : Fin n)
  | thirdMissing | thirdNonmember
  | thirdExits (d u v a b y : Fin n) (hit : Hit k)
  | malformed
  deriving Repr

def routeThird (d u v a b y : Fin n) : Plan N n k (Leaf n k) 2 0 :=
  .fast (.key d u v) fun
    | none => .stop .thirdMissing
    | some hit => .fast (.member hit.key y) fun marked =>
        if marked then .stop (.thirdExits d u v a b y hit)
        else .stop .thirdNonmember

def routeBlocks (d a b t : Fin n) : Plan N n k (Leaf n k) 5 0 :=
  .fast (.child d a) fun
    | none => .stop .malformed
    | some u => .fast (.child d b) fun
      | none => .stop .malformed
      | some v => .fast (.child d t) fun
        | none => .stop .outside
        | some y =>
            if y = u then .stop (.withinLeft a t)
            else if y = v then .stop (.withinRight b t)
            else routeThird d u v a b y

def routePair (a b t : Fin n) : Plan N n k (Leaf n k) 8 0 :=
  .fast (.ancestor a b) fun ab =>
    if ab then .stop (.comparableLeft a t)
    else .fast (.ancestor b a) fun ba =>
      if ba then .stop (.comparableRight b t)
      else .fast (.lca a b) fun d => routeBlocks d a b t

def routeRetained (r : Fin n) (a b t : Option (Fin n)) :
    Plan N n k (Leaf n k) 8 0 :=
  if Fails a b r then .stop .failedSource
  else match t with
    | none => .stop .unreachableTarget
    | some x =>
        if Fails a b x then .stop .failedTarget
        else match a, b with
          | none, none => .stop .zero
          | some u, none => .stop (.oneFirst u x)
          | none, some v => .stop (.oneSecond v x)
          | some u, some v => routePair u v x

def withID {α : Type} {f s : Nat} (i : Option (Fin N))
    (next : Option (Fin n) → Plan N n k α f s) :
    Plan N n k α (f + 1) s :=
  match i with
  | none => .widen (Nat.le_succ f) (Nat.le_refl s) (next none)
  | some j => .fast (.translate j) next

def route (r : Fin n) (a b : Option (Fin N)) (t : Fin N) :
    Plan N n k (Leaf n k) 11 0 :=
  withID a fun a' => withID b fun b' =>
    .fast (.translate t) fun t' => routeRetained r a' b' t'

def testSpan {α : Type} {f s : Nat} (a : Fin n) (span : Span n)
    (next : Bool → Plan N n k α f s) : Plan N n k α (f + 2) s :=
  match span with
  | none => .widen (by omega) (Nat.le_refl s) (next false)
  | some (first, last) =>
      .fast (.ancestor a first) fun h₁ =>
        .fast (.ancestor a last) fun h₂ => next (!h₁ || !h₂)

def testOne (a t : Fin n) : Plan N n k Bool 4 1 :=
  .fast (.ancestor a t) fun h => .stop (!h)

def answer : Leaf n k → Plan N n k Bool 4 1
  | .failedSource | .unreachableTarget | .failedTarget | .malformed =>
      .stop false
  | .zero | .outside | .thirdMissing | .thirdNonmember =>
      .stop true
  | .oneFirst a t | .oneSecond a t
  | .comparableLeft a t | .comparableRight a t
  | .withinLeft a t | .withinRight a t =>
      testOne a t
  | .thirdExits _ _ _ a b y hit =>
      .extrema hit.key y fun stored =>
        let requested := hit.orientation.order stored
        testSpan a requested.1 fun left =>
          testSpan b requested.2 fun right => .done (left || right)

structure QueryResult (n k : Nat) where
  leaf : Leaf n k
  survives : Bool
  events : List Event

def query (R : Runtime N n k B E) (a b : Option (Fin N)) (t : Fin N) :
    QueryResult n k :=
  let r := (route R.source a b t).run R
  let q := (answer r.value).run R
  ⟨r.value, q.value, r.events ++ q.events⟩

def reachable (R : Runtime N n k B E) (a b : Option (Fin N)) (t : Fin N) :
    Bool :=
  (query R a b t).survives

end PaperB.EX44
