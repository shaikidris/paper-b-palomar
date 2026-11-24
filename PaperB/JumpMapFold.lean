module

public import PaperB.ExitMap

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/- Append after the supplied `PaperB.ExitMap` algebra.

The trace interface is generic in the existing move type: pass a projection
`kind` from a move to `.parent` or `.jump`, and pass the checked move list
directly. No converted list or expanded parent path is built.

Maps point from the current vertex toward the ancestor. Thus an accumulator
is evaluated first, and the map for the next move is evaluated second.
-/

namespace PaperB.ExitMap.CheckedFold

private theorem two_ext {α : Type _} {x y : Two α}
    (h0 : x.x0 = y.x0) (h1 : x.x1 = y.x1) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  rfl

theorem eval_compose (inner outer : Map) (xs : Values) :
    Map.eval (Map.compose inner outer) xs =
      Map.eval outer (Map.eval inner xs) := by
  apply two_ext
  · simpa only [Two.get_zero] using Map.eval_compose_get inner outer xs 0
  · simpa only [Two.get_one] using Map.eval_compose_get inner outer xs 1

private theorem coord_compose_assoc (a b : Map) (c : Coord) :
    Coord.compose (Map.compose a b) c =
      Coord.compose a (Coord.compose b c) := by
  cases c with
  | mk base slot =>
    cases slot with
    | none => rfl
    | some i =>
      cases hb : Two.get b i with
      | mk bb bs =>
        cases bs <;> simp [Map.compose, Coord.compose, hb, Interval.join_assoc]

theorem compose_assoc (a b c : Map) :
    Map.compose (Map.compose a b) c = Map.compose a (Map.compose b c) :=
  two_ext (coord_compose_assoc a b c.x0) (coord_compose_assoc a b c.x1)

private theorem identity_get (i : Fin 2) :
    Two.get Map.identity i = ⟨.empty, some i⟩ := by
  have hi : i.val = 0 ∨ i.val = 1 := by
    have hlt := i.isLt
    omega
  rcases hi with h | h
  · have e : i = 0 := Fin.ext h
    simp [e, Map.identity]
  · have e : i = 1 := Fin.ext h
    simp [e, Map.identity]

theorem identity_compose (m : Map) : Map.compose Map.identity m = m := by
  have hc (c : Coord) : Coord.compose Map.identity c = c := by
    cases c with
    | mk base slot =>
      cases slot <;> simp [Coord.compose, identity_get]
  exact two_ext (hc m.x0) (hc m.x1)

theorem compose_identity (m : Map) : Map.compose m Map.identity = m := by
  cases m with
  | mk x y =>
    cases x <;> cases y <;>
      simp [Map.compose, Map.identity, Two.map, Coord.compose]

inductive Move where
  | parent
  | jump

/-- The two maps are stored in the same record as the two destinations. -/
structure Stored where
  parent : Nat
  jump : Nat
  parentMap : Map
  jumpMap : Map

abbrev Store := Nat → Stored

structure Selected where
  dst : Nat
  map : Map

def Stored.select (r : Stored) : Move → Selected
  | .parent => ⟨r.parent, r.parentMap⟩
  | .jump => ⟨r.jump, r.jumpMap⟩

/-- Specification only: consecutive parent edges, in traversal order.
`rank` can be the checked forest's `depthOf`. A self-parent root does not
supply a parent step. -/
inductive ParentPath (read : Store) (rank : Nat → Nat) :
    Nat → Nat → Map → Prop where
  | nil (u : Nat) : ParentPath read rank u u Map.identity
  | cons (u : Nat) {a : Nat} {m : Map}
      (down : rank (read u).parent < rank u)
      (tail : ParentPath read rank (read u).parent a m) :
      ParentPath read rank u a (Map.compose (read u).parentMap m)

namespace ParentPath

variable {read : Store} {rank : Nat → Nat}

theorem rank_le {u a : Nat} {m : Map} (h : ParentPath read rank u a m) :
    rank a ≤ rank u := by
  induction h with
  | nil u => exact Nat.le_refl u |> fun _ => Nat.le_refl (rank u)
  | @cons u a m down tail ih =>
    exact Nat.le_trans ih (Nat.le_of_lt down)

theorem append {u v : Nat} {m : Map} (h : ParentPath read rank u v m) :
    ∀ {a : Nat} {n : Map}, ParentPath read rank v a n →
      ParentPath read rank u a (Map.compose m n) := by
  induction h with
  | nil u =>
    intro a n g
    simpa only [identity_compose] using g
  | @cons u v m down tail ih =>
    intro a n g
    rw [compose_assoc]
    exact ParentPath.cons u down (ih g)

/-- A known ancestor determines the map, independently of how a trace
partitions the parent path into jumps. -/
theorem unique {u a : Nat} {m : Map} (h : ParentPath read rank u a m) :
    ∀ {n : Map}, ParentPath read rank u a n → m = n := by
  induction h with
  | nil u =>
    intro n g
    cases g with
    | nil => rfl
    | cons =>
      rename_i down tail
      exact False.elim (Nat.not_lt_of_ge (rank_le tail) down)
  | @cons u a m down tail ih =>
    intro n g
    cases g with
    | nil =>
      exact False.elim (Nat.not_lt_of_ge (rank_le tail) down)
    | cons =>
      rename_i tail'
      exact congrArg (Map.compose _) (ih tail')

end ParentPath

/-- Invariant of the stored jump map. This is equality of maps, not just
equality of their evaluations on a particular input. -/
def JumpOK (read : Store) (rank : Nat → Nat) (u : Nat) : Prop :=
  ParentPath read rank u (read u).jump (read u).jumpMap

def Stored.root (u : Nat) : Stored :=
  ⟨u, u, Map.identity, Map.identity⟩

def Stored.parentOnly (p : Nat) (edge : Map) : Stored :=
  ⟨p, p, edge, edge⟩

/-- For the checked skew-growth branch whose destination is `rp.jump`'s
jump. The caller supplies the two records already selected by that branch. -/
def Stored.skew (p : Nat) (edge : Map) (rp rq : Stored) : Stored :=
  ⟨p, rq.jump, edge, Map.compose edge (Map.compose rp.jumpMap rq.jumpMap)⟩

theorem jumpOK_root {read : Store} {rank : Nat → Nat} {u : Nat}
    (h : read u = Stored.root u) : JumpOK read rank u := by
  simpa [JumpOK, h, Stored.root] using (ParentPath.nil (read := read) (rank := rank) u)

theorem jumpOK_parentOnly {read : Store} {rank : Nat → Nat} {u p : Nat}
    {edge : Map} (h : read u = Stored.parentOnly p edge)
    (down : rank p < rank u) : JumpOK read rank u := by
  have hd : rank (read u).parent < rank u := by
    simpa [h, Stored.parentOnly] using down
  have hp := ParentPath.cons u hd
    (ParentPath.nil (read := read) (rank := rank) (read u).parent)
  simpa [JumpOK, h, Stored.parentOnly, compose_identity] using hp

/-- Local preservation at a new skew record: one parent edge followed by
the two previously certified jump segments. No parent chain is evaluated. -/
theorem jumpOK_skew {read : Store} {rank : Nat → Nat} {u p : Nat}
    {edge : Map}
    (h : read u = Stored.skew p edge (read p) (read (read p).jump))
    (down : rank p < rank u)
    (hp : JumpOK read rank p)
    (hq : JumpOK read rank (read p).jump) : JumpOK read rank u := by
  unfold JumpOK at hp hq
  have ep : (read u).parent = p := by
    simp [h, Stored.skew]
  have hd : rank (read u).parent < rank u := by
    simpa only [ep] using down
  have ht : ParentPath read rank (read u).parent (read (read p).jump).jump
      (Map.compose (read p).jumpMap (read (read p).jump).jumpMap) := by
    simpa only [ep] using ParentPath.append hp hq
  have hs := ParentPath.cons u hd ht
  simpa [JumpOK, h, Stored.skew] using hs

def Segment (read : Store) (rank : Nat → Nat) (u : Nat) (k : Move) : Prop :=
  ParentPath read rank u ((read u).select k).dst ((read u).select k).map

theorem parent_segment {read : Store} {rank : Nat → Nat} {u : Nat}
    (down : rank (read u).parent < rank u) : Segment read rank u .parent := by
  have h := ParentPath.cons u down
    (ParentPath.nil (read := read) (rank := rank) (read u).parent)
  simpa [Segment, Stored.select, compose_identity] using h

theorem jump_segment {read : Store} {rank : Nat → Nat} {u : Nat}
    (h : JumpOK read rank u) : Segment read rank u .jump :=
  h

/-- Adapter contract for a supplied trace. Use `parent_segment` for its
parent moves and `jump_segment` for its jump moves. The final index is the
endpoint certified by the trace. Neither this proof nor its parent-path
witnesses are retained at runtime. -/
inductive Checked {μ : Type} (kind : μ → Move) (read : Store)
    (rank : Nat → Nat) : Nat → List μ → Nat → Prop where
  | nil (u : Nat) : Checked kind read rank u [] u
  | cons (u : Nat) (k : μ) {ms : List μ} {a : Nat}
      (segment : Segment read rank u (kind k))
      (tail : Checked kind read rank ((read u).select (kind k)).dst ms a) :
      Checked kind read rank u (k :: ms) a

structure Result where
  stop : Nat
  composed : Map
  steps : Nat

/-- Each nonempty iteration calls `read` once, selects one stored map,
and performs one `Map.compose`. `steps` counts each of these operations.
There is no suffix-length calculation, path expansion, or extra lookup. -/
def foldAux {μ : Type} (kind : μ → Move) (read : Store) :
    List μ → Nat → Map → Nat → Result
  | [], u, acc, steps => ⟨u, acc, steps⟩
  | k :: ks, u, acc, steps =>
    let r := read u
    let e := r.select (kind k)
    foldAux kind read ks e.dst (Map.compose acc e.map) (steps + 1)

def fold {μ : Type} (kind : μ → Move) (read : Store)
    (u : Nat) (ms : List μ) : Result :=
  foldAux kind read ms u Map.identity 0

theorem foldAux_steps {μ : Type} (kind : μ → Move) (read : Store)
    (ms : List μ) (u : Nat) (acc : Map) (steps : Nat) :
    (foldAux kind read ms u acc steps).steps = steps + ms.length := by
  induction ms generalizing u acc steps with
  | nil => simp [foldAux]
  | cons k ks ih =>
    simp only [foldAux, ih, List.length_cons]
    omega

theorem fold_steps {μ : Type} (kind : μ → Move) (read : Store)
    (u : Nat) (ms : List μ) :
    (fold kind read u ms).steps = ms.length := by
  simpa only [fold, Nat.zero_add] using
    foldAux_steps kind read ms u Map.identity 0

theorem foldAux_spec {μ : Type} {kind : μ → Move} {read : Store}
    {rank : Nat → Nat} {u a : Nat} {ms : List μ}
    (h : Checked kind read rank u ms a) :
    ∀ (acc : Map) (steps : Nat),
      let r := foldAux kind read ms u acc steps
      r.stop = a ∧
        ∃ m, ParentPath read rank u a m ∧ r.composed = Map.compose acc m := by
  induction h with
  | nil u =>
    intro acc steps
    exact ⟨rfl, Map.identity, ParentPath.nil u, (compose_identity acc).symm⟩
  | @cons u k ms a segment tail ih =>
    intro acc steps
    let e := (read u).select (kind k)
    obtain ⟨hstop, m, hpath, hmap⟩ := ih (Map.compose acc e.map) (steps + 1)
    exact ⟨hstop, Map.compose e.map m, ParentPath.append segment hpath,
      hmap.trans (compose_assoc acc e.map m)⟩

/-- Reusable exact map fold. `reference` can be any consecutive-parent
certificate for the known ancestor, not necessarily one derived from `h`. -/
theorem fold_exact {μ : Type} {kind : μ → Move} {read : Store}
    {rank : Nat → Nat} {u a : Nat} {ms : List μ} {m : Map}
    (h : Checked kind read rank u ms a)
    (reference : ParentPath read rank u a m) :
    (fold kind read u ms).stop = a ∧
    (fold kind read u ms).composed = m := by
  obtain ⟨hstop, m', hpath, hmap⟩ := foldAux_spec h Map.identity 0
  exact ⟨hstop, hmap.trans
    ((identity_compose m').trans (ParentPath.unique hpath reference))⟩

/-- Evaluate once after the fold. The count excludes this final evaluation
and the cost of producing the existing trace. -/
def query {μ : Type} (kind : μ → Move) (read : Store)
    (u : Nat) (ms : List μ) (xs : Values) : Values × Nat :=
  let r := fold kind read u ms
  (Map.eval r.composed xs, r.steps)

theorem query_exact {μ : Type} {kind : μ → Move} {read : Store}
    {rank : Nat → Nat} {u a : Nat} {ms : List μ} {m : Map}
    (h : Checked kind read rank u ms a)
    (reference : ParentPath read rank u a m) (xs : Values) :
    query kind read u ms xs = (Map.eval m xs, ms.length) := by
  have hm := (fold_exact h reference).2
  simp only [query, hm, fold_steps]

/-- Instantiate `hBound` with the existing trace-length theorem. This
bounds both the added record reads and the number of map compositions. -/
theorem query_steps_le {μ : Type} (kind : μ → Move) (read : Store)
    (u : Nat) (ms : List μ) (xs : Values) {bound : Nat}
    (hBound : ms.length ≤ bound) :
    (query kind read u ms xs).2 ≤ bound := by
  simpa only [query, fold_steps] using hBound

end PaperB.ExitMap.CheckedFold
