module

public import PaperB.ExitKernels

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.BuiltExit.RawIncoming

open PaperB.ExitMap PaperB.LabelledQuotient PaperB.ExitSummary

variable {A V T : Type} {H : LabelledQuotient} {m : Nat}

/-- `readArc` reads the two fields of one stored occurrence. `knownLoss` is
the known-node DFS test, and `fused` is the register-only jump-map query.
The endpoint flags are reused in the direct contribution. -/
@[inline] def arcValue [DecidableEq V]
    (endpoint : Fin 2 → V) (rank : T → Nat)
    (readArc : A → V × T) (knownLoss : V → Bool) (fused : V → Values)
    (a : A) : Values :=
  let row := readArc a
  let s := row.1
  let tail := row.2
  let b₀ := decide (s = endpoint 0)
  let b₁ := decide (s = endpoint 1)
  match b₀ || b₁ with
  | true =>
    let point := singleton (rank tail)
    tab fun j => if (if j = 0 then b₀ else b₁) then point else .empty
  | false =>
    match knownLoss s with
    | true => fused s
    | false => zero

/-- `incoming` is the list already stored for this head. The driver walks
that list in place and passes only a source node to the fused query. It
constructs no adjacency list, path, `Route`, or `Site`. The fused reader
itself is supplied by the caller. -/
def run [DecidableEq V]
    (endpoint : Fin 2 → V) (rank : T → Nat)
    (readArc : A → V × T) (knownLoss : V → Bool) (fused : V → Values)
    (incoming : List A) : Values :=
  incoming.foldl
    (fun acc a => vjoin acc (arcValue endpoint rank readArc knownLoss fused a))
    zero

private theorem finTwo (j : Fin 2) : j = 0 ∨ j = 1 := by
  have hj := j.isLt
  have h : j.val = 0 ∨ j.val = 1 := by omega
  exact h.imp (fun e => Fin.ext e) (fun e => Fin.ext e)

private theorem lane_eq [DecidableEq V] (endpoint : Fin 2 → V)
    (s : V) (j : Fin 2) :
    (if j = 0 then decide (s = endpoint 0) else decide (s = endpoint 1)) =
      decide (s = endpoint j) := by
  rcases finTwo j with rfl | rfl
  · simp
  · simp [show (1 : Fin 2) ≠ 0 by decide]

private theorem hit_iff (W : Model H m) (B : CutPair H)
    (s : Fin H.vertexCount) :
    (decide (s = W.endpoint B 0) || decide (s = W.endpoint B 1)) = true ↔
      B.Mem s := by
  rw [W.mem_iff B s]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
  · rintro ⟨j, h⟩
    rcases finTwo j with rfl | rfl
    · exact Or.inl h.symm
    · exact Or.inr h.symm

private theorem false_of_not_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => exact (h rfl).elim

private theorem arcValue_eq_action
    {W : Model H m} {B : CutPair H} {a : W.Occ}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    (t : Action W B R S a) (rb : BaseReader R) (rm : MapReader S)
    (readArc : W.Occ → Fin H.vertexCount × Fin H.origVertexCount)
    (knownLoss : Fin H.vertexCount → Bool)
    (fused : Fin H.vertexCount → Values)
    (readOK : ∀ a, readArc a = (W.source a, W.physicalTail a))
    (dfsOK : ∀ z, ¬ B.Mem z → (knownLoss z = true ↔ H.ProperLoss B z))
    (fusedOK : ∀ z, H.ProperLoss B z →
      ∀ q : Query W R S B z, fused z = q.run rb rm) :
    arcValue (W.endpoint B) (fun x => W.rank x) readArc knownLoss fused a =
      t.run rb rm := by
  have hit := hit_iff W B (W.source a)
  cases t with
  | direct hm =>
    have hc := hit.mpr hm
    simp only [arcValue, readOK a, hc, Action.run]
    apply congrArg tab
    funext j
    simp only [lane_eq, decide_eq_true_eq]
  | lift hp q =>
    have hc := false_of_not_true (fun h => hp.2 (hit.mp h))
    have hd := (dfsOK _ hp.2).mpr hp
    simpa only [arcValue, readOK a, hc, hd, Action.run] using fusedOK _ hp q
  | skip hn hp =>
    have hc := false_of_not_true (fun h => hn (hit.mp h))
    have hd := false_of_not_true (fun h => hp ((dfsOK _ hn).mp h))
    simp only [arcValue, readOK a, hc, hd, Action.run]

/-- Pass `I.keep` as `stored` when `incoming` is the model's stored list.
The comparison is occurrence-for-occurrence and uses `Action.run` itself. -/
theorem run_eq_site
    {W : Model H m} {B : CutPair H} {y : Fin H.vertexCount}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    (I : Site W B y R S) (rb : BaseReader R) (rm : MapReader S)
    (incoming : List W.Occ) (stored : I.items.map Item.arc = incoming)
    (readArc : W.Occ → Fin H.vertexCount × Fin H.origVertexCount)
    (knownLoss : Fin H.vertexCount → Bool)
    (fused : Fin H.vertexCount → Values)
    (readOK : ∀ a, readArc a = (W.source a, W.physicalTail a))
    (dfsOK : ∀ z, ¬ B.Mem z → (knownLoss z = true ↔ H.ProperLoss B z))
    (fusedOK : ∀ z, H.ProperLoss B z →
      ∀ q : Query W R S B z, fused z = q.run rb rm) :
    run (W.endpoint B) (fun x => W.rank x) readArc knownLoss fused incoming =
      I.run rb rm := by
  have go (items : List (Item W B R S)) (acc : Values) :
      (items.map Item.arc).foldl
        (fun v a => vjoin v
          (arcValue (W.endpoint B) (fun x => W.rank x) readArc knownLoss fused a))
        acc =
      items.foldl (fun v t => vjoin v (t.action.run rb rm)) acc := by
    induction items generalizing acc with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_cons, List.foldl_cons,
        arcValue_eq_action t.action rb rm readArc knownLoss fused
          readOK dfsOK fusedOK, ih]
  rw [run, ← stored, Site.run]
  exact go I.items zero

private theorem foldl_visits {σ : Type} (step : σ → A → σ)
    (xs : List A) (acc : σ) (seen : List A) :
    xs.foldl (fun p a => (step p.1 a, a :: p.2)) (acc, seen) =
      (xs.foldl step acc, xs.reverse ++ seen) := by
  induction xs generalizing acc seen with
  | nil => simp
  | cons a xs ih =>
    simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]

/-- Proof-only instrumentation: record one entry at each `readArc` call.
The reverse log is exactly the stored list reversed, so every stored
position is visited once, in order, even when arc values repeat. Its length
is `incoming.length` by `List.length_reverse`. `run` allocates no log. -/
theorem exact_visits [DecidableEq V]
    (endpoint : Fin 2 → V) (rank : T → Nat)
    (readArc : A → V × T) (knownLoss : V → Bool) (fused : V → Values)
    (incoming : List A) :
    incoming.foldl
      (fun (p : Values × List A) a =>
        (vjoin p.1 (arcValue endpoint rank readArc knownLoss fused a), a :: p.2))
      (zero, []) =
      (run endpoint rank readArc knownLoss fused incoming, incoming.reverse) := by
  simpa only [run, List.append_nil] using
    (foldl_visits
      (fun acc a => vjoin acc (arcValue endpoint rank readArc knownLoss fused a))
      incoming zero [])

end PaperB.BuiltExit.RawIncoming
