module

public import PaperB.Forest
public import PaperB.ExitMap
public import PaperB.ExitSummary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Lean 4.35.0-rc3

The two driver declarations are not needed as imports. At the driver site,
specialize `Deps` to
  ⟨D.installBase, D.installMap, D.vertexBase, D.vertexMap⟩.
With `K` specialized to those dependencies, use these terms at the indicated
expected types:

  exitCallbacks% K   : Callbacks D ExitMap.Map ExitMap.Values
  exitExact% K       : Exact P C W.wantMap W.wantBase

`Model.transfer` is the supplied `exit_set_transfer` on the certified forest
edge, with freshness written as child membership and nonmembership in the
parent. `Model.tails` is reference data only. Neither callback reads it.

A route is a typed sequence of installed forest-edge keys. The route kernel
composes the maps returned by the reader, not the reference maps. Charges
below are for the callbacks, given the incoming lists and route descriptors;
they do not charge construction of the forest or of those descriptors.
-/

namespace PaperB.BuiltExit

open LabelledQuotient
open PaperB.ExitMap
open PaperB.ExitSummary

universe u v

private theorem finTwo (j : Fin 2) : j = 0 ∨ j = 1 := by
  have hb := j.isLt
  have hv : j.val = 0 ∨ j.val = 1 := by omega
  exact hv.elim (fun h => Or.inl (Fin.ext h))
    (fun h => Or.inr (Fin.ext h))

def tab {α : Type v} (f : Fin 2 → α) : Two α :=
  ⟨f 0, f 1⟩

@[simp] theorem get_tab {α : Type v} (f : Fin 2 → α) (j : Fin 2) :
    Two.get (tab f) j = f j := by
  rcases finTwo j with h | h
  · subst j
    exact Two.get_zero _
  · subst j
    exact Two.get_one _

private theorem twoExt {α : Type v} {a b : Two α}
    (h : ∀ j, Two.get a j = Two.get b j) : a = b := by
  cases a with
  | mk a0 a1 =>
    cases b with
    | mk b0 b1 =>
      have h0 : a0 = b0 := by simpa using h 0
      have h1 : a1 = b1 := by simpa using h 1
      cases h0
      cases h1
      rfl

def zero : Values :=
  tab fun _ => .empty

def vjoin (a b : Values) : Values :=
  tab fun j => Interval.join (Two.get a j) (Two.get b j)

@[simp] theorem get_vjoin (a b : Values) (j : Fin 2) :
    Two.get (vjoin a b) j = Interval.join (Two.get a j) (Two.get b j) :=
  get_tab _ _

def Test (l h : Nat) : Interval → Prop
  | .empty => True
  | .span lo hi => endpointsInside l h (.span lo hi) = true

@[simp] private theorem test_empty (l h : Nat) : Test l h Interval.empty :=
  True.intro

@[simp] theorem test_zero (l h : Nat) (j : Fin 2) :
    Test l h (Two.get zero j) := by
  simp only [zero, get_tab, test_empty]

private theorem test_singleton (l h k : Nat) :
    Test l h (singleton k) ↔ l ≤ k ∧ k < h :=
  endpointsInside_span_iff l h k k

private theorem test_join (l h : Nat) (a b : Interval) :
    Test l h (Interval.join a b) ↔ Test l h a ∧ Test l h b := by
  cases a with
  | empty => simp
  | span al ah =>
    cases b with
    | empty => simp
    | span bl bh =>
      simp only [Interval.join, Test, endpointsInside_span_iff,
        Nat.min_def, Nat.max_def]
      split <;> split <;>
        (constructor
         · rintro ⟨hl, hh⟩
           exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
         · rintro ⟨⟨hla, hha⟩, ⟨hlb, hhb⟩⟩
           exact ⟨by omega, by omega⟩)

-- Equality of all half-open containment tests determines the interval,
-- including its empty/nonempty tag. No well-formedness hypothesis is needed.
private theorem testExt {a b : Interval}
    (e : ∀ l h, Test l h a ↔ Test l h b) : a = b := by
  cases a with
  | empty =>
    cases b with
    | empty => rfl
    | span bl bh =>
      obtain ⟨bad, _⟩ :=
        (endpointsInside_span_iff (bl + 1) (bh + 1) bl bh).mp
          ((e (bl + 1) (bh + 1)).mp True.intro)
      omega
  | span al ah =>
    cases b with
    | empty =>
      obtain ⟨bad, _⟩ :=
        (endpointsInside_span_iff (al + 1) (ah + 1) al ah).mp
          ((e (al + 1) (ah + 1)).mpr True.intro)
      omega
    | span bl bh =>
      have ha : Test al (ah + 1) (.span al ah) :=
        (endpointsInside_span_iff al (ah + 1) al ah).mpr
          ⟨Nat.le_refl _, by omega⟩
      have hb : Test bl (bh + 1) (.span bl bh) :=
        (endpointsInside_span_iff bl (bh + 1) bl bh).mpr
          ⟨Nat.le_refl _, by omega⟩
      obtain ⟨hl₁, hh₁⟩ :=
        (endpointsInside_span_iff al (ah + 1) bl bh).mp
          ((e al (ah + 1)).mp ha)
      obtain ⟨hl₂, hh₂⟩ :=
        (endpointsInside_span_iff bl (bh + 1) al ah).mp
          ((e bl (bh + 1)).mpr hb)
      have el : al = bl := by omega
      have eh : ah = bh := by omega
      rw [el, eh]

structure Model (H : LabelledQuotient) (m : Nat) where
  Occ : Type u
  incoming : Fin H.vertexCount → List Occ
  source : Occ → Fin H.vertexCount
  physicalTail : Occ → Fin H.origVertexCount
  rank : Fin H.origVertexCount → Nat
  arc_iff : ∀ z y, H.HasQuotientArc z y ↔
    ∃ a ∈ incoming y, source a = z
  exit_iff : ∀ (B : CutPair H) s y x, B.Mem s →
    (H.ExitTailMem B s y x ↔
      ∃ w a, a ∈ incoming w ∧ source a = s ∧ physicalTail a = x ∧
        H.SurvivingPath B.Mem w y)
  ends : CutPair H → Two (Fin H.vertexCount)
  mem_iff : ∀ (B : CutPair H) s, B.Mem s ↔
    ∃ j : Fin 2, Two.get (ends B) j = s
  owner : Fin H.vertexCount → Option (CutPair H)
  ownerProper : ∀ y B, owner y = some B → H.ProperLoss B y
  forest : ProperLossForest H
  edgeNode : Fin m → Fin (forest.realNodeCount + 1)
  child : Fin m → CutPair H
  parent : Fin m → CutPair H
  childKey : ∀ i, forest.nodeKey? (edgeNode i) = some (child i)
  parentKey : ∀ i, forest.nodeKey? (forest.parent (edgeNode i)) = some (parent i)
  transfer : ∀ i s y x, (parent i).Mem s → H.ProperLoss (child i) y →
    (H.ExitTailMem (parent i) s y x ↔
      (∃ p, (child i).Mem p ∧ ¬ (parent i).Mem p ∧
        H.ExitTailMem (parent i) s p x) ∨
      ((child i).Mem s ∧ H.ExitTailMem (child i) s y x))
  tails : CutPair H → Fin H.vertexCount → Fin H.vertexCount →
    List (Fin H.origVertexCount)
  tails_iff : ∀ (B : CutPair H) s y x, B.Mem s →
    (x ∈ tails B s y ↔ H.ExitTailMem B s y x)

variable {H : LabelledQuotient} {m : Nat}

namespace Model

variable (W : Model H m)

abbrev endpoint (B : CutPair H) (j : Fin 2) :=
  Two.get (W.ends B) j

theorem endpoint_mem (B : CutPair H) (j : Fin 2) :
    B.Mem (W.endpoint B j) :=
  (W.mem_iff B _).mpr ⟨j, rfl⟩

def slot (B : CutPair H) (s : Fin H.vertexCount) : Option (Fin 2) :=
  if W.endpoint B 0 = s then some 0
  else if W.endpoint B 1 = s then some 1
  else none

theorem slot_sound {B : CutPair H} {s : Fin H.vertexCount} {j : Fin 2}
    (h : W.slot B s = some j) : W.endpoint B j = s := by
  by_cases h0 : W.endpoint B 0 = s
  · rw [slot, ite_eq_left h0] at h
    have e : (0 : Fin 2) = j := Option.some.inj h
    exact e ▸ h0
  · by_cases h1 : W.endpoint B 1 = s
    · rw [slot, ite_eq_right h0, ite_eq_left h1] at h
      have e : (1 : Fin 2) = j := Option.some.inj h
      exact e ▸ h1
    · rw [slot, ite_eq_right h0, ite_eq_right h1] at h
      cases h

theorem slot_none (B : CutPair H) (s : Fin H.vertexCount) :
    W.slot B s = none ↔ ¬ B.Mem s := by
  constructor
  · intro hn hm
    obtain ⟨j, hj⟩ := (W.mem_iff B s).mp hm
    rcases finTwo j with e | e
    · subst j
      change W.endpoint B 0 = s at hj
      rw [slot, ite_eq_left hj] at hn
      cases hn
    · subst j
      change W.endpoint B 1 = s at hj
      by_cases h0 : W.endpoint B 0 = s
      · rw [slot, ite_eq_left h0] at hn
        cases hn
      · rw [slot, ite_eq_right h0, ite_eq_left hj] at hn
        cases hn
  · intro hn
    have h0 : W.endpoint B 0 ≠ s :=
      fun h => hn ((W.mem_iff B s).mpr ⟨0, h⟩)
    have h1 : W.endpoint B 1 ≠ s :=
      fun h => hn ((W.mem_iff B s).mpr ⟨1, h⟩)
    rw [slot, ite_eq_right h0, ite_eq_right h1]

def contribution (B : CutPair H) (s : Fin H.vertexCount)
    (a : W.Occ) (x : Fin H.origVertexCount) : Prop :=
  (W.source a = s ∧ W.physicalTail a = x) ∨
    (H.ProperLoss B (W.source a) ∧ H.ExitTailMem B s (W.source a) x)

/-- EX4.2, with the union indexed by original occurrences. -/
theorem incoming_exact {B : CutPair H} {s y : Fin H.vertexCount}
    {x : Fin H.origVertexCount} (hs : B.Mem s) (hy : H.ProperLoss B y) :
    H.ExitTailMem B s y x ↔
      ∃ a ∈ W.incoming y, W.contribution B s a x := by
  have lastStep : ∀ {z : Fin H.vertexCount}, ¬ B.Mem z →
      H.HasQuotientArc z y → H.SurvivingPath B.Mem z y := by
    intro z hz hzy
    exact AvoidPath.step z y y hz hzy (AvoidPath.refl y hy.2)
  constructor
  · intro hx
    obtain ⟨w, a, ha, hsa, hxa, hwy⟩ := (W.exit_iff B s y x hs).mp hx
    rcases AvoidPath.eq_or_exists_last_arc hwy with e | ⟨z, hwz, hzy⟩
    · subst w
      exact ⟨a, ha, Or.inl ⟨hsa, hxa⟩⟩
    · obtain ⟨b, hb, hzb⟩ := (W.arc_iff z y).mp hzy
      have hzAlive : ¬ B.Mem z := AvoidPath.target_alive hwz
      have hzLost : H.Lost B z := by
        intro hzRoot
        exact hy.1 (AvoidPath.trans hzRoot (lastStep hzAlive hzy))
      have hxz : H.ExitTailMem B s z x :=
        (W.exit_iff B s z x hs).mpr ⟨w, a, ha, hsa, hxa, hwz⟩
      refine ⟨b, hb, Or.inr ?_⟩
      rw [hzb]
      exact ⟨⟨hzLost, hzAlive⟩, hxz⟩
  · rintro ⟨a, ha, hc⟩
    rcases hc with ⟨hsa, hxa⟩ | ⟨hp, hxa⟩
    · exact (W.exit_iff B s y x hs).mpr
        ⟨y, a, ha, hsa, hxa, AvoidPath.refl y hy.2⟩
    · have harc : H.HasQuotientArc (W.source a) y :=
        (W.arc_iff (W.source a) y).mpr ⟨a, ha, rfl⟩
      obtain ⟨w, b, hb, hsb, hxb, hwa⟩ :=
        (W.exit_iff B s (W.source a) x hs).mp hxa
      exact (W.exit_iff B s y x hs).mpr
        ⟨w, b, hb, hsb, hxb, AvoidPath.trans hwa (lastStep hp.2 harc)⟩

theorem incoming_extensional {B : CutPair H} {s y : Fin H.vertexCount}
    (hs : B.Mem s) (hy : H.ProperLoss B y) :
    (fun x => H.ExitTailMem B s y x) =
      (fun x => ∃ a ∈ W.incoming y, W.contribution B s a x) := by
  funext x
  exact propext (W.incoming_exact hs hy)

def Fits (l h : Nat) (B : CutPair H) (s y : Fin H.vertexCount) : Prop :=
  ∀ x, H.ExitTailMem B s y x → l ≤ W.rank x ∧ W.rank x < h

def ref (B : CutPair H) (y : Fin H.vertexCount) : Values :=
  tab fun j => summary ((W.tails B (W.endpoint B j) y).map W.rank)

theorem ref_test (B : CutPair H) (y : Fin H.vertexCount) (j : Fin 2)
    (l h : Nat) :
    Test l h (Two.get (W.ref B y) j) ↔ W.Fits l h B (W.endpoint B j) y := by
  have htest (a : Interval) : Test l h a ↔ endpointsInside l h a = true := by
    cases a with
    | empty => exact ⟨fun _ => rfl, fun _ => True.intro⟩
    | span lo hi => rfl
  rw [ref, get_tab, htest, endpointsInside_summary_iff]
  have hm := W.endpoint_mem B j
  constructor
  · intro hall x hx
    exact hall (W.rank x)
      (List.mem_map.mpr ⟨x, (W.tails_iff B _ y x hm).mpr hx, rfl⟩)
  · intro hall k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
    exact hall x ((W.tails_iff B _ y x hm).mp hx)

def wantBase (y : Fin H.vertexCount) : Values :=
  match W.owner y with
  | none => zero
  | some B => W.ref B y

def refFresh (i : Fin m) (k : Fin 2) : Values :=
  if W.slot (W.parent i) (W.endpoint (W.child i) k) = none then
    W.ref (W.parent i) (W.endpoint (W.child i) k)
  else zero

/-- Join the two vectors once, then attach endpoint-matching inherited slots. -/
def pack (i : Fin m) (a b : Values) : Map :=
  let c := vjoin a b
  tab fun j =>
    ⟨Two.get c j, W.slot (W.child i) (W.endpoint (W.parent i) j)⟩

def wantMap (i : Fin m) : Map :=
  W.pack i (W.refFresh i 0) (W.refFresh i 1)

private theorem fresh_test (i : Fin m) (k j : Fin 2) (l h : Nat) :
    Test l h (Two.get (W.refFresh i k) j) ↔
      (¬ (W.parent i).Mem (W.endpoint (W.child i) k) →
        W.Fits l h (W.parent i) (W.endpoint (W.parent i) j)
          (W.endpoint (W.child i) k)) := by
  by_cases e : W.slot (W.parent i) (W.endpoint (W.child i) k) = none
  · have hn := (W.slot_none _ _).mp e
    rw [refFresh, if_pos e, ref_test]
    exact ⟨fun hf _ => hf, fun hf => hf hn⟩
  · rw [refFresh, if_neg e]
    exact ⟨fun _ hn => (e ((W.slot_none _ _).mpr hn)).elim,
      fun _ => test_zero l h j⟩

private def copied (xs : Values) : Option (Fin 2) → Interval
  | none => .empty
  | some k => Two.get xs k

private theorem eval_as_join (c : Coord) (xs : Values) :
    Coord.eval c xs = Interval.join c.base (copied xs c.slot) := by
  cases c with
  | mk b s => cases s <;> simp [Coord.eval, copied]

private theorem copy_test (B : CutPair H) (s y : Fin H.vertexCount) (l h : Nat) :
    Test l h (copied (W.ref B y) (W.slot B s)) ↔
      (B.Mem s → W.Fits l h B s y) := by
  cases e : W.slot B s with
  | none =>
    have hn := (W.slot_none B s).mp e
    exact ⟨fun _ hm => (hn hm).elim, fun _ => True.intro⟩
  | some k =>
    have he : W.endpoint B k = s := W.slot_sound e
    have hm : B.Mem s := he ▸ W.endpoint_mem B k
    change Test l h (Two.get (W.ref B y) k) ↔ _
    rw [ref_test, he]
    exact ⟨fun hf _ => hf, fun hf => hf hm⟩

private theorem transfer_test (i : Fin m) (s y : Fin H.vertexCount)
    (hs : (W.parent i).Mem s) (hy : H.ProperLoss (W.child i) y) (l h : Nat) :
    (((¬ (W.parent i).Mem (W.endpoint (W.child i) 0) →
          W.Fits l h (W.parent i) s (W.endpoint (W.child i) 0)) ∧
       (¬ (W.parent i).Mem (W.endpoint (W.child i) 1) →
          W.Fits l h (W.parent i) s (W.endpoint (W.child i) 1))) ∧
       ((W.child i).Mem s → W.Fits l h (W.child i) s y)) ↔
      W.Fits l h (W.parent i) s y := by
  constructor
  · rintro ⟨⟨h0, h1⟩, hc⟩ x hx
    rcases (W.transfer i s y x hs hy).mp hx with
      ⟨p, hp, hf, hpx⟩ | ⟨hm, hxy⟩
    · obtain ⟨k, hk⟩ := (W.mem_iff (W.child i) p).mp hp
      subst p
      rcases finTwo k with e | e
      · subst k
        exact h0 hf x hpx
      · subst k
        exact h1 hf x hpx
    · exact hc hm x hxy
  · intro hall
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hf x hx
      exact hall x ((W.transfer i s y x hs hy).mpr
        (Or.inl ⟨_, W.endpoint_mem (W.child i) 0, hf, hx⟩))
    · intro hf x hx
      exact hall x ((W.transfer i s y x hs hy).mpr
        (Or.inl ⟨_, W.endpoint_mem (W.child i) 1, hf, hx⟩))
    · intro hm x hx
      exact hall x ((W.transfer i s y x hs hy).mpr (Or.inr ⟨hm, hx⟩))

/-- EX4.3: the installed map is exact as a two-coordinate interval value. -/
theorem wantMap_lifts (i : Fin m) (y : Fin H.vertexCount)
    (hy : H.ProperLoss (W.child i) y) :
    Map.eval (W.wantMap i) (W.ref (W.child i) y) = W.ref (W.parent i) y := by
  apply twoExt
  intro j
  apply testExt
  intro l h
  simp only [Map.eval, Two.get_map, wantMap, pack, get_tab, eval_as_join,
    get_vjoin, test_join, fresh_test, copy_test, ref_test]
  exact W.transfer_test i _ y (W.endpoint_mem (W.parent i) j) hy l h

end Model

structure Deps (n m : Nat) where
  installBase : Fin m → Fin n → Prop
  installMap : Fin m → Fin m → Prop
  vertexBase : Fin n → Fin n → Prop
  vertexMap : Fin n → Fin m → Prop

abbrev BaseReader {n : Nat} (R : Fin n → Prop) :=
  (z : Fin n) → R z → Option Values

abbrev MapReader {m : Nat} (S : Fin m → Prop) :=
  (i : Fin m) → S i → Option Map

inductive Route (W : Model H m) (S : Fin m → Prop) (z : Fin H.vertexCount) :
    CutPair H → Type where
  | seed {B : CutPair H} : W.owner z = some B → Route W S z B
  | step (i : Fin m) : S i → H.ProperLoss (W.child i) z →
      Route W S z (W.child i) → Route W S z (W.parent i)

namespace Route

variable {W : Model H m} {S : Fin m → Prop} {z : Fin H.vertexCount}

def actual (rm : MapReader S) {B : CutPair H} (r : Route W S z B) : Map :=
  match r with
  | .seed _ => Map.identity
  | .step i hi _ inner =>
    Map.compose (actual rm inner) ((rm i hi).getD Map.identity)

def hops {B : CutPair H} (r : Route W S z B) : Nat :=
  match r with
  | .seed _ => 0
  | .step _ _ _ inner => inner.hops + 1

theorem actual_exact {B : CutPair H} (r : Route W S z B)
    (rm : MapReader S) (hm : ∀ i hi, rm i hi = some (W.wantMap i)) :
    Map.eval (r.actual rm) (W.wantBase z) = W.ref B z := by
  induction r with
  | seed ho =>
    rw [actual, Map.eval_identity]
    simp [Model.wantBase, ho]
  | step i hi hp inner ih =>
    apply twoExt
    intro j
    rw [actual, Map.eval_compose_get, ih, hm i hi]
    exact congrArg (fun a => Two.get a j) (W.wantMap_lifts i z hp)

end Route

structure Query (W : Model H m) (R : Fin H.vertexCount → Prop)
    (S : Fin m → Prop) (B : CutPair H) (z : Fin H.vertexCount) where
  readOK : R z
  route : Route W S z B

namespace Query

variable {W : Model H m} {R : Fin H.vertexCount → Prop} {S : Fin m → Prop}
  {B : CutPair H} {z : Fin H.vertexCount}

def run (q : Query W R S B z) (rb : BaseReader R) (rm : MapReader S) : Values :=
  let seed := (rb z q.readOK).getD zero
  Map.eval (q.route.actual rm) seed

theorem run_exact (q : Query W R S B z) (rb : BaseReader R) (rm : MapReader S)
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ i hi, rm i hi = some (W.wantMap i)) :
    q.run rb rm = W.ref B z := by
  rw [run, hb z q.readOK]
  exact q.route.actual_exact rm hm

end Query

inductive Action (W : Model H m) (B : CutPair H) (R : Fin H.vertexCount → Prop)
    (S : Fin m → Prop) (a : W.Occ) where
  | direct : B.Mem (W.source a) → Action W B R S a
  | lift : H.ProperLoss B (W.source a) → Query W R S B (W.source a) →
      Action W B R S a
  | skip : ¬ B.Mem (W.source a) → ¬ H.ProperLoss B (W.source a) →
      Action W B R S a

namespace Action

variable {W : Model H m} {B : CutPair H} {R : Fin H.vertexCount → Prop}
  {S : Fin m → Prop} {a : W.Occ}

def run (t : Action W B R S a) (rb : BaseReader R) (rm : MapReader S) : Values :=
  match t with
  | .direct _ =>
    tab fun j =>
      if W.source a = W.endpoint B j then singleton (W.rank (W.physicalTail a))
      else .empty
  | .lift _ q => q.run rb rm
  | .skip _ _ => zero

theorem run_test (t : Action W B R S a) (rb : BaseReader R) (rm : MapReader S)
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ i hi, rm i hi = some (W.wantMap i)) (j : Fin 2) (l h : Nat) :
    Test l h (Two.get (t.run rb rm) j) ↔
      ∀ x, W.contribution B (W.endpoint B j) a x →
        l ≤ W.rank x ∧ W.rank x < h := by
  cases t with
  | direct ha =>
    have hn : ¬ H.ProperLoss B (W.source a) := fun hp => hp.2 ha
    simp only [run, get_tab, Model.contribution, hn, false_and, or_false]
    by_cases he : W.source a = W.endpoint B j
    · rw [if_pos he, test_singleton]
      constructor
      · intro ht x hx
        rw [← hx.2]
        exact ht
      · intro ht
        exact ht _ ⟨he, rfl⟩
    · rw [if_neg he]
      exact ⟨fun _ _ hx => (he hx.1).elim, fun _ => True.intro⟩
  | lift hp q =>
    simp only [run, q.run_exact rb rm hb hm, Model.ref_test, Model.Fits,
      Model.contribution, hp, true_and]
    constructor
    · intro ht x hx
      rcases hx with ⟨he, _⟩ | hx
      · have ha : B.Mem (W.source a) := he.symm ▸ W.endpoint_mem B j
        exact (hp.2 ha).elim
      · exact ht x hx
    · intro ht x hx
      exact ht x (Or.inr hx)
  | skip hn hp =>
    constructor
    · intro _ x hx
      rcases hx with ⟨he, _⟩ | ⟨ha, _⟩
      · have ha : B.Mem (W.source a) := he.symm ▸ W.endpoint_mem B j
        exact (hn ha).elim
      · exact (hp ha).elim
    · intro _
      exact test_zero l h j

end Action

structure Item (W : Model H m) (B : CutPair H) (R : Fin H.vertexCount → Prop)
    (S : Fin m → Prop) where
  arc : W.Occ
  action : Action W B R S arc

structure Site (W : Model H m) (B : CutPair H) (y : Fin H.vertexCount)
    (R : Fin H.vertexCount → Prop) (S : Fin m → Prop) where
  items : List (Item W B R S)
  keep : items.map Item.arc = W.incoming y

private theorem fold_test {α : Type v} (ts : List α) (f : α → Values)
    (acc : Values) (j : Fin 2) (l h : Nat) :
    Test l h (Two.get (ts.foldl (fun c t => vjoin c (f t)) acc) j) ↔
      Test l h (Two.get acc j) ∧
        ∀ t ∈ ts, Test l h (Two.get (f t) j) := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, get_vjoin, test_join]
    constructor
    · rintro ⟨⟨ha, ht⟩, hts⟩
      refine ⟨ha, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact ht
      · exact hts b hb
    · rintro ⟨ha, hall⟩
      exact ⟨⟨ha, hall t (List.mem_cons.mpr (Or.inl rfl))⟩,
        fun b hb => hall b (List.mem_cons.mpr (Or.inr hb))⟩

namespace Site

variable {W : Model H m} {B : CutPair H} {y : Fin H.vertexCount}
  {R : Fin H.vertexCount → Prop} {S : Fin m → Prop}

/-- The only entering-occurrence loop. `keep` is a list equality, not a
    membership equivalence: order and multiplicity are both preserved. -/
def run (I : Site W B y R S) (rb : BaseReader R) (rm : MapReader S) : Values :=
  I.items.foldl (fun acc t => vjoin acc (t.action.run rb rm)) zero

theorem run_exact (I : Site W B y R S) (hy : H.ProperLoss B y)
    (rb : BaseReader R) (rm : MapReader S)
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ i hi, rm i hi = some (W.wantMap i)) :
    I.run rb rm = W.ref B y := by
  apply twoExt
  intro j
  apply testExt
  intro l h
  rw [run, fold_test, W.ref_test]
  have hs := W.endpoint_mem B j
  constructor
  · rintro ⟨_, hall⟩ x hx
    obtain ⟨a, ha, hc⟩ := (W.incoming_exact hs hy).mp hx
    have hmapped : a ∈ I.items.map Item.arc := by
      rw [I.keep]
      exact ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmapped
    exact (t.action.run_test rb rm hb hm j l h).mp (hall t ht) x hc
  · intro hall
    refine ⟨test_zero l h j, ?_⟩
    intro t ht
    apply (t.action.run_test rb rm hb hm j l h).mpr
    intro x hc
    have ha : t.arc ∈ W.incoming y := by
      rw [← I.keep]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    exact hall x ((W.incoming_exact hs hy).mpr ⟨t.arc, ha, hc⟩)

end Site

structure Kernel (W : Model H m) (D : Deps H.vertexCount m) where
  fresh : ∀ i (k : Fin 2),
    W.slot (W.parent i) (W.endpoint (W.child i) k) = none →
      Query W (D.installBase i) (D.installMap i) (W.parent i)
        (W.endpoint (W.child i) k)
  site : ∀ y B, W.owner y = some B → Site W B y (D.vertexBase y) (D.vertexMap y)

namespace Kernel

variable {W : Model H m} {D : Deps H.vertexCount m} (K : Kernel W D)

def freshRun (i : Fin m) (k : Fin 2)
    (rb : BaseReader (D.installBase i)) (rm : MapReader (D.installMap i)) :
    Values :=
  if e : W.slot (W.parent i) (W.endpoint (W.child i) k) = none then
    (K.fresh i k e).run rb rm
  else zero

def install (_y : Fin H.vertexCount) (i : Fin m)
    (rb : BaseReader (D.installBase i)) (rm : MapReader (D.installMap i)) : Map :=
  let a := K.freshRun i 0 rb rm
  let b := K.freshRun i 1 rb rm
  W.pack i a b

def base (y : Fin H.vertexCount)
    (rb : BaseReader (D.vertexBase y)) (rm : MapReader (D.vertexMap y)) : Values :=
  match e : W.owner y with
  | none => zero
  | some B => (K.site y B e).run rb rm

theorem freshRun_exact (i : Fin m) (k : Fin 2)
    (rb : BaseReader (D.installBase i)) (rm : MapReader (D.installMap i))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a)) :
    K.freshRun i k rb rm = W.refFresh i k := by
  by_cases e : W.slot (W.parent i) (W.endpoint (W.child i) k) = none
  · rw [freshRun, dif_pos e, Model.refFresh, if_pos e]
    exact (K.fresh i k e).run_exact rb rm hb hm
  · simp [freshRun, Model.refFresh, e]

theorem install_exact (y : Fin H.vertexCount) (i : Fin m)
    (rb : BaseReader (D.installBase i)) (rm : MapReader (D.installMap i))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a)) :
    K.install y i rb rm = W.wantMap i := by
  simp only [install, Model.wantMap, K.freshRun_exact i 0 rb rm hb hm,
    K.freshRun_exact i 1 rb rm hb hm]

theorem base_exact (y : Fin H.vertexCount)
    (rb : BaseReader (D.vertexBase y)) (rm : MapReader (D.vertexMap y))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a)) :
    K.base y rb rm = W.wantBase y := by
  unfold base
  split
  next he =>
    rw [Model.wantBase, he]
  next B he =>
    have hWant : W.ref B y = W.wantBase y := by
      simp [Model.wantBase, he]
    exact Eq.trans ((K.site y B he).run_exact (W.ownerProper y B he) rb rm hb hm) hWant

/-- The built base answers exactly the extensional exit-tail containment test. -/
theorem base_exit_test (y : Fin H.vertexCount) (B : CutPair H)
    (e : W.owner y = some B)
    (rb : BaseReader (D.vertexBase y)) (rm : MapReader (D.vertexMap y))
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ a ha, rm a ha = some (W.wantMap a))
    (j : Fin 2) (l h : Nat) :
    Test l h (Two.get (K.base y rb rm) j) ↔
      ∀ x, H.ExitTailMem B (W.endpoint B j) y x →
        l ≤ W.rank x ∧ W.rank x < h := by
  rw [K.base_exact y rb rm hb hm, Model.wantBase, e]
  exact W.ref_test B y j l h

end Kernel

/-!
Charge ledger, not evaluated by either callback.

* One query reads one base, reads and composes one map per hop, and evaluates
  the composed map once. Composition and evaluation each join at most two
  intervals.
* Each item visit joins two intervals into the accumulator. A direct item
  uses at most two endpoint comparisons; a skipped item makes no reads.
* Installation uses two joins to combine the fresh vectors, at most four
  comparisons to test freshness, and at most four to select inherited slots.
* One interval join uses at most one `min` and one `max`. Singleton
  construction uses one physical rank lookup per matching coordinate.
-/

structure Charge where
  visits : Nat
  queries : Nat
  hops : Nat
  extraJoins : Nat
  endpointTests : Nat

namespace Charge

def zero : Charge := ⟨0, 0, 0, 0, 0⟩

def add (a b : Charge) : Charge :=
  ⟨a.visits + b.visits, a.queries + b.queries, a.hops + b.hops,
    a.extraJoins + b.extraJoins, a.endpointTests + b.endpointTests⟩

def baseReads (c : Charge) : Nat := c.queries
def mapReads (c : Charge) : Nat := c.hops
def joinBound (c : Charge) : Nat :=
  2 * c.visits + 2 * c.hops + 2 * c.queries + c.extraJoins

end Charge

def Action.charge {W : Model H m} {B : CutPair H} {R : Fin H.vertexCount → Prop}
    {S : Fin m → Prop} {a : W.Occ} (t : Action W B R S a) : Charge :=
  match t with
  | .direct _ => ⟨1, 0, 0, 0, 2⟩
  | .lift _ q => ⟨1, 1, q.route.hops, 0, 0⟩
  | .skip _ _ => ⟨1, 0, 0, 0, 0⟩

@[simp] theorem Action.charge_visits {W : Model H m} {B : CutPair H}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop} {a : W.Occ}
    (t : Action W B R S a) : t.charge.visits = 1 := by
  cases t <;> rfl

def Site.charge {W : Model H m} {B : CutPair H} {y : Fin H.vertexCount}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop} (I : Site W B y R S) :
    Charge :=
  I.items.foldr (fun t c => t.action.charge.add c) Charge.zero

theorem Site.charge_visits {W : Model H m} {B : CutPair H} {y : Fin H.vertexCount}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop} (I : Site W B y R S) :
    I.charge.visits = (W.incoming y).length := by
  have h : ∀ ts : List (Item W B R S),
      (ts.foldr (fun t c => t.action.charge.add c) Charge.zero).visits =
        ts.length := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      rw [List.foldr_cons]
      change t.action.charge.visits +
        (ts.foldr (fun item c => item.action.charge.add c) Charge.zero).visits =
          (t :: ts).length
      rw [Action.charge_visits, ih, List.length_cons] <;> omega
  rw [← I.keep, List.length_map]
  exact h I.items

namespace Kernel

variable {W : Model H m} {D : Deps H.vertexCount m} (K : Kernel W D)

def freshCharge (i : Fin m) (k : Fin 2) : Charge :=
  if e : W.slot (W.parent i) (W.endpoint (W.child i) k) = none then
    ⟨0, 1, (K.fresh i k e).route.hops, 0, 2⟩
  else ⟨0, 0, 0, 0, 2⟩

def installCharge (i : Fin m) : Charge :=
  ((K.freshCharge i 0).add (K.freshCharge i 1)).add ⟨0, 0, 0, 2, 4⟩

def baseCharge (y : Fin H.vertexCount) : Charge :=
  match e : W.owner y with
  | none => Charge.zero
  | some B => (K.site y B e).charge

theorem freshCharge_queries (i : Fin m) (k : Fin 2) :
    (K.freshCharge i k).queries ≤ 1 := by
  unfold freshCharge
  split <;> simp

theorem installCharge_queries (i : Fin m) :
    (K.installCharge i).queries ≤ 2 := by
  have h0 := K.freshCharge_queries i 0
  have h1 := K.freshCharge_queries i 1
  change (K.freshCharge i 0).queries + (K.freshCharge i 1).queries + 0 ≤ 2
  omega

theorem baseCharge_visits (y : Fin H.vertexCount) (B : CutPair H)
    (e : W.owner y = some B) :
    (K.baseCharge y).visits = (W.incoming y).length := by
  unfold baseCharge
  split
  next he =>
    have hbad : (none : Option (CutPair H)) = some B := he.symm.trans e
    cases hbad
  next B' he =>
    exact (K.site y B' he).charge_visits

end Kernel


end PaperB.BuiltExit
