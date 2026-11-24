module

public import PaperB.ForestPackedProbe

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.LabelledQuotient.ForestPackedSearch

open ForestHead _root_.EX24 _root_.EX24.PreStep
open ForestWordCharges (MeasuredProbe packedProbe packedProbe_result packedProbe_charge_of_prefix)

structure ChargedSearch where
  result : ForestHead.SearchResult
  charge : Nat

/-- Charge only the midpoint probes that the search evaluates. -/
def measuredSearch (p : Nat → MeasuredProbe) : Nat → Nat → Nat → ChargedSearch
  | 0, lo, _ => ⟨⟨lo, 0, 0, 0, 0⟩, 0⟩
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then ⟨⟨lo, 0, 0, 0, 0⟩, 0⟩
    else
      let mid := lo + (hi - lo) / 2
      let q := p mid
      let r := if q.result.ok then measuredSearch p fuel mid hi
               else measuredSearch p fuel lo mid
      ⟨ForestHead.addProbe q.result r.result, q.charge + r.charge⟩

/-- The trace of evaluated midpoints, in evaluation order. -/
def evaluatedMidpoints (ok : Nat → Bool) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then []
    else
      let mid := lo + (hi - lo) / 2
      mid :: (if ok mid then evaluatedMidpoints ok fuel mid hi
              else evaluatedMidpoints ok fuel lo mid)

theorem measuredSearch_project (p : Nat → MeasuredProbe)
    (q : Nat → ForestHead.Probe) (hProject : ∀ d, (p d).result = q d)
    (fuel lo hi : Nat) :
    (measuredSearch p fuel lo hi).result = ForestHead.measuredSearch q fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [measuredSearch, ForestHead.measuredSearch, hs]
    · by_cases hp : (q (lo + (hi - lo) / 2)).ok = true
      all_goals simp [measuredSearch, ForestHead.measuredSearch, hs, hProject, hp, ih]

theorem measuredSearch_charge_eq (p : Nat → MeasuredProbe)
    (q : Nat → ForestHead.Probe) (hProject : ∀ d, (p d).result = q d)
    (fuel lo hi : Nat) :
    (measuredSearch p fuel lo hi).charge =
      ((evaluatedMidpoints (fun d => (q d).ok) fuel lo hi).map
        (fun d => (p d).charge)).sum := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [measuredSearch, evaluatedMidpoints, hs]
    · by_cases hp : (q (lo + (hi - lo) / 2)).ok = true
      all_goals simp [measuredSearch, evaluatedMidpoints, hs, hProject, hp, ih]

theorem measuredSearch_charge_le (p : Nat → MeasuredProbe)
    (q : Nat → ForestHead.Probe) (hProject : ∀ d, (p d).result = q d)
    (L : Nat) (hCharge : ∀ d, (p d).charge ≤ 22 * L * (1 + (q d).tests))
    (fuel lo hi : Nat) :
    (measuredSearch p fuel lo hi).charge ≤
      22 * L * ((ForestHead.measuredSearch q fuel lo hi).comparisons +
        (ForestHead.measuredSearch q fuel lo hi).tests) := by
  induction fuel generalizing lo hi with
  | zero => simp [measuredSearch, ForestHead.measuredSearch]
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [measuredSearch, ForestHead.measuredSearch, hs]
    · let mid := lo + (hi - lo) / 2
      have combine (a b : Nat) :
          (p mid).charge + (measuredSearch p fuel a b).charge ≤
            22 * L * (((ForestHead.measuredSearch q fuel a b).comparisons + 1) +
              ((ForestHead.measuredSearch q fuel a b).tests + (q mid).tests)) := by
        calc
          _ ≤ 22 * L * (1 + (q mid).tests) +
                22 * L * ((ForestHead.measuredSearch q fuel a b).comparisons +
                  (ForestHead.measuredSearch q fuel a b).tests) :=
            Nat.add_le_add (hCharge mid) (ih a b)
          _ = _ := by
            simp only [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      by_cases hp : (q (lo + (hi - lo) / 2)).ok = true
      · simpa only [measuredSearch, ForestHead.measuredSearch, if_neg hs,
          hProject, if_pos hp, ForestHead.addProbe] using combine mid hi
      · simpa only [measuredSearch, ForestHead.measuredSearch, if_neg hs,
          hProject, if_neg hp, ForestHead.addProbe] using combine lo mid

def measuredLog (p : Nat → MeasuredProbe) (hi : Nat) : ChargedSearch :=
  measuredSearch p (Nat.log2 hi + 1) 0 hi

theorem measuredLog_project (p : Nat → MeasuredProbe)
    (q : Nat → ForestHead.Probe) (hProject : ∀ d, (p d).result = q d) (hi : Nat) :
    (measuredLog p hi).result = ForestHead.measuredLog q hi :=
  measuredSearch_project p q hProject (Nat.log2 hi + 1) 0 hi

def packedSearch {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (fuel lo hi : Nat) : ChargedSearch :=
  measuredSearch (packedProbe c s xs m) fuel lo hi

def packedSearch_project {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (fuel lo hi : Nat) :=
  show (packedSearch c s xs m fuel lo hi).result = _ from
    measuredSearch_project (packedProbe c s xs m) _
      (packedProbe_result c s xs m) fuel lo hi

def packedSearch_charge_eq {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (fuel lo hi : Nat) :=
  show (packedSearch c s xs m fuel lo hi).charge = _ from
    measuredSearch_charge_eq (packedProbe c s xs m) _
      (packedProbe_result c s xs m) fuel lo hi

/-- Use the concrete per-probe certificate at the same grounded prefix
throughout the search. -/
def packedSearch_charge_of_prefix {H : LabelledQuotient}
    {c : _} {s : _} {F : _} (g : _)
    (rank : Vertex H → Nat) (r : Nat) (xs : List (Vertex H)) (m : Vertex H)
    (fuel lo hi : Nat) {n L : Nat}
    (hInserted : _) (hPow : _) (hPivot : _) (hPrior : _) (hPred : _) :=
  show (packedSearch c s xs m fuel lo hi).charge ≤ _ from
    measuredSearch_charge_le (packedProbe c s xs m) _
      (packedProbe_result c s xs m) L
      (fun d => packedProbe_charge_of_prefix (c := c) (s := s) (F := F)
        (n := n) (L := L) g rank r xs m d hInserted hPow hPivot hPrior hPred)
      fuel lo hi

/-- Depth zero takes the sentinel path. At positive depth, charge the
unguarded packed ancestor query performed by `nodeAt`. -/
def lastNodeAtCharge {H : LabelledQuotient} (c : Config H) (s : State H)
    (m : Vertex H) (d : Nat) : Nat :=
  if d = 0 then 0
  else
    (ancestorAtDepthWords c.region s.tables.mem
      ((selectors c.usePackedWords s).label m) d).2.length

@[simp] theorem lastNodeAtCharge_zero {H : LabelledQuotient} (c : Config H)
    (s : State H) (m : Vertex H) : lastNodeAtCharge c s m 0 = 0 := rfl

theorem lastNodeAtCharge_of_ne_zero {H : LabelledQuotient} (c : Config H)
    (s : State H) (m : Vertex H) (d : Nat) (hd : d ≠ 0) :
    lastNodeAtCharge c s m d =
      (ancestorAtDepthWords c.region s.tables.mem
        ((selectors c.usePackedWords s).label m) d).2.length := by
  simp only [lastNodeAtCharge, if_neg hd]

theorem lastNodeAtCharge_le_of_prefix {H : LabelledQuotient} {c : Config H}
    {s : State H} {F : JumpForest} (g : Grounded c F s.tables)
    (m : Vertex H) (d : Nat) {n L : Nat} (hInserted : F.numInserted ≤ n)
    (hPow : n + 2 ≤ 2 ^ L)
    (hPivot : (selectors c.usePackedWords s).label m < s.tables.next) :
    lastNodeAtCharge c s m d ≤ 22 * L := by
  by_cases hd : d = 0
  · subst d
    simp only [lastNodeAtCharge_zero, Nat.zero_le]
  · have hu : (selectors c.usePackedWords s).label m < F.size := by
      simpa only [g.size_eq] using hPivot
    have hLen :
        (ancestorAtDepthWords c.region s.tables.mem
          ((selectors c.usePackedWords s).label m) d).2.length ≤
          1 + 3 * (6 * L + 1) :=
      (ancestorAtDepthWords_spec g.layout hu hInserted hPow d).2.2.1
    have hL : 1 ≤ L := by
      cases L with
      | zero =>
        simp only [Nat.pow_zero] at hPow
        omega
      | succ k =>
        exact Nat.succ_le_succ (Nat.zero_le k)
    rw [lastNodeAtCharge_of_ne_zero c s m d hd]
    omega

structure ChargedActive (H : LabelledQuotient) where
  result : ForestHead.Measured H
  charge : Nat

def activeWithCharge {H : LabelledQuotient} (S : Selectors H) (xs : List (Vertex H))
    (m : Vertex H) (key : Option (CutPair H)) (p : Nat → MeasuredProbe)
    (lastCharge : Nat → Nat)
    (_hProject : ∀ (d : Nat), (p d).result = ForestHead.probe S xs m d) :
    ChargedActive H :=
  let r := measuredLog p (S.depth (S.label m) + 1)
  ⟨⟨finish (nodeAt S (S.label m) r.result.cut) key, r.result⟩,
    r.charge + lastCharge r.result.cut⟩

theorem activeWithCharge_project {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H))
    (p : Nat → MeasuredProbe) (lastCharge : Nat → Nat)
    (hProject : ∀ (d : Nat), (p d).result = ForestHead.probe S xs m d) :
    (activeWithCharge S xs m key p lastCharge hProject).result =
      ForestHead.active S xs m key := by
  simp only [activeWithCharge, ForestHead.active,
    measuredLog_project p (ForestHead.probe S xs m) hProject]

theorem activeWithCharge_charge_eq {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H))
    (p : Nat → MeasuredProbe) (lastCharge : Nat → Nat)
    (hProject : ∀ (d : Nat), (p d).result = ForestHead.probe S xs m d) :
    let hi : Nat := S.depth (S.label m) + 1
    (activeWithCharge S xs m key p lastCharge hProject).charge =
      ((evaluatedMidpoints (fun (d : Nat) => (ForestHead.probe S xs m d).ok)
        (Nat.log2 hi + 1) 0 hi).map (fun (d : Nat) => (p d).charge)).sum +
        lastCharge (ForestHead.active S xs m key).search.cut := by
  simp only [activeWithCharge, ForestHead.active, measuredLog, ForestHead.measuredLog,
    measuredSearch_project p (ForestHead.probe S xs m) hProject,
    measuredSearch_charge_eq p (ForestHead.probe S xs m) hProject]

theorem activeWithCharge_charge_le {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H))
    (p : Nat → MeasuredProbe) (lastCharge : Nat → Nat)
    (hProject : ∀ (d : Nat), (p d).result = ForestHead.probe S xs m d)
    (L : Nat)
    (hCharge : ∀ (d : Nat),
      (p d).charge ≤ 22 * L * (1 + (ForestHead.probe S xs m d).tests)) :
    (activeWithCharge S xs m key p lastCharge hProject).charge ≤
      22 * L * ((ForestHead.active S xs m key).search.comparisons +
        (ForestHead.active S xs m key).search.tests) +
        lastCharge (ForestHead.active S xs m key).search.cut := by
  dsimp only [activeWithCharge, ForestHead.active, measuredLog, ForestHead.measuredLog]
  rw [measuredSearch_project p (ForestHead.probe S xs m) hProject]
  exact Nat.add_le_add_right
    (measuredSearch_charge_le p (ForestHead.probe S xs m) hProject L hCharge
      (Nat.log2 (S.depth (S.label m) + 1) + 1) 0 (S.depth (S.label m) + 1)) _

def packedActive {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H)) :
    ChargedActive H :=
  activeWithCharge (selectors c.usePackedWords s) xs m key
    (packedProbe c s xs m) (lastNodeAtCharge c s m) (packedProbe_result c s xs m)

theorem packedActive_project {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H)) :
    (packedActive c s xs m key).result =
      ForestHead.active (selectors c.usePackedWords s) xs m key :=
  activeWithCharge_project (selectors c.usePackedWords s) xs m key
    (packedProbe c s xs m) (lastNodeAtCharge c s m) (packedProbe_result c s xs m)

theorem packedActive_charge_eq {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H)) :
    let S : Selectors H := selectors c.usePackedWords s
    let hi : Nat := S.depth (S.label m) + 1
    (packedActive c s xs m key).charge =
      ((evaluatedMidpoints (fun (d : Nat) => (ForestHead.probe S xs m d).ok)
        (Nat.log2 hi + 1) 0 hi).map (fun (d : Nat) => (packedProbe c s xs m d).charge)).sum +
        lastNodeAtCharge c s m (ForestHead.active S xs m key).search.cut :=
  activeWithCharge_charge_eq (selectors c.usePackedWords s) xs m key
    (packedProbe c s xs m) (lastNodeAtCharge c s m) (packedProbe_result c s xs m)

theorem packedActive_charge_of_prefix {H : LabelledQuotient} {c : Config H}
    {s : State H} {F : JumpForest} (g : Grounded c F s.tables)
    (rank : Vertex H → Nat) (r : Nat) (xs : List (Vertex H)) (m : Vertex H)
    (key : Option (CutPair H)) {n L : Nat}
    (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L)
    (hPivot : (selectors c.usePackedWords s).label m < s.tables.next)
    (hPrior : ∀ (u : Vertex H), rank u < r →
      (selectors c.usePackedWords s).label u < s.tables.next)
    (hPred : ∀ (u : Vertex H), u ∈ xs → rank u < r) :
    (packedActive c s xs m key).charge ≤
      22 * L * ((ForestHead.active (selectors c.usePackedWords s) xs m key).search.comparisons +
        (ForestHead.active (selectors c.usePackedWords s) xs m key).search.tests + 1) := by
  let S : Selectors H := selectors c.usePackedWords s
  let a : ForestHead.Measured H := ForestHead.active S xs m key
  have hLast : lastNodeAtCharge c s m a.search.cut ≤ 22 * L :=
    lastNodeAtCharge_le_of_prefix g m a.search.cut hInserted hPow hPivot
  calc
    (packedActive c s xs m key).charge ≤
        22 * L * (a.search.comparisons + a.search.tests) +
          lastNodeAtCharge c s m a.search.cut :=
      activeWithCharge_charge_le S xs m key (packedProbe c s xs m)
        (lastNodeAtCharge c s m) (packedProbe_result c s xs m) L
        (fun (d : Nat) =>
          packedProbe_charge_of_prefix g rank r xs m d hInserted hPow hPivot hPrior hPred)
    _ ≤ 22 * L * (a.search.comparisons + a.search.tests) + 22 * L :=
      Nat.add_le_add_left hLast (22 * L * (a.search.comparisons + a.search.tests))
    _ = 22 * L * (a.search.comparisons + a.search.tests + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]

end PaperB.LabelledQuotient.ForestPackedSearch
