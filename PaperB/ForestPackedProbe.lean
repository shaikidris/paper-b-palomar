module

public import PaperB.ForestRealCounts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.LabelledQuotient.ForestWordCharges

open PaperB _root_.EX24 _root_.EX24.PreStep
open ForestHead

structure MeasuredTest where
  result : Bool × Nat
  charge : Nat

structure MeasuredProbe where
  result : Probe
  charge : Nat

/-- Keep the other selector operations unchanged and use the packed query results. -/
def wordSelectors {H : LabelledQuotient} (R : JumpWordRegion) (mem : Array Nat)
    (S : Selectors H) : Selectors H :=
  { S with
    atDepth := fun u d => (ancestorAtDepthWords R mem u d).1
    ancestor := fun a u => (decideAncestorWords R mem a u).1 }

def raw {H : LabelledQuotient} (R : JumpWordRegion) (mem : Array Nat)
    (S : Selectors H) (a : Nat) (B : CutPair H) (u : Vertex H) :
    MeasuredTest :=
  if B.Mem u then ⟨(true, 0), 0⟩
  else
    let q := decideAncestorWords R mem a (S.label u)
    ⟨(q.1, 1), q.2.length⟩

theorem raw_result {H : LabelledQuotient} (R : JumpWordRegion) (mem : Array Nat)
    (S : Selectors H) (a : Nat) (B : CutPair H) (u : Vertex H) :
    (raw R mem S a B u).result = ForestHead.raw (wordSelectors R mem S) a B u := by
  by_cases h : B.Mem u <;> simp [raw, ForestHead.raw, wordSelectors, h]

/-- Charge the failing test, but neither execute nor charge its tail. -/
def scan {α : Type} (test : α → MeasuredTest) : List α → MeasuredProbe
  | [] => ⟨⟨true, 0, 0, 0⟩, 0⟩
  | x :: xs =>
    let q := test x
    if q.result.1 then
      let r := scan test xs
      ⟨⟨r.result.ok, r.result.tests + 1, 0,
          r.result.ancestryCalls + q.result.2⟩, r.charge + q.charge⟩
    else
      ⟨⟨false, 1, 0, q.result.2⟩, q.charge⟩

theorem scan_result {α : Type} (test : α → MeasuredTest) (xs : List α) :
    (scan test xs).result = ForestHead.scan (fun x => (test x).result) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : (test x).result.1 = true
    · simp only [scan, ForestHead.scan, if_pos h, ih]
    · simp only [scan, ForestHead.scan, if_neg h]

theorem scan_charge_le {α : Type} (test : α → MeasuredTest) (K : Nat)
    (xs : List α) (hTest : ∀ x ∈ xs, (test x).charge ≤ K) :
    (scan test xs).charge ≤ K * (scan test xs).result.tests := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have hx := hTest x (List.mem_cons.mpr (Or.inl rfl))
    by_cases h : (test x).result.1 = true
    · have ht := ih (fun u hu => hTest u (List.mem_cons.mpr (Or.inr hu)))
      simpa only [scan, if_pos h, Nat.mul_add, Nat.mul_one] using
        (Nat.add_le_add ht hx)
    · simpa only [scan, if_neg h, Nat.mul_one] using hx

/-- Only the two packed query traces are charged here. The depth guard and
pair and label accesses are not part of this selector-word charge. -/
def probe {H : LabelledQuotient} (R : JumpWordRegion) (mem : Array Nat)
    (S : Selectors H) (xs : List (Vertex H)) (m : Vertex H) (d : Nat) :
    MeasuredProbe :=
  if d = 0 then ⟨⟨true, 0, 0, 0⟩, 0⟩
  else if d ≤ S.depth (S.label m) then
    let q := ancestorAtDepthWords R mem (S.label m) d
    let r := scan (raw R mem S q.1 (S.key q.1)) xs
    ⟨{ r.result with depthCalls := 1 }, q.2.length + r.charge⟩
  else ⟨⟨false, 0, 0, 0⟩, 0⟩

/-- The depth-zero sentinel bypasses even the depth guard. -/
@[simp] theorem probe_zero {H : LabelledQuotient} (R : JumpWordRegion)
    (mem : Array Nat) (S : Selectors H) (xs : List (Vertex H)) (m : Vertex H) :
    probe R mem S xs m 0 = ⟨⟨true, 0, 0, 0⟩, 0⟩ := by
  simp [probe]

theorem probe_result {H : LabelledQuotient} (R : JumpWordRegion) (mem : Array Nat)
    (S : Selectors H) (xs : List (Vertex H)) (m : Vertex H) (d : Nat) :
    (probe R mem S xs m d).result =
      ForestHead.probe (wordSelectors R mem S) xs m d := by
  by_cases hz : d = 0
  · simp only [probe, ForestHead.probe, if_pos hz]
  · by_cases hd : d ≤ S.depth (S.label m)
    · simp [probe, ForestHead.probe, hz, hd, scan_result, raw_result, wordSelectors, ForestHead.raw]
      exact ⟨rfl, rfl, rfl⟩
    · simp [probe, ForestHead.probe, wordSelectors, hz, hd]

private theorem aux_lt_size {F : JumpForest} (hF : ValidJumpForest F)
    (fuel u d : Nat) (hu : u < F.size) :
    F.ancestorAtDepthAux fuel u d < F.size := by
  induction fuel generalizing u with
  | zero => exact hu
  | succ fuel ih =>
    rw [JumpForest.ancestorAtDepthAux_succ]
    split
    · exact ih _ (hF.stepToDepth_lt_size hu d)
    · exact hu

theorem probe_charge_le {H : LabelledQuotient} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    (S : Selectors H) (xs : List (Vertex H)) (m : Vertex H) (d : Nat)
    {n L : Nat} (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L)
    (hPivot : S.label m < F.size)
    (hLabels : ∀ u ∈ xs, S.label u < F.size) :
    (probe R mem S xs m d).charge ≤ 22 * L * (1 + (probe R mem S xs m d).result.tests) := by
  by_cases hz : d = 0
  · simp [probe, hz]
  by_cases hd : d ≤ S.depth (S.label m)
  · have hL : 1 ≤ L := by
      by_cases h : 1 ≤ L
      · exact h
      · have h0 : L = 0 := by omega
        have hBad : n + 2 ≤ 1 := by simpa [h0] using hPow
        omega
    have hLinear : 1 + 3 * (6 * L + 1) ≤ 22 * L := by omega
    let q := ancestorAtDepthWords R mem (S.label m) d
    have hq := ancestorAtDepthWords_spec hLay hPivot hInserted hPow d
    have hqValue : q.1 = F.ancestorAtDepth (S.label m) d := hq.1
    have ha : q.1 < F.size := by
      rw [hqValue]
      change F.ancestorAtDepthAux (F.depthOf (S.label m) - d) (S.label m) d < F.size
      exact aux_lt_size hLay.valid _ _ _ hPivot
    have hqCharge : q.2.length ≤ 22 * L := Nat.le_trans hq.2.2.1 hLinear
    let test := raw R mem S q.1 (S.key q.1)
    have ht : ∀ u ∈ xs, (test u).charge ≤ 22 * L := by
      intro u hu
      by_cases hMem : (S.key q.1).Mem u
      · simp [test, raw, hMem]
      · have hAnc := decideAncestorWords_spec hLay ha (hLabels u hu) hInserted hPow
        simpa only [test, raw, if_neg hMem] using (Nat.le_trans hAnc.2.1 hLinear)
    have hs := scan_charge_le test (22 * L) xs ht
    simp only [probe, if_neg hz, if_pos hd]
    change q.2.length + (scan test xs).charge ≤
      22 * L * (1 + (scan test xs).result.tests)
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add hqCharge hs
  · simp [probe, hz, hd]

/-- An occupied back entry gives a physically valid argument to a packed query. -/
theorem occupied_lt_size {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} (g : Grounded c F t)
    {a : Nat} {B : CutPair H} (h : t.back[a]? = some (some B)) :
    a < F.size := by
  rw [g.size_eq]
  exact (g.backward a B h).1

/-- A prior label can also be the artificial root, which has no occupied back entry. -/
theorem zero_or_occupied_lt_size {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} (g : Grounded c F t) {a : Nat}
    (h : a = 0 ∨ ∃ B : CutPair H, t.back[a]? = some (some B)) :
    a < F.size := by
  rcases h with rfl | ⟨B, hB⟩
  · obtain ⟨_, inv⟩ := g.layout.valid.exists_forestInvariant
    exact inv.size_pos
  · exact occupied_lt_size g hB

def packedProbe {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (d : Nat) : MeasuredProbe :=
  probe c.region s.tables.mem (selectors c.usePackedWords s) xs m d

theorem packedProbe_result {H : LabelledQuotient} (c : Config H) (s : State H)
    (xs : List (Vertex H)) (m : Vertex H) (d : Nat) :
    (packedProbe c s xs m d).result =
      ForestHead.probe (selectors c.usePackedWords s) xs m d :=
  probe_result c.region s.tables.mem (selectors c.usePackedWords s) xs m d

/-- The local selector-word bound at a grounded prefix. The prefix supplies
physical label validity for earlier vertices; no primitive-time premise is used. -/
theorem packedProbe_charge_of_prefix {H : LabelledQuotient} {c : Config H}
    {s : State H} {F : JumpForest} (g : Grounded c F s.tables)
    (rank : Vertex H → Nat) (r : Nat) (xs : List (Vertex H)) (m : Vertex H)
    (d : Nat) {n L : Nat} (hInserted : F.numInserted ≤ n) (hPow : n + 2 ≤ 2 ^ L)
    (hPivot : (selectors c.usePackedWords s).label m < s.tables.next)
    (hPrior : ∀ u, rank u < r →
      (selectors c.usePackedWords s).label u < s.tables.next)
    (hPred : ∀ u ∈ xs, rank u < r) :
    (packedProbe c s xs m d).charge ≤
      22 * L * (1 + (ForestHead.probe (selectors c.usePackedWords s) xs m d).tests) := by
  rw [← packedProbe_result c s xs m d]
  apply probe_charge_le g.layout (selectors c.usePackedWords s) xs m d hInserted hPow
  · simpa only [g.size_eq] using hPivot
  · intro u hu
    simpa only [g.size_eq] using hPrior u (hPred u hu)

end PaperB.LabelledQuotient.ForestWordCharges
