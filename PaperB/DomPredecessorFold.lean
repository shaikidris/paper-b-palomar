module

public import PaperB.JumpLCA
public import PaperB.Graph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Place after the JumpForestCommonAncestor and reachable-predecessor declarations.
namespace PaperB
namespace JumpForestPredecessorFold

open JumpForestCommonAncestor

universe u

/-- Keep the original occurrence, not just its forest slot. -/
structure Step (α : Type u) where
  before : Nat
  occurrence : α
  probes : Nat

/-- The seed costs no LCA query. Each subsequent occurrence costs one query. -/
def run {α : Type u} (q : Nat → Nat → Nat × Nat) (slot : α → Nat) :
    Nat → List α → Nat × List (Step α)
  | seed, [] => (seed, [])
  | seed, x :: xs =>
      let ans := q seed (slot x)
      let rest := run q slot ans.1 xs
      (rest.1, ⟨seed, x, ans.2⟩ :: rest.2)

theorem run_occurrences {α : Type u} (q : Nat → Nat → Nat × Nat)
    (slot : α → Nat) (xs : List α) :
    ∀ seed : Nat, ((run q slot seed xs).2.map Step.occurrence) = xs := by
  induction xs with
  | nil =>
      intro seed
      rfl
  | cons x xs ih =>
      intro seed
      simp only [run, List.map_cons, ih]

def Exact (F : JumpForest) (q : Nat → Nat → Nat × Nat) : Prop :=
  ∀ u v : Nat, u < F.size → v < F.size →
    (q u v).1 < F.size ∧
      IsAncestor F (q u v).1 u ∧ IsAncestor F (q u v).1 v ∧
      ∀ a : Nat, (IsAncestor F a u ∧ IsAncestor F a v) ↔
        IsAncestor F a (q u v).1

theorem run_exact {α : Type u} {F : JumpForest}
    {q : Nat → Nat → Nat × Nat} (hq : Exact F q)
    (slot : α → Nat) (xs : List α) :
    ∀ seed : Nat, seed < F.size → (∀ x ∈ xs, slot x < F.size) →
      (run q slot seed xs).1 < F.size ∧
      (∀ a : Nat, IsAncestor F a (run q slot seed xs).1 ↔
        IsAncestor F a seed ∧ ∀ x ∈ xs, IsAncestor F a (slot x)) ∧
      ∀ s ∈ (run q slot seed xs).2,
        s.before < F.size ∧ slot s.occurrence < F.size ∧
          s.probes = (q s.before (slot s.occurrence)).2 := by
  induction xs with
  | nil =>
      intro seed hseed hslots
      simp [run, hseed]
  | cons x xs ih =>
      intro seed hseed hslots
      have hx : slot x < F.size := hslots x (List.mem_cons.mpr (Or.inl rfl))
      have htail : ∀ y ∈ xs, slot y < F.size :=
        fun y hy => hslots y (List.mem_cons.mpr (Or.inr hy))
      obtain ⟨hnext, _, _, hclass⟩ := hq seed (slot x) hseed hx
      obtain ⟨hresult, hanc, hsteps⟩ := ih (q seed (slot x)).1 hnext htail
      simp only [run]
      refine ⟨hresult, ?_, ?_⟩
      · intro a
        rw [hanc a, ← hclass a]
        constructor
        · rintro ⟨⟨ha, hax⟩, haxs⟩
          refine ⟨ha, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with he | hy
          · subst y
            exact hax
          · exact haxs y hy
        · rintro ⟨ha, hall⟩
          exact ⟨⟨ha, hall x (List.mem_cons.mpr (Or.inl rfl))⟩,
            fun y hy => hall y (List.mem_cons.mpr (Or.inr hy))⟩
      · intro s hs
        rcases List.mem_cons.mp hs with he | hs
        · subst s
          exact ⟨hseed, hx, rfl⟩
        · exact hsteps s hs

theorem run_refines {α : Type u} {F : JumpForest}
    {p q : Nat → Nat → Nat × Nat} (hq : Exact F q)
    (href : ∀ a b : Nat, a < F.size → b < F.size → p a b = q a b)
    (slot : α → Nat) (xs : List α) :
    ∀ seed : Nat, seed < F.size → (∀ x ∈ xs, slot x < F.size) →
      run p slot seed xs = run q slot seed xs := by
  induction xs with
  | nil =>
      intro seed hseed hslots
      rfl
  | cons x xs ih =>
      intro seed hseed hslots
      have hx : slot x < F.size := hslots x (List.mem_cons.mpr (Or.inl rfl))
      have htail : ∀ y ∈ xs, slot y < F.size :=
        fun y hy => hslots y (List.mem_cons.mpr (Or.inr hy))
      have hnext := (hq seed (slot x) hseed hx).1
      have he := href seed (slot x) hseed hx
      have ht := ih (q seed (slot x)).1 hnext htail
      simp only [run, he, ht]

def fold {α : Type u} (F : JumpForest) (slot : α → Nat)
    (head : α) (tail : List α) : Nat × List (Step α) :=
  run (query F) slot (slot head) tail

def wordFold {α : Type u} (R : JumpWordRegion) (mem : Array Nat)
    (slot : α → Nat) (head : α) (tail : List α) : Nat × List (Step α) :=
  run (wordQuery R mem) slot (slot head) tail

theorem fold_exact {α : Type u} {F : JumpForest} (hF : ValidJumpForest F)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size) :
    let w := (fold F slot head tail).1
    w < F.size ∧
      (∀ x ∈ head :: tail, IsAncestor F w (slot x)) ∧
      ∀ a : Nat, (∀ x ∈ head :: tail, IsAncestor F a (slot x)) ↔
        IsAncestor F a w := by
  dsimp only
  have hq : Exact F (query F) := fun _ _ hu hv => query_exact hF hu hv
  have hh : slot head < F.size :=
    hslots head (List.mem_cons.mpr (Or.inl rfl))
  have ht : ∀ x ∈ tail, slot x < F.size :=
    fun x hx => hslots x (List.mem_cons.mpr (Or.inr hx))
  obtain ⟨hw, hc, _⟩ := run_exact hq slot tail (slot head) hh ht
  have hclass (a : Nat) :
      (∀ x ∈ head :: tail, IsAncestor F a (slot x)) ↔
        IsAncestor F a (fold F slot head tail).1 := by
    change (∀ x ∈ head :: tail, IsAncestor F a (slot x)) ↔
      IsAncestor F a (run (query F) slot (slot head) tail).1
    rw [hc a]
    constructor
    · intro hall
      exact ⟨hall head (List.mem_cons.mpr (Or.inl rfl)),
        fun x hx => hall x (List.mem_cons.mpr (Or.inr hx))⟩
    · rintro ⟨ha, hat⟩ x hx
      rcases List.mem_cons.mp hx with he | hx
      · subst x
        exact ha
      · exact hat x hx
  have hrefl : IsAncestor F (fold F slot head tail).1 (fold F slot head tail).1 :=
    ⟨0, rfl⟩
  exact ⟨hw, (hclass _).mpr hrefl, hclass⟩

/-- Coverage identifies the collected sources with the reachable predecessors.
    It does not require distinct occurrences or a prefix-to-original ancestry map. -/
theorem fold_reachable_exact {α : Type u} {F : JumpForest}
    (hF : ValidJumpForest F) {g : Digraph} {r v : Fin g.vertexCount}
    (source : α → Fin g.vertexCount) (slot : Fin g.vertexCount → Nat)
    (head : α) (tail : List α)
    (hcover : ∀ p : Fin g.vertexCount,
      (g.HasArc p v ∧ g.InitiallyReachable r p) ↔
        ∃ x ∈ head :: tail, source x = p)
    (hslots : ∀ x ∈ head :: tail, slot (source x) < F.size) :
    let w := (fold F (fun x => slot (source x)) head tail).1
    w < F.size ∧
      (∀ p, g.HasArc p v → g.InitiallyReachable r p → IsAncestor F w (slot p)) ∧
      ∀ a : Nat,
        (∀ p, g.HasArc p v → g.InitiallyReachable r p → IsAncestor F a (slot p)) ↔
          IsAncestor F a w := by
  dsimp only
  obtain ⟨hw, hcommon, hclass⟩ :=
    fold_exact hF (fun x => slot (source x)) head tail hslots
  have hcollect (a : Nat) :
      (∀ p, g.HasArc p v → g.InitiallyReachable r p → IsAncestor F a (slot p)) ↔
        (∀ x ∈ head :: tail, IsAncestor F a (slot (source x))) := by
    constructor
    · intro hp x hx
      obtain ⟨ha, hr⟩ := (hcover (source x)).mpr ⟨x, hx, rfl⟩
      exact hp (source x) ha hr
    · intro hx p ha hr
      obtain ⟨x, hmem, he⟩ := (hcover p).mp ⟨ha, hr⟩
      rw [← he]
      exact hx x hmem
  exact ⟨hw, (hcollect _).mpr hcommon, fun a => (hcollect a).trans (hclass a)⟩

theorem wordFold_refines {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size) :
    wordFold R mem slot head tail = fold F slot head tail := by
  have hq : Exact F (query F) := fun _ _ hu hv => query_exact hLay.valid hu hv
  exact run_refines hq (fun _ _ hu hv => wordQuery_refines hLay hu hv hn hL)
    slot tail (slot head)
    (hslots head (List.mem_cons.mpr (Or.inl rfl)))
    (fun x hx => hslots x (List.mem_cons.mpr (Or.inr hx)))

theorem wordFold_exact {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size) :
    let w := (wordFold R mem slot head tail).1
    w < F.size ∧
      (∀ x ∈ head :: tail, IsAncestor F w (slot x)) ∧
      ∀ a : Nat, (∀ x ∈ head :: tail, IsAncestor F a (slot x)) ↔
        IsAncestor F a w := by
  dsimp only
  rw [wordFold_refines hLay hn hL slot head tail hslots]
  exact fold_exact hLay.valid slot head tail hslots

/-- Repeated original occurrences remain repeated, in their original order. -/
theorem wordFold_occurrences {α : Type u} (R : JumpWordRegion) (mem : Array Nat)
    (slot : α → Nat) (head : α) (tail : List α) :
    (wordFold R mem slot head tail).2.map Step.occurrence = tail :=
  run_occurrences (wordQuery R mem) slot tail (slot head)

theorem wordFold_query_count {α : Type u} (R : JumpWordRegion) (mem : Array Nat)
    (slot : α → Nat) (head : α) (tail : List α) :
    (wordFold R mem slot head tail).2.length = tail.length := by
  simpa only [List.length_map] using
    congrArg (fun xs : List α => xs.length)
      (wordFold_occurrences R mem slot head tail)

theorem wordFold_step_spec {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size)
    {s : Step α} (hs : s ∈ (wordFold R mem slot head tail).2) :
    s.before < F.size ∧ slot s.occurrence < F.size ∧
      s.probes = (wordQuery R mem s.before (slot s.occurrence)).2 := by
  have hq : Exact F (wordQuery R mem) :=
    fun _ _ hu hv => wordQuery_exact hLay hu hv hn hL
  exact (run_exact hq slot tail (slot head)
    (hslots head (List.mem_cons.mpr (Or.inl rfl)))
    (fun x hx => hslots x (List.mem_cons.mpr (Or.inr hx)))).2.2 s hs

/-- The fold is read-only: the same layout certifies every query's accesses,
    including the final retrieval at the cut depth. -/
theorem wordFold_step_safe {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size)
    {s : Step α} (hs : s ∈ (wordFold R mem slot head tail).2) :
    AllAccessesInRegion R.baseAddr R.endAddr (readRecordWords R mem s.before).2 ∧
    AllAccessesInRegion R.baseAddr R.endAddr
      (readRecordWords R mem (slot s.occurrence)).2 ∧
    (∀ d : Nat, AllAccessesInRegion R.baseAddr R.endAddr
      (ancestorAtDepthWords R mem s.before d).2) ∧
    (∀ d : Nat, AllAccessesInRegion R.baseAddr R.endAddr
      (ancestorAtDepthWords R mem (slot s.occurrence) d).2) := by
  obtain ⟨hu, hv, _⟩ := wordFold_step_spec hLay hn hL slot head tail hslots hs
  exact ⟨(readRecordWords_spec hLay hu).2.2, (readRecordWords_spec hLay hv).2.2,
    fun d => (ancestorAtDepthWords_spec hLay hu hn hL d).2.2.2,
    fun d => (ancestorAtDepthWords_spec hLay hv hn hL d).2.2.2⟩

def probeBudget {α : Type u} (F : JumpForest) (slot : α → Nat)
    (s : Step α) : Nat :=
  Nat.log2 (sharedDepth F s.before (slot s.occurrence) + 1) + 1

theorem wordFold_step_charges {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size)
    {s : Step α} (hs : s ∈ (wordFold R mem slot head tail).2)
    (ds : List Nat) (hds : ds.length ≤ s.probes) :
    evalCharge s.probes ≤ evalCharge (probeBudget F slot s) ∧
    wordReadBill R mem s.before (slot s.occurrence)
        (cut F s.before (slot s.occurrence)) ds ≤ readCharge L s.probes ∧
    wordOpBill R mem s.before (slot s.occurrence)
        (cut F s.before (slot s.occurrence)) ds ≤ operationCharge L s.probes ∧
    readCharge L s.probes ≤ readCharge L (probeBudget F slot s) ∧
    operationCharge L s.probes ≤ operationCharge L (probeBudget F slot s) := by
  obtain ⟨hu, hv, hp⟩ := wordFold_step_spec hLay hn hL slot head tail hslots hs
  have hd : ds.length ≤ (wordQuery R mem s.before (slot s.occurrence)).2 :=
    hp ▸ hds
  have hb := word_query_charges hLay hu hv hn hL ds hd
  dsimp only at hb
  simpa only [hp, probeBudget] using hb

def chargeSum {α : Type u} (charge : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => charge x + chargeSum charge xs

theorem chargeSum_le {α : Type u} (f g : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x ≤ g x) : chargeSum f xs ≤ chargeSum g xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      exact Nat.add_le_add (h x (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy))))

/-- Sum the query bills over occurrences, not over distinct slots. The seed has
    zero LCA charge. `depths` supplies the probes billed for each query. -/
theorem wordFold_charges {α : Type u} {R : JumpWordRegion}
    {F : JumpForest} {mem : Array Nat} (hLay : JumpWordLayout R F mem)
    {n L : Nat} (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (slot : α → Nat) (head : α) (tail : List α)
    (hslots : ∀ x ∈ head :: tail, slot x < F.size)
    (depths : Step α → List Nat)
    (hdepths : ∀ s ∈ (wordFold R mem slot head tail).2,
      (depths s).length ≤ s.probes) :
    let steps := (wordFold R mem slot head tail).2
    chargeSum (fun s => evalCharge s.probes) steps ≤
      chargeSum (fun s => evalCharge (probeBudget F slot s)) steps ∧
    chargeSum (fun s => wordReadBill R mem s.before (slot s.occurrence)
        (cut F s.before (slot s.occurrence)) (depths s)) steps ≤
      chargeSum (fun s => readCharge L (probeBudget F slot s)) steps ∧
    chargeSum (fun s => wordOpBill R mem s.before (slot s.occurrence)
        (cut F s.before (slot s.occurrence)) (depths s)) steps ≤
      chargeSum (fun s => operationCharge L (probeBudget F slot s)) steps := by
  dsimp only
  refine ⟨chargeSum_le _ _ _ ?_, chargeSum_le _ _ _ ?_, chargeSum_le _ _ _ ?_⟩
  · intro s hs
    exact (wordFold_step_charges hLay hn hL slot head tail hslots hs
      (depths s) (hdepths s hs)).1
  · intro s hs
    obtain ⟨_, hr, _, hr', _⟩ :=
      wordFold_step_charges hLay hn hL slot head tail hslots hs
        (depths s) (hdepths s hs)
    exact Nat.le_trans hr hr'
  · intro s hs
    obtain ⟨_, _, ho, _, ho'⟩ :=
      wordFold_step_charges hLay hn hL slot head tail hslots hs
        (depths s) (hdepths s hs)
    exact Nat.le_trans ho ho'

end JumpForestPredecessorFold
end PaperB
