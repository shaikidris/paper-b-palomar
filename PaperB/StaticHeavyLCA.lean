module

public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX16

universe u

variable {α : Type u}

structure Tables (α : Type u) where
  root : α
  parent : α → α
  depth : α → Nat
  heavy : α → Option α
  head : α → α
  size : α → Nat

/-- A downward path, represented by the parent edges at its lower endpoints. -/
inductive Path (T : Tables α) (ok : α → Prop) (a : α) : α → Prop where
  | refl : Path T ok a a
  | step {b : α} :
      b ≠ T.root → ok b → Path T ok a (T.parent b) → Path T ok a b

abbrev Anc (T : Tables α) (a b : α) : Prop :=
  Path T (fun _ => True) a b

abbrev HeavyPath (T : Tables α) (a b : α) : Prop :=
  Path T (fun c => T.heavy (T.parent c) = some c) a b

def Top (T : Tables α) (a : α) : Prop :=
  a ≠ T.root → T.heavy (T.parent a) ≠ some a

/-- Interface to the verified preprocessing. `head_path` and `head_top`
    describe the supplied maximal chain-head table. The size fields need
    only parent monotonicity and the verified light-edge halving theorem. -/
structure Valid (T : Tables α) : Prop where
  depth_root : T.depth T.root = 0
  depth_step : ∀ {b}, b ≠ T.root →
    T.depth (T.parent b) + 1 = T.depth b
  size_pos : ∀ b, 0 < T.size b
  size_step : ∀ {b}, b ≠ T.root → T.size b ≤ T.size (T.parent b)
  light_halves : ∀ {b}, b ≠ T.root → T.heavy (T.parent b) ≠ some b →
    2 * T.size b < T.size (T.parent b)
  head_path : ∀ b, HeavyPath T (T.head b) b
  head_top : ∀ b, Top T (T.head b)

variable {T : Tables α}

private theorem pathDepth (V : Valid T) {ok : α → Prop} {a b : α}
    (h : Path T ok a b) : T.depth a ≤ T.depth b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hn _ _ ih =>
      have hs := V.depth_step hn
      omega

private theorem pathSize (V : Valid T) {ok : α → Prop} {a b : α}
    (h : Path T ok a b) : T.size b ≤ T.size a := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hn _ _ ih => exact Nat.le_trans (V.size_step hn) ih

private theorem toAnc {ok : α → Prop} {a b : α}
    (h : Path T ok a b) : Anc T a b := by
  induction h with
  | refl => exact .refl
  | step hn _ _ ih => exact .step hn True.intro ih

private theorem ancTrans {a b c : α}
    (hab : Anc T a b) (hbc : Anc T b c) : Anc T a c := by
  induction hbc with
  | refl => exact hab
  | step hn _ _ ih => exact .step hn True.intro ih

private theorem rootAncAux [DecidableEq α] (V : Valid T)
    (n : Nat) (x : α) (h : T.depth x < n) : Anc T T.root x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
      exact if hx : x = T.root then
        hx.symm ▸ (Path.refl : Anc T T.root T.root)
      else
        Path.step hx True.intro
          (ih (T.parent x) (by
            have hs := V.depth_step hx
            omega))

private theorem rootAnc [DecidableEq α] (V : Valid T) (x : α) :
    Anc T T.root x :=
  rootAncAux V (T.depth x + 1) x (by omega)

/-- Truncate the filtered path at an ancestor of its endpoint. -/
private theorem pathPrefix (V : Valid T) {ok : α → Prop} {a b x : α}
    (ha : Anc T a x) (hb : Path T ok b x)
    (hle : T.depth b ≤ T.depth a) : Path T ok b a := by
  induction ha with
  | refl => exact hb
  | step hn _ hp ih =>
      cases hb with
      | refl =>
          have h₁ := pathDepth V hp
          have h₂ := V.depth_step hn
          omega
      | step _ _ hp' => exact ih hp'

private theorem ancParent (V : Valid T) {a b : α}
    (h : Anc T a b) (hlt : T.depth a < T.depth b) :
    Anc T a (T.parent b) := by
  cases h with
  | refl => omega
  | step _ _ hp => exact hp

private theorem topUnique {a b x : α}
    (ha : HeavyPath T a x) (hb : HeavyPath T b x)
    (hta : Top T a) (htb : Top T b) : a = b := by
  induction ha with
  | refl =>
      cases hb with
      | refl => rfl
      | step hn hh _ => exact False.elim (hta hn hh)
  | step hn hh _ ih =>
      cases hb with
      | refl => exact False.elim (htb hn hh)
      | step _ _ hp => exact ih hp

private theorem headOnPath (V : Valid T) {a x : α} (ha : Anc T a x)
    (hle : T.depth (T.head x) ≤ T.depth a) : T.head a = T.head x :=
  topUnique (V.head_path a) (pathPrefix V ha (V.head_path x) hle)
    (V.head_top a) (V.head_top x)

private theorem heavyAtDepth (V : Valid T) {a x y : α}
    (hx : HeavyPath T a x) (hy : HeavyPath T a y)
    (he : T.depth x = T.depth y) : x = y := by
  induction hx generalizing y with
  | refl =>
      cases hy with
      | refl => rfl
      | step hn _ hp =>
          have h₁ := pathDepth V hp
          have h₂ := V.depth_step hn
          omega
  | @step x hn hh hp ih =>
      cases hy with
      | refl =>
          have h₁ := pathDepth V hp
          have h₂ := V.depth_step hn
          omega
      | @step y hn' hh' hp' =>
          have d₁ := V.depth_step hn
          have d₂ := V.depth_step hn'
          have ep : T.parent x = T.parent y := by
            apply ih
            · exact hp'
            · omega
          have e : some x = some y := calc
            some x = T.heavy (T.parent x) := hh.symm
            _ = T.heavy (T.parent y) := congrArg T.heavy ep
            _ = some y := hh'
          exact Option.some.inj e

private theorem heavyAnc (V : Valid T) {a x y : α}
    (hx : HeavyPath T a x) (hy : HeavyPath T a y)
    (hle : T.depth x ≤ T.depth y) : Anc T x y := by
  induction hy with
  | refl =>
      have hd := pathDepth V hx
      have e := heavyAtDepth V hx (Path.refl : HeavyPath T a a) (by omega)
      cases e
      exact .refl
  | @step y hn hh hp ih =>
      by_cases he : T.depth x = T.depth y
      · have e := heavyAtDepth V hx (Path.step hn hh hp) he
        cases e
        exact .refl
      · have hd := V.depth_step hn
        exact .step hn True.intro (ih (by omega))

private theorem sameHeadAnc (V : Valid T) {x y : α}
    (hs : T.head x = T.head y) (hd : T.depth x ≤ T.depth y) :
    Anc T x y := by
  have hy := V.head_path y
  rw [← hs] at hy
  exact heavyAnc V (V.head_path x) hy hd

private theorem jumpNonroot [DecidableEq α] (V : Valid T) {x y : α}
    (hne : T.head x ≠ T.head y)
    (ord : T.depth (T.head y) ≤ T.depth (T.head x)) :
    T.head x ≠ T.root := by
  intro hx
  have hzero : T.depth (T.head y) = 0 := by
    rw [hx, V.depth_root] at ord
    omega
  have hy : T.head y = T.root :=
    if hr : T.head y = T.root then hr else False.elim (by
      have hd := V.depth_step hr
      omega)
  exact hne (hx.trans hy.symm)

private theorem jumpDepth (V : Valid T) {x : α} (hn : T.head x ≠ T.root) :
    T.depth (T.parent (T.head x)) < T.depth x := by
  have h₁ := pathDepth V (V.head_path x)
  have h₂ := V.depth_step hn
  omega

private theorem jumpSize (V : Valid T) {x : α} (hn : T.head x ≠ T.root) :
    2 * T.size x ≤ T.size (T.parent (T.head x)) :=
  Nat.le_trans (Nat.mul_le_mul_left 2 (pathSize V (V.head_path x)))
    (Nat.le_of_lt (V.light_halves hn (V.head_top x hn)))

/-- A jump at the deeper head preserves exactly the common ancestors. -/
private theorem jumpPreserves (V : Valid T) {x y a : α}
    (hn : T.head x ≠ T.root) (hne : T.head x ≠ T.head y)
    (ord : T.depth (T.head y) ≤ T.depth (T.head x)) :
    (Anc T a x ∧ Anc T a y) ↔
      (Anc T a (T.parent (T.head x)) ∧ Anc T a y) := by
  constructor
  · intro h
    by_cases hle : T.depth (T.head x) ≤ T.depth a
    · have hx := headOnPath V h.1 hle
      have hy := headOnPath V h.2 (Nat.le_trans ord hle)
      exact False.elim (hne (hx.symm.trans hy))
    · have hlt : T.depth a < T.depth (T.head x) := by omega
      have ha : Anc T a (T.head x) :=
        pathPrefix V (toAnc (V.head_path x)) h.1 (Nat.le_of_lt hlt)
      exact ⟨ancParent V ha hlt, h.2⟩
  · intro h
    have ha : Anc T a (T.head x) := .step hn True.intro h.1
    exact ⟨ancTrans ha (toAnc (V.head_path x)), h.2⟩

/-- The ancestors of the answer are exactly the common ancestors. -/
def IsLCA (T : Tables α) (x y a : α) : Prop :=
  ∀ z, (Anc T z x ∧ Anc T z y) ↔ Anc T z a

theorem IsLCA.common {x y a : α} (h : IsLCA T x y a) :
    Anc T a x ∧ Anc T a y :=
  (h a).mpr .refl

theorem IsLCA.lowest {x y a z : α} (h : IsLCA T x y a)
    (hx : Anc T z x) (hy : Anc T z y) : Anc T z a :=
  (h z).mp ⟨hx, hy⟩

theorem IsLCA.unique (V : Valid T) {x y a b : α}
    (ha : IsLCA T x y a) (hb : IsLCA T x y b) : a = b := by
  have hab := hb.lowest ha.common.1 ha.common.2
  have hba := ha.lowest hb.common.1 hb.common.2
  have he := Nat.le_antisymm (pathDepth V hab) (pathDepth V hba)
  cases hab with
  | refl => rfl
  | step hn _ hp =>
      have h₁ := V.depth_step hn
      have h₂ := pathDepth V hp
      omega

private theorem lcaOfAnc {x y : α} (h : Anc T x y) : IsLCA T x y x := by
  intro z
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, ancTrans hz h⟩⟩

private theorem lcaSwap {x y a : α} (h : IsLCA T x y a) :
    IsLCA T y x a := by
  intro z
  exact ⟨fun hz => (h z).mp ⟨hz.2, hz.1⟩,
    fun hz => let p := (h z).mpr hz; ⟨p.2, p.1⟩⟩

/-- Exact jump-count semantics. On equal head depths, jump on the left. -/
inductive Execution (T : Tables α) : α → α → α → Nat → Prop where
  | stopLeft {x y : α} :
      T.head x = T.head y → T.depth x ≤ T.depth y → Execution T x y x 0
  | stopRight {x y : α} :
      T.head x = T.head y → T.depth y < T.depth x → Execution T x y y 0
  | jumpLeft {x y a : α} {k : Nat} :
      T.head x ≠ T.head y → T.depth (T.head y) ≤ T.depth (T.head x) →
      Execution T (T.parent (T.head x)) y a k → Execution T x y a (k + 1)
  | jumpRight {x y a : α} {k : Nat} :
      T.head x ≠ T.head y → T.depth (T.head x) < T.depth (T.head y) →
      Execution T x (T.parent (T.head y)) a k → Execution T x y a (k + 1)

/-- Only `node` and `jumps` are retained at runtime. -/
structure Result (T : Tables α) (x y : α) where
  node : α
  jumps : Nat
  correct : IsLCA T x y node
  trace : Execution T x y node jumps
  charge : 2 ^ jumps * (T.size x * T.size y) ≤ T.size T.root * T.size T.root

private def finish [DecidableEq α] (V : Valid T) {x y a : α}
    (hc : IsLCA T x y a) (he : Execution T x y a 0) : Result T x y where
  node := a
  jumps := 0
  correct := hc
  trace := he
  charge := by
    simpa only [Nat.pow_zero, Nat.one_mul] using
      Nat.mul_le_mul (pathSize V (rootAnc V x)) (pathSize V (rootAnc V y))

private def run [DecidableEq α] (T : Tables α) (V : Valid T) :
    (fuel : Nat) → (x y : α) → T.depth x + T.depth y < fuel → Result T x y
  | 0, _, _, bound => False.elim (by omega)
  | n + 1, x, y, bound =>
    if hs : T.head x = T.head y then
      if hd : T.depth x ≤ T.depth y then
        finish V (lcaOfAnc (sameHeadAnc V hs hd)) (.stopLeft hs hd)
      else
        have hd' : T.depth y < T.depth x := by omega
        finish V (lcaSwap (lcaOfAnc (sameHeadAnc V hs.symm (Nat.le_of_lt hd'))))
          (.stopRight hs hd')
    else if hd : T.depth (T.head y) ≤ T.depth (T.head x) then
      have hn := jumpNonroot V hs hd
      have hdrop := jumpDepth V hn
      let r := run T V n (T.parent (T.head x)) y (by omega)
      { node := r.node
        jumps := r.jumps + 1
        correct := fun a => (jumpPreserves V hn hs hd).trans (r.correct a)
        trace := .jumpLeft hs hd r.trace
        charge := calc
          2 ^ (r.jumps + 1) * (T.size x * T.size y) =
              2 ^ r.jumps * ((2 * T.size x) * T.size y) := by
                simp only [Nat.pow_succ, Nat.mul_assoc]
          _ ≤ 2 ^ r.jumps * (T.size (T.parent (T.head x)) * T.size y) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (jumpSize V hn))
          _ ≤ T.size T.root * T.size T.root := r.charge }
    else
      have hd' : T.depth (T.head x) < T.depth (T.head y) := by omega
      have hn := jumpNonroot V (Ne.symm hs) (Nat.le_of_lt hd')
      have hdrop := jumpDepth V hn
      let r := run T V n x (T.parent (T.head y)) (by omega)
      { node := r.node
        jumps := r.jumps + 1
        correct := lcaSwap (fun a =>
          (jumpPreserves V hn (Ne.symm hs) (Nat.le_of_lt hd')).trans
            ((lcaSwap r.correct) a))
        trace := .jumpRight hs hd' r.trace
        charge := calc
          2 ^ (r.jumps + 1) * (T.size x * T.size y) =
              2 ^ r.jumps * (T.size x * (2 * T.size y)) := by
                simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ ≤ 2 ^ r.jumps * (T.size x * T.size (T.parent (T.head y))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (jumpSize V hn))
          _ ≤ T.size T.root * T.size T.root := r.charge }
termination_by structural fuel => fuel

/-- The depth sum is only a termination budget. The kernel performs one
    transition per charged jump, followed by one same-chain stop. -/
def lca [DecidableEq α] (V : Valid T) (x y : α) : Result T x y :=
  run T V (T.depth x + T.depth y + 1) x y (by omega)

theorem Result.pow_jumps_le (V : Valid T) {x y : α} (r : Result T x y) :
    2 ^ r.jumps ≤ T.size T.root * T.size T.root := by
  have hp := Nat.mul_pos (V.size_pos x) (V.size_pos y)
  calc
    2 ^ r.jumps = 2 ^ r.jumps * 1 := by simp
    _ ≤ 2 ^ r.jumps * (T.size x * T.size y) :=
      Nat.mul_le_mul_left _ (by omega)
    _ ≤ T.size T.root * T.size T.root := r.charge

private theorem powTwoMono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  induction b generalizing a with
  | zero =>
      have hz : a = 0 := by omega
      exact hz.symm ▸ (Nat.le_refl (2 ^ (0 : Nat)))
  | succ b ih =>
      by_cases he : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have h' : a ≤ b := by omega
        have hm := ih h'
        rw [Nat.pow_succ]
        omega

/-- If the root size fits in `bits` binary digits, fewer than `2 * bits`
    light edges are crossed. No logarithm is computed by the query. -/
theorem Result.jumps_lt_twice_bits (V : Valid T) {x y : α} (r : Result T x y)
    (bits : Nat) (hb : T.size T.root < 2 ^ bits) : r.jumps < bits + bits := by
  by_cases h : r.jumps < bits + bits
  · exact h
  · have hp := powTwoMono (a := bits + bits) (b := r.jumps) (by omega)
    rw [Nat.pow_add] at hp
    have h₁ := Nat.mul_le_mul_right (T.size T.root) (Nat.le_of_lt hb)
    have h₂ := Nat.mul_lt_mul_of_pos_left hb (show 0 < 2 ^ bits by omega)
    have h₃ := r.pow_jumps_le V
    omega

end EX16
