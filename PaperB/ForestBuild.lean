module

public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# `PaperB.ForestBuild` — Stage 1: Interface-Relative Prefix-Probe Charging Lemma

Standalone **interface-relative charging lemma** for EX2.4 (Paper B v1.3, Lemma 3.2).
This conditional arithmetic/aggregation theorem bounds total abstract operations by
`P.totalConst * ((n_H + m_H) * L ^ 2)` *given* explicit per-probe jump bounds,
per-predecessor ancestry-check bounds, per-head binary-search probe counts, and
linear/dictionary preprocessing bounds. It is **not** by itself a proof of the full
Lemma 3.2 bound until instantiated by the executable forest constructor, wired to
`PaperB.Forest` / `PaperB.Jumps`, and bridged to the `EX0.3` Word-RAM model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace ForestBuild

private theorem nat_zero_mul (b : Nat) : 0 * b = 0 := by
  induction b with
  | zero => rfl
  | succ k ih =>
      change 0 * k + 0 = 0
      omega

private theorem nat_succ_mul (a b : Nat) : (a + 1) * b = a * b + b := by
  induction b with
  | zero => rfl
  | succ k ih =>
      change (a + 1) * k + (a + 1) = (a * k + a) + (k + 1)
      omega

private theorem nat_mul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero =>
      change 0 = 0 * a
      exact (nat_zero_mul a).symm
  | succ k ih =>
      change a * k + a = (k + 1) * a
      rw [nat_succ_mul, ih]

private theorem nat_mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ k ih =>
      change a * (b + k) + a = a * b + (a * k + a)
      omega

private theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [nat_mul_comm (a + b) c, nat_mul_add c a b, nat_mul_comm c a, nat_mul_comm c b]

private theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ k ih =>
      change (a * b) * k + a * b = a * (b * k + b)
      rw [nat_mul_add, ih]

private theorem nat_mul_le_mul_right (c : Nat) {a b : Nat} (h : a ≤ b) :
    a * c ≤ b * c := by
  induction c with
  | zero =>
      change 0 ≤ 0
      omega
  | succ k ih =>
      change a * k + a ≤ b * k + b
      omega

private theorem nat_mul_le_mul_left (c : Nat) {a b : Nat} (h : a ≤ b) :
    c * a ≤ c * b := by
  rw [nat_mul_comm c a, nat_mul_comm c b]
  exact nat_mul_le_mul_right c h

private theorem nat_mul_le_mul {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d :=
  Nat.le_trans (nat_mul_le_mul_right c h₁) (nat_mul_le_mul_left b h₂)

private theorem nat_pow_two (a : Nat) : a ^ 2 = a * a := by
  change (1 * a) * a = a * a
  have h1 : 1 * a = a := by
    change (0 + 1) * a = a
    rw [nat_succ_mul, nat_zero_mul]
    omega
  rw [h1]

private theorem mul_L_mul_L (a b L : Nat) :
    (a * L) * (b * L) = a * b * L ^ 2 :=
  calc (a * L) * (b * L)
    _ = a * (L * (b * L)) := nat_mul_assoc a L (b * L)
    _ = a * ((L * b) * L) := congrArg (fun z => a * z) (nat_mul_assoc L b L).symm
    _ = a * ((b * L) * L) := congrArg (fun z => a * (z * L)) (nat_mul_comm L b)
    _ = a * (b * (L * L)) := congrArg (fun z => a * z) (nat_mul_assoc b L L)
    _ = (a * b) * (L * L) := (nat_mul_assoc a b (L * L)).symm
    _ = a * b * L ^ 2 := congrArg (fun z => (a * b) * z) (nat_pow_two L).symm

private theorem list_map_map {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      dsimp [List.map]
      rw [ih]

/-- Any `L` satisfying `n_H + 2 ≤ 2 ^ L` satisfies `1 ≤ L`. -/
theorem one_le_of_add_two_le_pow2 {n_H L : Nat} (hPow : n_H + 2 ≤ 2 ^ L) : 1 ≤ L := by
  cases L with
  | zero =>
      change n_H + 2 ≤ 1 at hPow
      omega
  | succ _ =>
      omega

theorem one_le_pow_two {L : Nat} (hL : 1 ≤ L) : 1 ≤ L ^ 2 :=
  calc 1
    _ = 1 * 1 := rfl
    _ ≤ L * L := nat_mul_le_mul hL hL
    _ = L ^ 2 := (nat_pow_two L).symm

theorem self_le_pow_two {L : Nat} (hL : 1 ≤ L) : L ≤ L ^ 2 :=
  calc L
    _ = L * 1 := by change L = L * 0 + L; omega
    _ ≤ L * L := nat_mul_le_mul_left L hL
    _ = L ^ 2 := (nat_pow_two L).symm

/-- Sum of natural-number operation counts across a list. -/
def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natSum xs

theorem natSum_le_length_mul (bound : Nat) (xs : List Nat)
    (hEach : ∀ x : Nat, x ∈ xs → x ≤ bound) :
    natSum xs ≤ xs.length * bound := by
  induction xs with
  | nil =>
      change 0 ≤ 0 * bound
      rw [nat_zero_mul]
      exact Nat.le_refl 0
  | cons x xs ih =>
      have hx : x ≤ bound := hEach x (List.mem_cons.mpr (Or.inl rfl))
      have hxs : natSum xs ≤ xs.length * bound :=
        ih (fun z hz => hEach z (List.mem_cons.mpr (Or.inr hz)))
      have hStep : x + natSum xs ≤ xs.length * bound + bound := by omega
      calc natSum (x :: xs)
        _ = x + natSum xs := rfl
        _ ≤ xs.length * bound + bound := hStep
        _ = (xs.length + 1) * bound := (nat_succ_mul xs.length bound).symm

/-- Explicit `Nat` cost constants for the interface-relative Lemma 3.2 charging model. -/
structure ChargingParams where
  /-- Prefix-probe factor: each head conducts at most `cProbe * L` binary-search probes. -/
  cProbe : Nat
  /-- Level-ancestor jump factor: locating the probed ancestor costs at most `cJump * L`. -/
  cJump : Nat
  /-- Predecessor-check factor: testing one distinct predecessor (endpoint check +
      growing-forest `decideAncestor`) costs at most `cAnc * L`. -/
  cAnc : Nat
  /-- Linear preprocessing / sweep-bookkeeping factor on `n_H + m_H`. -/
  cPre : Nat
  /-- Pair-key sorting / dictionary construction factor on `n_H * L`. -/
  cDict : Nat

/-- Combined explicit constant `cPre + cDict + cProbe * cJump + cProbe * cAnc`
    multiplying `(n_H + m_H) * L ^ 2`. -/
def ChargingParams.totalConst (P : ChargingParams) : Nat :=
  P.cPre + P.cDict + P.cProbe * P.cJump + P.cProbe * P.cAnc

/-- Single-probe charging lemma: 1 level-ancestor jump traversal (`≤ cJump * L`)
    plus `degY` predecessor loss checks each costing `≤ cAnc * L` costs at most
    `cJump * L + degY * (cAnc * L)`. -/
theorem probe_work_le (P : ChargingParams) (L degY jumpCost : Nat)
    (predCheckCosts : List Nat)
    (hJump : jumpCost ≤ P.cJump * L)
    (hDegLen : predCheckCosts.length = degY)
    (hPredChecks : ∀ c : Nat, c ∈ predCheckCosts → c ≤ P.cAnc * L) :
    jumpCost + natSum predCheckCosts ≤ P.cJump * L + degY * (P.cAnc * L) := by
  have hScan : natSum predCheckCosts ≤ degY * (P.cAnc * L) := by
    rw [← hDegLen]
    exact natSum_le_length_mul (P.cAnc * L) predCheckCosts hPredChecks
  omega

/-- Per-head aggregation across `probesY ≤ cProbe * L` prefix probes at head `y`. -/
theorem head_probe_work_le (P : ChargingParams) (L degY probesY headWork : Nat)
    (hProbes : probesY ≤ P.cProbe * L)
    (hHeadWork : headWork ≤ probesY * (P.cJump * L + degY * (P.cAnc * L))) :
    headWork ≤ P.cProbe * P.cJump * L ^ 2 + P.cProbe * P.cAnc * degY * L ^ 2 := by
  have hMulProbes :
      probesY * (P.cJump * L + degY * (P.cAnc * L)) ≤
        (P.cProbe * L) * (P.cJump * L + degY * (P.cAnc * L)) :=
    nat_mul_le_mul_right (P.cJump * L + degY * (P.cAnc * L)) hProbes
  have hDegRewrite : degY * (P.cAnc * L) = (P.cAnc * degY) * L :=
    calc degY * (P.cAnc * L)
      _ = (degY * P.cAnc) * L := (nat_mul_assoc degY P.cAnc L).symm
      _ = (P.cAnc * degY) * L := congrArg (fun z => z * L) (nat_mul_comm degY P.cAnc)
  have hExpand :
      (P.cProbe * L) * (P.cJump * L + degY * (P.cAnc * L)) =
        P.cProbe * P.cJump * L ^ 2 + P.cProbe * P.cAnc * degY * L ^ 2 :=
    calc (P.cProbe * L) * (P.cJump * L + degY * (P.cAnc * L))
      _ = (P.cProbe * L) * (P.cJump * L) +
            (P.cProbe * L) * (degY * (P.cAnc * L)) :=
          nat_mul_add (P.cProbe * L) (P.cJump * L) (degY * (P.cAnc * L))
      _ = (P.cProbe * L) * (P.cJump * L) +
            (P.cProbe * L) * ((P.cAnc * degY) * L) :=
          congrArg (fun z => (P.cProbe * L) * (P.cJump * L) + (P.cProbe * L) * z) hDegRewrite
      _ = P.cProbe * P.cJump * L ^ 2 +
            (P.cProbe * L) * ((P.cAnc * degY) * L) :=
          congrArg (fun z => z + (P.cProbe * L) * ((P.cAnc * degY) * L))
            (mul_L_mul_L P.cProbe P.cJump L)
      _ = P.cProbe * P.cJump * L ^ 2 +
            (P.cProbe * (P.cAnc * degY)) * L ^ 2 :=
          congrArg (fun z => P.cProbe * P.cJump * L ^ 2 + z)
            (mul_L_mul_L P.cProbe (P.cAnc * degY) L)
      _ = P.cProbe * P.cJump * L ^ 2 +
            P.cProbe * P.cAnc * degY * L ^ 2 :=
          congrArg (fun z => P.cProbe * P.cJump * L ^ 2 + z * L ^ 2)
            (nat_mul_assoc P.cProbe P.cAnc degY).symm
  calc headWork
    _ ≤ probesY * (P.cJump * L + degY * (P.cAnc * L)) := hHeadWork
    _ ≤ (P.cProbe * L) * (P.cJump * L + degY * (P.cAnc * L)) := hMulProbes
    _ = P.cProbe * P.cJump * L ^ 2 + P.cProbe * P.cAnc * degY * L ^ 2 := hExpand

/-- List-of-probes corollary at head `y`. -/
theorem head_probe_list_work_le (P : ChargingParams) (L degY : Nat)
    (probeCosts : List Nat)
    (hLen : probeCosts.length ≤ P.cProbe * L)
    (hEach : ∀ w : Nat, w ∈ probeCosts → w ≤ P.cJump * L + degY * (P.cAnc * L)) :
    natSum probeCosts ≤ P.cProbe * P.cJump * L ^ 2 + P.cProbe * P.cAnc * degY * L ^ 2 :=
  head_probe_work_le P L degY probeCosts.length (natSum probeCosts) hLen
    (natSum_le_length_mul (P.cJump * L + degY * (P.cAnc * L)) probeCosts hEach)

/-- Per-head charging entry `(deg, probes, work)` for a quotient head `y`. -/
structure HeadChargeEntry where
  deg : Nat
  probes : Nat
  work : Nat

/-- Sum of per-head binary-search + predecessor-scan work across a list of heads. -/
theorem heads_probe_work_sum_le (P : ChargingParams) (L : Nat)
    (entries : List HeadChargeEntry)
    (hProbes : ∀ e : HeadChargeEntry, e ∈ entries → e.probes ≤ P.cProbe * L)
    (hWork : ∀ e : HeadChargeEntry, e ∈ entries →
      e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L))) :
    natSum (entries.map HeadChargeEntry.work) ≤
      P.cProbe * P.cJump * entries.length * L ^ 2 +
        P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2 := by
  induction entries with
  | nil =>
      exact Nat.zero_le _
  | cons e es ih =>
      have heProbes : e.probes ≤ P.cProbe * L :=
        hProbes e (List.mem_cons.mpr (Or.inl rfl))
      have heWork : e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L)) :=
        hWork e (List.mem_cons.mpr (Or.inl rfl))
      have hHead : e.work ≤
          P.cProbe * P.cJump * L ^ 2 + P.cProbe * P.cAnc * e.deg * L ^ 2 :=
        head_probe_work_le P L e.deg e.probes e.work heProbes heWork
      have hTail : natSum (es.map HeadChargeEntry.work) ≤
          P.cProbe * P.cJump * es.length * L ^ 2 +
            P.cProbe * P.cAnc * natSum (es.map HeadChargeEntry.deg) * L ^ 2 :=
        ih (fun x hx => hProbes x (List.mem_cons.mpr (Or.inr hx)))
           (fun x hx => hWork x (List.mem_cons.mpr (Or.inr hx)))
      have hLenStep :
          P.cProbe * P.cJump * (es.length + 1) * L ^ 2 =
            P.cProbe * P.cJump * es.length * L ^ 2 + P.cProbe * P.cJump * L ^ 2 :=
        calc P.cProbe * P.cJump * (es.length + 1) * L ^ 2
          _ = (P.cProbe * P.cJump * es.length + P.cProbe * P.cJump) * L ^ 2 := rfl
          _ = P.cProbe * P.cJump * es.length * L ^ 2 + P.cProbe * P.cJump * L ^ 2 :=
              nat_add_mul (P.cProbe * P.cJump * es.length) (P.cProbe * P.cJump) (L ^ 2)
      have hDegStep :
          P.cProbe * P.cAnc * (e.deg + natSum (es.map HeadChargeEntry.deg)) * L ^ 2 =
            P.cProbe * P.cAnc * e.deg * L ^ 2 +
              P.cProbe * P.cAnc * natSum (es.map HeadChargeEntry.deg) * L ^ 2 :=
        calc P.cProbe * P.cAnc * (e.deg + natSum (es.map HeadChargeEntry.deg)) * L ^ 2
          _ = (P.cProbe * P.cAnc * e.deg +
                P.cProbe * P.cAnc * natSum (es.map HeadChargeEntry.deg)) * L ^ 2 :=
              congrArg (fun z => z * L ^ 2)
                (nat_mul_add (P.cProbe * P.cAnc) e.deg (natSum (es.map HeadChargeEntry.deg)))
          _ = P.cProbe * P.cAnc * e.deg * L ^ 2 +
                P.cProbe * P.cAnc * natSum (es.map HeadChargeEntry.deg) * L ^ 2 :=
              nat_add_mul (P.cProbe * P.cAnc * e.deg)
                (P.cProbe * P.cAnc * natSum (es.map HeadChargeEntry.deg)) (L ^ 2)
      change e.work + natSum (es.map HeadChargeEntry.work) ≤
        P.cProbe * P.cJump * (es.length + 1) * L ^ 2 +
          P.cProbe * P.cAnc * (e.deg + natSum (es.map HeadChargeEntry.deg)) * L ^ 2
      omega

/-- Interface-relative refined charging lemma (`List` of `n_H` heads with
    `deg := entries.map HeadChargeEntry.deg`, `deg.length = n_H`, `natSum deg ≤ m_H`). -/
theorem interface_charging_refined_list (P : ChargingParams)
    (n_H m_H L preWork dictWork : Nat)
    (entries : List HeadChargeEntry)
    (hCount : (entries.map HeadChargeEntry.deg).length = n_H)
    (hDegSum : natSum (entries.map HeadChargeEntry.deg) ≤ m_H)
    (hPre : preWork ≤ P.cPre * (n_H + m_H))
    (hDict : dictWork ≤ P.cDict * n_H * L)
    (hProbes : ∀ e : HeadChargeEntry, e ∈ entries → e.probes ≤ P.cProbe * L)
    (hWork : ∀ e : HeadChargeEntry, e ∈ entries →
      e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L))) :
    preWork + dictWork + natSum (entries.map HeadChargeEntry.work) ≤
      P.cPre * (n_H + m_H) + P.cDict * n_H * L +
        P.cProbe * P.cJump * n_H * L ^ 2 + P.cProbe * P.cAnc * m_H * L ^ 2 := by
  have hEntriesLen : entries.length = n_H := by
    rw [List.length_map] at hCount
    exact hCount
  have hSweep :
      natSum (entries.map HeadChargeEntry.work) ≤
        P.cProbe * P.cJump * n_H * L ^ 2 +
          P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2 :=
    calc natSum (entries.map HeadChargeEntry.work)
      _ ≤ P.cProbe * P.cJump * entries.length * L ^ 2 +
            P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2 :=
          heads_probe_work_sum_le P L entries hProbes hWork
      _ = P.cProbe * P.cJump * n_H * L ^ 2 +
            P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2 :=
          congrArg
            (fun k =>
              P.cProbe * P.cJump * k * L ^ 2 +
                P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2)
            hEntriesLen
  have hDegTerm :
      P.cProbe * P.cAnc * natSum (entries.map HeadChargeEntry.deg) * L ^ 2 ≤
        P.cProbe * P.cAnc * m_H * L ^ 2 :=
    nat_mul_le_mul_right (L ^ 2)
      (nat_mul_le_mul_left (P.cProbe * P.cAnc) hDegSum)
  omega

/-- Interface-relative concrete `O((n_H + m_H) * L ^ 2)` charging lemma (`1 ≤ L`). -/
theorem interface_charging_bigO_list (P : ChargingParams)
    (n_H m_H L preWork dictWork : Nat)
    (entries : List HeadChargeEntry)
    (hCount : (entries.map HeadChargeEntry.deg).length = n_H)
    (hDegSum : natSum (entries.map HeadChargeEntry.deg) ≤ m_H)
    (hL : 1 ≤ L)
    (hPre : preWork ≤ P.cPre * (n_H + m_H))
    (hDict : dictWork ≤ P.cDict * n_H * L)
    (hProbes : ∀ e : HeadChargeEntry, e ∈ entries → e.probes ≤ P.cProbe * L)
    (hWork : ∀ e : HeadChargeEntry, e ∈ entries →
      e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L))) :
    preWork + dictWork + natSum (entries.map HeadChargeEntry.work) ≤
      P.totalConst * ((n_H + m_H) * L ^ 2) := by
  have hRefined :=
    interface_charging_refined_list P n_H m_H L preWork dictWork entries
      hCount hDegSum hPre hDict hProbes hWork
  have hOneLeSq : 1 ≤ L ^ 2 := one_le_pow_two hL
  have hSelfLeSq : L ≤ L ^ 2 := self_le_pow_two hL
  have hNhLe : n_H ≤ n_H + m_H := by omega
  have hMhLe : m_H ≤ n_H + m_H := by omega
  have hTermPre : P.cPre * (n_H + m_H) ≤ P.cPre * ((n_H + m_H) * L ^ 2) := by
    have hBase : n_H + m_H ≤ (n_H + m_H) * L ^ 2 :=
      calc n_H + m_H
        _ = (n_H + m_H) * 1 := by change n_H + m_H = (n_H + m_H) * 0 + (n_H + m_H); omega
        _ ≤ (n_H + m_H) * L ^ 2 := nat_mul_le_mul_left (n_H + m_H) hOneLeSq
    exact nat_mul_le_mul_left P.cPre hBase
  have hTermDict : P.cDict * n_H * L ≤ P.cDict * ((n_H + m_H) * L ^ 2) :=
    calc P.cDict * n_H * L
      _ = P.cDict * (n_H * L) := nat_mul_assoc P.cDict n_H L
      _ ≤ P.cDict * ((n_H + m_H) * L ^ 2) :=
          nat_mul_le_mul_left P.cDict (nat_mul_le_mul hNhLe hSelfLeSq)
  have hTermJump :
      P.cProbe * P.cJump * n_H * L ^ 2 ≤
        (P.cProbe * P.cJump) * ((n_H + m_H) * L ^ 2) :=
    calc P.cProbe * P.cJump * n_H * L ^ 2
      _ = (P.cProbe * P.cJump) * (n_H * L ^ 2) :=
          nat_mul_assoc (P.cProbe * P.cJump) n_H (L ^ 2)
      _ ≤ (P.cProbe * P.cJump) * ((n_H + m_H) * L ^ 2) :=
          nat_mul_le_mul_left (P.cProbe * P.cJump) (nat_mul_le_mul_right (L ^ 2) hNhLe)
  have hTermAnc :
      P.cProbe * P.cAnc * m_H * L ^ 2 ≤
        (P.cProbe * P.cAnc) * ((n_H + m_H) * L ^ 2) :=
    calc P.cProbe * P.cAnc * m_H * L ^ 2
      _ = (P.cProbe * P.cAnc) * (m_H * L ^ 2) :=
          nat_mul_assoc (P.cProbe * P.cAnc) m_H (L ^ 2)
      _ ≤ (P.cProbe * P.cAnc) * ((n_H + m_H) * L ^ 2) :=
          nat_mul_le_mul_left (P.cProbe * P.cAnc) (nat_mul_le_mul_right (L ^ 2) hMhLe)
  let K := (n_H + m_H) * L ^ 2
  have hTotalExpand :
      P.totalConst * K =
        P.cPre * K + P.cDict * K + (P.cProbe * P.cJump) * K + (P.cProbe * P.cAnc) * K :=
    calc P.totalConst * K
      _ = ((P.cPre + P.cDict + P.cProbe * P.cJump) + P.cProbe * P.cAnc) * K := rfl
      _ = (P.cPre + P.cDict + P.cProbe * P.cJump) * K + (P.cProbe * P.cAnc) * K :=
          nat_add_mul (P.cPre + P.cDict + P.cProbe * P.cJump) (P.cProbe * P.cAnc) K
      _ = (P.cPre + P.cDict) * K + (P.cProbe * P.cJump) * K + (P.cProbe * P.cAnc) * K :=
          congrArg (fun z => z + (P.cProbe * P.cAnc) * K)
            (nat_add_mul (P.cPre + P.cDict) (P.cProbe * P.cJump) K)
      _ = P.cPre * K + P.cDict * K + (P.cProbe * P.cJump) * K + (P.cProbe * P.cAnc) * K :=
          congrArg (fun z => z + (P.cProbe * P.cJump) * K + (P.cProbe * P.cAnc) * K)
            (nat_add_mul P.cPre P.cDict K)
  dsimp [K] at hTotalExpand
  omega

/-- Interface-relative concrete `O((n_H + m_H) * L ^ 2)` charging lemma under `n_H + 2 ≤ 2 ^ L`. -/
theorem interface_charging_of_pow2_list (P : ChargingParams)
    (n_H m_H L preWork dictWork : Nat)
    (entries : List HeadChargeEntry)
    (hCount : (entries.map HeadChargeEntry.deg).length = n_H)
    (hDegSum : natSum (entries.map HeadChargeEntry.deg) ≤ m_H)
    (hPow : n_H + 2 ≤ 2 ^ L)
    (hPre : preWork ≤ P.cPre * (n_H + m_H))
    (hDict : dictWork ≤ P.cDict * n_H * L)
    (hProbes : ∀ e : HeadChargeEntry, e ∈ entries → e.probes ≤ P.cProbe * L)
    (hWork : ∀ e : HeadChargeEntry, e ∈ entries →
      e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L))) :
    preWork + dictWork + natSum (entries.map HeadChargeEntry.work) ≤
      P.totalConst * ((n_H + m_H) * L ^ 2) :=
  interface_charging_bigO_list P n_H m_H L preWork dictWork entries
    hCount hDegSum (one_le_of_add_two_le_pow2 hPow)
    hPre hDict hProbes hWork

/-- Canonical list `[0, 1, ..., n - 1]` of `Fin n` indices. -/
def finIndices : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 =>
      ⟨0, Nat.zero_lt_succ n⟩ ::
        (finIndices n).map (fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem length_finIndices (n : Nat) : (finIndices n).length = n := by
  induction n with
  | zero => rfl
  | succ _ ih =>
      dsimp [finIndices]
      rw [List.length_map, ih]

/-- Sum of `f : Fin n → Nat` across all `n` vertices. -/
def finNatSum (n : Nat) (f : Fin n → Nat) : Nat :=
  natSum ((finIndices n).map f)

/-- Interface-relative `O((n_H + m_H) * L ^ 2)` charging lemma indexed by `Fin n_H`. -/
theorem interface_charging_bigO_fin (P : ChargingParams)
    (n_H m_H L preWork dictWork : Nat)
    (deg probes headWork : Fin n_H → Nat)
    (hDegSum : finNatSum n_H deg ≤ m_H)
    (hPow : n_H + 2 ≤ 2 ^ L)
    (hPre : preWork ≤ P.cPre * (n_H + m_H))
    (hDict : dictWork ≤ P.cDict * n_H * L)
    (hProbes : ∀ y : Fin n_H, probes y ≤ P.cProbe * L)
    (hWork : ∀ y : Fin n_H,
      headWork y ≤ probes y * (P.cJump * L + deg y * (P.cAnc * L))) :
    preWork + dictWork + finNatSum n_H headWork ≤
      P.totalConst * ((n_H + m_H) * L ^ 2) := by
  let mkEntry : Fin n_H → HeadChargeEntry :=
    fun y => { deg := deg y, probes := probes y, work := headWork y }
  let entries : List HeadChargeEntry := (finIndices n_H).map mkEntry
  have hMapDeg : entries.map HeadChargeEntry.deg = (finIndices n_H).map deg :=
    list_map_map mkEntry HeadChargeEntry.deg (finIndices n_H)
  have hMapWork : entries.map HeadChargeEntry.work = (finIndices n_H).map headWork :=
    list_map_map mkEntry HeadChargeEntry.work (finIndices n_H)
  have hCount : (entries.map HeadChargeEntry.deg).length = n_H := by
    rw [hMapDeg, List.length_map, length_finIndices]
  have hDegSum' : natSum (entries.map HeadChargeEntry.deg) ≤ m_H := by
    rw [hMapDeg]
    exact hDegSum
  have hEntryProbes : ∀ e : HeadChargeEntry, e ∈ entries → e.probes ≤ P.cProbe * L := by
    intro e he
    let ⟨y, _, hyEq⟩ := List.mem_map.mp he
    rw [← hyEq]
    exact hProbes y
  have hEntryWork : ∀ e : HeadChargeEntry, e ∈ entries →
      e.work ≤ e.probes * (P.cJump * L + e.deg * (P.cAnc * L)) := by
    intro e he
    let ⟨y, _, hyEq⟩ := List.mem_map.mp he
    rw [← hyEq]
    exact hWork y
  have hBound :=
    interface_charging_of_pow2_list P n_H m_H L preWork dictWork entries
      hCount hDegSum' hPow hPre hDict hEntryProbes hEntryWork
  unfold finNatSum
  rw [← hMapWork]
  exact hBound

end ForestBuild

end PaperB
