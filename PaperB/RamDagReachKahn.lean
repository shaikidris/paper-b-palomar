module

public import PaperB.RamDagReachSetup
public import PaperB.ReachScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamDagReach

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph

section Helpers

private theorem nodup_filter_bool {α : Type} (p : α → Bool) {xs : List α} (hnd : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    have ihas := ih hcons.2
    by_cases hp : p a = true
    · rw [List.filter_cons, ite_eq_left hp]
      refine List.nodup_cons.mpr ⟨?_, ihas⟩
      intro hm
      exact hcons.1 (List.mem_filter.mp hm).1
    · have hp' : p a = false := by cases hpa : p a <;> simp_all
      rw [List.filter_cons, hp']
      exact ihas

private theorem nodup_filter_sum_le {α : Type} (xs : List α) (hnd : xs.Nodup)
    (p : α → Bool) (top : α) (f : α → Nat)
    (huniq : ∀ a ∈ xs, p a = false → a = top) :
    (xs.map f).sum ≤ ((xs.filter p).map f).sum + f top := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    by_cases hp : p a = true
    · have ihas := ih hcons.2 (fun b hb => huniq b (List.mem_cons_of_mem _ hb))
      simp only [List.filter_cons, hp, ↓reduceIte]
      simp only [List.map_cons, List.sum_cons] at ihas ⊢
      omega
    · have hp' : p a = false := by cases hpa : p a <;> simp_all
      have haTop : a = top := huniq a (List.mem_cons_self ..) hp'
      subst a
      have hEqF : (top :: as).filter p = as := by
        simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte]
        apply List.filter_eq_self.mpr
        intro b hb
        cases hpb : p b with
        | true => rfl
        | false =>
          have := huniq b (List.mem_cons_of_mem _ hb) hpb
          subst b
          exact False.elim (hcons.1 hb)
      rw [hEqF]
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem nodup_length_le_fin {n : Nat} (xs : List (Fin n)) (hnd : xs.Nodup) :
    xs.length ≤ n := by
  have hAll : ∀ (k : Nat) (ys : List (Fin n)), ys.Nodup → (∀ y ∈ ys, y.val < k) → ys.length ≤ k := by
    intro k
    induction k with
    | zero =>
      intro ys _ hlt
      cases ys with
      | nil => simp
      | cons y _ => have := hlt y (by simp); omega
    | succ k ih =>
      intro ys hynd hlt
      let ys' := ys.filter (fun y => decide (y.val ≠ k))
      have hy'nd : ys'.Nodup := nodup_filter_bool _ hynd
      have hy'lt : ∀ y ∈ ys', y.val < k := by
        intro y hy
        rcases List.mem_filter.mp hy with ⟨hyMem, hne⟩
        have := hlt y hyMem
        have hne' : y.val ≠ k := by simpa using hne
        omega
      have hSub := ih ys' hy'nd hy'lt
      have hLen : ys.length ≤ ys'.length + 1 := by
        by_cases hk : k < n
        · have hSum := nodup_filter_sum_le ys hynd (fun y => decide (y.val ≠ k)) ⟨k, hk⟩ (fun _ => 1)
            (fun a _ hfa => Fin.ext (by simpa using hfa))
          have hMapOne : ∀ zs : List (Fin n), (zs.map (fun _ => 1)).sum = zs.length := by
            intro zs; induction zs with | nil => simp | cons _ _ ihz => simp [ihz]; omega
          simpa only [hMapOne] using hSum
        · have hEqF : ys' = ys := by
            apply List.filter_eq_self.mpr
            intro b _
            have := b.isLt
            simp; omega
          rw [hEqF]
          omega
      exact Nat.le_trans hLen (Nat.add_le_add_right hSub 1)
  exact hAll n xs hnd (fun y _ => y.isLt)

private theorem list_split_at {α : Type} (xs : List α) (u : Nat) (hu : u < xs.length) :
    xs = xs.take u ++ xs[u]'hu :: xs.drop (u + 1) := by
  induction u generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hu
    | cons x xs => rfl
  | succ u ih =>
    cases xs with
    | nil => simp at hu
    | cons x xs =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
        List.cons_append]
      exact congrArg (List.cons x) (ih xs (Nat.lt_of_succ_lt_succ hu))

private theorem list_split_mem {α : Type} {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ a b : List α, xs = a ++ x :: b := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  subst x
  exact ⟨xs.take i, xs.drop (i + 1), list_split_at xs i hi⟩

private theorem topo_arc_tail_before (g : Digraph)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    {k : Nat} (hk : k < order.length) {p : Fin g.vertexCount}
    (harc : g.HasArc p (order[k]'hk)) :
    p ∈ order.take k := by
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp (hTopo.2.1 p)
  have hjk : j < k := by
    by_cases hle : k ≤ j
    · have hSplit : order = order.take j ++ order[j]'hj :: order.drop (j + 1) :=
        list_split_at order j hj
      have huPost : order[k]'hk ∈ order.drop (j + 1) := by
        rw [← hqj] at harc
        exact hTopo.2.2 (order.take j) (order[j]'hj) (order.drop (j + 1)) hSplit (order[k]'hk) harc
      obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp huPost
      have hdrop : order[j + 1 + t]'(by simp only [List.length_drop] at ht; omega) = order[k]'hk := by
        simpa only [List.getElem_drop] using hteq
      have hEqIdx := hTopo.1.eq_of_getElem_eq (by simp only [List.length_drop] at ht; omega) hk hdrop
      omega
    · omega
  rw [List.mem_iff_getElem]
  exact ⟨j, by simp only [List.length_take]; omega, by simpa only [List.getElem_take] using hqj⟩

end Helpers

/-! ### Phase 2A: Zero `marked[0..n-1]` and set `marked[r] := 1` -/

section Phase2InitMarked

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def initMarkedCode : Program L16 :=
  #[.add r5 rN rN,
    .imm r6 0,
    .branchLt r6 rN 3 7,
    .add r7 r5 r6,
    .storeData r7 rZero,
    .add r6 r6 rOne,
    .goto 2,
    .add r7 r5 rRoot,
    .storeData r7 rOne,
    .halt]

def initMarkedPhase : Phase L16 :=
  Phase.ofLast initMarkedCode 9 rfl rfl rfl

private theorem initMarkedPhase_size : (initMarkedPhase (hi := hi) (hw := hw)).code.size = 10 := rfl

private structure InitMarkedInv (g : Digraph) (root : Nat) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 2
  consts : ConstRegs g.vertexCount g.arcCount root s
  base : (reg s r5).val = 2 * g.vertexCount
  idx : (reg s r6).val = k
  zeros : ∀ j, j < k → (s.data[2 * g.vertexCount + j]?).map Fin.val = some 0
  frame : ∀ j, (j < 2 * g.vertexCount ∨ 2 * g.vertexCount + k ≤ j) → s.data[j]? = origData[j]?

theorem run_initMarkedPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀) :
    let n := g.vertexCount
    let m := g.arcCount
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 5 * n + 6 ∧
      run initMarkedPhase.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (∀ v : Fin n, (t.data[markedBase n m + v.val]?).map Fin.val = some (if v = r then 1 else 0)) ∧
      (∀ j, (j < 2 * n ∨ 3 * n ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m
  let code : Program L16 := initMarkedPhase.code
  have hSz : code.size = 10 := initMarkedPhase_size
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have h2nFit : 2 * n < 2 ^ bits := by
    unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hBaseFit : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits
    rw [hConsts.nVal]; omega
  obtain ⟨s1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨s2, hs1, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
    (s := s1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 2 s_start s2 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.zero s2))
  have hConsts2 : ConstRegs n m r.val s2 :=
    ⟨(congrArg Fin.val ((h2o rZero (by decide)).trans (h1o rZero (by decide)))).trans hConsts.zero,
     (congrArg Fin.val ((h2o rOne (by decide)).trans (h1o rOne (by decide)))).trans hConsts.one,
     (congrArg Fin.val ((h2o rN (by decide)).trans (h1o rN (by decide)))).trans hConsts.nVal,
     (congrArg Fin.val ((h2o rM (by decide)).trans (h1o rM (by decide)))).trans hConsts.mVal,
     (congrArg Fin.val ((h2o rRoot (by decide)).trans (h1o rRoot (by decide)))).trans hConsts.rootVal⟩
  have hInv0 : InitMarkedInv g r.val s₀.data 0 s2 := by
    refine ⟨by rw [h2pc, h1pc, hStartPc], hConsts2, ?_, by rw [h2v]; rfl,
      fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun _ _ => by rw [h2d, h1d]; rfl⟩
    rw [h2o _ (by decide), h1v, add_no_wrap _ _ hBaseFit]
    change (reg s₀ rN).val + (reg s₀ rN).val = 2 * n
    rw [hConsts.nVal]; omega
  let Post (k : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (∀ v : Fin n, (t.data[markedBase n m + v.val]?).map Fin.val = some (if v = r then 1 else 0)) ∧
    (∀ j, (j < 2 * n ∨ 3 * n ≤ j) → t.data[j]? = s₀.data[j]?)
  have hStepCase : ∀ k u, (k ≤ n ∧ InitMarkedInv g r.val s₀.data k u) →
      (∃ t, Post k t ∧ ∃ st, st ≤ 5 * (n - k) + 4 ∧ run code input st u = some ⟨t, st⟩) ∨
      (∃ k' u' st, (n - k') < (n - k) ∧ st + (5 * (n - k') + 4) ≤ 5 * (n - k) + 4 ∧
        Steps code input st u u' ∧ (k' ≤ n ∧ InitMarkedInv g r.val s₀.data k' u')) := by
    intro k u ⟨hkLe, hu⟩
    by_cases hk : k < n
    · right
      have hCmp : ltb (reg u r6) (reg u rN) = true :=
        branchLt_true (by rw [hu.idx, hu.consts.nVal]; exact hk)
      have hf2 : code[u.pc]? = some (.branchLt r6 rN 3 7) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 3 }
      have hu1Pc : u1.pc = 3 := rfl
      have hs2 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf2 (by rw [hSz, hCmp]; decide)
      have hAddrFit : (reg u1 r5).val + (reg u1 r6).val < 2 ^ bits := by
        change (reg u r5).val + (reg u r6).val < 2 ^ bits
        rw [hu.base, hu.idx]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs3, h2pc', h2v', h2o', h2d'⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r7 : (reg u2 r7).val = 2 * n + k := by
        rw [h2v', add_no_wrap _ _ hAddrFit]
        change (reg u r5).val + (reg u r6).val = _; rw [hu.base, hu.idx]
      have h2Bound : (reg u2 r7).val < u2.data.size := by
        rw [u2.data_size, h2_r7]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u3, hs4, h3pc, h3regs, h3data⟩ := step_storeData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc', hu1Pc]; rfl) (by rw [hSz, h2pc', hu1Pc]; decide) h2Bound
      have h3_r6 : (reg u3 r6).val = k := by
        rw [reg_eq_of_regs_eq h3regs r6, h2o' _ (by decide)]; exact hu.idx
      have h3_one : (reg u3 rOne).val = 1 := by
        rw [reg_eq_of_regs_eq h3regs rOne, h2o' _ (by decide)]; exact hu.consts.one
      have hk1Fit : k + 1 < 2 ^ bits := by
        unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u4, hs5, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc', hu1Pc]; rfl)
        (by rw [hSz, h3pc, h2pc', hu1Pc]; decide)
      let uNext : State L16 := { u4 with pc := 2 }
      have hs6 : step code input u4 = some (.next uNext) :=
        step_goto_at (code := code) (by rw [h4pc, h3pc, h2pc', hu1Pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7) :
          reg uNext regIdx = reg u regIdx := by
        change reg u4 regIdx = _
        rw [h4o _ hn6, reg_eq_of_regs_eq h3regs regIdx, h2o' _ hn7]; rfl
      have hDataNext : uNext.data = u.data.set (2 * n + k) (reg u rZero)
          (by rw [u.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
        change u4.data = _
        rw [h4d, h3data]
        have hZeroEq : reg u2 rZero = reg u rZero := h2o' _ (by decide)
        have h2dEq : u2.data = u.data := h2d'
        simp only [h2_r7, hZeroEq, h2dEq]
      have hInvNext : InitMarkedInv g r.val s₀.data (k + 1) uNext := by
        refine ⟨rfl, ?_, (congrArg Fin.val (hKeepNext r5 (by decide) (by decide))).trans hu.base,
          ?_, ?_, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide))).trans hu.consts.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide) (by decide))).trans hu.consts.one,
            (congrArg Fin.val (hKeepNext rN (by decide) (by decide))).trans hu.consts.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide) (by decide))).trans hu.consts.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide))).trans hu.consts.rootVal⟩
        · change (reg u4 r6).val = k + 1
          rw [h4v, add_no_wrap _ _ (by rw [h3_r6, h3_one]; exact hk1Fit), h3_r6, h3_one]
        · intro j hj
          rw [hDataNext]
          by_cases hjk : j = k
          · subst j
            rw [Array.getElem?_set_self, Option.map_some, hu.consts.zero]
          · rw [Array.getElem?_set_ne _ (by omega)]
            exact hu.zeros j (by omega)
        · intro j hj
          rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
          exact hu.frame j (by omega)
      refine ⟨k + 1, uNext, 5, by omega, by omega,
        Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.zero uNext))))),
        by omega, hInvNext⟩
    · left
      have hkEq : k = n := by omega
      have hCmp : ltb (reg u r6) (reg u rN) = false :=
        branchLt_false (by rw [hu.idx, hu.consts.nVal, hkEq]; exact Nat.le_refl _)
      have hf2 : code[u.pc]? = some (.branchLt r6 rN 3 7) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 7 }
      have hu1Pc : u1.pc = 7 := rfl
      have hs2 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf2 (by rw [hSz, hCmp]; decide)
      have hRootAddrFit : (reg u1 r5).val + (reg u1 rRoot).val < 2 ^ bits := by
        change (reg u r5).val + (reg u rRoot).val < 2 ^ bits
        rw [hu.base, hu.consts.rootVal]
        have := r.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs7, h2pc', h2v', h2o', h2d'⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r7 : (reg u2 r7).val = 2 * n + r.val := by
        rw [h2v', add_no_wrap _ _ hRootAddrFit]
        change (reg u r5).val + (reg u rRoot).val = _; rw [hu.base, hu.consts.rootVal]
      have h2Bound : (reg u2 r7).val < u2.data.size := by
        rw [u2.data_size, h2_r7]; have := r.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨t, hs8, h3pc, h3regs, h3data⟩ := step_storeData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc', hu1Pc]; rfl) (by rw [hSz, h2pc', hu1Pc]; decide) h2Bound
      have hHalt : step code input t = some (.halted t) :=
        step_halt_at (by rw [h3pc, h2pc', hu1Pc]; rfl)
      have hRun4 : run code input 4 u = some ⟨t, 4⟩ :=
        (Steps.cons hs2 (Steps.cons hs7 (Steps.cons hs8 (Steps.zero t)))).halts hHalt
      have hKeepT (regIdx : Fin 16) (hn7 : regIdx ≠ r7) : reg t regIdx = reg u regIdx := by
        rw [reg_eq_of_regs_eq h3regs regIdx, h2o' _ hn7]; rfl
      have hDataT : t.data = u.data.set (2 * n + r.val) (reg u rOne)
          (by rw [u.data_size]; have := r.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
        rw [h3data]
        have hOneEq : reg u2 rOne = reg u rOne := h2o' _ (by decide)
        have h2dEq : u2.data = u.data := h2d'
        simp only [h2_r7, hOneEq, h2dEq]
      refine ⟨t, ⟨?_, ?_, ?_⟩, 4, by omega, hRun4⟩
      · exact ⟨(congrArg Fin.val (hKeepT rZero (by decide))).trans hu.consts.zero,
          (congrArg Fin.val (hKeepT rOne (by decide))).trans hu.consts.one,
          (congrArg Fin.val (hKeepT rN (by decide))).trans hu.consts.nVal,
          (congrArg Fin.val (hKeepT rM (by decide))).trans hu.consts.mVal,
          (congrArg Fin.val (hKeepT rRoot (by decide))).trans hu.consts.rootVal⟩
      · intro v
        rw [markedBase_eq, hDataT]
        by_cases hvr : v = r
        · subst v; simp [Array.getElem?_set_self, hu.consts.one]
        · have hne : v.val ≠ r.val := fun h => hvr (Fin.ext h)
          rw [Array.getElem?_set_ne _ (by omega)]
          simpa [hvr] using hu.zeros v.val (by rw [hkEq]; exact v.isLt)
      · intro j hj
        have hne : 2 * n + r.val ≠ j := by have := r.isLt; omega
        rw [hDataT, Array.getElem?_set_ne _ hne]
        exact hu.frame j (by dsimp only [n] at *; rw [hkEq]; omega)
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ n ∧ InitMarkedInv g r.val s₀.data k s)
      (fun k => n - k) (fun k => 5 * (n - k) + 4)
      Post (fun k u h => hStepCase k u h) n 0 s2 (Nat.le_refl _) ⟨Nat.zero_le _, hInv0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hm, hf⟩
  exact ⟨tEnd, 2 + loopSteps, by omega, hExec, hc, hm, hf⟩

end Phase2InitMarked

/-! ### Phase 2B: Topological reachability sweep on `marked[0..n-1]` -/

section Phase2ReachSweep

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def reachSweepCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.add r5 rN rN,
    .imm r6 ⟨3, by omega⟩,
    .imm r7 ⟨4, by omega⟩,
    .add r7 r7 rN,
    .imm r8 0,
    .branchLt r8 rN 6 24,
    .add r9 rN r8,
    .loadData r9 r9,
    .add r10 r5 r9,
    .loadData r10 r10,
    .branchLt r10 rOne 22 11,
    .add r10 r6 r9,
    .loadInput r11 r10,
    .add r10 r10 rOne,
    .loadInput r12 r10,
    .branchLt r11 r12 16 22,
    .add r13 r7 r11,
    .loadInput r13 r13,
    .add r13 r5 r13,
    .storeData r13 rOne,
    .add r11 r11 rOne,
    .goto 15,
    .add r8 r8 rOne,
    .goto 5,
    .halt]

def reachSweepPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (reachSweepCode h5) 24 rfl rfl rfl

private theorem reachSweepPhase_size (h5 : 5 ≤ 2 ^ bits) :
    (reachSweepPhase (hi := hi) (hw := hw) h5).code.size = 25 := rfl

private structure ReachSweepOuterInv (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 5
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  markedBase : (reg s r5).val = 2 * g.vertexCount
  offBase : (reg s r6).val = 3
  tgtBase : (reg s r7).val = 4 + g.vertexCount
  idx : (reg s r8).val = k
  bits01 : ∀ v : Fin g.vertexCount,
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 0 ∨
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 1
  rootMarked : (s.data[2 * g.vertexCount + r.val]?).map Fin.val = some 1
  sound : ∀ v : Fin g.vertexCount,
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 1 → g.InitiallyReachable r v
  prefixDone : ∀ p : Fin g.vertexCount, p ∈ order.take k → g.InitiallyReachable r p →
    (s.data[2 * g.vertexCount + p.val]?).map Fin.val = some 1 ∧
    (∀ w : Fin g.vertexCount, g.HasArc p w →
      (s.data[2 * g.vertexCount + w.val]?).map Fin.val = some 1)
  frame : ∀ j, (j < 2 * g.vertexCount ∨ 3 * g.vertexCount ≤ j) → s.data[j]? = origData[j]?

private structure ReachSweepInnerInv (g : Digraph) (r : Fin g.vertexCount)
    (origData : Array (Word bits))
    (u : Fin g.vertexCount) (j : Nat) (s : State L16) : Prop where
  pc : s.pc = 15
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  markedBase : (reg s r5).val = 2 * g.vertexCount
  offBase : (reg s r6).val = 3
  tgtBase : (reg s r7).val = 4 + g.vertexCount
  idx : (reg s r8).val < g.vertexCount
  uReach : g.InitiallyReachable r u
  hjLe : j ≤ (g.outArcs u).length
  edgeIdx : (reg s r11).val = outPrefix g u.val + j
  edgeEnd : (reg s r12).val = outPrefix g u.val + (g.outArcs u).length
  bits01 : ∀ v : Fin g.vertexCount,
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 0 ∨
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 1
  mono : ∀ v : Fin g.vertexCount,
    (origData[2 * g.vertexCount + v.val]?).map Fin.val = some 1 →
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 1
  sound : ∀ v : Fin g.vertexCount,
    (s.data[2 * g.vertexCount + v.val]?).map Fin.val = some 1 → g.InitiallyReachable r v
  headsMarked : ∀ t : Nat, (ht : t < j) →
    (s.data[2 * g.vertexCount + ((g.outArcs u)[t]' (Nat.lt_of_lt_of_le ht hjLe)).val]?).map Fin.val = some 1
  frame : ∀ idx, (idx < 2 * g.vertexCount ∨ 3 * g.vertexCount ≤ idx) → s.data[idx]? = origData[idx]?

theorem run_reachSweepPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (order : List (Fin g.vertexCount)) (hlen : order.length = g.vertexCount)
    (hTopo : g.IsTopologicalList order)
    (hTopoMem : ∀ i : Nat, (hi : i < g.vertexCount) →
      (s₀.data[topoOrderBase g.vertexCount g.arcCount + i]?).map Fin.val =
        some (order[i]'(by rw [hlen]; exact hi)).val)
    (hInitMark : ∀ v : Fin g.vertexCount,
      (s₀.data[markedBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (if v = r then 1 else 0)) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 13 * n + 8 * m + 7 ∧
      run (reachSweepPhase h5).code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (∀ v : Fin n,
        (t.data[markedBase n m + v.val]?).map Fin.val =
          some (if ((g.scanReachability r order hTopo).marked[v.val]?).getD false then 1 else 0)) ∧
      (∀ j, (j < 2 * n ∨ 3 * n ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (reachSweepPhase h5).code
  have hSz : code.size = 25 := reachSweepPhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have h2nFit : 2 * n < 2 ^ bits := by
    unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hTgtFit : 4 + n < 2 ^ bits := by
    have := Fin.pos r; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h2nWordFit : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_imm16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  have h4WordFit : (reg t3 r7).val + (reg t3 rN).val < 2 ^ bits := by
    rw [h3v, h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change 4 + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; exact hTgtFit
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t5, hs4, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 5 s_start t5 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.zero t5)))))
  have hKeep5 (regIdx : Fin 16) (hn5 : regIdx ≠ r5) (hn6 : regIdx ≠ r6)
      (hn7 : regIdx ≠ r7) (hn8 : regIdx ≠ r8) : reg t5 regIdx = reg s_start regIdx := by
    rw [h5o _ hn8, h4o _ hn7, h3o _ hn7, h2o _ hn6, h1o _ hn5]
  have hData5 : t5.data = s₀.data := by rw [h5d, h4d, h3d, h2d, h1d]; rfl
  have hConsts5 : ConstRegs n m r.val t5 :=
    ⟨(congrArg Fin.val (hKeep5 rZero (by decide) (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep5 rOne (by decide) (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep5 rN (by decide) (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep5 rM (by decide) (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep5 rRoot (by decide) (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hOut0 : ReachSweepOuterInv g r order s₀.data 0 t5 := by
    refine ⟨by rw [h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts5, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, fun _ hp => by simp at hp, fun _ _ => by rw [hData5]⟩
    · rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1v,
        add_no_wrap _ _ h2nWordFit]
      change (reg s₀ rN).val + (reg s₀ rN).val = 2 * g.vertexCount
      rw [hConsts.nVal]; omega
    · rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2v]
    · rw [h5o _ (by decide), h4v, add_no_wrap _ _ h4WordFit, h3v, h3o _ (by decide),
        h2o _ (by decide), h1o _ (by decide)]
      change 4 + (reg s₀ rN).val = _; rw [hConsts.nVal]
    · rw [h5v]; rfl
    · intro v; rw [hData5]
      have hmv := hInitMark v
      rw [markedBase_eq] at hmv
      by_cases hvr : v = r
      · right; simpa [hvr] using hmv
      · left; simpa [hvr] using hmv
    · rw [hData5]; simpa [markedBase_eq] using hInitMark r
    · intro v hv; rw [hData5] at hv
      have hmv := hInitMark v; rw [markedBase_eq] at hmv
      by_cases hvr : v = r
      · rw [hvr]; exact initiallyReachable_source g r
      · simp [hvr] at hmv; rw [hmv] at hv; cases hv
  -- Inner loop runner starting at pc = 15
  have run_inner : ∀ (u : Fin n) (st0 : State L16) (origInner : Array (Word bits)),
      origInner = st0.data →
      ReachSweepInnerInv g r origInner u 0 st0 →
      ∃ stEnd innerSteps,
        innerSteps ≤ 7 * (g.outArcs u).length + 1 ∧
        Steps code input innerSteps st0 stEnd ∧
        stEnd.pc = 22 ∧
        ConstRegs n m r.val stEnd ∧
        (reg stEnd r5).val = 2 * n ∧
        (reg stEnd r6).val = 3 ∧
        (reg stEnd r7).val = 4 + n ∧
        (reg stEnd r8).val = (reg st0 r8).val ∧
        (∀ v : Fin n, (stEnd.data[2 * n + v.val]?).map Fin.val = some 0 ∨
          (stEnd.data[2 * n + v.val]?).map Fin.val = some 1) ∧
        (∀ v : Fin n, (origInner[2 * n + v.val]?).map Fin.val = some 1 →
          (stEnd.data[2 * n + v.val]?).map Fin.val = some 1) ∧
        (∀ v : Fin n, (stEnd.data[2 * n + v.val]?).map Fin.val = some 1 → g.InitiallyReachable r v) ∧
        (∀ w : Fin n, g.HasArc u w → (stEnd.data[2 * n + w.val]?).map Fin.val = some 1) ∧
        (∀ idx, (idx < 2 * n ∨ 3 * n ≤ idx) → stEnd.data[idx]? = origInner[idx]?) := by
    intro u st0 origInner hOrigEq hIn0
    let InnerPost (st : State L16) : Prop :=
      st.pc = 22 ∧
      ConstRegs n m r.val st ∧
      (reg st r5).val = 2 * n ∧
      (reg st r6).val = 3 ∧
      (reg st r7).val = 4 + n ∧
      (reg st r8).val = (reg st0 r8).val ∧
      (∀ v : Fin n, (st.data[2 * n + v.val]?).map Fin.val = some 0 ∨
        (st.data[2 * n + v.val]?).map Fin.val = some 1) ∧
      (∀ v : Fin n, (origInner[2 * n + v.val]?).map Fin.val = some 1 →
        (st.data[2 * n + v.val]?).map Fin.val = some 1) ∧
      (∀ v : Fin n, (st.data[2 * n + v.val]?).map Fin.val = some 1 → g.InitiallyReachable r v) ∧
      (∀ w : Fin n, g.HasArc u w → (st.data[2 * n + w.val]?).map Fin.val = some 1) ∧
      (∀ idx, (idx < 2 * n ∨ 3 * n ≤ idx) → st.data[idx]? = origInner[idx]?)
    have hInAux : ∀ (rem j : Nat) (st : State L16),
        (g.outArcs u).length - j ≤ rem →
        ReachSweepInnerInv g r origInner u j st →
        (reg st r8).val = (reg st0 r8).val →
        ∃ stEnd steps, steps ≤ 7 * ((g.outArcs u).length - j) + 1 ∧
          Steps code input steps st stEnd ∧ InnerPost stEnd := by
      intro rem
      induction rem with
      | zero =>
        intro j st hRem hIn hr8
        have hjEq : j = (g.outArcs u).length := by have := hIn.hjLe; omega
        have hCmp : ltb (reg st r11) (reg st r12) = false :=
          branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
        have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 22) := by rw [hIn.pc]; rfl
        let stEnd : State L16 := { st with pc := 22 }
        have hs15 : step code input st = some (.next stEnd) := by
          simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
        refine ⟨stEnd, 1, by omega, Steps.cons hs15 (Steps.zero stEnd),
          rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
          hIn.markedBase, hIn.offBase, hIn.tgtBase, hr8,
          hIn.bits01, hIn.mono, hIn.sound, ?_, hIn.frame⟩
        intro w hwArc
        obtain ⟨t, ht, hwt⟩ := List.mem_iff_getElem.mp hwArc
        have htLt : t < j := by omega
        simpa only [hwt] using hIn.headsMarked t htLt
      | succ rem ih =>
        intro j st hRem hIn hr8
        by_cases hj : j < (g.outArcs u).length
        · have hCmp : ltb (reg st r11) (reg st r12) = true :=
            branchLt_true (by rw [hIn.edgeIdx, hIn.edgeEnd]; omega)
          have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 22) := by rw [hIn.pc]; rfl
          let u1 : State L16 := { st with pc := 16 }
          have hu1Pc : u1.pc = 16 := rfl
          have hs15 : step code input st = some (.next u1) := by
            simpa only [u1, hCmp, ite_true] using
              step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
          have hEdgeBound : 4 + n + (outPrefix g u.val + j) < 2 ^ bits := by
            have h1 : outPrefix g u.val + j < outPrefix g (u.val + 1) := by
              rw [outPrefix_succ_lt g u]; omega
            have h2 : outPrefix g u.val + j < g.arcCount := by
              rw [← outPrefix_vertexCount g]
              exact Nat.lt_of_lt_of_le h1 (outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount))
            have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
          have hAddrWordFit : (reg u1 r7).val + (reg u1 r11).val < 2 ^ bits := by
            change (reg st r7).val + (reg st r11).val < 2 ^ bits
            rw [hIn.tgtBase, hIn.edgeIdx]; exact hEdgeBound
          obtain ⟨u2, hs16, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
            (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
          have h2_r13 : (reg u2 r13).val = 4 + n + (outPrefix g u.val + j) := by
            rw [h2v, add_no_wrap _ _ hAddrWordFit]
            change (reg st r7).val + (reg st r11).val = _; rw [hIn.tgtBase, hIn.edgeIdx]
          let v : Fin n := (g.outArcs u)[j]'hj
          have hvTarget := raw.out_targets u j hj
          have hvFit : v.val < 2 ^ bits := by
            have := raw.cap_ge; unfold rawDagInputCap at this; have := v.isLt; dsimp only [n] at *; omega
          have hvInput : input.words[(reg u2 r13).val]? = some ⟨v.val, hvFit⟩ := by
            rw [h2_r13, ← Nat.add_assoc]
            dsimp only [n]
            cases hcell : input.words[4 + g.vertexCount + outPrefix g u.val + j]? with
            | none => simp [hcell] at hvTarget
            | some w => rw [hcell, Option.map_some] at hvTarget; exact congrArg some (Fin.ext (Option.some.inj hvTarget))
          obtain ⟨u3, hs17, h3pc, h3v, h3o, h3d⟩ := step_loadInput16 (input := input)
            (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl)
            (by rw [hSz, h2pc, hu1Pc]; decide) hvInput
          have h3_r13 : (reg u3 r13).val = v.val := by rw [h3v]
          have hMarkAddrFit : (reg u3 r5).val + (reg u3 r13).val < 2 ^ bits := by
            rw [h3o _ (by decide), h2o _ (by decide)]
            change (reg st r5).val + (reg u3 r13).val < 2 ^ bits
            rw [hIn.markedBase, h3_r13]
            have := v.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u4, hs18, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
            (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
          have h4_r13 : (reg u4 r13).val = 2 * n + v.val := by
            rw [h4v, add_no_wrap _ _ hMarkAddrFit, h3o _ (by decide), h2o _ (by decide)]
            change (reg st r5).val + _ = _; rw [hIn.markedBase, h3_r13]
          have h4Bound : (reg u4 r13).val < u4.data.size := by
            rw [u4.data_size, h4_r13]; have := v.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u5, hs19, h5pc, h5regs, h5data⟩ := step_storeData16 (input := input)
            (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide) h4Bound
          have h5_r11 : (reg u5 r11).val = outPrefix g u.val + j := by
            rw [reg_eq_of_regs_eq h5regs r11, h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.edgeIdx
          have h5_one : (reg u5 rOne).val = 1 := by
            rw [reg_eq_of_regs_eq h5regs rOne, h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.consts.one
          have hEdgeNextFit : outPrefix g u.val + j + 1 < 2 ^ bits := by omega
          obtain ⟨u6, hs20, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
            (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          let uNext : State L16 := { u6 with pc := 15 }
          have hs21 : step code input u6 = some (.next uNext) :=
            step_goto_at (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz]; decide)
          have hKeepNext (regIdx : Fin 16) (hn11 : regIdx ≠ r11) (hn13 : regIdx ≠ r13) :
              reg uNext regIdx = reg st regIdx := by
            change reg u6 regIdx = reg st regIdx
            rw [h6o _ hn11, reg_eq_of_regs_eq h5regs regIdx, h4o _ hn13, h3o _ hn13, h2o _ hn13]; rfl
          have hDataNext : uNext.data = st.data.set (2 * n + v.val) (reg u4 rOne)
              (by rw [st.data_size]; have := v.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
            change u6.data = _
            rw [h6d, h5data]
            have h4DataEq : u4.data = st.data := by rw [h4d, h3d, h2d]
            simp only [h4_r13, h4DataEq]
          have hU4One : (reg u4 rOne).val = 1 := by
            rw [h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          have hvReach : g.InitiallyReachable r v :=
            initiallyReachable_extend hIn.uReach (List.getElem_mem hj)
          have hInNext : ReachSweepInnerInv g r origInner u (j + 1) uNext := by
            refine ⟨rfl, ?_, (congrArg Fin.val (hKeepNext r5 (by decide) (by decide))).trans hIn.markedBase,
              (congrArg Fin.val (hKeepNext r6 (by decide) (by decide))).trans hIn.offBase,
              (congrArg Fin.val (hKeepNext r7 (by decide) (by decide))).trans hIn.tgtBase,
              by rw [hKeepNext r8 (by decide) (by decide)]; exact hIn.idx,
              hIn.uReach, hj, ?_,
              (congrArg Fin.val (hKeepNext r12 (by decide) (by decide))).trans hIn.edgeEnd,
              ?_, ?_, ?_, ?_, ?_⟩
            · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide))).trans hIn.consts.zero,
                (congrArg Fin.val (hKeepNext rOne (by decide) (by decide))).trans hIn.consts.one,
                (congrArg Fin.val (hKeepNext rN (by decide) (by decide))).trans hIn.consts.nVal,
                (congrArg Fin.val (hKeepNext rM (by decide) (by decide))).trans hIn.consts.mVal,
                (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide))).trans hIn.consts.rootVal⟩
            · change (reg u6 r11).val = outPrefix g u.val + (j + 1)
              rw [h6v, add_no_wrap _ _ (by rw [h5_r11, h5_one]; exact hEdgeNextFit), h5_r11, h5_one]; omega
            · intro w
              rw [hDataNext]
              by_cases hwv : w = v
              · subst w; right; dsimp only [n] at *; simp [Array.getElem?_set_self, hU4One]
              · rw [Array.getElem?_set_ne _ (fun h => hwv (Fin.ext (by dsimp only [n] at *; omega)))]
                exact hIn.bits01 w
            · intro w hmw
              rw [hDataNext]
              by_cases hwv : w = v
              · subst w; dsimp only [n] at *; simp [Array.getElem?_set_self, hU4One]
              · rw [Array.getElem?_set_ne _ (fun h => hwv (Fin.ext (by dsimp only [n] at *; omega)))]
                exact hIn.mono w hmw
            · intro w hmw
              rw [hDataNext] at hmw
              by_cases hwv : w = v
              · rw [hwv]; exact hvReach
              · rw [Array.getElem?_set_ne _ (fun h => hwv (Fin.ext (by dsimp only [n] at *; omega)))] at hmw
                exact hIn.sound w hmw
            · intro t ht
              rw [hDataNext]
              by_cases htj : t = j
              · subst t; dsimp only [v, n] at *; simp [Array.getElem?_set_self, hU4One]
              · have htPrev : t < j := by omega
                by_cases hwv : (g.outArcs u)[t]'(Nat.lt_of_lt_of_le ht hj) = v
                · have hIdxEq : ((g.outArcs u)[t]'(Nat.lt_of_lt_of_le ht hj)).val = v.val := congrArg Fin.val hwv
                  dsimp only [n] at *; rw [hIdxEq, Array.getElem?_set_self, Option.map_some, hU4One]
                · rw [Array.getElem?_set_ne _ (fun h => hwv (Fin.ext (by dsimp only [n] at *; omega)))]
                  exact hIn.headsMarked t htPrev
            · intro idx hidx
              rw [hDataNext, Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n] at hidx ⊢; omega)]
              exact hIn.frame idx hidx
          have hSteps6 : Steps code input 7 st uNext :=
            Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21 (Steps.zero uNext)))))))
          obtain ⟨stEnd, tailSteps, hTailLe, hTailSteps, hPost⟩ :=
            ih (j + 1) uNext (by omega) hInNext (by rw [hKeepNext r8 (by decide) (by decide)]; exact hr8)
          exact ⟨stEnd, 7 + tailSteps, by omega, hSteps6.append hTailSteps, hPost⟩
        · have hjEq : j = (g.outArcs u).length := by have := hIn.hjLe; omega
          have hCmp : ltb (reg st r11) (reg st r12) = false :=
            branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
          have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 22) := by rw [hIn.pc]; rfl
          let stEnd : State L16 := { st with pc := 22 }
          have hs15 : step code input st = some (.next stEnd) := by
            simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
              step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
          refine ⟨stEnd, 1, by omega, Steps.cons hs15 (Steps.zero stEnd),
            rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
            hIn.markedBase, hIn.offBase, hIn.tgtBase, hr8,
            hIn.bits01, hIn.mono, hIn.sound, ?_, hIn.frame⟩
          intro w hwArc
          obtain ⟨t, ht, hwt⟩ := List.mem_iff_getElem.mp hwArc
          simpa only [hwt] using hIn.headsMarked t (by omega)
    simpa only [Nat.sub_zero] using hInAux (g.outArcs u).length 0 st0 (Nat.le_refl _) hIn0 rfl
  -- Note: step_loadData16 above didn't need to be wrapped awkwardly; let's clean it in the outer loop!
  let OuterState := Nat
  let OuterInv (k : Nat) (s : State L16) : Prop :=
    k ≤ n ∧ ReachSweepOuterInv g r order s₀.data k s
  let processedArcs (k : Nat) : Nat := ((order.take k).map (fun u => (g.outArcs u).length)).sum
  have hProcArcsLe : ∀ k ≤ n, processedArcs k ≤ m := by
    intro k _
    have hndTake : (order.take k).Nodup := hTopo.1.sublist (List.take_sublist _ _)
    have hSub : ∀ xs : List (Fin n), xs.Nodup → (xs.map (fun u => (g.outArcs u).length)).sum ≤ m := by
      intro xs hnd
      -- sum over nodup list ≤ sum over all vertices = m
      have hMem : ∀ (ys : List (Fin n)), ys.Nodup →
          (ys.map (fun u => (g.outArcs u).length)).sum ≤
            (List.ofFn (fun u : Fin n => (g.outArcs u).length)).sum := by
        intro ys hynd
        induction ys with
        | nil => simp
        | cons y ys ihy =>
          have hcons := List.nodup_cons.mp hynd
          have ihTail := ihy hcons.2
          -- Actually use nodup_filter_sum_le on List.finRange n or just simpler induction on n:
          -- Wait: use processedArcsCount-like induction on `k ≤ n` for `xs` with `< k`!
          have hAll : ∀ (b : Nat) (zs : List (Fin n)), zs.Nodup → (∀ z ∈ zs, z.val < b) →
              (zs.map (fun u => (g.outArcs u).length)).sum ≤
                (List.ofFn (fun i : Fin b =>
                  if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0)).sum := by
            intro b
            induction b with
            | zero =>
              intro zs _ hlt; cases zs with | nil => simp | cons z _ => have := hlt z (by simp); omega
            | succ b ihb =>
              intro zs hzs hlt
              let zs' := zs.filter (fun z => decide (z.val ≠ b))
              have hzs' : zs'.Nodup := nodup_filter_bool _ hzs
              have hlt' : ∀ z ∈ zs', z.val < b := by
                intro z hz; rcases List.mem_filter.mp hz with ⟨hz1, hz2⟩
                have := hlt z hz1
                have : z.val ≠ b := by simpa using hz2
                omega
              have ihSub := ihb zs' hzs' hlt'
              have hSumB : (List.ofFn (fun i : Fin (b + 1) =>
                  if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0)).sum =
                  (List.ofFn (fun i : Fin b =>
                    if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0)).sum +
                  (if h : b < n then (g.outArcs ⟨b, h⟩).length else 0) := by
                have hEq : List.ofFn (fun i : Fin (b + 1) =>
                    if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0) =
                    List.ofFn (fun i : Fin b =>
                      if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0) ++
                    [if h : b < n then (g.outArcs ⟨b, h⟩).length else 0] := by
                  apply List.ext_getElem
                  · simp
                  · intro i hi hj
                    by_cases hib : i < b
                    · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hib]), List.getElem_ofFn]
                    · have hibEq : i = b := by simp at hi; omega
                      subst i; rw [List.getElem_ofFn, List.getElem_append_right (by simp)]; simp
                rw [hEq, List.sum_append, List.sum_singleton]
              rw [hSumB]
              by_cases hb : b < n
              · have hF := nodup_filter_sum_le zs hzs (fun z => decide (z.val ≠ b)) ⟨b, hb⟩
                  (fun u => (g.outArcs u).length) (fun a _ hfa => Fin.ext (by simpa using hfa))
                rw [dite_eq_left hb]
                exact Nat.le_trans hF (Nat.add_le_add_right ihSub _)
              · have hEqF : zs' = zs := by
                  apply List.filter_eq_self.mpr
                  intro z _; have := z.isLt; simp; omega
                rw [hEqF] at ihSub; omega
          have hAllN := hAll n (y :: ys) hynd (fun z _ => z.isLt)
          have hEqFn : (List.ofFn (fun i : Fin n =>
              if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0)) =
              List.ofFn (fun u : Fin n => (g.outArcs u).length) := by
            apply List.ext_getElem <;> simp
          rw [← hEqFn]; exact hAllN
      have hTot : (List.ofFn (fun u : Fin n => (g.outArcs u).length)).sum = m := by
        dsimp only [m]
        rw [← outPrefix_vertexCount g]
        have : ∀ k ≤ n, outPrefix g k = (List.ofFn (fun i : Fin k =>
            if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0)).sum := by
          intro k
          induction k with
          | zero => intro _; simp [outPrefix]
          | succ k ihk =>
            intro hk
            have hkLt : k < n := by omega
            have hEq : List.ofFn (fun i : Fin (k + 1) =>
                if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0) =
                List.ofFn (fun i : Fin k =>
                  if h : i.val < n then (g.outArcs ⟨i.val, h⟩).length else 0) ++
                [if h : k < n then (g.outArcs ⟨k, h⟩).length else 0] := by
              apply List.ext_getElem
              · simp
              · intro i hi hj
                by_cases hik : i < k
                · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hik]), List.getElem_ofFn]
                · have : i = k := by simp at hi; omega
                  subst i; rw [List.getElem_ofFn, List.getElem_append_right (by simp)]; simp
            rw [hEq, List.sum_append, List.sum_singleton, ← ihk (by omega)]
            dsimp only [n] at hkLt ⊢
            simp only [outPrefix, dite_eq_left hkLt]
        rw [this n (Nat.le_refl _)]
        congr 1
        apply List.ext_getElem
        · simp
        · intro i hi hj
          rw [List.getElem_ofFn, List.getElem_ofFn]
          have hiN : i < n := by simpa using hi
          simp only [dite_eq_left hiN]
      simpa only [hTot] using hMem xs hnd
    exact hSub (order.take k) hndTake
  let OuterMeas (k : Nat) : Nat := n - k
  let OuterBudget (k : Nat) : Nat := 13 * (n - k) + 8 * (m - processedArcs k) + 2
  let OuterPost (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (∀ v : Fin n,
      (t.data[markedBase n m + v.val]?).map Fin.val =
        some (if ((g.scanReachability r order hTopo).marked[v.val]?).getD false then 1 else 0)) ∧
    (∀ j, (j < 2 * n ∨ 3 * n ≤ j) → t.data[j]? = s₀.data[j]?)
  have hOuterStep : ∀ k st, OuterInv k st →
      (∃ t, OuterPost k t ∧ ∃ steps, steps ≤ OuterBudget k ∧ run code input steps st = some ⟨t, steps⟩) ∨
      (∃ k' st' steps, OuterMeas k' < OuterMeas k ∧ steps + OuterBudget k' ≤ OuterBudget k ∧
        Steps code input steps st st' ∧ OuterInv k' st') := by
    intro k st ⟨hkLe, hOut⟩
    by_cases hk : k < n
    · right
      have hCmp : ltb (reg st r8) (reg st rN) = true :=
        branchLt_true (by rw [hOut.idx, hOut.consts.nVal]; exact hk)
      have hf5 : code[st.pc]? = some (.branchLt r8 rN 6 24) := by rw [hOut.pc]; rfl
      let u1 : State L16 := { st with pc := 6 }
      have hu1Pc : u1.pc = 6 := rfl
      have hs5 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf5 (by rw [hSz, hCmp]; decide)
      have hTopoAddrFit : (reg u1 rN).val + (reg u1 r8).val < 2 ^ bits := by
        change (reg st rN).val + (reg st r8).val < 2 ^ bits
        rw [hOut.consts.nVal, hOut.idx]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs6, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r9 : (reg u2 r9).val = n + k := by
        rw [h2v, add_no_wrap _ _ hTopoAddrFit]
        change (reg st rN).val + (reg st r8).val = _; rw [hOut.consts.nVal, hOut.idx]
      let u : Fin n := order[k]'(by rw [hlen]; exact hk)
      have huFit : u.val < 2 ^ bits := by
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      have huData : u2.data[(reg u2 r9).val]? = some ⟨u.val, huFit⟩ := by
        rw [h2d, h2_r9]
        change st.data[g.vertexCount + k]? = _
        have hFrame := hOut.frame (g.vertexCount + k) (Or.inl (by dsimp only [n] at *; omega))
        have hm := hTopoMem k hk
        rw [topoOrderBase_eq] at hm
        rw [hFrame]
        cases hcell : s₀.data[g.vertexCount + k]? with
        | none => simp [hcell] at hm
        | some w => rw [hcell, Option.map_some] at hm; exact congrArg some (Fin.ext (Option.some.inj hm))
      obtain ⟨u3, hs7, h3pc, h3v, h3o, h3d⟩ := step_loadData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) huData
        (by rw [hSz, h2pc, hu1Pc]; decide)
      have h3_r9 : (reg u3 r9).val = u.val := by rw [h3v]
      have hMarkAddrFit : (reg u3 r5).val + (reg u3 r9).val < 2 ^ bits := by
        rw [h3o _ (by decide), h2o _ (by decide)]
        change (reg st r5).val + (reg u3 r9).val < 2 ^ bits
        rw [hOut.markedBase, h3_r9]
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u4, hs8, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
      have h4_r10 : (reg u4 r10).val = 2 * n + u.val := by
        rw [h4v, add_no_wrap _ _ hMarkAddrFit, h3o _ (by decide), h2o _ (by decide)]
        change (reg st r5).val + _ = _; rw [hOut.markedBase, h3_r9]
      have htakeK1 : order.take (k + 1) = order.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hlen]; exact hk), Option.toList_some]
      have hProcInc : processedArcs (k + 1) = processedArcs k + (g.outArcs u).length := by
        dsimp only [processedArcs]
        rw [htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      have hProcLe1 := hProcArcsLe (k + 1) (by omega)
      rcases hOut.bits01 u with hu0 | hu1
      · -- Case marked[u] = 0 -> skip inner loop
        have huMark0 : u4.data[(reg u4 r10).val]? = some ⟨0, Nat.pow_pos Nat.zero_lt_two⟩ := by
          rw [h4d, h3d, h2d, h4_r10]
          change st.data[2 * g.vertexCount + u.val]? = _
          cases hcell : st.data[2 * g.vertexCount + u.val]? with
          | none => simp [hcell] at hu0
          | some w => rw [hcell, Option.map_some] at hu0; exact congrArg some (Fin.ext (Option.some.inj hu0))
        obtain ⟨u5, hs9, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
          (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) huMark0
          (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
        have hCmp10 : ltb (reg u5 r10) (reg u5 rOne) = true :=
          branchLt_true (by rw [h5v, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
            h2o _ (by decide)]; change 0 < (reg st rOne).val; rw [hOut.consts.one]; omega)
        have hf10 : code[u5.pc]? = some (.branchLt r10 rOne 22 11) := by
          rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
        let u6 : State L16 := { u5 with pc := 22 }
        have hu6Pc : u6.pc = 22 := rfl
        have hs10 : step code input u5 = some (.next u6) := by
          simpa only [u6, hCmp10, ite_true] using
            step_branchLt_at (input := input) hf10 (by rw [hSz, hCmp10]; decide)
        have h6_r8 : (reg u6 r8).val = k := by
          change (reg u5 r8).val = k
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hOut.idx
        have h6_one : (reg u6 rOne).val = 1 := by
          change (reg u5 rOne).val = 1
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hOut.consts.one
        have hk1Fit : k + 1 < 2 ^ bits := by
          unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u7, hs22, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
          (s := u6) (code := code) rfl (by rw [hSz, hu6Pc]; decide)
        let stNext : State L16 := { u7 with pc := 5 }
        have hs23 : step code input u7 = some (.next stNext) :=
          step_goto_at (code := code) (by rw [h7pc, hu6Pc]; rfl) (by rw [hSz]; decide)
        have hKeepNext (regIdx : Fin 16) (hn8 : regIdx ≠ r8) (hn9 : regIdx ≠ r9)
            (hn10 : regIdx ≠ r10) : reg stNext regIdx = reg st regIdx := by
          change reg u7 regIdx = reg st regIdx
          rw [h7o _ hn8]
          change reg u5 regIdx = reg st regIdx
          rw [h5o _ hn10, h4o _ hn10, h3o _ hn9, h2o _ hn9]; rfl
        have hDataNext : stNext.data = st.data := by
          change u7.data = st.data; rw [h7d]; change u5.data = st.data; rw [h5d, h4d, h3d, h2d]
        have huNotReach : ¬ g.InitiallyReachable r u := by
          intro hru
          have hMarkU : (st.data[2 * n + u.val]?).map Fin.val = some 1 := by
            rcases AvoidPath.eq_or_exists_last_arc hru with hur | ⟨p, hpReach, hpu⟩
            · subst hur; exact hOut.rootMarked
            · have hpPre := topo_arc_tail_before g order hTopo (by rw [hlen]; exact hk) hpu
              exact (hOut.prefixDone p hpPre hpReach).2 u hpu
          rw [hMarkU] at hu0; cases hu0
        have hOutNext : ReachSweepOuterInv g r order s₀.data (k + 1) stNext := by
          refine ⟨rfl, ?_,
            (congrArg Fin.val (hKeepNext r5 (by decide) (by decide) (by decide))).trans hOut.markedBase,
            (congrArg Fin.val (hKeepNext r6 (by decide) (by decide) (by decide))).trans hOut.offBase,
            (congrArg Fin.val (hKeepNext r7 (by decide) (by decide) (by decide))).trans hOut.tgtBase,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide))).trans hOut.consts.zero,
              (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide))).trans hOut.consts.one,
              (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide))).trans hOut.consts.nVal,
              (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide))).trans hOut.consts.mVal,
              (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide))).trans hOut.consts.rootVal⟩
          · change (reg u7 r8).val = k + 1
            rw [h7v, add_no_wrap _ _ (by rw [h6_r8, h6_one]; exact hk1Fit), h6_r8, h6_one]
          · intro v; rw [hDataNext]; exact hOut.bits01 v
          · rw [hDataNext]; exact hOut.rootMarked
          · intro v hv; rw [hDataNext] at hv; exact hOut.sound v hv
          · intro p hp hpReach
            rw [htakeK1, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · rw [hDataNext]; exact hOut.prefixDone p hp hpReach
            · exact False.elim (huNotReach hpReach)
          · intro j hj; rw [hDataNext]; exact hOut.frame j hj
        refine ⟨k + 1, stNext, 8, by dsimp only [OuterMeas]; omega,
          by dsimp only [OuterBudget]; omega,
          Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs22 (Steps.cons hs23 (Steps.zero stNext)))))))),
          by omega, hOutNext⟩
      · -- Case marked[u] = 1 -> run inner loop
        have huReach : g.InitiallyReachable r u := hOut.sound u hu1
        have huMark1 : u4.data[(reg u4 r10).val]? = some ⟨1, by omega⟩ := by
          rw [h4d, h3d, h2d, h4_r10]
          change st.data[2 * g.vertexCount + u.val]? = _
          cases hcell : st.data[2 * g.vertexCount + u.val]? with
          | none => simp [hcell] at hu1
          | some w => rw [hcell, Option.map_some] at hu1; exact congrArg some (Fin.ext (Option.some.inj hu1))
        obtain ⟨u5, hs9, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
          (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) huMark1
          (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
        have hCmp10 : ltb (reg u5 r10) (reg u5 rOne) = false :=
          branchLt_false (by rw [h5v, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
            h2o _ (by decide)]; change (reg st rOne).val ≤ 1; rw [hOut.consts.one]; exact Nat.le_refl _)
        have hf10 : code[u5.pc]? = some (.branchLt r10 rOne 22 11) := by
          rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
        let u6 : State L16 := { u5 with pc := 11 }
        have hu6Pc : u6.pc = 11 := rfl
        have hs10 : step code input u5 = some (.next u6) := by
          simpa only [u6, hCmp10, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf10 (by rw [hSz, hCmp10]; decide)
        have h6_r6 : (reg u6 r6).val = 3 := by
          change (reg u5 r6).val = 3
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hOut.offBase
        have h6_r9 : (reg u6 r9).val = u.val := by
          change (reg u5 r9).val = u.val
          rw [h5o _ (by decide), h4o _ (by decide)]; exact h3_r9
        have hOffAddrFit : (reg u6 r6).val + (reg u6 r9).val < 2 ^ bits := by
          rw [h6_r6, h6_r9]
          have := raw.cap_ge; unfold rawDagInputCap at this; have := u.isLt; dsimp only [n] at *; omega
        obtain ⟨u7, hs11, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
          (s := u6) (code := code) rfl (by rw [hSz, hu6Pc]; decide)
        have h7_r10 : (reg u7 r10).val = 3 + u.val := by
          rw [h7v, add_no_wrap _ _ hOffAddrFit, h6_r6, h6_r9]
        have hOffStartFit : outPrefix g u.val < 2 ^ bits := by
          have := outPrefix_mono g (Nat.le_of_lt u.isLt); rw [outPrefix_vertexCount] at this
          have := raw.cap_ge; unfold rawDagInputCap at this; omega
        have huOff0 : input.words[(reg u7 r10).val]? = some ⟨outPrefix g u.val, hOffStartFit⟩ := by
          rw [h7_r10]
          have ho := raw.out_off u.val (Nat.le_of_lt u.isLt)
          cases hcell : input.words[3 + u.val]? with
          | none => simp [hcell] at ho
          | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
        obtain ⟨u8, hs12, h8pc, h8v, h8o, h8d⟩ := step_loadInput16 (input := input)
          (s := u7) (code := code) (by rw [h7pc, hu6Pc]; rfl) (by rw [hSz, h7pc, hu6Pc]; decide) huOff0
        have h8_r10 : (reg u8 r10).val = 3 + u.val := by rw [h8o _ (by decide)]; exact h7_r10
        have h8_one : (reg u8 rOne).val = 1 := by
          rw [h8o _ (by decide), h7o _ (by decide)]
          change (reg u5 rOne).val = 1
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hOut.consts.one
        have hOffAddr2Fit : (reg u8 r10).val + (reg u8 rOne).val < 2 ^ bits := by
          rw [h8_r10, h8_one]; have := u.isLt; have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
        obtain ⟨u9, hs13, h9pc, h9v, h9o, h9d⟩ := step_add16 (input := input)
          (s := u8) (code := code) (by rw [h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h8pc, h7pc, hu6Pc]; decide)
        have h9_r10 : (reg u9 r10).val = 3 + (u.val + 1) := by
          rw [h9v, add_no_wrap _ _ hOffAddr2Fit, h8_r10, h8_one]; omega
        have hOffEndFit : outPrefix g (u.val + 1) < 2 ^ bits := by
          have := outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount); rw [outPrefix_vertexCount] at this
          have := raw.cap_ge; unfold rawDagInputCap at this; omega
        have huOff1 : input.words[(reg u9 r10).val]? = some ⟨outPrefix g (u.val + 1), hOffEndFit⟩ := by
          rw [h9_r10]
          have ho := raw.out_off (u.val + 1) (by omega)
          cases hcell : input.words[3 + (u.val + 1)]? with
          | none => simp [hcell] at ho
          | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
        obtain ⟨u10, hs14, h10pc, h10v, h10o, h10d⟩ := step_loadInput16 (input := input)
          (s := u9) (code := code) (by rw [h9pc, h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h9pc, h8pc, h7pc, hu6Pc]; decide) huOff1
        have hKeep10 (regIdx : Fin 16) (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10)
            (hn11 : regIdx ≠ r11) (hn12 : regIdx ≠ r12) : reg u10 regIdx = reg st regIdx := by
          rw [h10o _ hn12, h9o _ hn10, h8o _ hn11, h7o _ hn10]
          change reg u5 regIdx = reg st regIdx
          rw [h5o _ hn10, h4o _ hn10, h3o _ hn9, h2o _ hn9]; rfl
        have hData10 : u10.data = st.data := by
          rw [h10d, h9d, h8d, h7d]; change u5.data = st.data; rw [h5d, h4d, h3d, h2d]
        have hIn0 : ReachSweepInnerInv g r u10.data u 0 u10 := by
          refine ⟨by rw [h10pc, h9pc, h8pc, h7pc, hu6Pc], ?_,
            (congrArg Fin.val (hKeep10 r5 (by decide) (by decide) (by decide) (by decide))).trans hOut.markedBase,
            (congrArg Fin.val (hKeep10 r6 (by decide) (by decide) (by decide) (by decide))).trans hOut.offBase,
            (congrArg Fin.val (hKeep10 r7 (by decide) (by decide) (by decide) (by decide))).trans hOut.tgtBase,
            by rw [hKeep10 r8 (by decide) (by decide) (by decide) (by decide), hOut.idx]; exact hk,
            huReach, Nat.zero_le _,
            by rw [h10o _ (by decide), h9o _ (by decide), h8v, Nat.add_zero],
            (congrArg Fin.val h10v).trans (outPrefix_succ_lt g u),
            by rw [hData10]; exact hOut.bits01, fun _ h => h,
            by rw [hData10]; exact hOut.sound, fun _ ht => False.elim (Nat.not_lt_zero _ ht),
            fun _ _ => rfl⟩
          · exact ⟨(congrArg Fin.val (hKeep10 rZero (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.zero,
              (congrArg Fin.val (hKeep10 rOne (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.one,
              (congrArg Fin.val (hKeep10 rN (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.nVal,
              (congrArg Fin.val (hKeep10 rM (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.mVal,
              (congrArg Fin.val (hKeep10 rRoot (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.rootVal⟩
        obtain ⟨st22, innerSteps, hInnerLe, hInnerSteps, h22pc, h22c, h22mb, h22ob, h22tb,
          h22r8, h22bits, h22mono, h22sound, h22heads, h22frame⟩ := run_inner u u10 u10.data rfl hIn0
        have h22_r8 : (reg st22 r8).val = k := by
          rw [h22r8, hKeep10 r8 (by decide) (by decide) (by decide) (by decide)]; exact hOut.idx
        have h22_one : (reg st22 rOne).val = 1 := h22c.one
        have hk1Fit : k + 1 < 2 ^ bits := by
          unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u23, hs22, h23pc, h23v, h23o, h23d⟩ := step_add16 (input := input)
          (s := st22) (code := code) (by rw [h22pc]; rfl) (by rw [hSz, h22pc]; decide)
        let stNext : State L16 := { u23 with pc := 5 }
        have hs23 : step code input u23 = some (.next stNext) :=
          step_goto_at (input := input) (code := code) (by rw [h23pc, h22pc]; rfl) (by rw [hSz]; decide)
        have hKeepNext (regIdx : Fin 16) (hn8 : regIdx ≠ r8) : reg stNext regIdx = reg st22 regIdx :=
          h23o regIdx hn8
        have hDataNext : stNext.data = st22.data := h23d
        have hOutNext : ReachSweepOuterInv g r order s₀.data (k + 1) stNext := by
          refine ⟨rfl, ?_,
            (congrArg Fin.val (hKeepNext r5 (by decide))).trans h22mb,
            (congrArg Fin.val (hKeepNext r6 (by decide))).trans h22ob,
            (congrArg Fin.val (hKeepNext r7 (by decide))).trans h22tb,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide))).trans h22c.zero,
              (congrArg Fin.val (hKeepNext rOne (by decide))).trans h22c.one,
              (congrArg Fin.val (hKeepNext rN (by decide))).trans h22c.nVal,
              (congrArg Fin.val (hKeepNext rM (by decide))).trans h22c.mVal,
              (congrArg Fin.val (hKeepNext rRoot (by decide))).trans h22c.rootVal⟩
          · change (reg u23 r8).val = k + 1
            rw [h23v, add_no_wrap _ _ (by rw [h22_r8, h22_one]; exact hk1Fit), h22_r8, h22_one]
          · intro v; rw [hDataNext]; exact h22bits v
          · rw [hDataNext]; apply h22mono r; rw [hData10]; exact hOut.rootMarked
          · intro v hv; rw [hDataNext] at hv; exact h22sound v hv
          · intro p hp hpReach
            rw [hDataNext]
            rw [htakeK1, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · have hPrev := hOut.prefixDone p hp hpReach
              refine ⟨h22mono p (by rw [hData10]; exact hPrev.1), fun w hw => h22mono w (by rw [hData10]; exact hPrev.2 w hw)⟩
            · refine ⟨h22mono u (by rw [hData10]; exact hu1), fun w hw => h22heads w hw⟩
          · intro j hj; rw [hDataNext, h22frame j hj, hData10]; exact hOut.frame j hj
        have hPref10 : Steps code input 10 st u10 :=
          Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.zero u10))))))))))
        have hTail2 : Steps code input 2 st22 stNext :=
          Steps.cons hs22 (Steps.cons hs23 (Steps.zero stNext))
        refine ⟨k + 1, stNext, 10 + innerSteps + 2, by dsimp only [OuterMeas]; omega,
          by dsimp only [OuterBudget]; omega, (hPref10.append hInnerSteps).append hTail2,
          by omega, hOutNext⟩
    · left
      have hkEq : k = n := by omega
      have hCmp : ltb (reg st r8) (reg st rN) = false :=
        branchLt_false (by rw [hOut.idx, hOut.consts.nVal, hkEq]; exact Nat.le_refl _)
      have hf5 : code[st.pc]? = some (.branchLt r8 rN 6 24) := by rw [hOut.pc]; rfl
      let t : State L16 := { st with pc := 24 }
      have hs5 : step code input st = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf5 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 st = some ⟨t, 2⟩ :=
        (Steps.cons hs5 (Steps.zero t)).halts hHalt
      have hMarkedIff : ∀ v : Fin n,
          ((g.scanReachability r order hTopo).marked[v.val]?).getD false = true ↔
            (st.data[2 * n + v.val]?).map Fin.val = some 1 := by
        intro v
        rw [g.scanReachability_iff r order hTopo v]
        constructor
        · intro hv
          have hvOrd : v ∈ order.take k := by
            rw [List.take_of_length_le (by rw [hlen, hkEq]; exact Nat.le_refl _)]
            exact hTopo.2.1 v
          exact (hOut.prefixDone v hvOrd hv).1
        · exact hOut.sound v
      refine ⟨t, ⟨⟨hOut.consts.zero, hOut.consts.one, hOut.consts.nVal, hOut.consts.mVal, hOut.consts.rootVal⟩,
        ?_, hOut.frame⟩, 2, by dsimp only [OuterBudget]; omega, hRun2⟩
      intro v
      rw [markedBase_eq]
      cases hb : ((g.scanReachability r order hTopo).marked[v.val]?).getD false with
      | true => simp only [ite_true]; exact (hMarkedIff v).mp hb
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rcases hOut.bits01 v with h0 | h1
        · exact h0
        · have := (hMarkedIff v).mpr h1; rw [hb] at this; cases this
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget OuterInv OuterMeas OuterBudget OuterPost hOuterStep n 0 t5
      (by dsimp only [OuterMeas]; omega) ⟨Nat.zero_le _, hOut0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hm, hf⟩
  have hZeroArcs : processedArcs 0 = 0 := by simp [processedArcs]
  dsimp only [OuterBudget, OuterMeas] at hLoopLe
  rw [hZeroArcs, Nat.sub_zero, Nat.sub_zero] at hLoopLe
  exact ⟨tEnd, 5 + loopSteps, by omega, hExec, hc, hm, hf⟩

end Phase2ReachSweep

/-! ### Phase 3: Compact reachable vertices in topological order (`origToDensePlusOne`, `denseToOrig`) -/

section Phase3CompactReach

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

/-- Reachable vertices listed in the verified topological order. -/
def denseVertices (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order) :
    List (Fin g.vertexCount) :=
  order.filter (fun v => ((g.scanReachability r order hTopo).marked[v.val]?).getD false)

theorem denseVertices_nodup (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order) :
    (denseVertices g r order hTopo).Nodup :=
  nodup_filter_bool _ hTopo.1

theorem denseVertices_mem_iff (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    (v : Fin g.vertexCount) :
    v ∈ denseVertices g r order hTopo ↔ g.InitiallyReachable r v := by
  unfold denseVertices
  rw [List.mem_filter, g.scanReachability_iff r order hTopo v]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hTopo.2.1 v, h⟩⟩

theorem denseVertices_length_pos (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order) :
    1 ≤ (denseVertices g r order hTopo).length := by
  have hr : r ∈ denseVertices g r order hTopo :=
    (denseVertices_mem_iff g r order hTopo r).mpr (initiallyReachable_source g r)
  exact List.length_pos_of_mem hr

theorem denseVertices_length_le (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order) :
    (denseVertices g r order hTopo).length ≤ g.vertexCount :=
  nodup_length_le_fin _ (denseVertices_nodup g r order hTopo)

theorem denseVertices_head_eq (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order) :
    (denseVertices g r order hTopo)[0]'(denseVertices_length_pos g r order hTopo) = r := by
  obtain ⟨pre, post, hSplit⟩ := list_split_mem (hTopo.2.1 r)
  have hReachSplit : ∀ {x y : Fin g.vertexCount},
      AvoidPath g.HasArc (fun _ => False) x y →
      (x = r ∨ x ∈ post) →
      (y = r ∨ y ∈ post) ∧ (x ∈ post → y ∈ post) := by
    intro x y hpath
    induction hpath with
    | refl _ _ => intro hx; exact ⟨hx, fun h => h⟩
    | step a b c _ hab _ ih =>
      intro ha
      have hbInPost : b ∈ post := by
        rcases ha with rfl | haPost
        · exact hTopo.2.2 pre a post hSplit b hab
        · obtain ⟨q1, q2, hq⟩ := list_split_mem haPost
          have hSplitA : order = (pre ++ r :: q1) ++ (a :: q2) := by
            rw [hSplit, hq]; simp [List.append_assoc]
          have hbQ2 := hTopo.2.2 (pre ++ r :: q1) a q2 hSplitA b hab
          rw [hq]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hbQ2))
      have hRest := ih (Or.inr hbInPost)
      exact ⟨hRest.1, fun _ => hRest.2 hbInPost⟩
  have hrNotPost : r ∉ post := by
    have hnd := hTopo.1
    rw [hSplit] at hnd
    have hTailNd : (r :: post).Nodup := by
      clear hReachSplit hSplit hTopo
      induction pre with
      | nil => exact hnd
      | cons _ _ ih => exact ih (List.nodup_cons.mp hnd).2
    exact (List.nodup_cons.mp hTailNd).1
  have hPreNotReach : ∀ x ∈ pre, ¬ g.InitiallyReachable r x := by
    intro x hx hrx
    have hnd := hTopo.1
    rw [hSplit] at hnd
    have hmem : (x = r ∨ x ∈ post) := (hReachSplit hrx (Or.inl rfl)).1
    have hdisj : ∀ (as bs : List (Fin g.vertexCount)), (as ++ bs).Nodup → ∀ y ∈ as, y ∉ bs := by
      intro as bs hab
      induction as with
      | nil => simp
      | cons a as iha =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · intro hyb; exact (List.nodup_cons.mp hab).1 (List.mem_append.mpr (Or.inr hyb))
        · exact iha (List.nodup_cons.mp hab).2 y hy'
    exact hdisj pre (r :: post) hnd x hx (by rcases hmem with rfl | hx2; exact List.mem_cons_self ..; exact List.mem_cons_of_mem _ hx2)
  have hPreFilt : pre.filter (fun v => ((g.scanReachability r order hTopo).marked[v.val]?).getD false) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    cases hb : ((g.scanReachability r order hTopo).marked[x.val]?).getD false with
    | false => simp
    | true => exact False.elim (hPreNotReach x hx ((g.scanReachability_iff r order hTopo x).mp hb))
  have hrMark : ((g.scanReachability r order hTopo).marked[r.val]?).getD false = true :=
    (g.scanReachability_iff r order hTopo r).mpr (initiallyReachable_source g r)
  have hEq : denseVertices g r order hTopo =
      r :: post.filter (fun v => ((g.scanReachability r order hTopo).marked[v.val]?).getD false) := by
    unfold denseVertices
    conv => lhs; arg 2; rw [hSplit]
    rw [List.filter_append, hPreFilt, List.nil_append, List.filter_cons, ite_eq_left hrMark]
  simp only [hEq, List.getElem_cons_zero]

theorem denseVertices_strict_topo (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    (i j : Fin (denseVertices g r order hTopo).length)
    (harc : g.HasArc ((denseVertices g r order hTopo)[i.val]'i.isLt)
      ((denseVertices g r order hTopo)[j.val]'j.isLt)) :
    i.val < j.val := by
  have hOrdPair : order.Pairwise (fun a b => ¬ g.HasArc b a) := by
    have hGen : ∀ (pre xs : List (Fin g.vertexCount)),
        order = pre ++ xs → xs.Nodup → xs.Pairwise (fun a b => ¬ g.HasArc b a) := by
      intro pre xs
      induction xs generalizing pre with
      | nil => intro _ _; exact List.Pairwise.nil
      | cons a as ih =>
        intro hEq hNd
        refine List.pairwise_cons.mpr ⟨?_, ih (pre ++ [a]) (by rw [hEq, List.append_assoc]; rfl) (List.nodup_cons.mp hNd).2⟩
        intro b hb hba
        have hbMem : b ∈ as := hb
        -- If g.HasArc b a, then since b ∈ as, wait: a ∈ pre ++ [a] ... b ∈ post -> contradiction!
        obtain ⟨q1, q2, hq⟩ := list_split_mem hbMem
        have hSplitB : order = (pre ++ a :: q1) ++ (b :: q2) := by rw [hEq, hq]; simp [List.append_assoc]
        have haQ2 := hTopo.2.2 (pre ++ a :: q1) b q2 hSplitB a hba
        have hNdCons := List.nodup_cons.mp hNd
        apply hNdCons.1
        rw [hq]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ haQ2))
    exact hGen [] order rfl hTopo.1
  have hDensePair : (denseVertices g r order hTopo).Pairwise (fun a b => ¬ g.HasArc b a) :=
    hOrdPair.sublist (List.filter_sublist)
  by_cases hlt : i.val < j.val
  · exact hlt
  · have hle : j.val ≤ i.val := by omega
    by_cases heq : j.val = i.val
    · have hu := (denseVertices g r order hTopo)[i.val]'i.isLt
      have harcSelf : g.HasArc ((denseVertices g r order hTopo)[i.val]'i.isLt)
          ((denseVertices g r order hTopo)[i.val]'i.isLt) := by
        simpa only [heq] using harc
      have hMem := List.getElem_mem (l := denseVertices g r order hTopo) i.isLt
      have hMemOrd : (denseVertices g r order hTopo)[i.val]'i.isLt ∈ order :=
        (List.mem_filter.mp hMem).1
      obtain ⟨p, q, hpq⟩ := list_split_mem hMemOrd
      have hInQ := hTopo.2.2 p _ q hpq _ harcSelf
      have hNd := hTopo.1
      rw [hpq] at hNd
      have hTailNd : (((denseVertices g r order hTopo)[i.val]'i.isLt) :: q).Nodup := by
        clear harcSelf hpq hOrdPair hDensePair
        induction p with | nil => exact hNd | cons _ _ ih => exact ih (List.nodup_cons.mp hNd).2
      exact False.elim ((List.nodup_cons.mp hTailNd).1 hInQ)
    · have hjlt : j.val < i.val := by omega
      have hNeg := (List.pairwise_iff_getElem.mp hDensePair) j.val i.val j.isLt i.isLt hjlt
      exact False.elim (hNeg harc)

def compactReachCode : Program L16 :=
  #[.add r9 rN rN,
    .add r10 r9 rN,
    .add r11 r10 rN,
    .imm r5 0,
    .imm r8 0,
    .branchLt r8 rN 6 19,
    .add r12 rN r8,
    .loadData r12 r12,
    .add r13 r9 r12,
    .loadData r13 r13,
    .branchLt r13 rOne 15 11,
    .add r14 r11 r5,
    .storeData r14 r12,
    .add r5 r5 rOne,
    .mov r13 r5,
    .add r14 r10 r12,
    .storeData r14 r13,
    .add r8 r8 rOne,
    .goto 5,
    .halt]

def compactReachPhase : Phase L16 :=
  Phase.ofLast compactReachCode 19 rfl rfl rfl

private theorem compactReachPhase_size : (compactReachPhase (hi := hi) (hw := hw)).code.size = 20 := rfl

private structure CompactInv (g : Digraph) (r : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    (origData : Array (Word bits)) (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 5
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  markedBase : (reg s r9).val = 2 * g.vertexCount
  origBase : (reg s r10).val = 3 * g.vertexCount
  denseBase : (reg s r11).val = 4 * g.vertexCount
  idx : (reg s r8).val = k
  qCount : (reg s r5).val = ((order.take k).filter (fun v =>
    ((g.scanReachability r order hTopo).marked[v.val]?).getD false)).length
  denseMem : ∀ i : Nat, (hi_1 : i < ((order.take k).filter (fun v =>
      ((g.scanReachability r order hTopo).marked[v.val]?).getD false)).length) →
    (s.data[4 * g.vertexCount + i]?).map Fin.val =
      some (((order.take k).filter (fun v =>
        ((g.scanReachability r order hTopo).marked[v.val]?).getD false))[i]'hi_1).val
  origPos : ∀ i : Nat, (hi_1 : i < ((order.take k).filter (fun v =>
      ((g.scanReachability r order hTopo).marked[v.val]?).getD false)).length) →
    (s.data[3 * g.vertexCount + (((order.take k).filter (fun v =>
      ((g.scanReachability r order hTopo).marked[v.val]?).getD false))[i]'hi_1).val]?).map Fin.val =
      some (i + 1)
  origZero : ∀ v : Fin g.vertexCount, v ∈ order.take k → ¬ g.InitiallyReachable r v →
    (s.data[3 * g.vertexCount + v.val]?).map Fin.val = some 0
  frame : ∀ j, (j < 3 * g.vertexCount ∨ 5 * g.vertexCount ≤ j) → s.data[j]? = origData[j]?

theorem run_compactReachPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (order : List (Fin g.vertexCount)) (hlen : order.length = g.vertexCount)
    (hTopo : g.IsTopologicalList order)
    (hTopoMem : ∀ i : Nat, (hi_1 : i < g.vertexCount) →
      (s₀.data[topoOrderBase g.vertexCount g.arcCount + i]?).map Fin.val =
        some (order[i]'(by rw [hlen]; exact hi_1)).val)
    (hMarkMem : ∀ v : Fin g.vertexCount,
      (s₀.data[markedBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some (if ((g.scanReachability r order hTopo).marked[v.val]?).getD false then 1 else 0)) :
    let n := g.vertexCount
    let m := g.arcCount
    let dense := denseVertices g r order hTopo
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 14 * n + 7 ∧
      run compactReachPhase.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = dense.length ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (t.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val) ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (t.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1)) ∧
      (∀ v : Fin n, ¬ g.InitiallyReachable r v →
        (t.data[origToDensePlusOneBase n m + v.val]?).map Fin.val = some 0) ∧
      (∀ j, (j < 3 * n ∨ 5 * n ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m dense
  let code : Program L16 := compactReachPhase.code
  have hSz : code.size = 20 := compactReachPhase_size
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have h2nFit : 2 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h3nFit : 3 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h4nFit : 4 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hAdd1 : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  have h1_r9 : (reg t1 r9).val = 2 * n := by
    rw [h1v, add_no_wrap _ _ hAdd1]; change (reg s₀ rN).val + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd2 : (reg t1 r9).val + (reg t1 rN).val < 2 ^ bits := by
    rw [h1_r9, h1o _ (by decide)]; change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_r10 : (reg t2 r10).val = 3 * n := by
    rw [h2v, add_no_wrap _ _ hAdd2, h1_r9, h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd3 : (reg t2 r10).val + (reg t2 rN).val < 2 ^ bits := by
    rw [h2_r10, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_imm16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t5, hs4, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 5 s_start t5 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.zero t5)))))
  have hKeep5 (regIdx : Fin 16) (hn5 : regIdx ≠ r5) (hn8 : regIdx ≠ r8)
      (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10) (hn11 : regIdx ≠ r11) :
      reg t5 regIdx = reg s_start regIdx := by
    rw [h5o _ hn8, h4o _ hn5, h3o _ hn11, h2o _ hn10, h1o _ hn9]
  have hData5 : t5.data = s₀.data := by rw [h5d, h4d, h3d, h2d, h1d]; rfl
  have hConsts5 : ConstRegs n m r.val t5 :=
    ⟨(congrArg Fin.val (hKeep5 rZero (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep5 rOne (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep5 rN (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep5 rM (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep5 rRoot (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hInv0 : CompactInv g r order hTopo s₀.data 0 t5 := by
    refine ⟨by rw [h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact h1_r9
    · rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide)]; exact h2_r10
    · rw [h5o _ (by decide), h4o _ (by decide), h3v, add_no_wrap _ _ hAdd3, h2_r10, h2o _ (by decide), h1o _ (by decide)]
      change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
    · rw [h5v]; rfl
    · rw [h5o _ (by decide), h4v]; simp
    · intro i hi; simp at hi
    · intro i hi; simp at hi
    · intro v hv; simp at hv
    · intro _ _; rw [hData5]
  let Post (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (reg t r5).val = dense.length ∧
    (∀ i : Nat, (hi_1 : i < dense.length) →
      (t.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val) ∧
    (∀ i : Nat, (hi_1 : i < dense.length) →
      (t.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1)) ∧
    (∀ v : Fin n, ¬ g.InitiallyReachable r v →
      (t.data[origToDensePlusOneBase n m + v.val]?).map Fin.val = some 0) ∧
    (∀ j, (j < 3 * n ∨ 5 * n ≤ j) → t.data[j]? = s₀.data[j]?)
  have hStepCase : ∀ k st, (k ≤ n ∧ CompactInv g r order hTopo s₀.data k st) →
      (∃ t, Post k t ∧ ∃ steps, steps ≤ 14 * (n - k) + 2 ∧ run code input steps st = some ⟨t, steps⟩) ∨
      (∃ k' st' steps, (n - k') < (n - k) ∧ steps + (14 * (n - k') + 2) ≤ 14 * (n - k) + 2 ∧
        Steps code input steps st st' ∧ (k' ≤ n ∧ CompactInv g r order hTopo s₀.data k' st')) := by
    intro k st ⟨hkLe, hInv⟩
    by_cases hk : k < n
    · right
      have hCmp : ltb (reg st r8) (reg st rN) = true :=
        branchLt_true (by rw [hInv.idx, hInv.consts.nVal]; exact hk)
      have hf5 : code[st.pc]? = some (.branchLt r8 rN 6 19) := by rw [hInv.pc]; rfl
      let u1 : State L16 := { st with pc := 6 }
      have hu1Pc : u1.pc = 6 := rfl
      have hs5 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf5 (by rw [hSz, hCmp]; decide)
      have hTopoAddrFit : (reg u1 rN).val + (reg u1 r8).val < 2 ^ bits := by
        change (reg st rN).val + (reg st r8).val < 2 ^ bits
        rw [hInv.consts.nVal, hInv.idx]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs6, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r12 : (reg u2 r12).val = n + k := by
        rw [h2v, add_no_wrap _ _ hTopoAddrFit]; change (reg st rN).val + (reg st r8).val = _; rw [hInv.consts.nVal, hInv.idx]
      let u : Fin n := order[k]'(by rw [hlen]; exact hk)
      have huFit : u.val < 2 ^ bits := by
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      have huData : u2.data[(reg u2 r12).val]? = some ⟨u.val, huFit⟩ := by
        rw [h2d, h2_r12]; change st.data[g.vertexCount + k]? = _
        rw [hInv.frame (g.vertexCount + k) (Or.inl (by dsimp only [n] at *; omega))]
        have hm := hTopoMem k hk; rw [topoOrderBase_eq] at hm
        cases hcell : s₀.data[g.vertexCount + k]? with
        | none => simp [hcell] at hm
        | some w => rw [hcell, Option.map_some] at hm; exact congrArg some (Fin.ext (Option.some.inj hm))
      obtain ⟨u3, hs7, h3pc, h3v, h3o, h3d⟩ := step_loadData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) huData (by rw [hSz, h2pc, hu1Pc]; decide)
      have h3_r12 : (reg u3 r12).val = u.val := by rw [h3v]
      have hMarkAddrFit : (reg u3 r9).val + (reg u3 r12).val < 2 ^ bits := by
        rw [h3o _ (by decide), h2o _ (by decide)]
        change (reg st r9).val + _ < 2 ^ bits; rw [hInv.markedBase, h3_r12]
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u4, hs8, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
      have h4_r13 : (reg u4 r13).val = 2 * n + u.val := by
        rw [h4v, add_no_wrap _ _ hMarkAddrFit, h3o _ (by decide), h2o _ (by decide)]
        change (reg st r9).val + _ = _; rw [hInv.markedBase, h3_r12]
      let p : Fin n → Bool := fun v => ((g.scanReachability r order hTopo).marked[v.val]?).getD false
      let pref := (order.take k).filter p
      have hPrefLen : pref.length ≤ n := nodup_length_le_fin pref (nodup_filter_bool p (hTopo.1.sublist (List.take_sublist _ _)))
      have htakeK1 : order.take (k + 1) = order.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hlen]; exact hk), Option.toList_some]
      have huNotPre : u ∉ order.take k := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
        have hiLt : i < k := by simp only [List.length_take] at hi; omega
        have hqi : order[i]'(by rw [hlen]; omega) = u := by simpa only [List.getElem_take] using heq
        exact (Nat.ne_of_lt hiLt) (hTopo.1.eq_of_getElem_eq (by rw [hlen]; omega) (by rw [hlen]; exact hk) hqi)
      have huNotPref : u ∉ pref := fun hm => huNotPre (List.mem_filter.mp hm).1
      cases hpu : p u with
      | false =>
        have hm0 : u4.data[(reg u4 r13).val]? = some ⟨0, Nat.pow_pos Nat.zero_lt_two⟩ := by
          rw [h4d, h3d, h2d, h4_r13]
          change st.data[2 * n + u.val]? = _
          rw [hInv.frame (2 * n + u.val) (Or.inl (by have := u.isLt; omega))]
          have hmm := hMarkMem u; rw [markedBase_eq] at hmm
          have hpu' : ((g.scanReachability r order hTopo).marked[u.val]?).getD false = false := hpu
          simp only [hpu', Bool.false_eq_true, ite_false] at hmm
          cases hcell : s₀.data[2 * g.vertexCount + u.val]? with
          | none => simp [hcell] at hmm
          | some w => rw [hcell, Option.map_some] at hmm; exact congrArg some (Fin.ext (Option.some.inj hmm))
        obtain ⟨u5, hs9, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
          (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) hm0
          (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
        have hCmp10 : ltb (reg u5 r13) (reg u5 rOne) = true :=
          branchLt_true (by rw [h5v, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
            h2o _ (by decide)]; change 0 < (reg st rOne).val; rw [hInv.consts.one]; omega)
        have hf10 : code[u5.pc]? = some (.branchLt r13 rOne 15 11) := by
          rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
        let u6 : State L16 := { u5 with pc := 15 }
        have hu6Pc : u6.pc = 15 := rfl
        have hs10 : step code input u5 = some (.next u6) := by
          simpa only [u6, hCmp10, ite_true] using
            step_branchLt_at (input := input) hf10 (by rw [hSz, hCmp10]; decide)
        have h5_r10 : (reg u5 r10).val = 3 * n := by
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.origBase
        have h5_r12 : (reg u5 r12).val = u.val := by
          rw [h5o _ (by decide), h4o _ (by decide)]; exact h3_r12
        have hOrigAddrFit : (reg u6 r10).val + (reg u6 r12).val < 2 ^ bits := by
          change (reg u5 r10).val + (reg u5 r12).val < 2 ^ bits
          rw [h5_r10, h5_r12]
          have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u7, hs15, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
          (s := u6) (code := code) rfl (by rw [hSz, hu6Pc]; decide)
        have h7_r14 : (reg u7 r14).val = 3 * n + u.val := by
          rw [h7v, add_no_wrap _ _ hOrigAddrFit]
          change (reg u5 r10).val + (reg u5 r12).val = _; rw [h5_r10, h5_r12]
        have h7Bound : (reg u7 r14).val < u7.data.size := by
          rw [u7.data_size, h7_r14]; have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u8, hs16, h8pc, h8regs, h8data⟩ := step_storeData16 (input := input)
          (s := u7) (code := code) (by rw [h7pc, hu6Pc]; rfl) (by rw [hSz, h7pc, hu6Pc]; decide) h7Bound
        have h8_r8 : (reg u8 r8).val = k := by
          rw [reg_eq_of_regs_eq h8regs r8, h7o _ (by decide)]
          change (reg u5 r8).val = k
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.idx
        have h8_one : (reg u8 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h8regs rOne, h7o _ (by decide)]
          change (reg u5 rOne).val = 1
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.consts.one
        have hk1Fit : k + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u9, hs17, h9pc, h9v, h9o, h9d⟩ := step_add16 (input := input)
          (s := u8) (code := code) (by rw [h8pc, h7pc, hu6Pc]; rfl) (by rw [hSz, h8pc, h7pc, hu6Pc]; decide)
        let stNext : State L16 := { u9 with pc := 5 }
        have hs18 : step code input u9 = some (.next stNext) :=
          step_goto_at (code := code) (by rw [h9pc, h8pc, h7pc, hu6Pc]; rfl) (by rw [hSz]; decide)
        have hKeepNext (regIdx : Fin 16) (hn8 : regIdx ≠ r8) (hn12 : regIdx ≠ r12)
            (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) : reg stNext regIdx = reg st regIdx := by
          change reg u9 regIdx = reg st regIdx
          rw [h9o _ hn8, reg_eq_of_regs_eq h8regs regIdx, h7o _ hn14]
          change reg u5 regIdx = reg st regIdx
          rw [h5o _ hn13, h4o _ hn13, h3o _ hn12, h2o _ hn12]; rfl
        have hDataNext : stNext.data = st.data.set (3 * n + u.val) ⟨0, Nat.pow_pos Nat.zero_lt_two⟩
            (by rw [st.data_size]; have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
          change u9.data = _
          rw [h9d, h8data]
          have h7DataEq : u7.data = st.data := by rw [h7d]; change u5.data = _; rw [h5d, h4d, h3d, h2d]
          have h7_r13 : reg u7 r13 = ⟨0, Nat.pow_pos Nat.zero_lt_two⟩ := by
            rw [h7o _ (by decide)]; exact h5v
          simp only [h7_r14, h7_r13, h7DataEq]
        have hFiltNext : (order.take (k + 1)).filter (fun v =>
            ((g.scanReachability r order hTopo).marked[v.val]?).getD false) = pref := by
          have hpuf : ((g.scanReachability r order hTopo).marked[u.val]?).getD false = false := hpu
          rw [htakeK1, List.filter_append, List.filter_cons, hpuf]
          dsimp only [pref, p]
          simp only [List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rfl
        have huNotReach : ¬ g.InitiallyReachable r u := by
          intro hru
          have := (g.scanReachability_iff r order hTopo u).mpr hru
          have hpu' : ((g.scanReachability r order hTopo).marked[u.val]?).getD false = false := hpu
          rw [hpu'] at this; cases this
        have hInvNext : CompactInv g r order hTopo s₀.data (k + 1) stNext := by
          refine ⟨rfl, ?_,
            (congrArg Fin.val (hKeepNext r9 (by decide) (by decide) (by decide) (by decide))).trans hInv.markedBase,
            (congrArg Fin.val (hKeepNext r10 (by decide) (by decide) (by decide) (by decide))).trans hInv.origBase,
            (congrArg Fin.val (hKeepNext r11 (by decide) (by decide) (by decide) (by decide))).trans hInv.denseBase,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.zero,
              (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.one,
              (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.nVal,
              (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.mVal,
              (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.rootVal⟩
          · change (reg u9 r8).val = k + 1
            rw [h9v, add_no_wrap _ _ (by rw [h8_r8, h8_one]; exact hk1Fit), h8_r8, h8_one]
          · rw [hKeepNext r5 (by decide) (by decide) (by decide) (by decide), hFiltNext]; exact hInv.qCount
          · intro i hi
            rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
            revert hi; rw [hFiltNext]; intro hi; exact hInv.denseMem i hi
          · intro i hi
            rw [hDataNext]
            revert hi; rw [hFiltNext]; intro hi
            have hne : (pref[i]'hi).val ≠ u.val := fun h => huNotPref (Fin.ext h ▸ List.getElem_mem hi)
            rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
            exact hInv.origPos i hi
          · intro v hv hvNot
            rw [hDataNext]
            rw [htakeK1, List.mem_append, List.mem_singleton] at hv
            by_cases hvu : v = u
            · subst hvu; dsimp only [n] at *; rw [Array.getElem?_set_self]; simp
            · rcases hv with hv | rfl
              · rw [Array.getElem?_set_ne _ (fun h => hvu (Fin.ext (by dsimp only [n] at *; omega)))]
                exact hInv.origZero v hv hvNot
              · exact False.elim (hvu rfl)
          · intro j hj
            rw [hDataNext, Array.getElem?_set_ne _ (by have := u.isLt; dsimp only [n] at hj ⊢; omega)]
            exact hInv.frame j hj
        refine ⟨k + 1, stNext, 10, by omega, by omega,
          Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.zero stNext)))))))))),
          by omega, hInvNext⟩
      | true =>
        have hm1 : u4.data[(reg u4 r13).val]? = some ⟨1, by omega⟩ := by
          rw [h4d, h3d, h2d, h4_r13]
          change st.data[2 * n + u.val]? = _
          rw [hInv.frame (2 * n + u.val) (Or.inl (by have := u.isLt; omega))]
          have hmm := hMarkMem u; rw [markedBase_eq] at hmm
          have hpu' : ((g.scanReachability r order hTopo).marked[u.val]?).getD false = true := hpu
          simp only [hpu', ite_true] at hmm
          cases hcell : s₀.data[2 * g.vertexCount + u.val]? with
          | none => simp [hcell] at hmm
          | some w => rw [hcell, Option.map_some] at hmm; exact congrArg some (Fin.ext (Option.some.inj hmm))
        obtain ⟨u5, hs9, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
          (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) hm1
          (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
        have hCmp10 : ltb (reg u5 r13) (reg u5 rOne) = false :=
          branchLt_false (by rw [h5v, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
            h2o _ (by decide)]; change (reg st rOne).val ≤ 1; rw [hInv.consts.one]; exact Nat.le_refl _)
        have hf10 : code[u5.pc]? = some (.branchLt r13 rOne 15 11) := by
          rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl
        let u6 : State L16 := { u5 with pc := 11 }
        have hu6Pc : u6.pc = 11 := rfl
        have hs10 : step code input u5 = some (.next u6) := by
          simpa only [u6, hCmp10, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf10 (by rw [hSz, hCmp10]; decide)
        have hFiltNext : (order.take (k + 1)).filter p = pref ++ [u] := by
          rw [htakeK1, List.filter_append, List.filter_cons, hpu]; simp [pref]
        have hPrefNextLen : pref.length + 1 ≤ n := by
          have := nodup_length_le_fin ((order.take (k + 1)).filter p)
            (nodup_filter_bool p (hTopo.1.sublist (List.take_sublist _ _)))
          rw [hFiltNext, List.length_append, List.length_singleton] at this; exact this
        have h6_r11 : (reg u6 r11).val = 4 * n := by
          change (reg u5 r11).val = 4 * n
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.denseBase
        have h6_r5 : (reg u6 r5).val = pref.length := by
          change (reg u5 r5).val = pref.length
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.qCount
        have hDenseAddrFit : (reg u6 r11).val + (reg u6 r5).val < 2 ^ bits := by
          rw [h6_r11, h6_r5]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u7, hs11, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
          (s := u6) (code := code) rfl (by rw [hSz, hu6Pc]; decide)
        have h7_r14 : (reg u7 r14).val = 4 * n + pref.length := by
          rw [h7v, add_no_wrap _ _ hDenseAddrFit, h6_r11, h6_r5]
        have h7Bound : (reg u7 r14).val < u7.data.size := by
          rw [u7.data_size, h7_r14]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u8, hs12, h8pc, h8regs, h8data⟩ := step_storeData16 (input := input)
          (s := u7) (code := code) (by rw [h7pc, hu6Pc]; rfl) (by rw [hSz, h7pc, hu6Pc]; decide) h7Bound
        have h8_r5 : (reg u8 r5).val = pref.length := by
          rw [reg_eq_of_regs_eq h8regs r5, h7o _ (by decide)]; exact h6_r5
        have h8_one : (reg u8 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h8regs rOne, h7o _ (by decide)]; change (reg u5 rOne).val = 1
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.consts.one
        have hQFit : pref.length + 1 < 2 ^ bits := by
          unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u9, hs13, h9pc, h9v, h9o, h9d⟩ := step_add16 (input := input)
          (s := u8) (code := code) (by rw [h8pc, h7pc, hu6Pc]; rfl) (by rw [hSz, h8pc, h7pc, hu6Pc]; decide)
        have h9_r5 : (reg u9 r5).val = pref.length + 1 := by
          rw [h9v, add_no_wrap _ _ (by rw [h8_r5, h8_one]; exact hQFit), h8_r5, h8_one]
        obtain ⟨u10, hs14, h10pc, h10v, h10o, h10d⟩ := step_mov16 (input := input)
          (s := u9) (code := code) (by rw [h9pc, h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h9pc, h8pc, h7pc, hu6Pc]; decide)
        have h10_r13 : (reg u10 r13).val = pref.length + 1 := by rw [h10v]; exact h9_r5
        have h10_r10 : (reg u10 r10).val = 3 * n := by
          rw [h10o _ (by decide), h9o _ (by decide), reg_eq_of_regs_eq h8regs r10, h7o _ (by decide)]
          change (reg u5 r10).val = _; rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
          exact hInv.origBase
        have h10_r12 : (reg u10 r12).val = u.val := by
          rw [h10o _ (by decide), h9o _ (by decide), reg_eq_of_regs_eq h8regs r12, h7o _ (by decide)]
          change (reg u5 r12).val = _; rw [h5o _ (by decide), h4o _ (by decide), h3_r12]
        have hOrigAddrFit : (reg u10 r10).val + (reg u10 r12).val < 2 ^ bits := by
          rw [h10_r10, h10_r12]; have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u11, hs15, h11pc, h11v, h11o, h11d⟩ := step_add16 (input := input)
          (s := u10) (code := code) (by rw [h10pc, h9pc, h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h10pc, h9pc, h8pc, h7pc, hu6Pc]; decide)
        have h11_r14 : (reg u11 r14).val = 3 * n + u.val := by
          rw [h11v, add_no_wrap _ _ hOrigAddrFit, h10_r10, h10_r12]
        have h11Bound : (reg u11 r14).val < u11.data.size := by
          rw [u11.data_size, h11_r14]; have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u12, hs16, h12pc, h12regs, h12data⟩ := step_storeData16 (input := input)
          (s := u11) (code := code) (by rw [h11pc, h10pc, h9pc, h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h11pc, h10pc, h9pc, h8pc, h7pc, hu6Pc]; decide) h11Bound
        have h12_r8 : (reg u12 r8).val = k := by
          rw [reg_eq_of_regs_eq h12regs r8, h11o _ (by decide), h10o _ (by decide), h9o _ (by decide),
            reg_eq_of_regs_eq h8regs r8, h7o _ (by decide)]
          change (reg u5 r8).val = k
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.idx
        have h12_one : (reg u12 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq h12regs rOne, h11o _ (by decide), h10o _ (by decide), h9o _ (by decide),
            reg_eq_of_regs_eq h8regs rOne, h7o _ (by decide)]
          change (reg u5 rOne).val = 1
          rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hInv.consts.one
        have hk1Fit : k + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
        obtain ⟨u13, hs17, h13pc, h13v, h13o, h13d⟩ := step_add16 (input := input)
          (s := u12) (code := code) (by rw [h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, hu6Pc]; rfl)
          (by rw [hSz, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, hu6Pc]; decide)
        let stNext : State L16 := { u13 with pc := 5 }
        have hs18 : step code input u13 = some (.next stNext) :=
          step_goto_at (code := code) (by rw [h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, hu6Pc]; rfl)
            (by rw [hSz]; decide)
        have hKeepNext (regIdx : Fin 16) (hn5 : regIdx ≠ r5) (hn8 : regIdx ≠ r8)
            (hn12 : regIdx ≠ r12) (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) :
            reg stNext regIdx = reg st regIdx := by
          change reg u13 regIdx = reg st regIdx
          rw [h13o _ hn8, reg_eq_of_regs_eq h12regs regIdx, h11o _ hn14, h10o _ hn13, h9o _ hn5,
            reg_eq_of_regs_eq h8regs regIdx, h7o _ hn14]
          change reg u5 regIdx = reg st regIdx
          rw [h5o _ hn13, h4o _ hn13, h3o _ hn12, h2o _ hn12]; rfl
        have h7_r12 : reg u7 r12 = ⟨u.val, huFit⟩ := by
          rw [h7o _ (by decide)]
          change reg u5 r12 = _
          rw [h5o _ (by decide), h4o _ (by decide)]
          exact h3v
        have hDataMid : u8.data = st.data.set (4 * n + pref.length) (reg u7 r12)
            (by rw [st.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
          rw [h8data]
          have h7DataEq : u7.data = st.data := by rw [h7d]; change u5.data = _; rw [h5d, h4d, h3d, h2d]
          simp only [h7_r14, h7DataEq]
        have hDataNext : stNext.data = u8.data.set (3 * n + u.val) (reg u11 r13)
            (by rw [u8.data_size]; have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
          change u13.data = _
          rw [h13d, h12data]
          have h11DataEq : u11.data = u8.data := by rw [h11d, h10d, h9d]
          simp only [h11_r14, h11DataEq]
        have h11_r13 : (reg u11 r13).val = pref.length + 1 := by
          rw [h11o _ (by decide)]; exact h10_r13
        have huReach : g.InitiallyReachable r u :=
          (g.scanReachability_iff r order hTopo u).mp hpu
        have hFiltNext' : (order.take (k + 1)).filter (fun v =>
            ((g.scanReachability r order hTopo).marked[v.val]?).getD false) = pref ++ [u] := by
          simpa only [p] using hFiltNext
        have hInvNext : CompactInv g r order hTopo s₀.data (k + 1) stNext := by
          refine ⟨rfl, ?_,
            (congrArg Fin.val (hKeepNext r9 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.markedBase,
            (congrArg Fin.val (hKeepNext r10 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.origBase,
            (congrArg Fin.val (hKeepNext r11 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.denseBase,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.zero,
              (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.one,
              (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.nVal,
              (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.mVal,
              (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide) (by decide) (by decide))).trans hInv.consts.rootVal⟩
          · change (reg u13 r8).val = k + 1
            rw [h13v, add_no_wrap _ _ (by rw [h12_r8, h12_one]; exact hk1Fit), h12_r8, h12_one]
          · change (reg u13 r5).val = _
            rw [h13o _ (by decide), reg_eq_of_regs_eq h12regs r5, h11o _ (by decide), h10o _ (by decide), h9_r5, hFiltNext']
            simp
          · intro i hi
            rw [hDataNext, Array.getElem?_set_ne _ (by have := u.isLt; dsimp only [n] at *; omega), hDataMid]
            revert hi; rw [hFiltNext']; intro hi
            by_cases hilast : i = pref.length
            · subst i
              dsimp only [n] at *
              rw [Array.getElem?_set_self, Option.map_some, h7_r12]
              simp
            · have hiLt : i < pref.length := by simp at hi; omega
              rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega), List.getElem_append_left hiLt]
              exact hInv.denseMem i hiLt
          · intro i hi
            rw [hDataNext]
            revert hi; rw [hFiltNext']; intro hi
            by_cases hilast : i = pref.length
            · subst i
              dsimp only [n] at *
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp [Array.getElem?_set_self, h11_r13]
            · have hiLt : i < pref.length := by simp at hi; omega
              rw [List.getElem_append_left hiLt]
              have hne : (pref[i]'hiLt).val ≠ u.val := fun h => huNotPref (Fin.ext h ▸ List.getElem_mem hiLt)
              rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega), hDataMid,
                Array.getElem?_set_ne _ (by have := (pref[i]'hiLt).isLt; dsimp only [n] at *; omega)]
              exact hInv.origPos i hiLt
          · intro v hv hvNot
            rw [htakeK1, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · have hne : v.val ≠ u.val := fun h => by
                apply hvNot; rw [Fin.ext h]; exact huReach
              rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega), hDataMid,
                Array.getElem?_set_ne _ (by have := v.isLt; dsimp only [n] at *; omega)]
              exact hInv.origZero v hv hvNot
            · exact False.elim (hvNot huReach)
          · intro j hj
            rw [hDataNext, Array.getElem?_set_ne _ (by have := u.isLt; dsimp only [n] at hj ⊢; omega),
              hDataMid, Array.getElem?_set_ne _ (by dsimp only [n] at hj hPrefNextLen ⊢; omega)]
            exact hInv.frame j hj
        have hSteps14 : Steps code input 14 st stNext :=
          Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
              (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.zero stNext))))))))))))))
        exact ⟨k + 1, stNext, 14, by omega, by omega, hSteps14, by omega, hInvNext⟩
    · left
      have hkEq : k = n := by omega
      have hCmp : ltb (reg st r8) (reg st rN) = false :=
        branchLt_false (by rw [hInv.idx, hInv.consts.nVal, hkEq]; exact Nat.le_refl _)
      have hf5 : code[st.pc]? = some (.branchLt r8 rN 6 19) := by rw [hInv.pc]; rfl
      let t : State L16 := { st with pc := 19 }
      have hs5 : step code input st = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf5 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 st = some ⟨t, 2⟩ :=
        (Steps.cons hs5 (Steps.zero t)).halts hHalt
      have hTakeAll : order.take k = order := List.take_of_length_le (by rw [hlen, hkEq]; exact Nat.le_refl _)
      have hFiltEq : (order.take k).filter (fun v =>
          ((g.scanReachability r order hTopo).marked[v.val]?).getD false) = dense := by
        rw [hTakeAll]; rfl
      refine ⟨t, ⟨⟨hInv.consts.zero, hInv.consts.one, hInv.consts.nVal, hInv.consts.mVal, hInv.consts.rootVal⟩,
        ?_, ?_, ?_, ?_, hInv.frame⟩, 2, by omega, hRun2⟩
      · change (reg st r5).val = dense.length; rw [hInv.qCount, hFiltEq]
      · intro i hi
        rw [denseToOrigBase_eq]
        have hi' := hi; rw [← hFiltEq] at hi'
        simpa only [hFiltEq] using hInv.denseMem i hi'
      · intro i hi
        rw [origToDensePlusOneBase_eq]
        have hi' := hi; rw [← hFiltEq] at hi'
        simpa only [hFiltEq] using hInv.origPos i hi'
      · intro v hv
        rw [origToDensePlusOneBase_eq]
        exact hInv.origZero v (by rw [hTakeAll]; exact hTopo.2.1 v) hv
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ n ∧ CompactInv g r order hTopo s₀.data k s)
      (fun k => n - k) (fun k => 14 * (n - k) + 2) Post
      (fun k st h => hStepCase k st h) n 0 t5 (Nat.le_refl _) ⟨Nat.zero_le _, hInv0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hlenEq, hdm, hop, hoz, hf⟩
  exact ⟨tEnd, 5 + loopSteps, by omega, hExec, hc, hlenEq, hdm, hop, hoz, hf⟩

end Phase3CompactReach

/-! ### Dense reachable incoming-arc CSR definitions and counting lemmas -/

section DenseCsrDefs

def denseInDegCount (g : Digraph) (dense : List (Fin g.vertexCount))
    (v : Fin g.vertexCount) : Nat :=
  (dense.map (fun u => countOccurrence v (g.outArcs u))).sum

def denseReachArcCount (g : Digraph) (dense : List (Fin g.vertexCount)) : Nat :=
  (dense.map (fun u => (g.outArcs u).length)).sum

def denseInPrefix (g : Digraph) (dense : List (Fin g.vertexCount)) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      denseInPrefix g dense i +
        if h : i < dense.length then denseInDegCount g dense (dense[i]'h) else 0

theorem denseInPrefix_succ_lt (g : Digraph) (dense : List (Fin g.vertexCount))
    (i : Nat) (hi : i < dense.length) :
    denseInPrefix g dense (i + 1) =
      denseInPrefix g dense i + denseInDegCount g dense (dense[i]'hi) := by
  simp only [denseInPrefix, dite_eq_left hi]

theorem denseInPrefix_mono (g : Digraph) (dense : List (Fin g.vertexCount))
    {i j : Nat} (h : i ≤ j) :
    denseInPrefix g dense i ≤ denseInPrefix g dense j := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    rw [hi0]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · rw [hij]; exact Nat.le_refl _
    · have := ih (by omega); simp only [denseInPrefix]; omega

private theorem countOccurrence_sublist_le {n : Nat} {v : Fin n} {as bs : List (Fin n)}
    (h : List.Sublist as bs) : countOccurrence v as ≤ countOccurrence v bs := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons _ _ ih => simp only [countOccurrence]; split <;> omega
  | cons_cons _ _ ih => simp only [countOccurrence]; omega

private theorem countOccurrence_le_length {n : Nat} (x : Fin n) (xs : List (Fin n)) :
    countOccurrence x xs ≤ xs.length := by
  induction xs with
  | nil => simp [countOccurrence]
  | cons a as ih => simp [countOccurrence]; split <;> omega

theorem denseInDegCount_le_denseReachArcCount (g : Digraph)
    (dense : List (Fin g.vertexCount)) (v : Fin g.vertexCount) :
    denseInDegCount g dense v ≤ denseReachArcCount g dense := by
  unfold denseInDegCount denseReachArcCount
  induction dense with
  | nil => simp
  | cons u us ih =>
    simp only [List.map_cons, List.sum_cons]
    have hc := countOccurrence_le_length v (g.outArcs u)
    omega

theorem denseReachArcCount_le (g : Digraph) (dense : List (Fin g.vertexCount))
    (hnd : dense.Nodup) :
    denseReachArcCount g dense ≤ g.arcCount := by
  unfold denseReachArcCount
  have hAll : ∀ (b : Nat) (zs : List (Fin g.vertexCount)), zs.Nodup → (∀ z ∈ zs, z.val < b) →
      (zs.map (fun u => (g.outArcs u).length)).sum ≤
        (List.ofFn (fun i : Fin b =>
          if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0)).sum := by
    intro b
    induction b with
    | zero =>
      intro zs _ hlt; cases zs with | nil => simp | cons z _ => have := hlt z (by simp); omega
    | succ b ihb =>
      intro zs hzs hlt
      let zs' := zs.filter (fun z => decide (z.val ≠ b))
      have hzs' : zs'.Nodup := nodup_filter_bool _ hzs
      have hlt' : ∀ z ∈ zs', z.val < b := by
        intro z hz; rcases List.mem_filter.mp hz with ⟨hz1, hz2⟩
        have := hlt z hz1; have : z.val ≠ b := by simpa using hz2
        omega
      have ihSub := ihb zs' hzs' hlt'
      have hSumB : (List.ofFn (fun i : Fin (b + 1) =>
          if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0)).sum =
          (List.ofFn (fun i : Fin b =>
            if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0)).sum +
          (if h : b < g.vertexCount then (g.outArcs ⟨b, h⟩).length else 0) := by
        have hEq : List.ofFn (fun i : Fin (b + 1) =>
            if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0) =
            List.ofFn (fun i : Fin b =>
              if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0) ++
            [if h : b < g.vertexCount then (g.outArcs ⟨b, h⟩).length else 0] := by
          apply List.ext_getElem
          · simp
          · intro i hi hj
            by_cases hib : i < b
            · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hib]), List.getElem_ofFn]
            · have : i = b := by simp at hi; omega
              subst i; rw [List.getElem_ofFn, List.getElem_append_right (by simp)]; simp
        rw [hEq, List.sum_append, List.sum_singleton]
      rw [hSumB]
      by_cases hb : b < g.vertexCount
      · have hF := nodup_filter_sum_le zs hzs (fun z => decide (z.val ≠ b)) ⟨b, hb⟩
          (fun u => (g.outArcs u).length) (fun a _ hfa => Fin.ext (by simpa using hfa))
        rw [dite_eq_left hb]
        exact Nat.le_trans hF (Nat.add_le_add_right ihSub _)
      · have hEqF : zs' = zs := by
          apply List.filter_eq_self.mpr; intro z _; have := z.isLt; simp; omega
        rw [hEqF] at ihSub; omega
  have hBound := hAll g.vertexCount dense hnd (fun z _ => z.isLt)
  have hTot : (List.ofFn (fun i : Fin g.vertexCount =>
      if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0)).sum = g.arcCount := by
    rw [← outPrefix_vertexCount g]
    have : ∀ k ≤ g.vertexCount, outPrefix g k = (List.ofFn (fun i : Fin k =>
        if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0)).sum := by
      intro k
      induction k with
      | zero => intro _; simp [outPrefix]
      | succ k ihk =>
        intro hk
        have hkLt : k < g.vertexCount := by omega
        have hEq : List.ofFn (fun i : Fin (k + 1) =>
            if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0) =
            List.ofFn (fun i : Fin k =>
              if h : i.val < g.vertexCount then (g.outArcs ⟨i.val, h⟩).length else 0) ++
            [if h : k < g.vertexCount then (g.outArcs ⟨k, h⟩).length else 0] := by
          apply List.ext_getElem
          · simp
          · intro i hi hj
            by_cases hik : i < k
            · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hik]), List.getElem_ofFn]
            · have : i = k := by simp at hi; omega
              subst i; rw [List.getElem_ofFn, List.getElem_append_right (by simp)]; simp
        rw [hEq, List.sum_append, List.sum_singleton, ← ihk (by omega)]
        simp only [outPrefix, dite_eq_left hkLt]
    exact (this g.vertexCount (Nat.le_refl _)).symm
  simpa only [hTot] using hBound

private theorem sum_ofFn_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun x => f x + g x)).sum = (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, ih]
    omega

private theorem sum_ofFn_countOccurrence {m : Nat} (dense : List (Fin m)) (hnd : dense.Nodup)
    (xs : List (Fin m)) (hClosed : ∀ v ∈ xs, v ∈ dense) :
    (List.ofFn (fun i : Fin dense.length => countOccurrence (dense[i.val]'i.isLt) xs)).sum = xs.length := by
  induction xs with
  | nil =>
    have hZ : ∀ k (f : Fin k → Nat), (∀ i, f i = 0) → (List.ofFn f).sum = 0 := by
      intro k f hf; induction k with
      | zero => simp
      | succ k ihk => simp only [List.ofFn_succ, List.sum_cons, hf 0, ihk (fun i => f i.succ) (fun i => hf i.succ)]
    exact hZ _ _ (fun _ => rfl)
  | cons v vs ih =>
    have hvMem : v ∈ dense := hClosed v (List.mem_cons_self ..)
    obtain ⟨idx, hidx, hvEq⟩ := List.mem_iff_getElem.mp hvMem
    have hStep : (fun i : Fin dense.length => countOccurrence (dense[i.val]'i.isLt) (v :: vs)) =
        fun i : Fin dense.length =>
          (if i.val = idx then 1 else 0) + countOccurrence (dense[i.val]'i.isLt) vs := by
      funext i
      simp only [countOccurrence]
      by_cases hiIdx : i.val = idx
      · have hEq : dense[i.val]'i.isLt = v := by
          have : i.val = idx := hiIdx
          simp [this, hvEq]
        rw [ite_eq_left hiIdx, ite_eq_left hEq.symm]
      · have hNe : dense[i.val]'i.isLt ≠ v := by
          intro heq
          rw [← hvEq] at heq
          exact hiIdx (hnd.eq_of_getElem_eq i.isLt hidx heq)
        rw [ite_eq_right hiIdx, ite_eq_right (Ne.symm hNe), Nat.zero_add]
    rw [hStep, sum_ofFn_add]
    have hZeroSum : ∀ k, (List.ofFn (fun _ : Fin k => (0 : Nat))).sum = 0 := fun k => by
      induction k with
      | zero => simp
      | succ k ihk => simp only [List.ofFn_succ, List.sum_cons, Nat.zero_add, ihk]
    have hOneHot : ∀ (len target : Nat), target < len →
        (List.ofFn (fun i : Fin len => if i.val = target then 1 else 0)).sum = 1 := by
      intro len
      induction len with
      | zero => intro target ht; omega
      | succ len ihl =>
        intro target ht
        simp only [List.ofFn_succ, List.sum_cons]
        cases target with
        | zero =>
          have hRest : (List.ofFn (fun i : Fin len => if i.succ.val = 0 then 1 else 0)).sum = 0 := by
            have : (fun i : Fin len => if i.succ.val = 0 then 1 else 0) = fun _ => 0 := by
              funext i; simp
            rw [this]
            exact hZeroSum len
          rw [hRest, Nat.add_zero]; simp
        | succ t =>
          have hEq : (fun i : Fin len => if i.succ.val = t + 1 then 1 else 0) =
              fun i : Fin len => if i.val = t then 1 else 0 := by
            funext i; simp
          rw [hEq, ihl t (by omega)]
          simp
    rw [hOneHot dense.length idx hidx, ih (fun x hx => hClosed x (List.mem_cons_of_mem _ hx))]
    simp; omega

theorem sum_denseInDegCount_eq (g : Digraph) (dense : List (Fin g.vertexCount))
    (hnd : dense.Nodup) (hClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense) :
    (List.ofFn (fun i : Fin dense.length =>
      denseInDegCount g dense (dense[i.val]'i.isLt))).sum = denseReachArcCount g dense := by
  unfold denseInDegCount denseReachArcCount
  have hZeroSum : ∀ k, (List.ofFn (fun _ : Fin k => (0 : Nat))).sum = 0 := fun k => by
    induction k with
    | zero => simp
    | succ k ihk => simp only [List.ofFn_succ, List.sum_cons, Nat.zero_add, ihk]
  have hAux : ∀ xs : List (Fin g.vertexCount), (∀ u ∈ xs, ∀ v ∈ g.outArcs u, v ∈ dense) →
      (List.ofFn (fun i : Fin dense.length =>
        (xs.map (fun u => countOccurrence (dense[i.val]'i.isLt) (g.outArcs u))).sum)).sum =
        (xs.map (fun u => (g.outArcs u).length)).sum := by
    intro xs hxs
    induction xs with
    | nil =>
      simp
      exact hZeroSum dense.length
    | cons u us ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [sum_ofFn_add, sum_ofFn_countOccurrence dense hnd (g.outArcs u) (hxs u (List.mem_cons_self ..)),
        ih (fun w hw => hxs w (List.mem_cons_of_mem _ hw))]
  exact hAux dense hClosed

theorem denseInPrefix_length (g : Digraph) (dense : List (Fin g.vertexCount))
    (hnd : dense.Nodup) (hClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense) :
    denseInPrefix g dense dense.length = denseReachArcCount g dense := by
  rw [← sum_denseInDegCount_eq g dense hnd hClosed]
  have hPrefixSum : ∀ k ≤ dense.length,
      denseInPrefix g dense k = (List.ofFn (fun i : Fin k =>
        if h : i.val < dense.length then denseInDegCount g dense (dense[i.val]'h) else 0)).sum := by
    intro k
    induction k with
    | zero => intro _; simp [denseInPrefix]
    | succ k ihk =>
      intro hk
      have hkLt : k < dense.length := by omega
      have hEq : List.ofFn (fun i : Fin (k + 1) =>
          if h : i.val < dense.length then denseInDegCount g dense (dense[i.val]'h) else 0) =
          List.ofFn (fun i : Fin k =>
            if h : i.val < dense.length then denseInDegCount g dense (dense[i.val]'h) else 0) ++
          [if h : k < dense.length then denseInDegCount g dense (dense[k]'h) else 0] := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          by_cases hik : i < k
          · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hik]), List.getElem_ofFn]
          · have : i = k := by simp at hi; omega
            subst i; rw [List.getElem_ofFn, List.getElem_append_right (by simp)]; simp
      rw [hEq, List.sum_append, List.sum_singleton, ← ihk (by omega), denseInPrefix_succ_lt g dense k hkLt,
        dite_eq_left hkLt]
  rw [hPrefixSum dense.length (Nat.le_refl _)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have hiLen : i < dense.length := by simpa using hi
    simp only [dite_eq_left hiLen]

end DenseCsrDefs

/-! ### Phase 4A: Zero `denseInDeg[0..qCount-1]` -/

section Phase4ZeroDenseInDeg

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def zeroDenseInDegCode : Program L16 :=
  #[.add r6 rN rN,
    .add r6 r6 r6,
    .add r6 r6 rN,
    .imm r7 0,
    .branchLt r7 r5 5 9,
    .add r8 r6 r7,
    .storeData r8 rZero,
    .add r7 r7 rOne,
    .goto 4,
    .halt]

def zeroDenseInDegPhase : Phase L16 :=
  Phase.ofLast zeroDenseInDegCode 9 rfl rfl rfl

private theorem zeroDenseInDegPhase_size :
    (zeroDenseInDegPhase (hi := hi) (hw := hw)).code.size = 10 := rfl

private structure ZeroDenseInDegInv (g : Digraph) (root qCount : Nat) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 4
  consts : ConstRegs g.vertexCount g.arcCount root s
  qCountReg : (reg s r5).val = qCount
  base : (reg s r6).val = 5 * g.vertexCount
  idx : (reg s r7).val = k
  zeros : ∀ i, i < k → (s.data[5 * g.vertexCount + i]?).map Fin.val = some 0
  frame : ∀ j, (j < 5 * g.vertexCount ∨ 5 * g.vertexCount + k ≤ j) → s.data[j]? = origData[j]?

theorem run_zeroDenseInDegPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (qCount : Nat) (hqLe : qCount ≤ g.vertexCount)
    (hqReg : (reg s₀ r5).val = qCount) :
    let n := g.vertexCount
    let m := g.arcCount
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 5 * n + 6 ∧
      run zeroDenseInDegPhase.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = qCount ∧
      (∀ i, i < qCount → (t.data[denseInDegBase n m + i]?).map Fin.val = some 0) ∧
      (∀ j, (j < 5 * n ∨ 6 * n ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m
  let code : Program L16 := zeroDenseInDegPhase.code
  have hSz : code.size = 10 := zeroDenseInDegPhase_size
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have h2nFit : 2 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h4nFit : 4 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h5nFit : 5 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hAdd1 : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  have h1_r6 : (reg t1 r6).val = 2 * n := by
    rw [h1v, add_no_wrap _ _ hAdd1]; change (reg s₀ rN).val + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd2 : (reg t1 r6).val + (reg t1 r6).val < 2 ^ bits := by rw [h1_r6]; omega
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_r6 : (reg t2 r6).val = 4 * n := by
    rw [h2v, add_no_wrap _ _ hAdd2, h1_r6]; omega
  have hAdd3 : (reg t2 r6).val + (reg t2 rN).val < 2 ^ bits := by
    rw [h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_imm16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 4 s_start t4 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.zero t4))))
  have hKeep4 (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7) :
      reg t4 regIdx = reg s_start regIdx := by
    rw [h4o _ hn7, h3o _ hn6, h2o _ hn6, h1o _ hn6]
  have hData4 : t4.data = s₀.data := by rw [h4d, h3d, h2d, h1d]; rfl
  have hConsts4 : ConstRegs n m r.val t4 :=
    ⟨(congrArg Fin.val (hKeep4 rZero (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep4 rOne (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep4 rN (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep4 rM (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep4 rRoot (by decide) (by decide))).trans hConsts.rootVal⟩
  have hInv0 : ZeroDenseInDegInv g r.val qCount s₀.data 0 t4 := by
    refine ⟨by rw [h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts4,
      (congrArg Fin.val (hKeep4 r5 (by decide) (by decide))).trans hqReg, ?_,
      by rw [h4v]; rfl, fun _ hi => False.elim (Nat.not_lt_zero _ hi), fun _ _ => by rw [hData4]⟩
    rw [h4o _ (by decide), h3v, add_no_wrap _ _ hAdd3, h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  let Post (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (reg t r5).val = qCount ∧
    (∀ i, i < qCount → (t.data[denseInDegBase n m + i]?).map Fin.val = some 0) ∧
    (∀ j, (j < 5 * n ∨ 6 * n ≤ j) → t.data[j]? = s₀.data[j]?)
  have hStepCase : ∀ k u, (k ≤ qCount ∧ ZeroDenseInDegInv g r.val qCount s₀.data k u) →
      (∃ t, Post k t ∧ ∃ st, st ≤ 5 * (qCount - k) + 2 ∧ run code input st u = some ⟨t, st⟩) ∨
      (∃ k' u' st, (qCount - k') < (qCount - k) ∧ st + (5 * (qCount - k') + 2) ≤ 5 * (qCount - k) + 2 ∧
        Steps code input st u u' ∧ (k' ≤ qCount ∧ ZeroDenseInDegInv g r.val qCount s₀.data k' u')) := by
    intro k u ⟨hkLe, hu⟩
    by_cases hk : k < qCount
    · right
      have hCmp : ltb (reg u r7) (reg u r5) = true :=
        branchLt_true (by rw [hu.idx, hu.qCountReg]; exact hk)
      have hf4 : code[u.pc]? = some (.branchLt r7 r5 5 9) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 5 }
      have hu1Pc : u1.pc = 5 := rfl
      have hs4 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp]; decide)
      have hAddrFit : (reg u1 r6).val + (reg u1 r7).val < 2 ^ bits := by
        change (reg u r6).val + (reg u r7).val < 2 ^ bits
        rw [hu.base, hu.idx]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs5, h2pc', h2v', h2o', h2d'⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r8 : (reg u2 r8).val = 5 * n + k := by
        rw [h2v', add_no_wrap _ _ hAddrFit]; change (reg u r6).val + (reg u r7).val = _; rw [hu.base, hu.idx]
      have h2Bound : (reg u2 r8).val < u2.data.size := by
        rw [u2.data_size, h2_r8]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u3, hs6, h3pc, h3regs, h3data⟩ := step_storeData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc', hu1Pc]; rfl) (by rw [hSz, h2pc', hu1Pc]; decide) h2Bound
      have h3_r7 : (reg u3 r7).val = k := by
        rw [reg_eq_of_regs_eq h3regs r7, h2o' _ (by decide)]; exact hu.idx
      have h3_one : (reg u3 rOne).val = 1 := by
        rw [reg_eq_of_regs_eq h3regs rOne, h2o' _ (by decide)]; exact hu.consts.one
      have hk1Fit : k + 1 < 2 ^ bits := by
        unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u4, hs7, h4pc', h4v', h4o', h4d'⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc', hu1Pc]; rfl)
        (by rw [hSz, h3pc, h2pc', hu1Pc]; decide)
      let uNext : State L16 := { u4 with pc := 4 }
      have hs8 : step code input u4 = some (.next uNext) :=
        step_goto_at (input := input) (code := code) (by rw [h4pc', h3pc, h2pc', hu1Pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn7 : regIdx ≠ r7) (hn8 : regIdx ≠ r8) :
          reg uNext regIdx = reg u regIdx := by
        change reg u4 regIdx = reg u regIdx
        rw [h4o' _ hn7, reg_eq_of_regs_eq h3regs regIdx, h2o' _ hn8]; rfl
      have hDataNext : uNext.data = u.data.set (5 * n + k) (reg u rZero)
          (by rw [u.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
        change u4.data = _
        rw [h4d', h3data]
        have hZeroEq : reg u2 rZero = reg u rZero := h2o' _ (by decide)
        have h2dEq : u2.data = u.data := h2d'
        simp only [h2_r8, hZeroEq, h2dEq]
      have hInvNext : ZeroDenseInDegInv g r.val qCount s₀.data (k + 1) uNext := by
        refine ⟨rfl, ?_,
          (congrArg Fin.val (hKeepNext r5 (by decide) (by decide))).trans hu.qCountReg,
          (congrArg Fin.val (hKeepNext r6 (by decide) (by decide))).trans hu.base,
          ?_, ?_, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide))).trans hu.consts.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide) (by decide))).trans hu.consts.one,
            (congrArg Fin.val (hKeepNext rN (by decide) (by decide))).trans hu.consts.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide) (by decide))).trans hu.consts.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide))).trans hu.consts.rootVal⟩
        · change (reg u4 r7).val = k + 1
          rw [h4v', add_no_wrap _ _ (by rw [h3_r7, h3_one]; exact hk1Fit), h3_r7, h3_one]
        · intro i hi
          rw [hDataNext]
          by_cases hik : i = k
          · subst i; dsimp only [n]; rw [Array.getElem?_set_self, Option.map_some, hu.consts.zero]
          · rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]; exact hu.zeros i (by omega)
        · intro j hj
          rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
          exact hu.frame j (by dsimp only [n] at *; omega)
      refine ⟨k + 1, uNext, 5, by omega, by omega,
        Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.zero uNext))))),
        by omega, hInvNext⟩
    · left
      have hkEq : k = qCount := by omega
      have hCmp : ltb (reg u r7) (reg u r5) = false :=
        branchLt_false (by rw [hu.idx, hu.qCountReg, hkEq]; exact Nat.le_refl _)
      have hf4 : code[u.pc]? = some (.branchLt r7 r5 5 9) := by rw [hu.pc]; rfl
      let t : State L16 := { u with pc := 9 }
      have hs4 : step code input u = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf4 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 u = some ⟨t, 2⟩ :=
        (Steps.cons hs4 (Steps.zero t)).halts hHalt
      refine ⟨t, ⟨⟨hu.consts.zero, hu.consts.one, hu.consts.nVal, hu.consts.mVal, hu.consts.rootVal⟩,
        hu.qCountReg, ?_, ?_⟩, 2, by omega, hRun2⟩
      · intro i hi; rw [denseInDegBase_eq]; exact hu.zeros i (by omega)
      · intro j hj; exact hu.frame j (by dsimp only [n] at *; rw [hkEq]; omega)
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ qCount ∧ ZeroDenseInDegInv g r.val qCount s₀.data k s)
      (fun k => qCount - k) (fun k => 5 * (qCount - k) + 2) Post
      (fun k u h => hStepCase k u h) qCount 0 t4 (Nat.le_refl _) ⟨Nat.zero_le _, hInv0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hq, hz, hf⟩
  exact ⟨tEnd, 4 + loopSteps, by omega, hExec, hc, hq, hz, hf⟩

end Phase4ZeroDenseInDeg

/-! ### Phase 4B: Count `denseInDeg[0..qCount-1]` over reachable outgoing arcs -/

section Phase4CountDenseInDeg

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def countDenseInDegCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.add r6 rN rN,
    .add r6 r6 rN,
    .add r7 r6 rN,
    .add r8 r7 rN,
    .imm r9 ⟨4, by omega⟩,
    .add r9 r9 rN,
    .imm r10 0,
    .branchLt r10 r5 8 29,
    .add r13 r7 r10,
    .loadData r13 r13,
    .imm r14 ⟨3, by omega⟩,
    .add r14 r14 r13,
    .loadInput r11 r14,
    .add r14 r14 rOne,
    .loadInput r12 r14,
    .branchLt r11 r12 16 27,
    .add r13 r9 r11,
    .loadInput r13 r13,
    .add r13 r6 r13,
    .loadData r13 r13,
    .sub r13 r13 rOne,
    .add r13 r8 r13,
    .loadData r14 r13,
    .add r14 r14 rOne,
    .storeData r13 r14,
    .add r11 r11 rOne,
    .goto 15,
    .add r10 r10 rOne,
    .goto 7,
    .halt]

def countDenseInDegPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (countDenseInDegCode h5) 29 rfl rfl rfl

private theorem countDenseInDegPhase_size (h5 : 5 ≤ 2 ^ bits) :
    (countDenseInDegPhase (hi := hi) (hw := hw) h5).code.size = 30 := rfl

private structure CountDenseInDegOuterInv (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 7
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  qCount : (reg s r5).val = dense.length
  origBase : (reg s r6).val = 3 * g.vertexCount
  denseBase : (reg s r7).val = 4 * g.vertexCount
  denseInBase : (reg s r8).val = 5 * g.vertexCount
  tgtBase : (reg s r9).val = 4 + g.vertexCount
  uDense : (reg s r10).val = k
  counts : ∀ i : Nat, (hi_1 : i < dense.length) →
    (s.data[5 * g.vertexCount + i]?).map Fin.val =
      some (((dense.take k).map (fun u => countOccurrence (dense[i]'hi_1) (g.outArcs u))).sum)
  frame : ∀ j, (j < 5 * g.vertexCount ∨ 6 * g.vertexCount ≤ j) → s.data[j]? = origData[j]?

private structure CountDenseInDegInnerInv (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k j : Nat) (hk : k < dense.length) (s : State L16) : Prop where
  pc : s.pc = 15
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  qCount : (reg s r5).val = dense.length
  origBase : (reg s r6).val = 3 * g.vertexCount
  denseBase : (reg s r7).val = 4 * g.vertexCount
  denseInBase : (reg s r8).val = 5 * g.vertexCount
  tgtBase : (reg s r9).val = 4 + g.vertexCount
  uDense : (reg s r10).val = k
  hjLe : j ≤ (g.outArcs (dense[k]'hk)).length
  edgeIdx : (reg s r11).val = outPrefix g (dense[k]'hk).val + j
  edgeEnd : (reg s r12).val = outPrefix g (dense[k]'hk).val + (g.outArcs (dense[k]'hk)).length
  counts : ∀ i : Nat, (hi_1 : i < dense.length) →
    (s.data[5 * g.vertexCount + i]?).map Fin.val =
      some (((dense.take k).map (fun u => countOccurrence (dense[i]'hi_1) (g.outArcs u))).sum +
        countOccurrence (dense[i]'hi_1) ((g.outArcs (dense[k]'hk)).take j))
  frame : ∀ idx, (idx < 5 * g.vertexCount ∨ 6 * g.vertexCount ≤ idx) → s.data[idx]? = origData[idx]?

theorem run_countDenseInDegPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (dense : List (Fin g.vertexCount)) (hdNd : dense.Nodup)
    (hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense)
    (hqReg : (reg s₀ r5).val = dense.length)
    (hDenseToOrig : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val = some (dense[i]'hi_1).val)
    (hOrigToDense : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1))
    (hZeroIn : ∀ i : Nat, i < dense.length →
      (s₀.data[denseInDegBase g.vertexCount g.arcCount + i]?).map Fin.val = some 0) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 11 * n + 12 * m + 9 ∧
      run (countDenseInDegPhase h5).code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = dense.length ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (t.data[denseInDegBase n m + i]?).map Fin.val = some (denseInDegCount g dense (dense[i]'hi_1))) ∧
      (∀ j, (j < 5 * n ∨ 6 * n ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (countDenseInDegPhase h5).code
  have hSz : code.size = 30 := countDenseInDegPhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have hdLenLe : dense.length ≤ n := nodup_length_le_fin dense hdNd
  have h2nFit : 2 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h3nFit : 3 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h4nFit : 4 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h5nFit : 5 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hTgtFit : 4 + n < 2 ^ bits := by have := Fin.pos r; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hAdd1 : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  have h1_r6 : (reg t1 r6).val = 2 * n := by
    rw [h1v, add_no_wrap _ _ hAdd1]; change (reg s₀ rN).val + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd2 : (reg t1 r6).val + (reg t1 rN).val < 2 ^ bits := by
    rw [h1_r6, h1o _ (by decide)]; change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_r6 : (reg t2 r6).val = 3 * n := by
    rw [h2v, add_no_wrap _ _ hAdd2, h1_r6, h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd3 : (reg t2 r6).val + (reg t2 rN).val < 2 ^ bits := by
    rw [h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  have h3_r7 : (reg t3 r7).val = 4 * n := by
    rw [h3v, add_no_wrap _ _ hAdd3, h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd4 : (reg t3 r7).val + (reg t3 rN).val < 2 ^ bits := by
    rw [h3_r7, h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t5, hs4, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hAdd5 : (reg t5 r9).val + (reg t5 rN).val < 2 ^ bits := by
    rw [h5v, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change 4 + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; exact hTgtFit
  obtain ⟨t6, hs5, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
    (s := t5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t7, hs6, h7pc, h7v, h7o, h7d⟩ := step_imm16 (input := input)
    (s := t6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 7 s_start t7 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.zero t7)))))))
  have hKeep7 (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7)
      (hn8 : regIdx ≠ r8) (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10) :
      reg t7 regIdx = reg s_start regIdx := by
    rw [h7o _ hn10, h6o _ hn9, h5o _ hn9, h4o _ hn8, h3o _ hn7, h2o _ hn6, h1o _ hn6]
  have hData7 : t7.data = s₀.data := by rw [h7d, h6d, h5d, h4d, h3d, h2d, h1d]; rfl
  have hConsts7 : ConstRegs n m r.val t7 :=
    ⟨(congrArg Fin.val (hKeep7 rZero (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep7 rOne (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep7 rN (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep7 rM (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep7 rRoot (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hOut0 : CountDenseInDegOuterInv g r dense s₀.data 0 t7 := by
    refine ⟨by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts7,
      (congrArg Fin.val (hKeep7 r5 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hqReg,
      ?_, ?_, ?_, ?_, by rw [h7v]; rfl, ?_, fun _ _ => by rw [hData7]⟩
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide)]
      exact h2_r6
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]
      exact h3_r7
    · rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4v, add_no_wrap _ _ hAdd4, h3_r7,
        h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
      change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
    · rw [h7o _ (by decide), h6v, add_no_wrap _ _ hAdd5, h5v, h5o _ (by decide), h4o _ (by decide),
        h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
      change 4 + (reg s₀ rN).val = _; rw [hConsts.nVal]
    · intro i hi
      rw [hData7]; simpa [denseInDegBase_eq] using hZeroIn i hi
  -- Inner loop runner
  have run_inner : ∀ (k : Nat) (hk : k < dense.length) (st0 : State L16),
      CountDenseInDegInnerInv g r dense s₀.data k 0 hk st0 →
      ∃ stEnd innerSteps,
        innerSteps ≤ 12 * (g.outArcs (dense[k]'hk)).length + 1 ∧
        Steps code input innerSteps st0 stEnd ∧
        stEnd.pc = 27 ∧
        ConstRegs n m r.val stEnd ∧
        (reg stEnd r5).val = dense.length ∧
        (reg stEnd r6).val = 3 * n ∧
        (reg stEnd r7).val = 4 * n ∧
        (reg stEnd r8).val = 5 * n ∧
        (reg stEnd r9).val = 4 + n ∧
        (reg stEnd r10).val = k ∧
        (∀ i : Nat, (hi_1 : i < dense.length) →
          (stEnd.data[5 * n + i]?).map Fin.val =
            some (((dense.take (k + 1)).map (fun u => countOccurrence (dense[i]'hi_1) (g.outArcs u))).sum)) ∧
        (∀ idx, (idx < 5 * n ∨ 6 * n ≤ idx) → stEnd.data[idx]? = s₀.data[idx]?) := by
    intro k hk st0 hIn0
    let u := dense[k]'hk
    let InnerPost (st : State L16) : Prop :=
      st.pc = 27 ∧ ConstRegs n m r.val st ∧
      (reg st r5).val = dense.length ∧ (reg st r6).val = 3 * n ∧
      (reg st r7).val = 4 * n ∧ (reg st r8).val = 5 * n ∧
      (reg st r9).val = 4 + n ∧ (reg st r10).val = k ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (st.data[5 * n + i]?).map Fin.val =
          some (((dense.take (k + 1)).map (fun u => countOccurrence (dense[i]'hi_1) (g.outArcs u))).sum)) ∧
      (∀ idx, (idx < 5 * n ∨ 6 * n ≤ idx) → st.data[idx]? = s₀.data[idx]?)
    have hInAux : ∀ (rem j : Nat) (st : State L16),
        (g.outArcs u).length - j ≤ rem →
        CountDenseInDegInnerInv g r dense s₀.data k j hk st →
        ∃ stEnd steps, steps ≤ 12 * ((g.outArcs u).length - j) + 1 ∧
          Steps code input steps st stEnd ∧ InnerPost stEnd := by
      intro rem
      induction rem with
      | zero =>
        intro j st hRem hIn
        have hjEq : j = (g.outArcs (dense[k]'hk)).length := by
          have := hIn.hjLe; dsimp only [u] at *; omega
        have hCmp : ltb (reg st r11) (reg st r12) = false :=
          branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
        have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 27) := by rw [hIn.pc]; rfl
        let stEnd : State L16 := { st with pc := 27 }
        have hs15 : step code input st = some (.next stEnd) := by
          simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
            step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
        have htakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
        refine ⟨stEnd, 1, by omega, Steps.cons hs15 (Steps.zero stEnd),
          rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
          hIn.qCount, hIn.origBase, hIn.denseBase, hIn.denseInBase, hIn.tgtBase, hIn.uDense, ?_, hIn.frame⟩
        intro i hi
        have hc := hIn.counts i hi
        rw [hjEq, List.take_length] at hc
        rw [htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        exact hc
      | succ rem ih =>
        intro j st hRem hIn
        by_cases hj : j < (g.outArcs u).length
        · have hCmp : ltb (reg st r11) (reg st r12) = true :=
            branchLt_true (by rw [hIn.edgeIdx, hIn.edgeEnd]; dsimp only [u] at hj; omega)
          have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 27) := by rw [hIn.pc]; rfl
          let u1 : State L16 := { st with pc := 16 }
          have hu1Pc : u1.pc = 16 := rfl
          have hs15 : step code input st = some (.next u1) := by
            simpa only [u1, hCmp, ite_true] using
              step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
          have hEdgeBound : 4 + n + (outPrefix g u.val + j) < 2 ^ bits := by
            have h1 : outPrefix g u.val + j < outPrefix g (u.val + 1) := by
              rw [outPrefix_succ_lt g u]; omega
            have h2 : outPrefix g u.val + j < g.arcCount := by
              rw [← outPrefix_vertexCount g]
              exact Nat.lt_of_lt_of_le h1 (outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount))
            have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
          have hAddrWordFit : (reg u1 r9).val + (reg u1 r11).val < 2 ^ bits := by
            change (reg st r9).val + (reg st r11).val < 2 ^ bits
            rw [hIn.tgtBase, hIn.edgeIdx]; exact hEdgeBound
          obtain ⟨u2, hs16, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
            (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
          have h2_r13 : (reg u2 r13).val = 4 + n + (outPrefix g u.val + j) := by
            rw [h2v, add_no_wrap _ _ hAddrWordFit]
            change (reg st r9).val + (reg st r11).val = _; rw [hIn.tgtBase, hIn.edgeIdx]
          let v : Fin n := (g.outArcs u)[j]'hj
          have hvTarget := raw.out_targets u j hj
          have hvFit : v.val < 2 ^ bits := by
            have := raw.cap_ge; unfold rawDagInputCap at this; have := v.isLt; dsimp only [n] at *; omega
          have hvInput : input.words[(reg u2 r13).val]? = some ⟨v.val, hvFit⟩ := by
            rw [h2_r13, ← Nat.add_assoc]; dsimp only [n]
            cases hcell : input.words[4 + g.vertexCount + outPrefix g u.val + j]? with
            | none => simp [hcell] at hvTarget
            | some w => rw [hcell, Option.map_some] at hvTarget; exact congrArg some (Fin.ext (Option.some.inj hvTarget))
          obtain ⟨u3, hs17, h3pc, h3v, h3o, h3d⟩ := step_loadInput16 (input := input)
            (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) (by rw [hSz, h2pc, hu1Pc]; decide) hvInput
          have h3_r13 : (reg u3 r13).val = v.val := by rw [h3v]
          have hOrigAddrFit : (reg u3 r6).val + (reg u3 r13).val < 2 ^ bits := by
            rw [h3o _ (by decide), h2o _ (by decide)]
            change (reg st r6).val + (reg u3 r13).val < 2 ^ bits
            rw [hIn.origBase, h3_r13]; have := v.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u4, hs18, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
            (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
          have h4_r13 : (reg u4 r13).val = 3 * n + v.val := by
            rw [h4v, add_no_wrap _ _ hOrigAddrFit, h3o _ (by decide), h2o _ (by decide)]
            change (reg st r6).val + _ = _; rw [hIn.origBase, h3_r13]
          have hvDenseMem : v ∈ dense := hdClosed u (List.getElem_mem hk) v (List.getElem_mem hj)
          obtain ⟨vIdx, hvIdxLt, hvIdxEq⟩ := List.mem_iff_getElem.mp hvDenseMem
          have hvIdx1Fit : vIdx + 1 < 2 ^ bits := by
            unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          have hvPlusMem : u4.data[(reg u4 r13).val]? = some ⟨vIdx + 1, hvIdx1Fit⟩ := by
            rw [h4d, h3d, h2d, h4_r13]
            change st.data[3 * g.vertexCount + v.val]? = _
            rw [hIn.frame (3 * g.vertexCount + v.val) (Or.inl (by have := v.isLt; omega))]
            have ho := hOrigToDense vIdx hvIdxLt
            rw [origToDensePlusOneBase_eq, hvIdxEq] at ho
            cases hcell : s₀.data[3 * g.vertexCount + v.val]? with
            | none => simp [hcell] at ho
            | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
          obtain ⟨u5, hs19, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
            (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) hvPlusMem
            (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h5_r13 : (reg u5 r13).val = vIdx + 1 := by rw [h5v]
          have h5_one : (reg u5 rOne).val = 1 := by
            rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          obtain ⟨u6, hs20, h6pc, h6v, h6o, h6d⟩ := step_sub16 (input := input)
            (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h6_r13 : (reg u6 r13).val = vIdx := by
            rw [h6v, sub_exact _ _ (by rw [h5_r13, h5_one]; omega), h5_r13, h5_one]; omega
          have hInDegAddrFit : (reg u6 r8).val + (reg u6 r13).val < 2 ^ bits := by
            rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            change (reg st r8).val + (reg u6 r13).val < 2 ^ bits
            rw [hIn.denseInBase, h6_r13]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u7, hs21, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
            (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h7_r13 : (reg u7 r13).val = 5 * n + vIdx := by
            rw [h7v, add_no_wrap _ _ hInDegAddrFit, h6o _ (by decide), h5o _ (by decide),
              h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            change (reg st r8).val + _ = _; rw [hIn.denseInBase, h6_r13]
          let curCnt := ((dense.take k).map (fun x => countOccurrence v (g.outArcs x))).sum +
            countOccurrence v ((g.outArcs u).take j)
          have hCurLeSum : curCnt ≤ denseInDegCount g dense v := by
            dsimp only [curCnt, denseInDegCount]
            have hTakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
              rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
            have hSub : List.Sublist ((dense.take (k + 1)).map (fun x => countOccurrence v (g.outArcs x)))
                (dense.map (fun x => countOccurrence v (g.outArcs x))) :=
              (List.take_sublist _ _).map _
            have hSumTake : ((dense.take (k + 1)).map (fun x => countOccurrence v (g.outArcs x))).sum ≤
                (dense.map (fun x => countOccurrence v (g.outArcs x))).sum := by
              have sublist_sum_le : ∀ {xs ys : List Nat}, List.Sublist xs ys → xs.sum ≤ ys.sum := by
                intro xs ys h
                induction h with
                | slnil => exact Nat.le_refl _
                | cons _ _ ih => simp only [List.sum_cons]; omega
                | cons_cons _ _ ih => simp only [List.sum_cons]; omega
              exact sublist_sum_le hSub
            rw [hTakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton] at hSumTake
            have hOccTake : countOccurrence v ((g.outArcs u).take j) ≤ countOccurrence v (g.outArcs u) :=
              countOccurrence_sublist_le (List.take_sublist _ _)
            omega
          have hTakeJ1 : (g.outArcs u).take (j + 1) = (g.outArcs u).take j ++ [v] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
          have hIncLeSum : curCnt + 1 ≤ denseInDegCount g dense v := by
            have hTakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
              rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
            have hSub : List.Sublist ((dense.take (k + 1)).map (fun x => countOccurrence v (g.outArcs x)))
                (dense.map (fun x => countOccurrence v (g.outArcs x))) :=
              (List.take_sublist _ _).map _
            have hSumTake : ((dense.take (k + 1)).map (fun x => countOccurrence v (g.outArcs x))).sum ≤
                (dense.map (fun x => countOccurrence v (g.outArcs x))).sum := by
              have sublist_sum_le : ∀ {xs ys : List Nat}, List.Sublist xs ys → xs.sum ≤ ys.sum := by
                intro xs ys h
                induction h with
                | slnil => exact Nat.le_refl _
                | cons _ _ ih => simp only [List.sum_cons]; omega
                | cons_cons _ _ ih => simp only [List.sum_cons]; omega
              exact sublist_sum_le hSub
            rw [hTakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton] at hSumTake
            have hOccTake : countOccurrence v ((g.outArcs u).take (j + 1)) ≤ countOccurrence v (g.outArcs u) :=
              countOccurrence_sublist_le (List.take_sublist _ _)
            have hCountApp : ∀ (as : List (Fin n)), countOccurrence v (as ++ [v]) = countOccurrence v as + 1 := by
              intro as; induction as with | nil => simp [countOccurrence] | cons a as iha => simp [countOccurrence, iha]; split <;> omega
            rw [hTakeJ1, hCountApp] at hOccTake
            dsimp only [curCnt, denseInDegCount]; omega
          have hCurLtBits : curCnt + 1 < 2 ^ bits := by
            have h1 := denseInDegCount_le_denseReachArcCount g dense v
            have h2 := denseReachArcCount_le g dense hdNd
            have := raw.cap_ge; unfold rawDagInputCap at this; omega
          have hCurMem : u7.data[(reg u7 r13).val]? = some ⟨curCnt, by omega⟩ := by
            rw [h7d, h6d, h5d, h4d, h3d, h2d, h7_r13]
            change st.data[5 * g.vertexCount + vIdx]? = _
            have hOld := hIn.counts vIdx hvIdxLt
            rw [hvIdxEq] at hOld
            cases hcell : st.data[5 * g.vertexCount + vIdx]? with
            | none => simp [hcell] at hOld
            | some w => rw [hcell, Option.map_some] at hOld; exact congrArg some (Fin.ext (Option.some.inj hOld))
          obtain ⟨u8, hs22, h8pc, h8v, h8o, h8d⟩ := step_loadData16 (input := input)
            (s := u7) (code := code) (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl) hCurMem
            (by rw [hSz, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h8_r14 : (reg u8 r14).val = curCnt := by rw [h8v]
          have h8_one : (reg u8 rOne).val = 1 := by
            rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
              h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          obtain ⟨u9, hs23, h9pc, h9v, h9o, h9d⟩ := step_add16 (input := input)
            (s := u8) (code := code) (by rw [h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h9_r14 : (reg u9 r14).val = curCnt + 1 := by
            rw [h9v, add_no_wrap _ _ (by rw [h8_r14, h8_one]; exact hCurLtBits), h8_r14, h8_one]
          have h9_r13 : (reg u9 r13).val = 5 * n + vIdx := by
            rw [h9o _ (by decide), h8o _ (by decide)]; exact h7_r13
          have h9Bound : (reg u9 r13).val < u9.data.size := by
            rw [u9.data_size, h9_r13]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u10, hs24, h10pc, h10regs, h10data⟩ := step_storeData16 (input := input)
            (s := u9) (code := code) (by rw [h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) h9Bound
          have h10_r11 : (reg u10 r11).val = outPrefix g u.val + j := by
            rw [reg_eq_of_regs_eq h10regs r11, h9o _ (by decide), h8o _ (by decide), h7o _ (by decide),
              h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.edgeIdx
          have h10_one : (reg u10 rOne).val = 1 := by
            rw [reg_eq_of_regs_eq h10regs rOne, h9o _ (by decide), h8o _ (by decide), h7o _ (by decide),
              h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.consts.one
          have hEdgeNextFit : outPrefix g u.val + j + 1 < 2 ^ bits := by omega
          obtain ⟨u11, hs25, h11pc, h11v, h11o, h11d⟩ := step_add16 (input := input)
            (s := u10) (code := code) (by rw [h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          let uNext : State L16 := { u11 with pc := 15 }
          have hs26 : step code input u11 = some (.next uNext) :=
            step_goto_at (input := input) (code := code)
              (by rw [h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
              (by rw [hSz]; decide)
          have hKeepNext (regIdx : Fin 16) (hn11 : regIdx ≠ r11) (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) :
              reg uNext regIdx = reg st regIdx := by
            change reg u11 regIdx = reg st regIdx
            rw [h11o _ hn11, reg_eq_of_regs_eq h10regs regIdx, h9o _ hn14, h8o _ hn14, h7o _ hn13,
              h6o _ hn13, h5o _ hn13, h4o _ hn13, h3o _ hn13, h2o _ hn13]; rfl
          have hDataNext : uNext.data = st.data.set (5 * n + vIdx) (reg u9 r14)
              (by rw [st.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
            change u11.data = _
            rw [h11d, h10data]
            have h9DataEq : u9.data = st.data := by rw [h9d, h8d, h7d, h6d, h5d, h4d, h3d, h2d]
            simp only [h9_r13, h9DataEq]
          have hInNext : CountDenseInDegInnerInv g r dense s₀.data k (j + 1) hk uNext := by
            refine ⟨rfl, ?_,
              (congrArg Fin.val (hKeepNext r5 (by decide) (by decide) (by decide))).trans hIn.qCount,
              (congrArg Fin.val (hKeepNext r6 (by decide) (by decide) (by decide))).trans hIn.origBase,
              (congrArg Fin.val (hKeepNext r7 (by decide) (by decide) (by decide))).trans hIn.denseBase,
              (congrArg Fin.val (hKeepNext r8 (by decide) (by decide) (by decide))).trans hIn.denseInBase,
              (congrArg Fin.val (hKeepNext r9 (by decide) (by decide) (by decide))).trans hIn.tgtBase,
              (congrArg Fin.val (hKeepNext r10 (by decide) (by decide) (by decide))).trans hIn.uDense,
              hj, ?_,
              (congrArg Fin.val (hKeepNext r12 (by decide) (by decide) (by decide))).trans hIn.edgeEnd,
              ?_, ?_⟩
            · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide))).trans hIn.consts.zero,
                (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide))).trans hIn.consts.one,
                (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide))).trans hIn.consts.nVal,
                (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide))).trans hIn.consts.mVal,
                (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide))).trans hIn.consts.rootVal⟩
            · change (reg u11 r11).val = outPrefix g u.val + (j + 1)
              rw [h11v, add_no_wrap _ _ (by rw [h10_r11, h10_one]; exact hEdgeNextFit), h10_r11, h10_one]; omega
            · intro i hi
              rw [hDataNext, hTakeJ1]
              by_cases hiv : i = vIdx
              · subst i; dsimp only [n] at *; rw [Array.getElem?_set_self, Option.map_some, h9_r14, hvIdxEq]
                have hCountApp : ∀ (as : List (Fin n)), countOccurrence v (as ++ [v]) = countOccurrence v as + 1 := by
                  intro as; induction as with | nil => simp [countOccurrence] | cons a as iha => simp [countOccurrence, iha]; split <;> omega
                rw [hCountApp]
                dsimp only [curCnt, u]
                rw [Nat.add_assoc]
              · rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
                have hNeV : dense[i]'hi ≠ v := by
                  intro heq; rw [← hvIdxEq] at heq; exact hiv (hdNd.eq_of_getElem_eq hi hvIdxLt heq)
                have hCountAppNe : ∀ (as : List (Fin n)), countOccurrence (dense[i]'hi) (as ++ [v]) =
                    countOccurrence (dense[i]'hi) as := by
                  intro as; induction as with
                  | nil => simp [countOccurrence]; exact Ne.symm hNeV
                  | cons a as iha => simp [countOccurrence, iha]
                rw [hCountAppNe]; exact hIn.counts i hi
            · intro idx hidx
              rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at hidx ⊢; omega)]
              exact hIn.frame idx hidx
          have hSteps11 : Steps code input 12 st uNext :=
            Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19
              (Steps.cons hs20 (Steps.cons hs21 (Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24
                (Steps.cons hs25 (Steps.cons hs26 (Steps.zero uNext))))))))))))
          obtain ⟨stEnd, tailSteps, hTailLe, hTailSteps, hPost⟩ := ih (j + 1) uNext (by omega) hInNext
          exact ⟨stEnd, 12 + tailSteps, by omega, hSteps11.append hTailSteps, hPost⟩
        · have hjEq : j = (g.outArcs (dense[k]'hk)).length := by
            have := hIn.hjLe; dsimp only [u] at *; omega
          have hCmp : ltb (reg st r11) (reg st r12) = false :=
            branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
          have hf15 : code[st.pc]? = some (.branchLt r11 r12 16 27) := by rw [hIn.pc]; rfl
          let stEnd : State L16 := { st with pc := 27 }
          have hs15 : step code input st = some (.next stEnd) := by
            simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
              step_branchLt_at (input := input) hf15 (by rw [hSz, hCmp]; decide)
          have htakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
          refine ⟨stEnd, 1, by omega, Steps.cons hs15 (Steps.zero stEnd),
            rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
            hIn.qCount, hIn.origBase, hIn.denseBase, hIn.denseInBase, hIn.tgtBase, hIn.uDense, ?_, hIn.frame⟩
          intro i hi
          have hc := hIn.counts i hi
          rw [hjEq, List.take_length] at hc
          rw [htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
          exact hc
    simpa only [Nat.sub_zero] using hInAux (g.outArcs u).length 0 st0 (Nat.le_refl _) hIn0
  -- Outer loop
  let processedArcs (k : Nat) : Nat := denseReachArcCount g (dense.take k)
  have hProcLe : ∀ k, processedArcs k ≤ m := fun k =>
    denseReachArcCount_le g (dense.take k) (hdNd.sublist (List.take_sublist _ _))
  let OuterMeas (k : Nat) : Nat := dense.length - k
  let OuterBudget (k : Nat) : Nat := 11 * (dense.length - k) + 12 * (m - processedArcs k) + 2
  let OuterPost (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (reg t r5).val = dense.length ∧
    (∀ i : Nat, (hi_1 : i < dense.length) →
      (t.data[denseInDegBase n m + i]?).map Fin.val = some (denseInDegCount g dense (dense[i]'hi_1))) ∧
    (∀ j, (j < 5 * n ∨ 6 * n ≤ j) → t.data[j]? = s₀.data[j]?)
  have hOuterStep : ∀ k st, (k ≤ dense.length ∧ CountDenseInDegOuterInv g r dense s₀.data k st) →
      (∃ t, OuterPost k t ∧ ∃ steps, steps ≤ OuterBudget k ∧ run code input steps st = some ⟨t, steps⟩) ∨
      (∃ k' st' steps, OuterMeas k' < OuterMeas k ∧ steps + OuterBudget k' ≤ OuterBudget k ∧
        Steps code input steps st st' ∧ (k' ≤ dense.length ∧ CountDenseInDegOuterInv g r dense s₀.data k' st')) := by
    intro k st ⟨hkLe, hOut⟩
    by_cases hk : k < dense.length
    · right
      have hCmp : ltb (reg st r10) (reg st r5) = true :=
        branchLt_true (by rw [hOut.uDense, hOut.qCount]; exact hk)
      have hf7 : code[st.pc]? = some (.branchLt r10 r5 8 29) := by rw [hOut.pc]; rfl
      let u1 : State L16 := { st with pc := 8 }
      have hu1Pc : u1.pc = 8 := rfl
      have hs7 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf7 (by rw [hSz, hCmp]; decide)
      have hDenseAddrFit : (reg u1 r7).val + (reg u1 r10).val < 2 ^ bits := by
        change (reg st r7).val + (reg st r10).val < 2 ^ bits
        rw [hOut.denseBase, hOut.uDense]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs8, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r13 : (reg u2 r13).val = 4 * n + k := by
        rw [h2v, add_no_wrap _ _ hDenseAddrFit]; change (reg st r7).val + (reg st r10).val = _
        rw [hOut.denseBase, hOut.uDense]
      let u : Fin n := dense[k]'hk
      have huFit : u.val < 2 ^ bits := by
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      have huData : u2.data[(reg u2 r13).val]? = some ⟨u.val, huFit⟩ := by
        rw [h2d, h2_r13]; change st.data[4 * g.vertexCount + k]? = _
        rw [hOut.frame (4 * g.vertexCount + k) (Or.inl (by omega))]
        have hm := hDenseToOrig k hk; rw [denseToOrigBase_eq] at hm
        cases hcell : s₀.data[4 * g.vertexCount + k]? with
        | none => simp [hcell] at hm
        | some w => rw [hcell, Option.map_some] at hm; exact congrArg some (Fin.ext (Option.some.inj hm))
      obtain ⟨u3, hs9, h3pc, h3v, h3o, h3d⟩ := step_loadData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) huData (by rw [hSz, h2pc, hu1Pc]; decide)
      have h3_r13 : (reg u3 r13).val = u.val := by rw [h3v]
      obtain ⟨u4, hs10, h4pc, h4v, h4o, h4d⟩ := step_imm16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
      have h4_r13 : (reg u4 r13).val = u.val := by rw [h4o _ (by decide)]; exact h3_r13
      have hOffAddrFit : (reg u4 r14).val + (reg u4 r13).val < 2 ^ bits := by
        rw [h4v, h4_r13]; have := raw.cap_ge; unfold rawDagInputCap at this; have := u.isLt; dsimp only [n] at *; omega
      obtain ⟨u5, hs11, h5pc, h5v, h5o, h5d⟩ := step_add16 (input := input)
        (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h5_r14 : (reg u5 r14).val = 3 + u.val := by
        rw [h5v, add_no_wrap _ _ hOffAddrFit, h4v, h4_r13]
      have hOffStartFit : outPrefix g u.val < 2 ^ bits := by
        have := outPrefix_mono g (Nat.le_of_lt u.isLt); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff0 : input.words[(reg u5 r14).val]? = some ⟨outPrefix g u.val, hOffStartFit⟩ := by
        rw [h5_r14]
        have ho := raw.out_off u.val (Nat.le_of_lt u.isLt)
        cases hcell : input.words[3 + u.val]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u6, hs12, h6pc, h6v, h6o, h6d⟩ := step_loadInput16 (input := input)
        (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff0
      have h6_r14 : (reg u6 r14).val = 3 + u.val := by rw [h6o _ (by decide)]; exact h5_r14
      have h6_one : (reg u6 rOne).val = 1 := by
        rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
        exact hOut.consts.one
      have hOffAddr2Fit : (reg u6 r14).val + (reg u6 rOne).val < 2 ^ bits := by
        rw [h6_r14, h6_one]; have := u.isLt; have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      obtain ⟨u7, hs13, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
        (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h7_r14 : (reg u7 r14).val = 3 + (u.val + 1) := by
        rw [h7v, add_no_wrap _ _ hOffAddr2Fit, h6_r14, h6_one]; omega
      have hOffEndFit : outPrefix g (u.val + 1) < 2 ^ bits := by
        have := outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff1 : input.words[(reg u7 r14).val]? = some ⟨outPrefix g (u.val + 1), hOffEndFit⟩ := by
        rw [h7_r14]
        have ho := raw.out_off (u.val + 1) (by omega)
        cases hcell : input.words[3 + (u.val + 1)]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u8, hs14, h8pc, h8v, h8o, h8d⟩ := step_loadInput16 (input := input)
        (s := u7) (code := code) (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff1
      have hKeep8 (regIdx : Fin 16) (hn11 : regIdx ≠ r11) (hn12 : regIdx ≠ r12)
          (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) : reg u8 regIdx = reg st regIdx := by
        rw [h8o _ hn12, h7o _ hn14, h6o _ hn11, h5o _ hn14, h4o _ hn14, h3o _ hn13, h2o _ hn13]; rfl
      have hData8 : u8.data = st.data := by rw [h8d, h7d, h6d, h5d, h4d, h3d, h2d]
      have hIn0 : CountDenseInDegInnerInv g r dense s₀.data k 0 hk u8 := by
        refine ⟨by rw [h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc], ?_,
          (congrArg Fin.val (hKeep8 r5 (by decide) (by decide) (by decide) (by decide))).trans hOut.qCount,
          (congrArg Fin.val (hKeep8 r6 (by decide) (by decide) (by decide) (by decide))).trans hOut.origBase,
          (congrArg Fin.val (hKeep8 r7 (by decide) (by decide) (by decide) (by decide))).trans hOut.denseBase,
          (congrArg Fin.val (hKeep8 r8 (by decide) (by decide) (by decide) (by decide))).trans hOut.denseInBase,
          (congrArg Fin.val (hKeep8 r9 (by decide) (by decide) (by decide) (by decide))).trans hOut.tgtBase,
          (congrArg Fin.val (hKeep8 r10 (by decide) (by decide) (by decide) (by decide))).trans hOut.uDense,
          Nat.zero_le _, by rw [h8o _ (by decide), h7o _ (by decide), h6v, Nat.add_zero],
          (congrArg Fin.val h8v).trans (outPrefix_succ_lt g u), ?_, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeep8 rZero (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.zero,
            (congrArg Fin.val (hKeep8 rOne (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.one,
            (congrArg Fin.val (hKeep8 rN (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.nVal,
            (congrArg Fin.val (hKeep8 rM (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.mVal,
            (congrArg Fin.val (hKeep8 rRoot (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.rootVal⟩
        · intro i hi; rw [hData8, List.take_zero]; simpa [countOccurrence] using hOut.counts i hi
        · intro idx hidx; rw [hData8]; exact hOut.frame idx hidx
      obtain ⟨st27, innerSteps, hInnerLe, hInnerSteps, h27pc, h27c, h27q, h27ob, h27db, h27dib,
        h27tb, h27u, h27cnt, h27frame⟩ := run_inner k hk u8 hIn0
      have hk1Fit : k + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u28, hs27, h28pc, h28v, h28o, h28d⟩ := step_add16 (input := input)
        (s := st27) (code := code) (by rw [h27pc]; rfl) (by rw [hSz, h27pc]; decide)
      let stNext : State L16 := { u28 with pc := 7 }
      have hs28 : step code input u28 = some (.next stNext) :=
        step_goto_at (input := input) (code := code) (by rw [h28pc, h27pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn10 : regIdx ≠ r10) : reg stNext regIdx = reg st27 regIdx :=
        h28o regIdx hn10
      have hOutNext : CountDenseInDegOuterInv g r dense s₀.data (k + 1) stNext := by
        refine ⟨rfl, ?_,
          (congrArg Fin.val (hKeepNext r5 (by decide))).trans h27q,
          (congrArg Fin.val (hKeepNext r6 (by decide))).trans h27ob,
          (congrArg Fin.val (hKeepNext r7 (by decide))).trans h27db,
          (congrArg Fin.val (hKeepNext r8 (by decide))).trans h27dib,
          (congrArg Fin.val (hKeepNext r9 (by decide))).trans h27tb,
          ?_, fun i hi => by change (u28.data[5 * g.vertexCount + i]?).map Fin.val = _; rw [h28d]; exact h27cnt i hi,
          fun idx hidx => by change u28.data[idx]? = _; rw [h28d]; exact h27frame idx hidx⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide))).trans h27c.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide))).trans h27c.one,
            (congrArg Fin.val (hKeepNext rN (by decide))).trans h27c.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide))).trans h27c.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide))).trans h27c.rootVal⟩
        · change (reg u28 r10).val = k + 1
          rw [h28v, add_no_wrap _ _ (by rw [h27u, h27c.one]; exact hk1Fit), h27u, h27c.one]
      have htakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
      have hProcInc : processedArcs (k + 1) = processedArcs k + (g.outArcs u).length := by
        dsimp only [processedArcs, denseReachArcCount]
        rw [htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      have hProcLe1 := hProcLe (k + 1)
      have hPref8 : Steps code input 8 st u8 :=
        Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11
          (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.zero u8))))))))
      have hTail2 : Steps code input 2 st27 stNext :=
        Steps.cons hs27 (Steps.cons hs28 (Steps.zero stNext))
      refine ⟨k + 1, stNext, 8 + innerSteps + 2, by dsimp only [OuterMeas]; omega,
        by dsimp only [OuterBudget, u] at *; omega, (hPref8.append hInnerSteps).append hTail2,
        by omega, hOutNext⟩
    · left
      have hkEq : k = dense.length := by omega
      have hCmp : ltb (reg st r10) (reg st r5) = false :=
        branchLt_false (by rw [hOut.uDense, hOut.qCount, hkEq]; exact Nat.le_refl _)
      have hf7 : code[st.pc]? = some (.branchLt r10 r5 8 29) := by rw [hOut.pc]; rfl
      let t : State L16 := { st with pc := 29 }
      have hs7 : step code input st = some (.next t) := by
        simpa only [t, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf7 (by rw [hSz, hCmp]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at rfl
      have hRun2 : run code input 2 st = some ⟨t, 2⟩ :=
        (Steps.cons hs7 (Steps.zero t)).halts hHalt
      refine ⟨t, ⟨⟨hOut.consts.zero, hOut.consts.one, hOut.consts.nVal, hOut.consts.mVal, hOut.consts.rootVal⟩,
        hOut.qCount, ?_, hOut.frame⟩, 2, by dsimp only [OuterBudget]; omega, hRun2⟩
      intro i hi
      rw [denseInDegBase_eq]
      have hc := hOut.counts i hi
      rw [List.take_of_length_le (by omega)] at hc
      exact hc
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ dense.length ∧ CountDenseInDegOuterInv g r dense s₀.data k s)
      OuterMeas OuterBudget OuterPost hOuterStep dense.length 0 t7
      (by dsimp only [OuterMeas]; omega) ⟨Nat.zero_le _, hOut0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hq, hcnt, hf⟩
  have hZeroArcs : processedArcs 0 = 0 := by simp [processedArcs, denseReachArcCount]
  dsimp only [OuterBudget, OuterMeas] at hLoopLe
  rw [hZeroArcs, Nat.sub_zero, Nat.sub_zero] at hLoopLe
  exact ⟨tEnd, 7 + loopSteps, by omega, hExec, hc, hq, hcnt, hf⟩

end Phase4CountDenseInDeg

/-! ### Phase 4C: Prefix sum `inStart[0..qCount]` -/

section Phase4DenseInStartPrefix

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def denseInStartPrefixCode : Program L16 :=
  #[.add r7 rN rN,
    .add r7 r7 r7,
    .add r7 r7 rN,
    .add r8 r7 rN,
    .imm r6 0,
    .imm r9 0,
    .branchLt r9 r5 7 14,
    .add r10 r8 r9,
    .storeData r10 r6,
    .add r10 r7 r9,
    .loadData r10 r10,
    .add r6 r6 r10,
    .add r9 r9 rOne,
    .goto 6,
    .add r10 r8 r5,
    .storeData r10 r6,
    .halt]

def denseInStartPrefixPhase : Phase L16 :=
  Phase.ofLast denseInStartPrefixCode 16 rfl rfl rfl

private theorem denseInStartPrefixPhase_size :
    (denseInStartPrefixPhase (hi := hi) (hw := hw)).code.size = 17 := rfl

private structure DenseInStartInv (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 6
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  qCount : (reg s r5).val = dense.length
  acc : (reg s r6).val = denseInPrefix g dense k
  denseInBase : (reg s r7).val = 5 * g.vertexCount
  inStartBase : (reg s r8).val = 6 * g.vertexCount
  idx : (reg s r9).val = k
  starts : ∀ i, i < k → (s.data[6 * g.vertexCount + i]?).map Fin.val = some (denseInPrefix g dense i)
  frame : ∀ j, (j < 6 * g.vertexCount ∨ 6 * g.vertexCount + k ≤ j) → s.data[j]? = origData[j]?

theorem run_denseInStartPrefixPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (dense : List (Fin g.vertexCount)) (hdNd : dense.Nodup)
    (hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense)
    (hqReg : (reg s₀ r5).val = dense.length)
    (hCounts : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[denseInDegBase g.vertexCount g.arcCount + i]?).map Fin.val =
        some (denseInDegCount g dense (dense[i]'hi_1))) :
    let n := g.vertexCount
    let m := g.arcCount
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 8 * n + 10 ∧
      run denseInStartPrefixPhase.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = dense.length ∧
      (reg t r6).val = denseReachArcCount g dense ∧
      (∀ i, i ≤ dense.length →
        (t.data[inStartBase n m + i]?).map Fin.val = some (denseInPrefix g dense i)) ∧
      (∀ j, (j < 6 * n ∨ 7 * n + 1 ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m
  let code : Program L16 := denseInStartPrefixPhase.code
  have hSz : code.size = 17 := denseInStartPrefixPhase_size
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have hdLenLe : dense.length ≤ n := nodup_length_le_fin dense hdNd
  have hReachLe : denseReachArcCount g dense ≤ m := denseReachArcCount_le g dense hdNd
  have h2nFit : 2 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h4nFit : 4 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h5nFit : 5 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h6nFit : 6 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hAdd1 : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  have h1_r7 : (reg t1 r7).val = 2 * n := by
    rw [h1v, add_no_wrap _ _ hAdd1]; change (reg s₀ rN).val + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd2 : (reg t1 r7).val + (reg t1 r7).val < 2 ^ bits := by rw [h1_r7]; omega
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_r7 : (reg t2 r7).val = 4 * n := by rw [h2v, add_no_wrap _ _ hAdd2, h1_r7]; omega
  have hAdd3 : (reg t2 r7).val + (reg t2 rN).val < 2 ^ bits := by
    rw [h2_r7, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  have h3_r7 : (reg t3 r7).val = 5 * n := by
    rw [h3v, add_no_wrap _ _ hAdd3, h2_r7, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd4 : (reg t3 r7).val + (reg t3 rN).val < 2 ^ bits := by
    rw [h3_r7, h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t5, hs4, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t6, hs5, h6pc, h6v, h6o, h6d⟩ := step_imm16 (input := input)
    (s := t5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 6 s_start t6 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.zero t6))))))
  have hKeep6 (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7)
      (hn8 : regIdx ≠ r8) (hn9 : regIdx ≠ r9) : reg t6 regIdx = reg s_start regIdx := by
    rw [h6o _ hn9, h5o _ hn6, h4o _ hn8, h3o _ hn7, h2o _ hn7, h1o _ hn7]
  have hData6 : t6.data = s₀.data := by rw [h6d, h5d, h4d, h3d, h2d, h1d]; rfl
  have hConsts6 : ConstRegs n m r.val t6 :=
    ⟨(congrArg Fin.val (hKeep6 rZero (by decide) (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep6 rOne (by decide) (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep6 rN (by decide) (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep6 rM (by decide) (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep6 rRoot (by decide) (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hInv0 : DenseInStartInv g r dense s₀.data 0 t6 := by
    refine ⟨by rw [h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts6,
      (congrArg Fin.val (hKeep6 r5 (by decide) (by decide) (by decide) (by decide))).trans hqReg,
      by rw [h6o _ (by decide), h5v]; rfl,
      by rw [h6o _ (by decide), h5o _ (by decide), h4o _ (by decide)]; exact h3_r7,
      ?_, by rw [h6v]; rfl, fun _ hi => False.elim (Nat.not_lt_zero _ hi), fun _ _ => by rw [hData6]⟩
    rw [h6o _ (by decide), h5o _ (by decide), h4v, add_no_wrap _ _ hAdd4, h3_r7, h3o _ (by decide),
      h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  let Post (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (reg t r5).val = dense.length ∧
    (reg t r6).val = denseReachArcCount g dense ∧
    (∀ i, i ≤ dense.length →
      (t.data[inStartBase n m + i]?).map Fin.val = some (denseInPrefix g dense i)) ∧
    (∀ j, (j < 6 * n ∨ 7 * n + 1 ≤ j) → t.data[j]? = s₀.data[j]?)
  have hStepCase : ∀ k u, (k ≤ dense.length ∧ DenseInStartInv g r dense s₀.data k u) →
      (∃ t, Post k t ∧ ∃ st, st ≤ 8 * (dense.length - k) + 4 ∧ run code input st u = some ⟨t, st⟩) ∨
      (∃ k' u' st, (dense.length - k') < (dense.length - k) ∧
        st + (8 * (dense.length - k') + 4) ≤ 8 * (dense.length - k) + 4 ∧
        Steps code input st u u' ∧ (k' ≤ dense.length ∧ DenseInStartInv g r dense s₀.data k' u')) := by
    intro k u ⟨hkLe, hu⟩
    by_cases hk : k < dense.length
    · right
      have hCmp : ltb (reg u r9) (reg u r5) = true :=
        branchLt_true (by rw [hu.idx, hu.qCount]; exact hk)
      have hf6 : code[u.pc]? = some (.branchLt r9 r5 7 14) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 7 }
      have hu1Pc : u1.pc = 7 := rfl
      have hs6 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf6 (by rw [hSz, hCmp]; decide)
      have hStartAddrFit : (reg u1 r8).val + (reg u1 r9).val < 2 ^ bits := by
        change (reg u r8).val + (reg u r9).val < 2 ^ bits
        rw [hu.inStartBase, hu.idx]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs7, h2pc', h2v', h2o', h2d'⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r10 : (reg u2 r10).val = 6 * n + k := by
        rw [h2v', add_no_wrap _ _ hStartAddrFit]; change (reg u r8).val + (reg u r9).val = _
        rw [hu.inStartBase, hu.idx]
      have h2Bound : (reg u2 r10).val < u2.data.size := by
        rw [u2.data_size, h2_r10]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u3, hs8, h3pc, h3regs, h3data⟩ := step_storeData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc', hu1Pc]; rfl) (by rw [hSz, h2pc', hu1Pc]; decide) h2Bound
      have h3_r7 : (reg u3 r7).val = 5 * n := by
        rw [reg_eq_of_regs_eq h3regs r7, h2o' _ (by decide)]; exact hu.denseInBase
      have h3_r9 : (reg u3 r9).val = k := by
        rw [reg_eq_of_regs_eq h3regs r9, h2o' _ (by decide)]; exact hu.idx
      have hDegAddrFit : (reg u3 r7).val + (reg u3 r9).val < 2 ^ bits := by
        rw [h3_r7, h3_r9]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u4, hs9, h4pc', h4v', h4o', h4d'⟩ := step_add16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc', hu1Pc]; rfl) (by rw [hSz, h3pc, h2pc', hu1Pc]; decide)
      have h4_r10 : (reg u4 r10).val = 5 * n + k := by
        rw [h4v', add_no_wrap _ _ hDegAddrFit, h3_r7, h3_r9]
      let cnt := denseInDegCount g dense (dense[k]'hk)
      have hPrefNextLe : denseInPrefix g dense (k + 1) ≤ m := by
        have h1 := denseInPrefix_mono g dense (by omega : k + 1 ≤ dense.length)
        rw [denseInPrefix_length g dense hdNd hdClosed] at h1
        exact Nat.le_trans h1 hReachLe
      have hCntFit : cnt < 2 ^ bits := by
        have h1 := denseInDegCount_le_denseReachArcCount g dense (dense[k]'hk)
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have hCntMem : u4.data[(reg u4 r10).val]? = some ⟨cnt, hCntFit⟩ := by
        rw [h4d', h3data, h4_r10, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega), h2d']
        change u.data[5 * g.vertexCount + k]? = _
        rw [hu.frame (5 * g.vertexCount + k) (Or.inl (by omega))]
        have hc := hCounts k hk; rw [denseInDegBase_eq] at hc
        cases hcell : s₀.data[5 * g.vertexCount + k]? with
        | none => simp [hcell] at hc
        | some w => rw [hcell, Option.map_some] at hc; exact congrArg some (Fin.ext (Option.some.inj hc))
      obtain ⟨u5, hs10, h5pc, h5v, h5o, h5d⟩ := step_loadData16 (input := input)
        (s := u4) (code := code) (by rw [h4pc', h3pc, h2pc', hu1Pc]; rfl) hCntMem
        (by rw [hSz, h4pc', h3pc, h2pc', hu1Pc]; decide)
      have h5_r6 : (reg u5 r6).val = denseInPrefix g dense k := by
        rw [h5o _ (by decide), h4o' _ (by decide), reg_eq_of_regs_eq h3regs r6, h2o' _ (by decide)]
        exact hu.acc
      have h5_r10 : (reg u5 r10).val = cnt := by rw [h5v]
      have hAccFit : (reg u5 r6).val + (reg u5 r10).val < 2 ^ bits := by
        rw [h5_r6, h5_r10, ← denseInPrefix_succ_lt g dense k hk]
        have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [m] at *; omega
      obtain ⟨u6, hs11, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
        (s := u5) (code := code) (by rw [h5pc, h4pc', h3pc, h2pc', hu1Pc]; rfl)
        (by rw [hSz, h5pc, h4pc', h3pc, h2pc', hu1Pc]; decide)
      have h6_r9 : (reg u6 r9).val = k := by
        rw [h6o _ (by decide), h5o _ (by decide), h4o' _ (by decide)]; exact h3_r9
      have h6_one : (reg u6 rOne).val = 1 := by
        rw [h6o _ (by decide), h5o _ (by decide), h4o' _ (by decide), reg_eq_of_regs_eq h3regs rOne, h2o' _ (by decide)]
        exact hu.consts.one
      have hk1Fit : k + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u7, hs12, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
        (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc', h3pc, h2pc', hu1Pc]; rfl)
        (by rw [hSz, h6pc, h5pc, h4pc', h3pc, h2pc', hu1Pc]; decide)
      let uNext : State L16 := { u7 with pc := 6 }
      have hs13 : step code input u7 = some (.next uNext) :=
        step_goto_at (input := input) (code := code)
          (by rw [h7pc, h6pc, h5pc, h4pc', h3pc, h2pc', hu1Pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10) :
          reg uNext regIdx = reg u regIdx := by
        change reg u7 regIdx = reg u regIdx
        rw [h7o _ hn9, h6o _ hn6, h5o _ hn10, h4o' _ hn10, reg_eq_of_regs_eq h3regs regIdx, h2o' _ hn10]; rfl
      have hDataNext : uNext.data = u.data.set (6 * n + k) (reg u2 r6)
          (by rw [u.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
        change u7.data = _
        rw [h7d, h6d, h5d, h4d', h3data]
        have h2dEq : u2.data = u.data := h2d'
        simp only [h2_r10, h2dEq]
      have h2_r6 : (reg u2 r6).val = denseInPrefix g dense k := by
        rw [h2o' _ (by decide)]; exact hu.acc
      have hInvNext : DenseInStartInv g r dense s₀.data (k + 1) uNext := by
        refine ⟨rfl, ?_,
          (congrArg Fin.val (hKeepNext r5 (by decide) (by decide) (by decide))).trans hu.qCount,
          ?_,
          (congrArg Fin.val (hKeepNext r7 (by decide) (by decide) (by decide))).trans hu.denseInBase,
          (congrArg Fin.val (hKeepNext r8 (by decide) (by decide) (by decide))).trans hu.inStartBase,
          ?_, ?_, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide))).trans hu.consts.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide))).trans hu.consts.one,
            (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide))).trans hu.consts.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide))).trans hu.consts.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide))).trans hu.consts.rootVal⟩
        · change (reg u7 r6).val = _
          rw [h7o _ (by decide), h6v, add_no_wrap _ _ hAccFit, h5_r6, h5_r10, ← denseInPrefix_succ_lt g dense k hk]
        · change (reg u7 r9).val = k + 1
          rw [h7v, add_no_wrap _ _ (by rw [h6_r9, h6_one]; exact hk1Fit), h6_r9, h6_one]
        · intro i hi
          rw [hDataNext]
          by_cases hik : i = k
          · subst i; dsimp only [n]; rw [Array.getElem?_set_self, Option.map_some, h2_r6]
          · rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]; exact hu.starts i (by omega)
        · intro j hj
          rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at hj ⊢; omega)]
          exact hu.frame j (by omega)
      have hSteps8 : Steps code input 8 u uNext :=
        Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
          (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.zero uNext))))))))
      exact ⟨k + 1, uNext, 8, by omega, by omega, hSteps8, by omega, hInvNext⟩
    · left
      have hkEq : k = dense.length := by omega
      have hCmp : ltb (reg u r9) (reg u r5) = false :=
        branchLt_false (by rw [hu.idx, hu.qCount, hkEq]; exact Nat.le_refl _)
      have hf6 : code[u.pc]? = some (.branchLt r9 r5 7 14) := by rw [hu.pc]; rfl
      let u1 : State L16 := { u with pc := 14 }
      have hu1Pc : u1.pc = 14 := rfl
      have hs6 : step code input u = some (.next u1) := by
        simpa only [u1, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf6 (by rw [hSz, hCmp]; decide)
      have hEndAddrFit : (reg u1 r8).val + (reg u1 r5).val < 2 ^ bits := by
        change (reg u r8).val + (reg u r5).val < 2 ^ bits
        rw [hu.inStartBase, hu.qCount]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs14, h2pc', h2v', h2o', h2d'⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r10 : (reg u2 r10).val = 6 * n + dense.length := by
        rw [h2v', add_no_wrap _ _ hEndAddrFit]; change (reg u r8).val + (reg u r5).val = _
        rw [hu.inStartBase, hu.qCount]
      have h2Bound : (reg u2 r10).val < u2.data.size := by
        rw [u2.data_size, h2_r10]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨t, hs15, h3pc, h3regs, h3data⟩ := step_storeData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc', hu1Pc]; rfl) (by rw [hSz, h2pc', hu1Pc]; decide) h2Bound
      have hHalt : step code input t = some (.halted t) :=
        step_halt_at (by rw [h3pc, h2pc', hu1Pc]; rfl)
      have hRun4 : run code input 4 u = some ⟨t, 4⟩ :=
        (Steps.cons hs6 (Steps.cons hs14 (Steps.cons hs15 (Steps.zero t)))).halts hHalt
      have hKeepT (regIdx : Fin 16) (hn10 : regIdx ≠ r10) : reg t regIdx = reg u regIdx := by
        rw [reg_eq_of_regs_eq h3regs regIdx, h2o' _ hn10]; rfl
      have hDataT : t.data = u.data.set (6 * n + dense.length) (reg u r6)
          (by rw [u.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
        rw [h3data]
        have h6Eq : reg u2 r6 = reg u r6 := h2o' _ (by decide)
        have h2dEq : u2.data = u.data := h2d'
        simp only [h2_r10, h6Eq, h2dEq]
      have hAccEnd : (reg u r6).val = denseReachArcCount g dense := by
        rw [hu.acc, hkEq, denseInPrefix_length g dense hdNd hdClosed]
      refine ⟨t, ⟨?_, ?_, ?_, ?_, ?_⟩, 4, by omega, hRun4⟩
      · exact ⟨(congrArg Fin.val (hKeepT rZero (by decide))).trans hu.consts.zero,
          (congrArg Fin.val (hKeepT rOne (by decide))).trans hu.consts.one,
          (congrArg Fin.val (hKeepT rN (by decide))).trans hu.consts.nVal,
          (congrArg Fin.val (hKeepT rM (by decide))).trans hu.consts.mVal,
          (congrArg Fin.val (hKeepT rRoot (by decide))).trans hu.consts.rootVal⟩
      · exact (congrArg Fin.val (hKeepT r5 (by decide))).trans hu.qCount
      · exact (congrArg Fin.val (hKeepT r6 (by decide))).trans hAccEnd
      · intro i hi
        rw [inStartBase_eq, hDataT]
        by_cases hil : i = dense.length
        · subst i; dsimp only [n]; rw [Array.getElem?_set_self, Option.map_some, hu.acc, hkEq]
        · rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]; exact hu.starts i (by omega)
      · intro j hj
        rw [hDataT, Array.getElem?_set_ne _ (by dsimp only [n] at hj ⊢; omega)]
        exact hu.frame j (by dsimp only [n] at hj ⊢; omega)
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ dense.length ∧ DenseInStartInv g r dense s₀.data k s)
      (fun k => dense.length - k) (fun k => 8 * (dense.length - k) + 4) Post
      (fun k u h => hStepCase k u h) dense.length 0 t6 (Nat.le_refl _) ⟨Nat.zero_le _, hInv0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hq, ha, hs, hf⟩
  exact ⟨tEnd, 6 + loopSteps, by omega, hExec, hc, hq, ha, hs, hf⟩

end Phase4DenseInStartPrefix

/-! ### Phase 4D: Scatter reachable dense incoming arcs into `inSrc` -/

section Phase4ScatterDenseInSrc

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def inSrcSlice (data : Array (Word bits)) (n lo hiIdx : Nat) : List Nat :=
  List.ofFn (fun i : Fin (hiIdx - lo) =>
    ((data[7 * n + 1 + lo + i.val]?).map Fin.val).getD 0)

theorem inSrcSlice_length (data : Array (Word bits)) (n lo hiIdx : Nat) :
    (inSrcSlice data n lo hiIdx).length = hiIdx - lo := by
  simp [inSrcSlice]

private theorem inSrcSlice_set_outside (data : Array (Word bits)) (n lo hiIdx idx : Nat)
    (w : Word bits) (hb : idx < data.size) (hout : idx < 7 * n + 1 + lo ∨ 7 * n + 1 + hiIdx ≤ idx) :
    inSrcSlice (data.set idx w hb) n lo hiIdx = inSrcSlice data n lo hiIdx := by
  unfold inSrcSlice
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have hiLt : i < hiIdx - lo := by simpa using h1
    rw [Array.getElem?_set_ne _ (by omega)]

private theorem inSrcSlice_set_cons (data : Array (Word bits)) (n lo hiIdx : Nat)
    (w : Word bits) (hb : 7 * n + 1 + lo < data.size) (hlt : lo < hiIdx) :
    inSrcSlice (data.set (7 * n + 1 + lo) w hb) n lo hiIdx =
      w.val :: inSrcSlice data n (lo + 1) hiIdx := by
  unfold inSrcSlice
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hiLt : i < hiIdx - lo := by simpa using h1
    cases i with
    | zero =>
      rw [List.getElem_ofFn]
      simp [Array.getElem?_set_self]
    | succ i =>
      rw [List.getElem_ofFn, List.getElem_cons_succ, List.getElem_ofFn]
      have hne : 7 * n + 1 + lo ≠ 7 * n + 1 + lo + (i + 1) := by omega
      rw [Array.getElem?_set_ne _ hne]
      have hIdxEq : 7 * n + 1 + (lo + 1) + i = 7 * n + 1 + lo + (i + 1) := by omega
      rw [hIdxEq]

private theorem list_count_cons_nat (a x : Nat) (xs : List Nat) :
    (a :: xs).count x = (if a == x then 1 else 0) + xs.count x := by
  rw [List.count_cons]
  by_cases h : a = x
  · subst h; simp; omega
  · simp [beq_false_of_ne h]

def scatterDenseInSrcCode (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  #[.add r6 rN rN,
    .add r6 r6 rN,
    .add r7 r6 rN,
    .add r7 r7 rN,
    .add r8 r7 rN,
    .add r9 r8 rN,
    .add r9 r9 rOne,
    .imm r10 0,
    .branchLt r10 r5 9 38,
    .add r13 r6 rN,
    .add r13 r13 r10,
    .loadData r13 r13,
    .imm r14 ⟨3, by omega⟩,
    .add r14 r14 r13,
    .loadInput r11 r14,
    .add r14 r14 rOne,
    .loadInput r12 r14,
    .branchLt r11 r12 18 36,
    .imm r13 ⟨4, by omega⟩,
    .add r13 r13 rN,
    .add r13 r13 r11,
    .loadInput r13 r13,
    .add r13 r6 r13,
    .loadData r13 r13,
    .sub r13 r13 rOne,
    .add r14 r7 r13,
    .loadData r15 r14,
    .sub r15 r15 rOne,
    .storeData r14 r15,
    .add r14 r8 r13,
    .loadData r14 r14,
    .add r14 r14 r15,
    .add r14 r9 r14,
    .storeData r14 r10,
    .add r11 r11 rOne,
    .goto 17,
    .add r10 r10 rOne,
    .goto 8,
    .add r13 r8 r5,
    .loadData r6 r13,
    .halt]

def scatterDenseInSrcPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (scatterDenseInSrcCode h5) 40 rfl rfl rfl

private theorem scatterDenseInSrcPhase_size (h5 : 5 ≤ 2 ^ bits) :
    (scatterDenseInSrcPhase (hi := hi) (hw := hw) h5).code.size = 41 := rfl

private def doneDegOuter (g : Digraph) (dense : List (Fin g.vertexCount))
    (k : Nat) (v : Fin g.vertexCount) : Nat :=
  ((dense.take k).map (fun x => countOccurrence v (g.outArcs x))).sum

private def doneDegInner (g : Digraph) (dense : List (Fin g.vertexCount))
    (k j : Nat) (hk : k < dense.length) (v : Fin g.vertexCount) : Nat :=
  doneDegOuter g dense k v + countOccurrence v ((g.outArcs (dense[k]'hk)).take j)

private def doneArcsInner (g : Digraph) (dense : List (Fin g.vertexCount))
    (k j : Nat) (hk : k < dense.length) (uIdx : Nat) (v : Fin g.vertexCount) : Nat :=
  if h : uIdx < k then countOccurrence v (g.outArcs (dense[uIdx]'(Nat.lt_trans h hk)))
  else if uIdx = k then countOccurrence v ((g.outArcs (dense[k]'hk)).take j)
  else 0

private def doneArcsOuter (g : Digraph) (dense : List (Fin g.vertexCount))
    (k uIdx : Nat) (v : Fin g.vertexCount) : Nat :=
  if h : uIdx < min k dense.length then countOccurrence v (g.outArcs (dense[uIdx]'(Nat.lt_of_lt_of_le h (Nat.min_le_right _ _))))
  else 0

private theorem doneDegOuter_le (g : Digraph) (dense : List (Fin g.vertexCount))
    (k : Nat) (v : Fin g.vertexCount) :
    doneDegOuter g dense k v ≤ denseInDegCount g dense v := by
  unfold doneDegOuter denseInDegCount
  have hSub : List.Sublist ((dense.take k).map (fun x => countOccurrence v (g.outArcs x)))
      (dense.map (fun x => countOccurrence v (g.outArcs x))) :=
    (List.take_sublist _ _).map _
  clear hSub
  have sublist_sum_le : ∀ {xs ys : List Nat}, List.Sublist xs ys → xs.sum ≤ ys.sum := by
    intro xs ys h
    induction h with
    | slnil => exact Nat.le_refl _
    | cons _ _ ih => simp only [List.sum_cons]; omega
    | cons_cons _ _ ih => simp only [List.sum_cons]; omega
  exact sublist_sum_le ((List.take_sublist _ _).map _)

private theorem doneDegInner_le (g : Digraph) (dense : List (Fin g.vertexCount))
    (k j : Nat) (hk : k < dense.length) (v : Fin g.vertexCount) :
    doneDegInner g dense k j hk v ≤ denseInDegCount g dense v := by
  unfold doneDegInner doneDegOuter denseInDegCount
  have hTakeK1 : dense.take (k + 1) = dense.take k ++ [dense[k]'hk] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have sublist_sum_le : ∀ {xs ys : List Nat}, List.Sublist xs ys → xs.sum ≤ ys.sum := by
    intro xs ys h
    induction h with
    | slnil => exact Nat.le_refl _
    | cons _ _ ih => simp only [List.sum_cons]; omega
    | cons_cons _ _ ih => simp only [List.sum_cons]; omega
  have hSum := sublist_sum_le ((List.take_sublist (k + 1) dense).map (fun x => countOccurrence v (g.outArcs x)))
  rw [hTakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton] at hSum
  have hOcc := countOccurrence_sublist_le (v := v) (List.take_sublist j (g.outArcs (dense[k]'hk)))
  omega

private structure ScatterOuterInv (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k : Nat) (s : State L16) : Prop where
  pc : s.pc = 8
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  qCount : (reg s r5).val = dense.length
  origBase : (reg s r6).val = 3 * g.vertexCount
  denseInBase : (reg s r7).val = 5 * g.vertexCount
  inStartBase : (reg s r8).val = 6 * g.vertexCount
  inSrcBaseReg : (reg s r9).val = 7 * g.vertexCount + 1
  uDense : (reg s r10).val = k
  remDegs : ∀ i : Nat, (hi_1 : i < dense.length) →
    (s.data[5 * g.vertexCount + i]?).map Fin.val =
      some (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense k (dense[i]'hi_1))
  sliceCounts : ∀ i : Nat, (hi_1 : i < dense.length) → ∀ uIdx : Nat, uIdx < dense.length →
    (inSrcSlice s.data g.vertexCount
      (denseInPrefix g dense i + (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense k (dense[i]'hi_1)))
      (denseInPrefix g dense (i + 1))).count uIdx =
      doneArcsOuter g dense k uIdx (dense[i]'hi_1)
  writtenMem : ∀ i : Nat, (hi_1 : i < dense.length) → ∀ pos : Nat,
    denseInPrefix g dense i + (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense k (dense[i]'hi_1)) ≤ pos →
    pos < denseInPrefix g dense (i + 1) →
    ∃ uIdx : Fin dense.length, (s.data[7 * g.vertexCount + 1 + pos]?).map Fin.val = some uIdx.val
  frame : ∀ idx, (idx < 5 * g.vertexCount ∨ (6 * g.vertexCount ≤ idx ∧ idx < 7 * g.vertexCount + 1) ∨
    7 * g.vertexCount + 1 + denseReachArcCount g dense ≤ idx) → s.data[idx]? = origData[idx]?

private structure ScatterInnerInv (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k j : Nat) (hk : k < dense.length) (s : State L16) : Prop where
  pc : s.pc = 17
  consts : ConstRegs g.vertexCount g.arcCount r.val s
  qCount : (reg s r5).val = dense.length
  origBase : (reg s r6).val = 3 * g.vertexCount
  denseInBase : (reg s r7).val = 5 * g.vertexCount
  inStartBase : (reg s r8).val = 6 * g.vertexCount
  inSrcBaseReg : (reg s r9).val = 7 * g.vertexCount + 1
  uDense : (reg s r10).val = k
  hjLe : j ≤ (g.outArcs (dense[k]'hk)).length
  edgeIdx : (reg s r11).val = outPrefix g (dense[k]'hk).val + j
  edgeEnd : (reg s r12).val = outPrefix g (dense[k]'hk).val + (g.outArcs (dense[k]'hk)).length
  remDegs : ∀ i : Nat, (hi_1 : i < dense.length) →
    (s.data[5 * g.vertexCount + i]?).map Fin.val =
      some (denseInDegCount g dense (dense[i]'hi_1) - doneDegInner g dense k j hk (dense[i]'hi_1))
  sliceCounts : ∀ i : Nat, (hi_1 : i < dense.length) → ∀ uIdx : Nat, uIdx < dense.length →
    (inSrcSlice s.data g.vertexCount
      (denseInPrefix g dense i + (denseInDegCount g dense (dense[i]'hi_1) - doneDegInner g dense k j hk (dense[i]'hi_1)))
      (denseInPrefix g dense (i + 1))).count uIdx =
      doneArcsInner g dense k j hk uIdx (dense[i]'hi_1)
  writtenMem : ∀ i : Nat, (hi_1 : i < dense.length) → ∀ pos : Nat,
    denseInPrefix g dense i + (denseInDegCount g dense (dense[i]'hi_1) - doneDegInner g dense k j hk (dense[i]'hi_1)) ≤ pos →
    pos < denseInPrefix g dense (i + 1) →
    ∃ uIdx : Fin dense.length, (s.data[7 * g.vertexCount + 1 + pos]?).map Fin.val = some uIdx.val
  frame : ∀ idx, (idx < 5 * g.vertexCount ∨ (6 * g.vertexCount ≤ idx ∧ idx < 7 * g.vertexCount + 1) ∨
    7 * g.vertexCount + 1 + denseReachArcCount g dense ≤ idx) → s.data[idx]? = origData[idx]?

private def ScatterInnerPost (g : Digraph) (r : Fin g.vertexCount)
    (dense : List (Fin g.vertexCount)) (origData : Array (Word bits))
    (k : Nat) (st : State L16) : Prop :=
  let n := g.vertexCount
  let m := g.arcCount
  st.pc = 36 ∧ ConstRegs n m r.val st ∧
  (reg st r5).val = dense.length ∧ (reg st r6).val = 3 * n ∧
  (reg st r7).val = 5 * n ∧ (reg st r8).val = 6 * n ∧
  (reg st r9).val = 7 * n + 1 ∧ (reg st r10).val = k ∧
  (∀ i : Nat, (hi_1 : i < dense.length) →
    (st.data[5 * n + i]?).map Fin.val =
      some (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense (k + 1) (dense[i]'hi_1))) ∧
  (∀ i : Nat, (hi_1 : i < dense.length) → ∀ uIdx : Nat, uIdx < dense.length →
    (inSrcSlice st.data n
      (denseInPrefix g dense i +
        (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense (k + 1) (dense[i]'hi_1)))
      (denseInPrefix g dense (i + 1))).count uIdx =
      doneArcsOuter g dense (k + 1) uIdx (dense[i]'hi_1)) ∧
  (∀ i : Nat, (hi_1 : i < dense.length) → ∀ pos : Nat,
    denseInPrefix g dense i +
      (denseInDegCount g dense (dense[i]'hi_1) - doneDegOuter g dense (k + 1) (dense[i]'hi_1)) ≤ pos →
    pos < denseInPrefix g dense (i + 1) →
    ∃ uIdx : Fin dense.length, (st.data[7 * n + 1 + pos]?).map Fin.val = some uIdx.val) ∧
  (∀ idx, (idx < 5 * n ∨ (6 * n ≤ idx ∧ idx < 7 * n + 1) ∨
    7 * n + 1 + denseReachArcCount g dense ≤ idx) → st.data[idx]? = origData[idx]?)

private theorem scatter_inner_exit (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (s₀Data : Array (Word bits))
    (dense : List (Fin g.vertexCount)) (h5 : 5 ≤ 2 ^ bits)
    (k j : Nat) (hk : k < dense.length) (st : State L16)
    (hjEq : j = (g.outArcs (dense[k]'hk)).length)
    (hIn : ScatterInnerInv g r dense s₀Data k j hk st) :
    ∃ stEnd steps, steps ≤ 1 ∧
      Steps (scatterDenseInSrcPhase h5).code input steps st stEnd ∧
      ScatterInnerPost g r dense s₀Data k stEnd := by
  let code : Program L16 := (scatterDenseInSrcPhase h5).code
  have hSz : code.size = 41 := scatterDenseInSrcPhase_size h5
  have hCmp : ltb (reg st r11) (reg st r12) = false :=
    branchLt_false (by rw [hIn.edgeIdx, hIn.edgeEnd, hjEq]; exact Nat.le_refl _)
  have hf17 : code[st.pc]? = some (.branchLt r11 r12 18 36) := by rw [hIn.pc]; rfl
  let stEnd : State L16 := { st with pc := 36 }
  have hs17 : step code input st = some (.next stEnd) := by
    simpa only [stEnd, hCmp, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hf17 (by rw [hSz, hCmp]; decide)
  have htakeK1 : dense.take (k + 1) = dense.take k ++ [dense[k]'hk] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hDoneEq : ∀ v, doneDegInner g dense k j hk v = doneDegOuter g dense (k + 1) v := by
    intro v; unfold doneDegInner doneDegOuter
    rw [hjEq, List.take_length, htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
  have hArcsEq : ∀ uIdx v, uIdx < dense.length →
      doneArcsInner g dense k j hk uIdx v = doneArcsOuter g dense (k + 1) uIdx v := by
    intro uIdx v hu
    unfold doneArcsInner doneArcsOuter
    by_cases huk : uIdx < k
    · have hukMin : uIdx < min (k + 1) dense.length := by omega
      rw [dite_eq_left huk, dite_eq_left hukMin]
    · by_cases hue : uIdx = k
      · subst uIdx
        have hukMin : k < min (k + 1) dense.length := by omega
        rw [dite_eq_right huk, ite_eq_left rfl, dite_eq_left hukMin, hjEq, List.take_length]
      · have hnMin : ¬ uIdx < min (k + 1) dense.length := by omega
        rw [dite_eq_right huk, ite_eq_right hue, dite_eq_right hnMin]
  refine ⟨stEnd, 1, by omega, Steps.cons hs17 (Steps.zero stEnd),
    rfl, ⟨hIn.consts.zero, hIn.consts.one, hIn.consts.nVal, hIn.consts.mVal, hIn.consts.rootVal⟩,
    hIn.qCount, hIn.origBase, hIn.denseInBase, hIn.inStartBase, hIn.inSrcBaseReg, hIn.uDense,
    ?_, ?_, ?_, hIn.frame⟩
  · intro i hi; rw [← hDoneEq]; exact hIn.remDegs i hi
  · intro i hi uIdx hu; rw [← hDoneEq, ← hArcsEq uIdx (dense[i]'hi) hu]; exact hIn.sliceCounts i hi uIdx hu
  · intro i hi pos hge hlt; rw [← hDoneEq] at hge; exact hIn.writtenMem i hi pos hge hlt

private theorem scatter_inner_step (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀Data : Array (Word bits))
    (dense : List (Fin g.vertexCount)) (hdNd : dense.Nodup)
    (hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense)
    (hOrigToDense : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀Data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1))
    (hInStart : ∀ i : Nat, i ≤ dense.length →
      (s₀Data[inStartBase g.vertexCount g.arcCount + i]?).map Fin.val = some (denseInPrefix g dense i))
    (h5 : 5 ≤ 2 ^ bits)
    (k j : Nat) (hk : k < dense.length) (hj : j < (g.outArcs (dense[k]'hk)).length)
    (st : State L16) (hIn : ScatterInnerInv g r dense s₀Data k j hk st) :
    ∃ uNext : State L16,
      Steps (scatterDenseInSrcPhase h5).code input 19 st uNext ∧
      ScatterInnerInv g r dense s₀Data k (j + 1) hk uNext := by
        · let n := g.vertexCount
          let m := g.arcCount
          let code : Program L16 := (scatterDenseInSrcPhase h5).code
          have hSz : code.size = 41 := scatterDenseInSrcPhase_size h5
          have hdLenLe : dense.length ≤ n := nodup_length_le_fin dense hdNd
          have hReachLe : denseReachArcCount g dense ≤ m := denseReachArcCount_le g dense hdNd
          let u := dense[k]'hk
          have hCmp : ltb (reg st r11) (reg st r12) = true :=
            branchLt_true (by rw [hIn.edgeIdx, hIn.edgeEnd]; omega)
          have hf17 : code[st.pc]? = some (.branchLt r11 r12 18 36) := by rw [hIn.pc]; rfl
          let u1 : State L16 := { st with pc := 18 }
          have hu1Pc : u1.pc = 18 := rfl
          have hs17 : step code input st = some (.next u1) := by
            simpa only [u1, hCmp, ite_true] using
              step_branchLt_at (input := input) hf17 (by rw [hSz, hCmp]; decide)
          obtain ⟨u2, hs18, h2pc, h2v, h2o, h2d⟩ := step_imm16 (input := input)
            (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
          have h4nFit' : (reg u2 r13).val + (reg u2 rN).val < 2 ^ bits := by
            rw [h2v, h2o _ (by decide)]; change 4 + (reg st rN).val < 2 ^ bits
            rw [hIn.consts.nVal]; have := Fin.pos r; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u3, hs19, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
            (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) (by rw [hSz, h2pc, hu1Pc]; decide)
          have h3_r13 : (reg u3 r13).val = 4 + n := by
            rw [h3v, add_no_wrap _ _ h4nFit', h2v, h2o _ (by decide)]; change 4 + (reg st rN).val = _; rw [hIn.consts.nVal]
          have hEdgeBound : 4 + n + (outPrefix g u.val + j) < 2 ^ bits := by
            have h1 : outPrefix g u.val + j < outPrefix g (u.val + 1) := by
              rw [outPrefix_succ_lt g u]; dsimp only [u]; omega
            have h2 : outPrefix g u.val + j < g.arcCount := by
              rw [← outPrefix_vertexCount g]
              exact Nat.lt_of_lt_of_le h1 (outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount))
            have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
          have hEdgeAddrFit : (reg u3 r13).val + (reg u3 r11).val < 2 ^ bits := by
            rw [h3_r13, h3o _ (by decide), h2o _ (by decide)]; change _ + (reg st r11).val < 2 ^ bits
            rw [hIn.edgeIdx]; exact hEdgeBound
          obtain ⟨u4, hs20, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
            (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
          have h4_r13 : (reg u4 r13).val = 4 + n + (outPrefix g u.val + j) := by
            rw [h4v, add_no_wrap _ _ hEdgeAddrFit, h3_r13, h3o _ (by decide), h2o _ (by decide)]
            change _ + (reg st r11).val = _; rw [hIn.edgeIdx]
          let v : Fin n := (g.outArcs u)[j]'hj
          have hvTarget := raw.out_targets u j hj
          have hvFit : v.val < 2 ^ bits := by
            have := raw.cap_ge; unfold rawDagInputCap at this; have := v.isLt; dsimp only [n] at *; omega
          have hvInput : input.words[(reg u4 r13).val]? = some ⟨v.val, hvFit⟩ := by
            rw [h4_r13, ← Nat.add_assoc]; dsimp only [n]
            cases hcell : input.words[4 + g.vertexCount + outPrefix g u.val + j]? with
            | none => simp [hcell] at hvTarget
            | some w => rw [hcell, Option.map_some] at hvTarget; exact congrArg some (Fin.ext (Option.some.inj hvTarget))
          obtain ⟨u5, hs21, h5pc, h5v, h5o, h5d⟩ := step_loadInput16 (input := input)
            (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide) hvInput
          have h5_r13 : (reg u5 r13).val = v.val := by rw [h5v]
          have hOrigAddrFit : (reg u5 r6).val + (reg u5 r13).val < 2 ^ bits := by
            rw [h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            change (reg st r6).val + (reg u5 r13).val < 2 ^ bits; rw [hIn.origBase, h5_r13]
            have := v.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u6, hs22, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
            (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h6_r13 : (reg u6 r13).val = 3 * n + v.val := by
            rw [h6v, add_no_wrap _ _ hOrigAddrFit, h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]
            change (reg st r6).val + _ = _; rw [hIn.origBase, h5_r13]
          have hvDenseMem : v ∈ dense := hdClosed u (List.getElem_mem hk) v (List.getElem_mem hj)
          obtain ⟨vIdx, hvIdxLt, hvIdxEq⟩ := List.mem_iff_getElem.mp hvDenseMem
          have hvIdx1Fit : vIdx + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          have hvPlusMem : u6.data[(reg u6 r13).val]? = some ⟨vIdx + 1, hvIdx1Fit⟩ := by
            rw [h6d, h5d, h4d, h3d, h2d, h6_r13]
            change st.data[3 * g.vertexCount + v.val]? = _
            rw [hIn.frame (3 * g.vertexCount + v.val) (Or.inl (by have := v.isLt; omega))]
            have ho := hOrigToDense vIdx hvIdxLt
            rw [origToDensePlusOneBase_eq, hvIdxEq] at ho
            cases hcell : s₀Data[3 * g.vertexCount + v.val]? with
            | none => simp [hcell] at ho
            | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
          obtain ⟨u7, hs23, h7pc, h7v, h7o, h7d⟩ := step_loadData16 (input := input)
            (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl) hvPlusMem
            (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h7_r13 : (reg u7 r13).val = vIdx + 1 := by rw [h7v]
          have h7_one : (reg u7 rOne).val = 1 := by
            rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          obtain ⟨u8, hs24, h8pc, h8v, h8o, h8d⟩ := step_sub16 (input := input)
            (s := u7) (code := code) (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h8_r13 : (reg u8 r13).val = vIdx := by
            rw [h8v, sub_exact _ _ (by rw [h7_r13, h7_one]; omega), h7_r13, h7_one]; omega
          have hDegAddrFit : (reg u8 r7).val + (reg u8 r13).val < 2 ^ bits := by
            rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
              h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            change (reg st r7).val + (reg u8 r13).val < 2 ^ bits; rw [hIn.denseInBase, h8_r13]
            unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u9, hs25, h9pc, h9v, h9o, h9d⟩ := step_add16 (input := input)
            (s := u8) (code := code) (by rw [h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h9_r14 : (reg u9 r14).val = 5 * n + vIdx := by
            rw [h9v, add_no_wrap _ _ hDegAddrFit, h8o _ (by decide), h7o _ (by decide),
              h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            change (reg st r7).val + _ = _; rw [hIn.denseInBase, h8_r13]
          let doneBefore := doneDegInner g dense k j hk v
          let doneAfter := doneDegInner g dense k (j + 1) hk v
          have hTakeJ1 : (g.outArcs u).take (j + 1) = (g.outArcs u).take j ++ [v] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
          have hDoneStep : doneAfter = doneBefore + 1 := by
            dsimp only [doneAfter, doneBefore, doneDegInner, u]
            rw [hTakeJ1]
            have hCountApp : ∀ (as : List (Fin g.vertexCount)),
                countOccurrence v (as ++ [v]) = countOccurrence v as + 1 := by
              intro as; induction as with | nil => simp [countOccurrence] | cons a as iha => simp [countOccurrence, iha]; split <;> omega
            rw [hCountApp ((g.outArcs (dense[k]'hk)).take j)]; omega
          have hDoneAfterLe : doneAfter ≤ denseInDegCount g dense v := doneDegInner_le g dense k (j + 1) hk v
          let remBefore := denseInDegCount g dense v - doneBefore
          let remAfter := denseInDegCount g dense v - doneAfter
          have hRemPos : 1 ≤ remBefore := by omega
          have hRemRel : remBefore = remAfter + 1 := by omega
          have hRemFit : remBefore < 2 ^ bits := by
            have h1 := denseInDegCount_le_denseReachArcCount g dense v
            have := raw.cap_ge; unfold rawDagInputCap at this; omega
          have hRemMem : u9.data[(reg u9 r14).val]? = some ⟨remBefore, hRemFit⟩ := by
            rw [h9d, h8d, h7d, h6d, h5d, h4d, h3d, h2d, h9_r14]
            change st.data[5 * g.vertexCount + vIdx]? = _
            have hr := hIn.remDegs vIdx hvIdxLt
            rw [hvIdxEq] at hr
            cases hcell : st.data[5 * g.vertexCount + vIdx]? with
            | none => simp [hcell] at hr
            | some w => rw [hcell, Option.map_some] at hr; exact congrArg some (Fin.ext (Option.some.inj hr))
          obtain ⟨u10, hs26, h10pc, h10v, h10o, h10d⟩ := step_loadData16 (input := input)
            (s := u9) (code := code) (by rw [h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            hRemMem (by rw [hSz, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h10_r15 : (reg u10 r15).val = remBefore := by rw [h10v]
          have h10_one : (reg u10 rOne).val = 1 := by
            rw [h10o _ (by decide), h9o _ (by decide), h8o _ (by decide), h7o _ (by decide),
              h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.consts.one
          obtain ⟨u11, hs27, h11pc, h11v, h11o, h11d⟩ := step_sub16 (input := input)
            (s := u10) (code := code) (by rw [h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h11_r15 : (reg u11 r15).val = remAfter := by
            rw [h11v, sub_exact _ _ (by rw [h10_r15, h10_one]; exact hRemPos), h10_r15, h10_one]; omega
          have h11_r14 : (reg u11 r14).val = 5 * n + vIdx := by
            rw [h11o _ (by decide), h10o _ (by decide)]; exact h9_r14
          have h11Bound : (reg u11 r14).val < u11.data.size := by
            rw [u11.data_size, h11_r14]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u12, hs28, h12pc, h12regs, h12data⟩ := step_storeData16 (input := input)
            (s := u11) (code := code) (by rw [h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) h11Bound
          have h12_r8 : (reg u12 r8).val = 6 * n := by
            rw [reg_eq_of_regs_eq h12regs r8, h11o _ (by decide), h10o _ (by decide), h9o _ (by decide),
              h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.inStartBase
          have h12_r13 : (reg u12 r13).val = vIdx := by
            rw [reg_eq_of_regs_eq h12regs r13, h11o _ (by decide), h10o _ (by decide), h9o _ (by decide)]; exact h8_r13
          have hStartAddrFit : (reg u12 r8).val + (reg u12 r13).val < 2 ^ bits := by
            rw [h12_r8, h12_r13]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u13, hs29, h13pc, h13v, h13o, h13d⟩ := step_add16 (input := input)
            (s := u12) (code := code) (by rw [h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h13_r14 : (reg u13 r14).val = 6 * n + vIdx := by
            rw [h13v, add_no_wrap _ _ hStartAddrFit, h12_r8, h12_r13]
          have hStartFit : denseInPrefix g dense vIdx < 2 ^ bits := by
            have h1 := denseInPrefix_mono g dense (by omega : vIdx ≤ dense.length)
            rw [denseInPrefix_length g dense hdNd hdClosed] at h1
            have := raw.cap_ge; unfold rawDagInputCap at this; omega
          have hStartMem : u13.data[(reg u13 r14).val]? = some ⟨denseInPrefix g dense vIdx, hStartFit⟩ := by
            rw [h13d, h12data, h13_r14, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega),
              h11d, h10d, h9d, h8d, h7d, h6d, h5d, h4d, h3d, h2d]
            change st.data[6 * g.vertexCount + vIdx]? = _
            rw [hIn.frame (6 * g.vertexCount + vIdx) (Or.inr (Or.inl (by omega)))]
            have hs := hInStart vIdx (by omega); rw [inStartBase_eq] at hs
            cases hcell : s₀Data[6 * g.vertexCount + vIdx]? with
            | none => simp [hcell] at hs
            | some w => rw [hcell, Option.map_some] at hs; exact congrArg some (Fin.ext (Option.some.inj hs))
          obtain ⟨u14, hs30, h14pc, h14v, h14o, h14d⟩ := step_loadData16 (input := input)
            (s := u13) (code := code) (by rw [h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            hStartMem (by rw [hSz, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h14_r14 : (reg u14 r14).val = denseInPrefix g dense vIdx := by rw [h14v]
          have h14_r15 : (reg u14 r15).val = remAfter := by
            rw [h14o _ (by decide), h13o _ (by decide), reg_eq_of_regs_eq h12regs r15]; exact h11_r15
          have hPosLtReach : denseInPrefix g dense vIdx + remAfter < denseReachArcCount g dense := by
            have h1 : denseInPrefix g dense vIdx + remAfter < denseInPrefix g dense (vIdx + 1) := by
              rw [denseInPrefix_succ_lt g dense vIdx hvIdxLt, hvIdxEq]; omega
            have h2 := Nat.lt_of_lt_of_le h1 (denseInPrefix_mono g dense (by omega : vIdx + 1 ≤ dense.length))
            rw [denseInPrefix_length g dense hdNd hdClosed] at h2; exact h2
          have hOffPosFit : (reg u14 r14).val + (reg u14 r15).val < 2 ^ bits := by
            rw [h14_r14, h14_r15]; have := raw.cap_ge; unfold rawDagInputCap at this; omega
          obtain ⟨u15, hs31, h15pc, h15v, h15o, h15d⟩ := step_add16 (input := input)
            (s := u14) (code := code)
            (by rw [h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h15_r14 : (reg u15 r14).val = denseInPrefix g dense vIdx + remAfter := by
            rw [h15v, add_no_wrap _ _ hOffPosFit, h14_r14, h14_r15]
          have h15_r9 : (reg u15 r9).val = 7 * n + 1 := by
            rw [h15o _ (by decide), h14o _ (by decide), h13o _ (by decide), reg_eq_of_regs_eq h12regs r9,
              h11o _ (by decide), h10o _ (by decide), h9o _ (by decide), h8o _ (by decide), h7o _ (by decide),
              h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]
            exact hIn.inSrcBaseReg
          have hSrcAddrFit : (reg u15 r9).val + (reg u15 r14).val < 2 ^ bits := by
            rw [h15_r9, h15_r14]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u16, hs32, h16pc, h16v, h16o, h16d⟩ := step_add16 (input := input)
            (s := u15) (code := code)
            (by rw [h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          have h16_r14 : (reg u16 r14).val = 7 * n + 1 + (denseInPrefix g dense vIdx + remAfter) := by
            rw [h16v, add_no_wrap _ _ hSrcAddrFit, h15_r9, h15_r14]
          have h16Bound : (reg u16 r14).val < u16.data.size := by
            rw [u16.data_size, h16_r14]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
          obtain ⟨u17, hs33, h17pc, h17regs, h17data⟩ := step_storeData16 (input := input)
            (s := u16) (code := code)
            (by rw [h16pc, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h16pc, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
            h16Bound
          have h17_r11 : (reg u17 r11).val = outPrefix g u.val + j := by
            rw [reg_eq_of_regs_eq h17regs r11, h16o _ (by decide), h15o _ (by decide), h14o _ (by decide),
              h13o _ (by decide), reg_eq_of_regs_eq h12regs r11, h11o _ (by decide), h10o _ (by decide),
              h9o _ (by decide), h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
              h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.edgeIdx
          have h17_one : (reg u17 rOne).val = 1 := by
            rw [reg_eq_of_regs_eq h17regs rOne, h16o _ (by decide), h15o _ (by decide), h14o _ (by decide),
              h13o _ (by decide), reg_eq_of_regs_eq h12regs rOne, h11o _ (by decide), h10o _ (by decide),
              h9o _ (by decide), h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide),
              h4o _ (by decide), h3o _ (by decide), h2o _ (by decide)]; exact hIn.consts.one
          have hEdgeNextFit : outPrefix g u.val + j + 1 < 2 ^ bits := by omega
          obtain ⟨u18, hs34, h18pc, h18v, h18o, h18d⟩ := step_add16 (input := input)
            (s := u17) (code := code)
            (by rw [h17pc, h16pc, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
            (by rw [hSz, h17pc, h16pc, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
          let uNext : State L16 := { u18 with pc := 17 }
          have hs35 : step code input u18 = some (.next uNext) :=
            step_goto_at (input := input) (code := code)
              (by rw [h18pc, h17pc, h16pc, h15pc, h14pc, h13pc, h12pc, h11pc, h10pc, h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
              (by rw [hSz]; decide)
          have hKeepNext (regIdx : Fin 16) (hn11 : regIdx ≠ r11) (hn13 : regIdx ≠ r13)
              (hn14 : regIdx ≠ r14) (hn15 : regIdx ≠ r15) : reg uNext regIdx = reg st regIdx := by
            change reg u18 regIdx = reg st regIdx
            rw [h18o _ hn11, reg_eq_of_regs_eq h17regs regIdx, h16o _ hn14, h15o _ hn14, h14o _ hn14,
              h13o _ hn14, reg_eq_of_regs_eq h12regs regIdx, h11o _ hn15, h10o _ hn15, h9o _ hn14,
              h8o _ hn13, h7o _ hn13, h6o _ hn13, h5o _ hn13, h4o _ hn13, h3o _ hn13, h2o _ hn13]; rfl
          have h16_r10 : (reg u16 r10).val = k := by
            rw [h16o _ (by decide), h15o _ (by decide), h14o _ (by decide), h13o _ (by decide),
              reg_eq_of_regs_eq h12regs r10, h11o _ (by decide), h10o _ (by decide), h9o _ (by decide),
              h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide),
              h3o _ (by decide), h2o _ (by decide)]; exact hIn.uDense
          have hDataMid : u12.data = st.data.set (5 * n + vIdx) (reg u11 r15)
              (by rw [st.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
            rw [h12data]
            have h11DataEq : u11.data = st.data := by rw [h11d, h10d, h9d, h8d, h7d, h6d, h5d, h4d, h3d, h2d]
            simp only [h11_r14, h11DataEq]
          have hDataNext : uNext.data = u12.data.set (7 * n + 1 + (denseInPrefix g dense vIdx + remAfter))
              (reg u16 r10) (by rw [u12.data_size]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega) := by
            change u18.data = _
            rw [h18d, h17data]
            have h16DataEq : u16.data = u12.data := by rw [h16d, h15d, h14d, h13d]
            simp only [h16_r14, h16DataEq]
          have hInNext : ScatterInnerInv g r dense s₀Data k (j + 1) hk uNext := by
            refine ⟨rfl, ?_,
              (congrArg Fin.val (hKeepNext r5 (by decide) (by decide) (by decide) (by decide))).trans hIn.qCount,
              (congrArg Fin.val (hKeepNext r6 (by decide) (by decide) (by decide) (by decide))).trans hIn.origBase,
              (congrArg Fin.val (hKeepNext r7 (by decide) (by decide) (by decide) (by decide))).trans hIn.denseInBase,
              (congrArg Fin.val (hKeepNext r8 (by decide) (by decide) (by decide) (by decide))).trans hIn.inStartBase,
              (congrArg Fin.val (hKeepNext r9 (by decide) (by decide) (by decide) (by decide))).trans hIn.inSrcBaseReg,
              (congrArg Fin.val (hKeepNext r10 (by decide) (by decide) (by decide) (by decide))).trans hIn.uDense,
              hj, ?_,
              (congrArg Fin.val (hKeepNext r12 (by decide) (by decide) (by decide) (by decide))).trans hIn.edgeEnd,
              ?_, ?_, ?_, ?_⟩
            · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.zero,
                (congrArg Fin.val (hKeepNext rOne (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.one,
                (congrArg Fin.val (hKeepNext rN (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.nVal,
                (congrArg Fin.val (hKeepNext rM (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.mVal,
                (congrArg Fin.val (hKeepNext rRoot (by decide) (by decide) (by decide) (by decide))).trans hIn.consts.rootVal⟩
            · change (reg u18 r11).val = outPrefix g u.val + (j + 1)
              rw [h18v, add_no_wrap _ _ (by rw [h17_r11, h17_one]; exact hEdgeNextFit), h17_r11, h17_one]; omega
            · intro i hi
              rw [hDataNext, Array.getElem?_set_ne _ (by dsimp only [n] at *; omega), hDataMid]
              by_cases hiv : i = vIdx
              · subst i; dsimp only [n] at *; rw [Array.getElem?_set_self, Option.map_some, h11_r15, hvIdxEq]
              · rw [Array.getElem?_set_ne _ (by dsimp only [n] at *; omega)]
                have hNeV : dense[i]'hi ≠ v := by
                  intro heq; rw [← hvIdxEq] at heq; exact hiv (hdNd.eq_of_getElem_eq hi hvIdxLt heq)
                have hSameDone : doneDegInner g dense k (j + 1) hk (dense[i]'hi) =
                    doneDegInner g dense k j hk (dense[i]'hi) := by
                  dsimp only [doneDegInner, u]; rw [hTakeJ1]
                  have hCountAppNe : ∀ (as : List (Fin n)), countOccurrence (dense[i]'hi) (as ++ [v]) =
                      countOccurrence (dense[i]'hi) as := by
                    intro as; induction as with
                    | nil => simp [countOccurrence]; exact Ne.symm hNeV
                    | cons a as iha => simp [countOccurrence, iha]
                  rw [hCountAppNe]
                rw [hSameDone]; exact hIn.remDegs i hi
            · intro i hi uIdx hu
              rw [hDataNext]
              by_cases hiv : i = vIdx
              · subst i
                have hDoneEq : doneDegInner g dense k (j + 1) hk (dense[vIdx]'hi) = doneAfter := by
                  rw [hvIdxEq]
                have hDonePrev : doneDegInner g dense k j hk (dense[vIdx]'hi) = doneBefore := by
                  rw [hvIdxEq]
                have hLoLt : denseInPrefix g dense vIdx + remAfter < denseInPrefix g dense (vIdx + 1) := by
                  rw [denseInPrefix_succ_lt g dense vIdx hvIdxLt, hvIdxEq]; omega
                rw [hDoneEq, show denseInDegCount g dense (dense[vIdx]'hi) - doneAfter = remAfter by rw [hvIdxEq]]
                dsimp only [n]
                rw [inSrcSlice_set_cons u12.data g.vertexCount (denseInPrefix g dense vIdx + remAfter)
                    (denseInPrefix g dense (vIdx + 1)) (reg u16 r10) _ hLoLt]
                have hMidSlice : inSrcSlice u12.data g.vertexCount
                    (denseInPrefix g dense vIdx + remAfter + 1) (denseInPrefix g dense (vIdx + 1)) =
                    inSrcSlice st.data g.vertexCount
                      (denseInPrefix g dense vIdx + remAfter + 1) (denseInPrefix g dense (vIdx + 1)) := by
                  rw [hDataMid]
                  exact inSrcSlice_set_outside st.data g.vertexCount _ _ _ _ _ (Or.inl (by dsimp only [n]; omega))
                rw [hMidSlice, list_count_cons_nat, h16_r10, Nat.add_assoc, ← hRemRel]
                have hPrev := hIn.sliceCounts vIdx hi uIdx hu
                rw [hDonePrev, hvIdxEq] at hPrev
                change (inSrcSlice st.data g.vertexCount (denseInPrefix g dense vIdx + remBefore)
                    (denseInPrefix g dense (vIdx + 1))).count uIdx = _ at hPrev
                rw [hPrev, ← hvIdxEq]
                unfold doneArcsInner
                by_cases huk : uIdx < k
                · have hne : (k == uIdx) = false := beq_false_of_ne (by omega)
                  simp [huk, hne]
                · by_cases hue : uIdx = k
                  · subst uIdx
                    simp [huk, hvIdxEq]
                    have hCountApp : ∀ (as : List (Fin g.vertexCount)),
                        countOccurrence v (as ++ [v]) = countOccurrence v as + 1 := by
                      intro as; induction as with | nil => simp [countOccurrence] | cons a as iha => simp [countOccurrence, iha]; split <;> omega
                    dsimp only [u] at hTakeJ1; rw [hTakeJ1, hCountApp ((g.outArcs (dense[k]'hk)).take j)]; omega
                  · have hne : (k == uIdx) = false := beq_false_of_ne (fun h => hue h.symm)
                    simp [huk, hue, hne]
              · have hNeV : dense[i]'hi ≠ v := by
                  intro heq; rw [← hvIdxEq] at heq; exact hiv (hdNd.eq_of_getElem_eq hi hvIdxLt heq)
                have hSameDone : doneDegInner g dense k (j + 1) hk (dense[i]'hi) =
                    doneDegInner g dense k j hk (dense[i]'hi) := by
                  dsimp only [doneDegInner, u]; rw [hTakeJ1]
                  have hCountAppNe : ∀ (as : List (Fin n)), countOccurrence (dense[i]'hi) (as ++ [v]) =
                      countOccurrence (dense[i]'hi) as := by
                    intro as; induction as with
                    | nil => simp [countOccurrence]; exact Ne.symm hNeV
                    | cons a as iha => simp [countOccurrence, iha]
                  rw [hCountAppNe]
                have hSameArcs : doneArcsInner g dense k (j + 1) hk uIdx (dense[i]'hi) =
                    doneArcsInner g dense k j hk uIdx (dense[i]'hi) := by
                  unfold doneArcsInner
                  by_cases huk : uIdx < k
                  · simp [huk]
                  · by_cases hue : uIdx = k
                    · subst uIdx; dsimp only [u] at hTakeJ1
                      rw [dite_eq_right huk, ite_eq_left rfl, dite_eq_right huk, ite_eq_left rfl, hTakeJ1]
                      have hCountAppNe : ∀ (as : List (Fin g.vertexCount)),
                          countOccurrence (dense[i]'hi) (as ++ [v]) =
                          countOccurrence (dense[i]'hi) as := by
                        intro as; induction as with
                        | nil => simp [countOccurrence]; exact Ne.symm hNeV
                        | cons a as iha => simp [countOccurrence, iha]
                      exact hCountAppNe ((g.outArcs (dense[k]'hk)).take j)
                    · simp [huk, hue]
                have hOutPos : 7 * g.vertexCount + 1 + (denseInPrefix g dense vIdx + remAfter) <
                    7 * g.vertexCount + 1 + (denseInPrefix g dense i +
                      (denseInDegCount g dense (dense[i]'hi) - doneDegInner g dense k j hk (dense[i]'hi))) ∨
                    7 * g.vertexCount + 1 + denseInPrefix g dense (i + 1) ≤
                    7 * g.vertexCount + 1 + (denseInPrefix g dense vIdx + remAfter) := by
                  have hLt : denseInPrefix g dense vIdx + remAfter < denseInPrefix g dense (vIdx + 1) := by
                    rw [denseInPrefix_succ_lt g dense vIdx hvIdxLt, hvIdxEq]; omega
                  by_cases hlt : i < vIdx
                  · right
                    have hMono := denseInPrefix_mono g dense (by omega : i + 1 ≤ vIdx)
                    omega
                  · left
                    have hMono := denseInPrefix_mono g dense (by omega : vIdx + 1 ≤ i)
                    omega
                rw [hSameDone, hSameArcs]
                dsimp only [n]
                rw [inSrcSlice_set_outside _ g.vertexCount _ _ _ _ _ hOutPos, hDataMid,
                  inSrcSlice_set_outside _ g.vertexCount _ _ _ _ _ (Or.inl (by dsimp only [n]; omega))]
                exact hIn.sliceCounts i hi uIdx hu
            · intro i hi pos hge hlt
              rw [hDataNext]
              by_cases hiv : i = vIdx
              · subst i
                have hDoneEq : doneDegInner g dense k (j + 1) hk (dense[vIdx]'hi) = doneAfter := by rw [hvIdxEq]
                rw [hDoneEq] at hge
                by_cases hpos : pos = denseInPrefix g dense vIdx + remAfter
                · subst pos; refine ⟨⟨k, hk⟩, ?_⟩
                  dsimp only [n] at *; rw [Array.getElem?_set_self, Option.map_some, h16_r10]
                · have hNeNext' : 7 * g.vertexCount + 1 + pos ≠ 7 * n + 1 + (denseInPrefix g dense vIdx + remAfter) := by
                    dsimp only [n]
                    intro heq
                    exact hpos (Nat.add_left_cancel heq)
                  have hNeMid' : 7 * g.vertexCount + 1 + pos ≠ 5 * n + vIdx := by
                    have hdLen := nodup_length_le_fin dense hdNd
                    dsimp only [n]
                    exact Nat.ne_of_gt (by omega)
                  rw [Array.getElem?_set_ne _ hNeNext'.symm, hDataMid,
                    Array.getElem?_set_ne _ hNeMid'.symm]
                  have hDonePrev : doneDegInner g dense k j hk (dense[vIdx]'hi) = doneBefore := by rw [hvIdxEq]
                  have hgeBefore : denseInPrefix g dense vIdx + remBefore ≤ pos := by
                    rw [hvIdxEq] at hge
                    change denseInPrefix g dense vIdx + remAfter ≤ pos at hge
                    omega
                  exact hIn.writtenMem vIdx hi pos (by rw [hDonePrev, hvIdxEq]; exact hgeBefore) hlt
              · have hNeV : dense[i]'hi ≠ v := by
                  intro heq; rw [← hvIdxEq] at heq; exact hiv (hdNd.eq_of_getElem_eq hi hvIdxLt heq)
                have hSameDone : doneDegInner g dense k (j + 1) hk (dense[i]'hi) =
                    doneDegInner g dense k j hk (dense[i]'hi) := by
                  dsimp only [doneDegInner, u]; rw [hTakeJ1]
                  have hCountAppNe : ∀ (as : List (Fin n)), countOccurrence (dense[i]'hi) (as ++ [v]) =
                      countOccurrence (dense[i]'hi) as := by
                    intro as; induction as with
                    | nil => simp [countOccurrence]; exact Ne.symm hNeV
                    | cons a as iha => simp [countOccurrence, iha]
                  rw [hCountAppNe]
                rw [hSameDone] at hge
                have hLtV : denseInPrefix g dense vIdx + remAfter < denseInPrefix g dense (vIdx + 1) := by
                  rw [denseInPrefix_succ_lt g dense vIdx hvIdxLt, hvIdxEq]; omega
                have hnePos : pos ≠ denseInPrefix g dense vIdx + remAfter := by
                  have hGeV : denseInPrefix g dense vIdx ≤ denseInPrefix g dense vIdx + remAfter := Nat.le_add_right _ _
                  by_cases hlt' : i < vIdx
                  · have hMono := denseInPrefix_mono g dense (Nat.succ_le_of_lt hlt')
                    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_trans hMono hGeV))
                  · have hiGt : vIdx + 1 ≤ i := by omega
                    have hMono := denseInPrefix_mono g dense hiGt
                    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hLtV (Nat.le_trans hMono (Nat.le_trans (Nat.le_add_right _ _) hge)))
                have hNeNext : 7 * g.vertexCount + 1 + pos ≠ 7 * n + 1 + (denseInPrefix g dense vIdx + remAfter) := by
                  dsimp only [n]
                  intro heq
                  exact hnePos (Nat.add_left_cancel heq)
                have hNeMid : 7 * g.vertexCount + 1 + pos ≠ 5 * n + vIdx := by
                  have hdLen := nodup_length_le_fin dense hdNd
                  dsimp only [n]
                  exact Nat.ne_of_gt (by omega)
                rw [Array.getElem?_set_ne _ hNeNext.symm, hDataMid,
                  Array.getElem?_set_ne _ hNeMid.symm]
                exact hIn.writtenMem i hi pos hge hlt
            · intro idx hidx
              have hLtV : denseInPrefix g dense vIdx + remAfter < denseInPrefix g dense (vIdx + 1) := by
                rw [denseInPrefix_succ_lt g dense vIdx hvIdxLt, hvIdxEq]; omega
              have hLtTotal : denseInPrefix g dense vIdx + remAfter < denseReachArcCount g dense := by
                have hMono := denseInPrefix_mono g dense (Nat.succ_le_of_lt hvIdxLt)
                rw [← denseInPrefix_length g dense hdNd hdClosed]
                exact Nat.lt_of_lt_of_le hLtV hMono
              have hNeNext : idx ≠ 7 * n + 1 + (denseInPrefix g dense vIdx + remAfter) := by
                dsimp only [n]
                rcases hidx with hlo | ⟨_, hmid2⟩ | hhi
                · exact Nat.ne_of_lt (Nat.lt_trans hlo (by omega))
                · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hmid2 (Nat.le_add_right _ _))
                · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hLtTotal _) hhi)
              have hNeMid : idx ≠ 5 * n + vIdx := by
                have hdLen := nodup_length_le_fin dense hdNd
                dsimp only [n]
                rcases hidx with hlo | ⟨hmid1, _⟩ | hhi
                · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hlo (Nat.le_add_right _ _))
                · exact Nat.ne_of_gt (by omega)
                · exact Nat.ne_of_gt (by omega)
              rw [hDataNext, Array.getElem?_set_ne _ hNeNext.symm, hDataMid,
                Array.getElem?_set_ne _ hNeMid.symm]
              exact hIn.frame idx hidx
          have hSteps19 : Steps code input 19 st uNext :=
            Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21
              (Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24 (Steps.cons hs25 (Steps.cons hs26
                (Steps.cons hs27 (Steps.cons hs28 (Steps.cons hs29 (Steps.cons hs30 (Steps.cons hs31
                  (Steps.cons hs32 (Steps.cons hs33 (Steps.cons hs34 (Steps.cons hs35 (Steps.zero uNext)))))))))))))))))))
          exact ⟨uNext, hSteps19, hInNext⟩

private theorem scatter_run_inner (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀Data : Array (Word bits))
    (dense : List (Fin g.vertexCount)) (hdNd : dense.Nodup)
    (hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense)
    (hOrigToDense : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀Data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1))
    (hInStart : ∀ i : Nat, i ≤ dense.length →
      (s₀Data[inStartBase g.vertexCount g.arcCount + i]?).map Fin.val = some (denseInPrefix g dense i))
    (h5 : 5 ≤ 2 ^ bits)
    (k : Nat) (hk : k < dense.length) (st0 : State L16)
    (hIn0 : ScatterInnerInv g r dense s₀Data k 0 hk st0) :
    ∃ stEnd innerSteps,
      innerSteps ≤ 19 * (g.outArcs (dense[k]'hk)).length + 1 ∧
      Steps (scatterDenseInSrcPhase h5).code input innerSteps st0 stEnd ∧
      ScatterInnerPost g r dense s₀Data k stEnd := by
  let u := dense[k]'hk
  have hInAux : ∀ (rem j : Nat) (st : State L16),
      (g.outArcs u).length - j ≤ rem →
      ScatterInnerInv g r dense s₀Data k j hk st →
      ∃ stEnd steps, steps ≤ 19 * ((g.outArcs u).length - j) + 1 ∧
        Steps (scatterDenseInSrcPhase h5).code input steps st stEnd ∧
        ScatterInnerPost g r dense s₀Data k stEnd := by
    intro rem
    induction rem with
    | zero =>
      intro j st hRem hIn
      have hjEq : j = (g.outArcs (dense[k]'hk)).length := by
        have := hIn.hjLe; dsimp only [u] at *; omega
      obtain ⟨stEnd, steps, hLe, hSt, hPost⟩ := scatter_inner_exit input s₀Data dense h5 k j hk st hjEq hIn
      exact ⟨stEnd, steps, by omega, hSt, hPost⟩
    | succ rem ih =>
      intro j st hRem hIn
      by_cases hj : j < (g.outArcs u).length
      · obtain ⟨uNext, hSteps19, hInNext⟩ :=
          scatter_inner_step input raw workRoom s₀Data dense hdNd hdClosed hOrigToDense hInStart h5 k j hk hj st hIn
        obtain ⟨stEnd, tailSteps, hTailLe, hTailSteps, hPost⟩ := ih (j + 1) uNext (by omega) hInNext
        exact ⟨stEnd, 19 + tailSteps, by omega, hSteps19.append hTailSteps, hPost⟩
      · have hjEq : j = (g.outArcs (dense[k]'hk)).length := by
          have := hIn.hjLe; dsimp only [u] at *; omega
        obtain ⟨stEnd, steps, hLe, hSt, hPost⟩ := scatter_inner_exit input s₀Data dense h5 k j hk st hjEq hIn
        exact ⟨stEnd, steps, by omega, hSt, hPost⟩
  simpa only [Nat.sub_zero] using hInAux (g.outArcs u).length 0 st0 (Nat.le_refl _) hIn0

theorem run_scatterDenseInSrcPhase (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16)
    (hConsts : ConstRegs g.vertexCount g.arcCount r.val s₀)
    (dense : List (Fin g.vertexCount)) (hdNd : dense.Nodup)
    (hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense)
    (hqReg : (reg s₀ r5).val = dense.length)
    (hDenseToOrig : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val = some (dense[i]'hi_1).val)
    (hOrigToDense : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1))
    (hDenseIn : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s₀.data[denseInDegBase g.vertexCount g.arcCount + i]?).map Fin.val =
        some (denseInDegCount g dense (dense[i]'hi_1)))
    (hInStart : ∀ i : Nat, i ≤ dense.length →
      (s₀.data[inStartBase g.vertexCount g.arcCount + i]?).map Fin.val = some (denseInPrefix g dense i)) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (steps : Nat),
      steps ≤ 12 * n + 19 * m + 12 ∧
      run (scatterDenseInSrcPhase h5).code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = dense.length ∧
      (reg t r6).val = denseReachArcCount g dense ∧
      (∀ v : Fin dense.length, ∀ pos : Nat,
        denseInPrefix g dense v.val ≤ pos → pos < denseInPrefix g dense (v.val + 1) →
        ∃ u : Fin dense.length, (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) ∧
      (∀ u v : Fin dense.length,
        (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).count u.val =
          countOccurrence (dense[v.val]'v.isLt) (g.outArcs (dense[u.val]'u.isLt))) ∧
      (∀ u v : Fin dense.length,
        g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt) ↔
          ∃ pos : Nat, denseInPrefix g dense v.val ≤ pos ∧ pos < denseInPrefix g dense (v.val + 1) ∧
            (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) ∧
      (∀ j, (j < 5 * n ∨ (6 * n ≤ j ∧ j < 7 * n + 1) ∨
        7 * n + 1 + denseReachArcCount g dense ≤ j) → t.data[j]? = s₀.data[j]?) := by
  intro n m h5
  let code : Program L16 := (scatterDenseInSrcPhase h5).code
  have hSz : code.size = 41 := scatterDenseInSrcPhase_size h5
  let s_start := Phase.initial s₀
  have hStartPc : s_start.pc = 0 := rfl
  have hdLenLe : dense.length ≤ n := nodup_length_le_fin dense hdNd
  have hReachLe : denseReachArcCount g dense ≤ m := denseReachArcCount_le g dense hdNd
  have h2nFit : 2 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h3nFit : 3 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h4nFit : 4 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h5nFit : 5 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h6nFit : 6 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h7nFit : 7 * n < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have h7n1Fit : 7 * n + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
  have hAdd1 : (reg s_start rN).val + (reg s_start rN).val < 2 ^ bits := by
    change (reg s₀ rN).val + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t1, hs0, h1pc, h1v, h1o, h1d⟩ := step_add16 (input := input)
    (s := s_start) (code := code) rfl (by rw [hSz, hStartPc]; decide)
  have h1_r6 : (reg t1 r6).val = 2 * n := by
    rw [h1v, add_no_wrap _ _ hAdd1]; change (reg s₀ rN).val + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd2 : (reg t1 r6).val + (reg t1 rN).val < 2 ^ bits := by
    rw [h1_r6, h1o _ (by decide)]; change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t2, hs1, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
    (s := t1) (code := code) (by rw [h1pc]; rfl) (by rw [hSz, h1pc, hStartPc]; decide)
  have h2_r6 : (reg t2 r6).val = 3 * n := by
    rw [h2v, add_no_wrap _ _ hAdd2, h1_r6, h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd3 : (reg t2 r6).val + (reg t2 rN).val < 2 ^ bits := by
    rw [h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t3, hs2, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
    (s := t2) (code := code) (by rw [h2pc, h1pc]; rfl) (by rw [hSz, h2pc, h1pc, hStartPc]; decide)
  have h3_r7 : (reg t3 r7).val = 4 * n := by
    rw [h3v, add_no_wrap _ _ hAdd3, h2_r6, h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd4 : (reg t3 r7).val + (reg t3 rN).val < 2 ^ bits := by
    rw [h3_r7, h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t4, hs3, h4pc, h4v, h4o, h4d⟩ := step_add16 (input := input)
    (s := t3) (code := code) (by rw [h3pc, h2pc, h1pc]; rfl) (by rw [hSz, h3pc, h2pc, h1pc, hStartPc]; decide)
  have h4_r7 : (reg t4 r7).val = 5 * n := by
    rw [h4v, add_no_wrap _ _ hAdd4, h3_r7, h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd5 : (reg t4 r7).val + (reg t4 rN).val < 2 ^ bits := by
    rw [h4_r7, h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t5, hs4, h5pc, h5v, h5o, h5d⟩ := step_add16 (input := input)
    (s := t4) (code := code) (by rw [h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have h5_r8 : (reg t5 r8).val = 6 * n := by
    rw [h5v, add_no_wrap _ _ hAdd5, h4_r7, h4o _ (by decide), h3o _ (by decide),
      h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd6 : (reg t5 r8).val + (reg t5 rN).val < 2 ^ bits := by
    rw [h5_r8, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val < 2 ^ bits; rw [hConsts.nVal]; omega
  obtain ⟨t6, hs5, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
    (s := t5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have h6_r9 : (reg t6 r9).val = 7 * n := by
    rw [h6v, add_no_wrap _ _ hAdd6, h5_r8, h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
      h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rN).val = _; rw [hConsts.nVal]; omega
  have hAdd7 : (reg t6 r9).val + (reg t6 rOne).val < 2 ^ bits := by
    rw [h6_r9, h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide),
      h2o _ (by decide), h1o _ (by decide)]
    change _ + (reg s₀ rOne).val < 2 ^ bits; rw [hConsts.one]; omega
  obtain ⟨t7, hs6, h7pc, h7v, h7o, h7d⟩ := step_add16 (input := input)
    (s := t6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  obtain ⟨t8, hs7, h8pc, h8v, h8o, h8d⟩ := step_imm16 (input := input)
    (s := t7) (code := code) (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc]; rfl)
    (by rw [hSz, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc]; decide)
  have hSetup : Steps code input 8 s_start t8 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero t8))))))))
  have hKeep8 (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn7 : regIdx ≠ r7)
      (hn8 : regIdx ≠ r8) (hn9 : regIdx ≠ r9) (hn10 : regIdx ≠ r10) :
      reg t8 regIdx = reg s_start regIdx := by
    rw [h8o _ hn10, h7o _ hn9, h6o _ hn9, h5o _ hn8, h4o _ hn7, h3o _ hn7, h2o _ hn6, h1o _ hn6]
  have hData8 : t8.data = s₀.data := by rw [h8d, h7d, h6d, h5d, h4d, h3d, h2d, h1d]; rfl
  have hConsts8 : ConstRegs n m r.val t8 :=
    ⟨(congrArg Fin.val (hKeep8 rZero (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.zero,
     (congrArg Fin.val (hKeep8 rOne (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.one,
     (congrArg Fin.val (hKeep8 rN (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.nVal,
     (congrArg Fin.val (hKeep8 rM (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.mVal,
     (congrArg Fin.val (hKeep8 rRoot (by decide) (by decide) (by decide) (by decide) (by decide))).trans hConsts.rootVal⟩
  have hOut0 : ScatterOuterInv g r dense s₀.data 0 t8 := by
    refine ⟨by rw [h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, h1pc, hStartPc], hConsts8,
      (congrArg Fin.val (hKeep8 r5 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hqReg,
      ?_, ?_, ?_, ?_, by rw [h8v]; rfl, ?_, ?_, ?_, fun _ _ => by rw [hData8]⟩
    · rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide), h3o _ (by decide)]
      exact h2_r6
    · rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide), h5o _ (by decide)]; exact h4_r7
    · rw [h8o _ (by decide), h7o _ (by decide), h6o _ (by decide)]; exact h5_r8
    · rw [h8o _ (by decide), h7v, add_no_wrap _ _ hAdd7, h6_r9, h6o _ (by decide), h5o _ (by decide),
        h4o _ (by decide), h3o _ (by decide), h2o _ (by decide), h1o _ (by decide)]
      change _ + (reg s₀ rOne).val = _; rw [hConsts.one]
    · intro i hi
      rw [hData8, doneDegOuter, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero]
      simpa [denseInDegBase_eq] using hDenseIn i hi
    · intro i hi uIdx hu
      have hDone0 : doneDegOuter g dense 0 (dense[i]'hi) = 0 := by simp [doneDegOuter]
      have hArc0 : doneArcsOuter g dense 0 uIdx (dense[i]'hi) = 0 := by simp [doneArcsOuter]
      rw [hDone0, Nat.sub_zero, hArc0, ← denseInPrefix_succ_lt g dense i hi]
      have hNil : inSrcSlice t8.data g.vertexCount (denseInPrefix g dense (i + 1))
          (denseInPrefix g dense (i + 1)) = [] := by
        apply List.eq_nil_of_length_eq_zero; simp [inSrcSlice]
      rw [hNil]; simp
    · intro i hi pos hge hlt
      have hDone0 : doneDegOuter g dense 0 (dense[i]'hi) = 0 := by simp [doneDegOuter]
      rw [hDone0, Nat.sub_zero, ← denseInPrefix_succ_lt g dense i hi] at hge
      omega
  have run_inner : ∀ (k : Nat) (hk : k < dense.length) (st0 : State L16),
      ScatterInnerInv g r dense s₀.data k 0 hk st0 →
      ∃ stEnd innerSteps,
        innerSteps ≤ 19 * (g.outArcs (dense[k]'hk)).length + 1 ∧
        Steps code input innerSteps st0 stEnd ∧
        ScatterInnerPost g r dense s₀.data k stEnd :=
    scatter_run_inner input raw workRoom s₀.data dense hdNd hdClosed hOrigToDense hInStart h5
  -- Outer loop
  let processedArcs (k : Nat) : Nat := denseReachArcCount g (dense.take k)
  have hProcLe : ∀ k, processedArcs k ≤ m := fun k =>
    denseReachArcCount_le g (dense.take k) (hdNd.sublist (List.take_sublist _ _))
  let OuterMeas (k : Nat) : Nat := dense.length - k
  let OuterBudget (k : Nat) : Nat := 12 * (dense.length - k) + 19 * (m - processedArcs k) + 4
  let OuterPost (_ : Nat) (t : State L16) : Prop :=
    ConstRegs n m r.val t ∧
    (reg t r5).val = dense.length ∧
    (reg t r6).val = denseReachArcCount g dense ∧
    (∀ v : Fin dense.length, ∀ pos : Nat,
      denseInPrefix g dense v.val ≤ pos → pos < denseInPrefix g dense (v.val + 1) →
      ∃ u : Fin dense.length, (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) ∧
    (∀ u v : Fin dense.length,
      (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).count u.val =
        countOccurrence (dense[v.val]'v.isLt) (g.outArcs (dense[u.val]'u.isLt))) ∧
    (∀ u v : Fin dense.length,
      g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt) ↔
        ∃ pos : Nat, denseInPrefix g dense v.val ≤ pos ∧ pos < denseInPrefix g dense (v.val + 1) ∧
          (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) ∧
    (∀ j, (j < 5 * n ∨ (6 * n ≤ j ∧ j < 7 * n + 1) ∨
      7 * n + 1 + denseReachArcCount g dense ≤ j) → t.data[j]? = s₀.data[j]?)
  have hOuterStep : ∀ k st, (k ≤ dense.length ∧ ScatterOuterInv g r dense s₀.data k st) →
      (∃ t, OuterPost k t ∧ ∃ steps, steps ≤ OuterBudget k ∧ run code input steps st = some ⟨t, steps⟩) ∨
      (∃ k' st' steps, OuterMeas k' < OuterMeas k ∧ steps + OuterBudget k' ≤ OuterBudget k ∧
        Steps code input steps st st' ∧ (k' ≤ dense.length ∧ ScatterOuterInv g r dense s₀.data k' st')) := by
    intro k st ⟨hkLe, hOut⟩
    by_cases hk : k < dense.length
    · right
      have hCmp : ltb (reg st r10) (reg st r5) = true :=
        branchLt_true (by rw [hOut.uDense, hOut.qCount]; exact hk)
      have hf8 : code[st.pc]? = some (.branchLt r10 r5 9 38) := by rw [hOut.pc]; rfl
      let u1 : State L16 := { st with pc := 9 }
      have hu1Pc : u1.pc = 9 := rfl
      have hs8 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, ite_true] using
          step_branchLt_at (input := input) hf8 (by rw [hSz, hCmp]; decide)
      have h4nAddFit : (reg u1 r6).val + (reg u1 rN).val < 2 ^ bits := by
        change (reg st r6).val + (reg st rN).val < 2 ^ bits; rw [hOut.origBase, hOut.consts.nVal]; omega
      obtain ⟨u2, hs9, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r13 : (reg u2 r13).val = 4 * n := by
        rw [h2v, add_no_wrap _ _ h4nAddFit]; change (reg st r6).val + (reg st rN).val = _
        rw [hOut.origBase, hOut.consts.nVal]; omega
      have hDenseAddrFit : (reg u2 r13).val + (reg u2 r10).val < 2 ^ bits := by
        rw [h2_r13, h2o _ (by decide)]; change _ + (reg st r10).val < 2 ^ bits
        rw [hOut.uDense]; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u3, hs10, h3pc, h3v, h3o, h3d⟩ := step_add16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) (by rw [hSz, h2pc, hu1Pc]; decide)
      have h3_r13 : (reg u3 r13).val = 4 * n + k := by
        rw [h3v, add_no_wrap _ _ hDenseAddrFit, h2_r13, h2o _ (by decide)]
        change _ + (reg st r10).val = _; rw [hOut.uDense]
      let u : Fin n := dense[k]'hk
      have huFit : u.val < 2 ^ bits := by
        have := u.isLt; unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      have huData : u3.data[(reg u3 r13).val]? = some ⟨u.val, huFit⟩ := by
        rw [h3d, h2d, h3_r13]; change st.data[4 * g.vertexCount + k]? = _
        rw [hOut.frame (4 * g.vertexCount + k) (Or.inl (by omega))]
        have hm := hDenseToOrig k hk; rw [denseToOrigBase_eq] at hm
        cases hcell : s₀.data[4 * g.vertexCount + k]? with
        | none => simp [hcell] at hm
        | some w => rw [hcell, Option.map_some] at hm; exact congrArg some (Fin.ext (Option.some.inj hm))
      obtain ⟨u4, hs11, h4pc, h4v, h4o, h4d⟩ := step_loadData16 (input := input)
        (s := u3) (code := code) (by rw [h3pc, h2pc, hu1Pc]; rfl) huData (by rw [hSz, h3pc, h2pc, hu1Pc]; decide)
      have h4_r13 : (reg u4 r13).val = u.val := by rw [h4v]
      obtain ⟨u5, hs12, h5pc, h5v, h5o, h5d⟩ := step_imm16 (input := input)
        (s := u4) (code := code) (by rw [h4pc, h3pc, h2pc, hu1Pc]; rfl) (by rw [hSz, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h5_r13 : (reg u5 r13).val = u.val := by rw [h5o _ (by decide)]; exact h4_r13
      have hOffAddrFit : (reg u5 r14).val + (reg u5 r13).val < 2 ^ bits := by
        rw [h5v, h5_r13]; have := raw.cap_ge; unfold rawDagInputCap at this; have := u.isLt; dsimp only [n] at *; omega
      obtain ⟨u6, hs13, h6pc, h6v, h6o, h6d⟩ := step_add16 (input := input)
        (s := u5) (code := code) (by rw [h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h6_r14 : (reg u6 r14).val = 3 + u.val := by rw [h6v, add_no_wrap _ _ hOffAddrFit, h5v, h5_r13]
      have hOffStartFit : outPrefix g u.val < 2 ^ bits := by
        have := outPrefix_mono g (Nat.le_of_lt u.isLt); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff0 : input.words[(reg u6 r14).val]? = some ⟨outPrefix g u.val, hOffStartFit⟩ := by
        rw [h6_r14]; have ho := raw.out_off u.val (Nat.le_of_lt u.isLt)
        cases hcell : input.words[3 + u.val]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u7, hs14, h7pc, h7v, h7o, h7d⟩ := step_loadInput16 (input := input)
        (s := u6) (code := code) (by rw [h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff0
      have h7_r14 : (reg u7 r14).val = 3 + u.val := by rw [h7o _ (by decide)]; exact h6_r14
      have h7_one : (reg u7 rOne).val = 1 := by
        rw [h7o _ (by decide), h6o _ (by decide), h5o _ (by decide), h4o _ (by decide),
          h3o _ (by decide), h2o _ (by decide)]; exact hOut.consts.one
      have hOffAddr2Fit : (reg u7 r14).val + (reg u7 rOne).val < 2 ^ bits := by
        rw [h7_r14, h7_one]; have := u.isLt; have := raw.cap_ge; unfold rawDagInputCap at this; dsimp only [n] at *; omega
      obtain ⟨u8, hs15, h8pc, h8v, h8o, h8d⟩ := step_add16 (input := input)
        (s := u7) (code := code) (by rw [h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide)
      have h8_r14 : (reg u8 r14).val = 3 + (u.val + 1) := by
        rw [h8v, add_no_wrap _ _ hOffAddr2Fit, h7_r14, h7_one]; omega
      have hOffEndFit : outPrefix g (u.val + 1) < 2 ^ bits := by
        have := outPrefix_mono g (by omega : u.val + 1 ≤ g.vertexCount); rw [outPrefix_vertexCount] at this
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have huOff1 : input.words[(reg u8 r14).val]? = some ⟨outPrefix g (u.val + 1), hOffEndFit⟩ := by
        rw [h8_r14]; have ho := raw.out_off (u.val + 1) (by omega)
        cases hcell : input.words[3 + (u.val + 1)]? with
        | none => simp [hcell] at ho
        | some w => rw [hcell, Option.map_some] at ho; exact congrArg some (Fin.ext (Option.some.inj ho))
      obtain ⟨u9, hs16, h9pc, h9v, h9o, h9d⟩ := step_loadInput16 (input := input)
        (s := u8) (code := code) (by rw [h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; rfl)
        (by rw [hSz, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc]; decide) huOff1
      have hKeep9 (regIdx : Fin 16) (hn11 : regIdx ≠ r11) (hn12 : regIdx ≠ r12)
          (hn13 : regIdx ≠ r13) (hn14 : regIdx ≠ r14) : reg u9 regIdx = reg st regIdx := by
        rw [h9o _ hn12, h8o _ hn14, h7o _ hn11, h6o _ hn14, h5o _ hn14, h4o _ hn13, h3o _ hn13, h2o _ hn13]; rfl
      have hData9 : u9.data = st.data := by rw [h9d, h8d, h7d, h6d, h5d, h4d, h3d, h2d]
      have hIn0 : ScatterInnerInv g r dense s₀.data k 0 hk u9 := by
        refine ⟨by rw [h9pc, h8pc, h7pc, h6pc, h5pc, h4pc, h3pc, h2pc, hu1Pc], ?_,
          (congrArg Fin.val (hKeep9 r5 (by decide) (by decide) (by decide) (by decide))).trans hOut.qCount,
          (congrArg Fin.val (hKeep9 r6 (by decide) (by decide) (by decide) (by decide))).trans hOut.origBase,
          (congrArg Fin.val (hKeep9 r7 (by decide) (by decide) (by decide) (by decide))).trans hOut.denseInBase,
          (congrArg Fin.val (hKeep9 r8 (by decide) (by decide) (by decide) (by decide))).trans hOut.inStartBase,
          (congrArg Fin.val (hKeep9 r9 (by decide) (by decide) (by decide) (by decide))).trans hOut.inSrcBaseReg,
          (congrArg Fin.val (hKeep9 r10 (by decide) (by decide) (by decide) (by decide))).trans hOut.uDense,
          Nat.zero_le _, by rw [h9o _ (by decide), h8o _ (by decide), h7v, Nat.add_zero],
          (congrArg Fin.val h9v).trans (outPrefix_succ_lt g u), ?_, ?_, ?_, ?_⟩
        · exact ⟨(congrArg Fin.val (hKeep9 rZero (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.zero,
            (congrArg Fin.val (hKeep9 rOne (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.one,
            (congrArg Fin.val (hKeep9 rN (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.nVal,
            (congrArg Fin.val (hKeep9 rM (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.mVal,
            (congrArg Fin.val (hKeep9 rRoot (by decide) (by decide) (by decide) (by decide))).trans hOut.consts.rootVal⟩
        · intro i hi; rw [hData9]; simpa [doneDegInner, List.take_zero, countOccurrence] using hOut.remDegs i hi
        · intro i hi uIdx hu; rw [hData9]
          have hDegEq : doneDegInner g dense k 0 hk (dense[i]'hi) = doneDegOuter g dense k (dense[i]'hi) := by
            simp [doneDegInner, countOccurrence]
          have hArcEq : doneArcsInner g dense k 0 hk uIdx (dense[i]'hi) = doneArcsOuter g dense k uIdx (dense[i]'hi) := by
            unfold doneArcsInner doneArcsOuter
            by_cases huk : uIdx < k
            · have hukMin : uIdx < min k dense.length := by omega
              rw [dite_eq_left huk, dite_eq_left hukMin]
            · have hnMin : ¬ uIdx < min k dense.length := by omega
              rw [dite_eq_right huk, dite_eq_right hnMin]
              by_cases hue : uIdx = k <;> simp [hue, countOccurrence]
          rw [hDegEq, hArcEq]; exact hOut.sliceCounts i hi uIdx hu
        · intro i hi pos hge hlt; rw [hData9]
          have hDegEq : doneDegInner g dense k 0 hk (dense[i]'hi) = doneDegOuter g dense k (dense[i]'hi) := by
            simp [doneDegInner, countOccurrence]
          rw [hDegEq] at hge; exact hOut.writtenMem i hi pos hge hlt
        · intro idx hidx; rw [hData9]; exact hOut.frame idx hidx
      obtain ⟨st36, innerSteps, hInnerLe, hInnerSteps, h36pc, h36c, h36q, h36ob, h36dib,
        h36isb, h36srb, h36u, h36rem, h36slice, h36mem, h36frame⟩ := run_inner k hk u9 hIn0
      have hk1Fit : k + 1 < 2 ^ bits := by unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u37, hs36, h37pc, h37v, h37o, h37d⟩ := step_add16 (input := input)
        (s := st36) (code := code) (by rw [h36pc]; rfl) (by rw [hSz, h36pc]; decide)
      let stNext : State L16 := { u37 with pc := 8 }
      have hs37 : step code input u37 = some (.next stNext) :=
        step_goto_at (input := input) (code := code) (by rw [h37pc, h36pc]; rfl) (by rw [hSz]; decide)
      have hKeepNext (regIdx : Fin 16) (hn10 : regIdx ≠ r10) : reg stNext regIdx = reg st36 regIdx :=
        h37o regIdx hn10
      have hOutNext : ScatterOuterInv g r dense s₀.data (k + 1) stNext := by
        refine ⟨rfl, ?_,
          (congrArg Fin.val (hKeepNext r5 (by decide))).trans h36q,
          (congrArg Fin.val (hKeepNext r6 (by decide))).trans h36ob,
          (congrArg Fin.val (hKeepNext r7 (by decide))).trans h36dib,
          (congrArg Fin.val (hKeepNext r8 (by decide))).trans h36isb,
          (congrArg Fin.val (hKeepNext r9 (by decide))).trans h36srb,
          ?_, fun i hi => by change (u37.data[5 * g.vertexCount + i]?).map Fin.val = _; rw [h37d]; exact h36rem i hi,
          fun i hi uIdx hu => by change (inSrcSlice u37.data _ _ _).count uIdx = _; rw [h37d]; exact h36slice i hi uIdx hu,
          fun i hi pos hge hlt => by
            change ∃ uIdx : Fin dense.length, (u37.data[7 * g.vertexCount + 1 + pos]?).map Fin.val = some uIdx.val
            rw [h37d]; exact h36mem i hi pos hge hlt,
          fun idx hidx => by change u37.data[idx]? = _; rw [h37d]; exact h36frame idx hidx⟩
        · exact ⟨(congrArg Fin.val (hKeepNext rZero (by decide))).trans h36c.zero,
            (congrArg Fin.val (hKeepNext rOne (by decide))).trans h36c.one,
            (congrArg Fin.val (hKeepNext rN (by decide))).trans h36c.nVal,
            (congrArg Fin.val (hKeepNext rM (by decide))).trans h36c.mVal,
            (congrArg Fin.val (hKeepNext rRoot (by decide))).trans h36c.rootVal⟩
        · change (reg u37 r10).val = k + 1
          rw [h37v, add_no_wrap _ _ (by rw [h36u, h36c.one]; exact hk1Fit), h36u, h36c.one]
      have htakeK1 : dense.take (k + 1) = dense.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
      have hProcInc : processedArcs (k + 1) = processedArcs k + (g.outArcs u).length := by
        dsimp only [processedArcs, denseReachArcCount]
        rw [htakeK1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      have hProcLe1 := hProcLe (k + 1)
      have hPref9 : Steps code input 9 st u9 :=
        Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12
          (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16 (Steps.zero u9)))))))))
      have hTail2 : Steps code input 2 st36 stNext :=
        Steps.cons hs36 (Steps.cons hs37 (Steps.zero stNext))
      refine ⟨k + 1, stNext, 9 + innerSteps + 2, by dsimp only [OuterMeas]; omega,
        by dsimp only [OuterBudget, u] at *; omega, (hPref9.append hInnerSteps).append hTail2,
        by omega, hOutNext⟩
    · left
      have hkEq : k = dense.length := by omega
      have hCmp : ltb (reg st r10) (reg st r5) = false :=
        branchLt_false (by rw [hOut.uDense, hOut.qCount, hkEq]; exact Nat.le_refl _)
      have hf8 : code[st.pc]? = some (.branchLt r10 r5 9 38) := by rw [hOut.pc]; rfl
      let u1 : State L16 := { st with pc := 38 }
      have hu1Pc : u1.pc = 38 := rfl
      have hs8 : step code input st = some (.next u1) := by
        simpa only [u1, hCmp, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf8 (by rw [hSz, hCmp]; decide)
      have hEndAddrFit : (reg u1 r8).val + (reg u1 r5).val < 2 ^ bits := by
        change (reg st r8).val + (reg st r5).val < 2 ^ bits; rw [hOut.inStartBase, hOut.qCount]
        unfold rawDagWorkCap at workRoom; dsimp only [n] at *; omega
      obtain ⟨u2, hs38, h2pc, h2v, h2o, h2d⟩ := step_add16 (input := input)
        (s := u1) (code := code) rfl (by rw [hSz, hu1Pc]; decide)
      have h2_r13 : (reg u2 r13).val = 6 * n + dense.length := by
        rw [h2v, add_no_wrap _ _ hEndAddrFit]; change (reg st r8).val + (reg st r5).val = _
        rw [hOut.inStartBase, hOut.qCount]
      have hReachFit : denseReachArcCount g dense < 2 ^ bits := by
        have := raw.cap_ge; unfold rawDagInputCap at this; omega
      have hReachMem : u2.data[(reg u2 r13).val]? = some ⟨denseReachArcCount g dense, hReachFit⟩ := by
        rw [h2d, h2_r13]; change st.data[6 * g.vertexCount + dense.length]? = _
        rw [hOut.frame (6 * g.vertexCount + dense.length) (Or.inr (Or.inl (by omega)))]
        have hs := hInStart dense.length (Nat.le_refl _); rw [inStartBase_eq, denseInPrefix_length g dense hdNd hdClosed] at hs
        cases hcell : s₀.data[6 * g.vertexCount + dense.length]? with
        | none => simp [hcell] at hs
        | some w => rw [hcell, Option.map_some] at hs; exact congrArg some (Fin.ext (Option.some.inj hs))
      obtain ⟨t, hs39, h3pc, h3v, h3o, h3d⟩ := step_loadData16 (input := input)
        (s := u2) (code := code) (by rw [h2pc, hu1Pc]; rfl) hReachMem (by rw [hSz, h2pc, hu1Pc]; decide)
      have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [h3pc, h2pc, hu1Pc]; rfl)
      have hRun4 : run code input 4 st = some ⟨t, 4⟩ :=
        (Steps.cons hs8 (Steps.cons hs38 (Steps.cons hs39 (Steps.zero t)))).halts hHalt
      have hKeepT (regIdx : Fin 16) (hn6 : regIdx ≠ r6) (hn13 : regIdx ≠ r13) :
          reg t regIdx = reg st regIdx := by
        rw [h3o _ hn6, h2o _ hn13]; rfl
      have hDataT : t.data = st.data := by rw [h3d, h2d]
      have hDoneAll : ∀ v, doneDegOuter g dense k v = denseInDegCount g dense v := by
        intro v; unfold doneDegOuter denseInDegCount
        rw [hkEq, List.take_length]
      have hArcAll : ∀ uIdx v, (hu : uIdx < dense.length) →
          doneArcsOuter g dense k uIdx v =
            countOccurrence v (g.outArcs (dense[uIdx]'hu)) := by
        intro uIdx v hu; unfold doneArcsOuter
        have huMin : uIdx < min k dense.length := by omega
        rw [dite_eq_left huMin]
      have hSliceEnd : ∀ u v : Fin dense.length,
          (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).count u.val =
            countOccurrence (dense[v.val]'v.isLt) (g.outArcs (dense[u.val]'u.isLt)) := by
        intro u v
        have hSc := hOut.sliceCounts v.val v.isLt u.val u.isLt
        rw [hDoneAll, Nat.sub_self, Nat.add_zero, hArcAll u.val (dense[v.val]'v.isLt) u.isLt] at hSc
        rw [hDataT]; exact hSc
      have hMemEnd : ∀ v : Fin dense.length, ∀ pos : Nat,
          denseInPrefix g dense v.val ≤ pos → pos < denseInPrefix g dense (v.val + 1) →
          ∃ u : Fin dense.length, (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val := by
        intro v pos hge hlt
        have hm := hOut.writtenMem v.val v.isLt pos (by rw [hDoneAll, Nat.sub_self, Nat.add_zero]; exact hge) hlt
        rw [inSrcBase_eq, hDataT]; exact hm
      refine ⟨t, ⟨?_, (congrArg Fin.val (hKeepT r5 (by decide) (by decide))).trans hOut.qCount,
        by rw [h3v], hMemEnd, hSliceEnd, ?_, fun j hj => by rw [hDataT]; exact hOut.frame j hj⟩, 4,
        by dsimp only [OuterBudget]; omega, hRun4⟩
      · exact ⟨(congrArg Fin.val (hKeepT rZero (by decide) (by decide))).trans hOut.consts.zero,
          (congrArg Fin.val (hKeepT rOne (by decide) (by decide))).trans hOut.consts.one,
          (congrArg Fin.val (hKeepT rN (by decide) (by decide))).trans hOut.consts.nVal,
          (congrArg Fin.val (hKeepT rM (by decide) (by decide))).trans hOut.consts.mVal,
          (congrArg Fin.val (hKeepT rRoot (by decide) (by decide))).trans hOut.consts.rootVal⟩
      · intro u v
        have hCnt := hSliceEnd u v
        have hHasIff : g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt) ↔
            0 < countOccurrence (dense[v.val]'v.isLt) (g.outArcs (dense[u.val]'u.isLt)) := by
          change dense[v.val]'v.isLt ∈ g.outArcs (dense[u.val]'u.isLt) ↔ _
          exact (Kahn.countOccurrence_pos_iff_row_mem _ _).symm
        have hMemIff : 0 < (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).count u.val ↔
            u.val ∈ inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1)) :=
          List.count_pos_iff
        rw [hHasIff, ← hCnt, hMemIff]
        constructor
        · intro hmem
          obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hmem
          rw [inSrcSlice_length] at hidx
          simp only [inSrcSlice, List.getElem_ofFn] at heq
          let pos := denseInPrefix g dense v.val + idx
          have hge : denseInPrefix g dense v.val ≤ pos := Nat.le_add_right _ _
          have hlt : pos < denseInPrefix g dense (v.val + 1) := by omega
          obtain ⟨u', hu'⟩ := hMemEnd v pos hge hlt
          rw [inSrcBase_eq] at hu'
          have hu'Eq : u'.val = u.val := by
            have hu'G : ((t.data[7 * n + 1 + denseInPrefix g dense v.val + idx]?).map Fin.val).getD 0 = u'.val := by
              rw [Nat.add_assoc (7 * n + 1)]; dsimp only [pos] at hu'; rw [hu']; rfl
            exact hu'G.symm.trans heq
          refine ⟨pos, hge, hlt, ?_⟩
          rw [inSrcBase_eq]; simpa [hu'Eq] using hu'
        · rintro ⟨pos, hge, hlt, hcell⟩
          rw [inSrcBase_eq] at hcell
          let idx := pos - denseInPrefix g dense v.val
          have hidx : idx < (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).length := by
            rw [inSrcSlice_length]; omega
          have heq : (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1)))[idx]'hidx = u.val := by
            simp only [inSrcSlice, List.getElem_ofFn]
            have hPosEq : 7 * n + 1 + denseInPrefix g dense v.val + idx = 7 * n + 1 + pos := by omega
            rw [hPosEq, hcell]; rfl
          exact heq ▸ List.getElem_mem hidx
  obtain ⟨_, tEnd, loopSteps, hLoopLe, hRunLoop, hPost⟩ :=
    while_steps_budget (fun k s => k ≤ dense.length ∧ ScatterOuterInv g r dense s₀.data k s)
      OuterMeas OuterBudget OuterPost hOuterStep dense.length 0 t8
      (by dsimp only [OuterMeas]; omega) ⟨Nat.zero_le _, hOut0⟩
  obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input last = some (.halted tEnd) := by
    change tEnd = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
  have hExec := (hSetup.append route).halts terminal
  change loopSteps = k' + 1 at cost
  rw [Nat.add_assoc, ← cost] at hExec
  rcases hPost with ⟨hc, hq, hm, hmem, hcnt, hiff, hf⟩
  have hZeroArcs : processedArcs 0 = 0 := by simp [processedArcs, denseReachArcCount]
  dsimp only [OuterBudget, OuterMeas] at hLoopLe
  rw [hZeroArcs, Nat.sub_zero, Nat.sub_zero] at hLoopLe
  exact ⟨tEnd, 8 + loopSteps, by omega, hExec, hc, hq, hm, hmem, hcnt, hiff, hf⟩

end Phase4ScatterDenseInSrc

/-! ### Full EX5.1 Phase B1 Word-RAM Pipeline (`dagReachKahnProgram`, `run_dag_reach_kahn`) -/

section Pipeline

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def dagReachKahnPhases (h5 : 5 ≤ 2 ^ bits) : List (Phase L16) :=
  [initPhase h5, countInDegPhase h5, seedQueuePhase h5, kahnBfsPhase h5,
   initMarkedPhase, reachSweepPhase h5, compactReachPhase,
   zeroDenseInDegPhase, countDenseInDegPhase h5, denseInStartPrefixPhase, scatterDenseInSrcPhase h5]

def dagReachKahnPhase (h5 : 5 ≤ 2 ^ bits) : Phase L16 :=
  pipelinePhase (dagReachKahnPhases h5)

def dagReachKahnProgram (h5 : 5 ≤ 2 ^ bits) : Program L16 :=
  pipeline (dagReachKahnPhases h5)

theorem dagReachKahnPhase_code (h5 : 5 ≤ 2 ^ bits) :
    (dagReachKahnPhase (hi := hi) (hw := hw) h5).code = dagReachKahnProgram h5 :=
  pipelinePhase_code _

theorem run_dag_reach_kahn (input : Input L16) {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (workRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap)
    (s₀ : State L16) :
    let n := g.vertexCount
    let m := g.arcCount
    let h5 : 5 ≤ 2 ^ bits := by
      have := Fin.pos r
      have := raw.cap_ge
      unfold rawDagInputCap at this
      omega
    ∃ (t : State L16) (states : List (State L16)) (steps : Nat)
      (order : List (Fin n)) (hlen : order.length = n) (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      steps ≤ 90 * (n + m + 1) ∧
      run (dagReachKahnProgram h5) input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace (dagReachKahnProgram h5) input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = inputCap + workCap + 16 ∧
      ConstRegs n m r.val t ∧
      (reg t r5).val = dense.length ∧
      (reg t r6).val = denseReachArcCount g dense ∧
      1 ≤ dense.length ∧
      dense.length ≤ n ∧
      denseReachArcCount g dense ≤ m ∧
      (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
      (∀ i : Nat, (hi_1 : i < n) →
        (t.data[topoOrderBase n m + i]?).map Fin.val =
          some (order[i]'(by rw [hlen]; exact hi_1)).val) ∧
      (∀ v : Fin n,
        (t.data[markedBase n m + v.val]?).map Fin.val =
          some (if ((g.scanReachability r order hTopo).marked[v.val]?).getD false then 1 else 0)) ∧
      (∀ v : Fin n,
        (t.data[markedBase n m + v.val]?).map Fin.val = some 1 ↔ g.InitiallyReachable r v) ∧
      (∀ i : Nat, (hi_1 : i < dense.length) → g.InitiallyReachable r (dense[i]'hi_1)) ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (t.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val) ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        (t.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1)) ∧
      (∀ v : Fin n, ¬ g.InitiallyReachable r v →
        (t.data[origToDensePlusOneBase n m + v.val]?).map Fin.val = some 0) ∧
      (∀ u v : Fin dense.length,
        g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt) → u.val < v.val) ∧
      (∀ i : Nat, i ≤ dense.length →
        (t.data[inStartBase n m + i]?).map Fin.val = some (denseInPrefix g dense i)) ∧
      (denseInPrefix g dense 0 = 0 ∧ denseInPrefix g dense dense.length = denseReachArcCount g dense) ∧
      (∀ i : Nat, (hi_1 : i < dense.length) →
        denseInPrefix g dense (i + 1) - denseInPrefix g dense i = denseInDegCount g dense (dense[i]'hi_1)) ∧
      (∀ v : Fin dense.length, ∀ pos : Nat,
        denseInPrefix g dense v.val ≤ pos → pos < denseInPrefix g dense (v.val + 1) →
        ∃ u : Fin dense.length, (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) ∧
      (∀ u v : Fin dense.length,
        (inSrcSlice t.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1))).count u.val =
          countOccurrence (dense[v.val]'v.isLt) (g.outArcs (dense[u.val]'u.isLt))) ∧
      (∀ u v : Fin dense.length,
        g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt) ↔
          ∃ pos : Nat, denseInPrefix g dense v.val ≤ pos ∧ pos < denseInPrefix g dense (v.val + 1) ∧
            (t.data[inSrcBase n m + pos]?).map Fin.val = some u.val) := by
  intro n m h5
  obtain ⟨s1, hr1, hc1, hz1, hf1⟩ := run_initPhase input raw workRoom s₀
  obtain ⟨s2, hr2, hc2, hindeg2, hf2⟩ := run_countInDegPhase input raw workRoom s1 hc1 hz1
  obtain ⟨s3, st3, q0, hst3, hr3, hc3, hq0nd, hq0len, hq0tail, hq0zero, hindeg3, hq0mem, hf3⟩ :=
    run_seedQueuePhase input raw workRoom s2 hc2 hindeg2
  obtain ⟨s4, st4, order, hlen, hst4, hr4, hc4, hTopo, htopo4, hf4⟩ :=
    run_kahnBfsPhase input raw acyc workRoom s3 hc3 q0 hq0nd hq0tail hq0zero hindeg3 hq0mem
  obtain ⟨s5, st5, hst5, hr5, hc5, hmark5, hf5⟩ := run_initMarkedPhase input workRoom s4 hc4
  obtain ⟨s6, st6, hst6, hr6, hc6, hmark6, hf6⟩ :=
    run_reachSweepPhase input raw workRoom s5 hc5 order hlen hTopo
      (fun i hi => by rw [hf5 (topoOrderBase n m + i) (Or.inl (by simp [topoOrderBase]; omega))]; exact htopo4 i hi)
      hmark5
  let dense := denseVertices g r order hTopo
  have hdNd : dense.Nodup := denseVertices_nodup g r order hTopo
  have hdClosed : ∀ u ∈ dense, ∀ v ∈ g.outArcs u, v ∈ dense := fun u hu v hv =>
    (denseVertices_mem_iff g r order hTopo v).mpr
      (initiallyReachable_extend ((denseVertices_mem_iff g r order hTopo u).mp hu) hv)
  have htopo6 : ∀ i : Nat, (hi_1 : i < n) →
      (s6.data[topoOrderBase n m + i]?).map Fin.val =
        some (order[i]'(by rw [hlen]; exact hi_1)).val := fun i hi => by
    rw [hf6 (topoOrderBase n m + i) (Or.inl (by simp [topoOrderBase]; omega)),
      hf5 (topoOrderBase n m + i) (Or.inl (by simp [topoOrderBase]; omega))]
    exact htopo4 i hi
  obtain ⟨s7, st7, hst7, hr7, hc7, hq7, hdense7, horig7, hzero7, hf7⟩ :=
    run_compactReachPhase input workRoom s6 hc6 order hlen hTopo htopo6 hmark6
  have hmark7 : ∀ v : Fin n,
      (s7.data[markedBase n m + v.val]?).map Fin.val =
        some (if ((g.scanReachability r order hTopo).marked[v.val]?).getD false then 1 else 0) := fun v => by
    rw [hf7 (markedBase n m + v.val) (Or.inl (by simp [markedBase]; have := v.isLt; omega))]
    exact hmark6 v
  have htopo7 : ∀ i : Nat, (hi_1 : i < n) →
      (s7.data[topoOrderBase n m + i]?).map Fin.val =
        some (order[i]'(by rw [hlen]; exact hi_1)).val := fun i hi => by
    rw [hf7 (topoOrderBase n m + i) (Or.inl (by simp [topoOrderBase]; omega))]
    exact htopo6 i hi
  obtain ⟨s8, st8, hst8, hr8, hc8, hq8, hzero8, hf8⟩ :=
    run_zeroDenseInDegPhase input workRoom s7 hc7 dense.length
      (denseVertices_length_le g r order hTopo) hq7
  have hdense8 : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s8.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val := fun i hi => by
    have hdLen : dense.length ≤ g.vertexCount := denseVertices_length_le g r order hTopo
    dsimp only [n]
    rw [hf8 (denseToOrigBase g.vertexCount m + i) (Or.inl (by simp [denseToOrigBase]; omega))]
    exact hdense7 i hi
  have horig8 : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s8.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1) := fun i hi => by
    rw [hf8 (origToDensePlusOneBase n m + (dense[i]'hi).val)
      (Or.inl (by simp [origToDensePlusOneBase]; have := (dense[i]'hi).isLt; omega))]
    exact horig7 i hi
  obtain ⟨s9, st9, hst9, hr9, hc9, hq9, hcnt9, hf9⟩ :=
    run_countDenseInDegPhase input raw workRoom s8 hc8 dense hdNd hdClosed hq8 hdense8 horig8 hzero8
  obtain ⟨s10, st10, hst10, hr10, hc10, hq10, hm10, hstart10, hf10⟩ :=
    run_denseInStartPrefixPhase input raw workRoom s9 hc9 dense hdNd hdClosed hq9 hcnt9
  have hdense10 : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s10.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val := fun i hi => by
    have hdLen : dense.length ≤ g.vertexCount := denseVertices_length_le g r order hTopo
    dsimp only [n]
    rw [hf10 (denseToOrigBase g.vertexCount m + i) (Or.inl (by simp [denseToOrigBase]; omega)),
      hf9 (denseToOrigBase g.vertexCount m + i) (Or.inl (by simp [denseToOrigBase]; omega))]
    exact hdense8 i hi
  have horig10 : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s10.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1) := fun i hi => by
    rw [hf10 (origToDensePlusOneBase n m + (dense[i]'hi).val)
      (Or.inl (by simp [origToDensePlusOneBase]; have := (dense[i]'hi).isLt; omega)),
      hf9 (origToDensePlusOneBase n m + (dense[i]'hi).val)
      (Or.inl (by simp [origToDensePlusOneBase]; have := (dense[i]'hi).isLt; omega))]
    exact horig8 i hi
  have hcnt10 : ∀ i : Nat, (hi_1 : i < dense.length) →
      (s10.data[denseInDegBase n m + i]?).map Fin.val = some (denseInDegCount g dense (dense[i]'hi_1)) := fun i hi => by
    have hdLen : dense.length ≤ g.vertexCount := denseVertices_length_le g r order hTopo
    dsimp only [n]
    rw [hf10 (denseInDegBase g.vertexCount m + i) (Or.inl (by simp [denseInDegBase]; omega))]
    exact hcnt9 i hi
  obtain ⟨s11, st11, hst11, hr11, hc11, hq11, hm11, hmem11, hcnt11, hiff11, hf11⟩ :=
    run_scatterDenseInSrcPhase input raw workRoom s10 hc10 dense hdNd hdClosed hq10 hdense10 horig10 hcnt10 hstart10
  have hPr : PhasesRun input (dagReachKahnPhases h5) s₀ (Phase.initial s11)
      ((4 * n + 9) + ((8 * m + 5) + (st3 + (st4 + (st5 + (st6 + (st7 +
        (st8 + (st9 + (st10 + (st11 + 1))))))))))) :=
    .cons hr1 (.cons hr2 (.cons hr3 (.cons hr4 (.cons hr5 (.cons hr6 (.cons hr7
      (.cons hr8 (.cons hr9 (.cons hr10 (.cons hr11 .nil))))))))))
  obtain ⟨tFinal, states, hRegsEq, hDataEq, hRunFinal, hTraceFinal, hPeakFinal⟩ := run_pipeline hPr
  have hKeepReg : ∀ regIdx : Fin 16, reg tFinal regIdx = reg s11 regIdx := fun regIdx => by
    change reg tFinal regIdx = reg (Phase.initial s11) regIdx
    exact reg_eq_of_regs_eq hRegsEq regIdx
  have hDataFinal : ∀ idx : Nat, tFinal.data[idx]? = s11.data[idx]? := fun idx => by
    change tFinal.data[idx]? = (Phase.initial s11).data[idx]?
    rw [hDataEq]
  have hPresPre5n : ∀ idx : Nat, idx < 5 * n → s11.data[idx]? = s7.data[idx]? := fun idx hidx => by
    rw [hf11 idx (Or.inl hidx), hf10 idx (Or.inl (by omega)), hf9 idx (Or.inl hidx), hf8 idx (Or.inl hidx)]
  have hPresInStart : ∀ idx : Nat, 6 * n ≤ idx → idx < 7 * n + 1 → s11.data[idx]? = s10.data[idx]? :=
    fun idx hlo hhi => hf11 idx (Or.inr (Or.inl ⟨hlo, hhi⟩))
  refine ⟨tFinal, states, _, order, hlen, hTopo, by omega, hRunFinal, hTraceFinal, ?_,
    ?_, (congrArg Fin.val (hKeepReg r5)).trans hq11, (congrArg Fin.val (hKeepReg r6)).trans hm11,
    denseVertices_length_pos g r order hTopo, denseVertices_length_le g r order hTopo,
    denseReachArcCount_le g dense hdNd, denseVertices_head_eq g r order hTopo,
    ?_, ?_, ?_, fun i hi => (denseVertices_mem_iff g r order hTopo _).mp (List.getElem_mem hi),
    ?_, ?_, ?_, denseVertices_strict_topo g r order hTopo, ?_,
    ⟨rfl, denseInPrefix_length g dense hdNd hdClosed⟩,
    fun i hi => by
      rw [denseInPrefix_succ_lt g (denseVertices g r order hTopo) i hi]; omega,
    fun v pos hge hlt => by rw [hDataFinal]; exact hmem11 v pos hge hlt,
    fun u v => by
      change (inSrcSlice tFinal.data n _ _).count u.val = _
      have heqSlice : inSrcSlice tFinal.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1)) =
          inSrcSlice s11.data n (denseInPrefix g dense v.val) (denseInPrefix g dense (v.val + 1)) := by
        unfold inSrcSlice
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          rw [List.getElem_ofFn, List.getElem_ofFn, hDataFinal]
      rw [heqSlice]; exact hcnt11 u v,
    fun u v => by
      have := hiff11 u v
      simpa only [hDataFinal] using this⟩
  · simpa [footprint, layout16] using hPeakFinal
  · exact ⟨(congrArg Fin.val (hKeepReg rZero)).trans hc11.zero,
      (congrArg Fin.val (hKeepReg rOne)).trans hc11.one,
      (congrArg Fin.val (hKeepReg rN)).trans hc11.nVal,
      (congrArg Fin.val (hKeepReg rM)).trans hc11.mVal,
      (congrArg Fin.val (hKeepReg rRoot)).trans hc11.rootVal⟩
  · intro i hi
    rw [hDataFinal, hPresPre5n (topoOrderBase n m + i) (by simp [topoOrderBase]; omega)]
    exact htopo7 i hi
  · intro v
    rw [hDataFinal, hPresPre5n (markedBase n m + v.val) (by simp [markedBase]; have := v.isLt; omega)]
    exact hmark7 v
  · intro v
    rw [hDataFinal, hPresPre5n (markedBase n m + v.val) (by simp [markedBase]; have := v.isLt; omega),
      hmark7 v, ← g.scanReachability_iff r order hTopo v]
    cases ((g.scanReachability r order hTopo).marked[v.val]?).getD false <;> simp
  · intro i hi
    have hdLen := denseVertices_length_le g r order hTopo
    rw [hDataFinal, hPresPre5n (denseToOrigBase n m + i) (by simp [denseToOrigBase]; omega)]
    exact hdense7 i hi
  · intro i hi
    rw [hDataFinal, hPresPre5n (origToDensePlusOneBase n m + (dense[i]'hi).val)
      (by simp [origToDensePlusOneBase]; have := (dense[i]'hi).isLt; omega)]
    exact horig7 i hi
  · intro v hv
    rw [hDataFinal, hPresPre5n (origToDensePlusOneBase n m + v.val)
      (by simp [origToDensePlusOneBase]; have := v.isLt; omega)]
    exact hzero7 v hv
  · intro i hi
    have hdLen := denseVertices_length_le g r order hTopo
    rw [hDataFinal, hPresInStart (inStartBase n m + i) (by simp [inStartBase]) (by simp [inStartBase]; omega)]
    exact hstart10 i hi

end Pipeline

end PaperB.RamDagReach



