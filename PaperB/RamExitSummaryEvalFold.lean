module

public import PaperB.RamExitSummaryCopy

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute
open PaperB.JumpForest

/-- A jump from positive depth in a valid forest decreases depth strictly. -/
theorem validJumpForest_jump_depth_lt {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) (hPos : 0 < F.depthOf u) :
    F.depthOf (F.jumpOf u) < F.depthOf u := by
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  have huPos : 0 < u := by
    by_cases hZero : u = 0
    · rw [hZero, inv.root_depth] at hPos
      omega
    · omega
  exact inv.depth_jump_lt huPos hu

/-- The actual stored record picks a live endpoint strictly nearer the root. -/
theorem eval_selected_live_down {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {u d : Nat} (hu : live u) (hCmp : d < F.depthOf u) :
    let mv := selectAtDepth F.depthOf d (ref u)
    live mv.dst ∧ F.depthOf mv.dst < F.depthOf u := by
  by_cases h : d ≤ F.depthOf (ref u).jump
  · rw [show selectAtDepth F.depthOf d (ref u) = (ref u).select .jump by
          unfold selectAtDepth; rw [ite_eq_left h]]
    simpa only [Stored.select, ok.jump_eq u hu] using
      And.intro (ok.jump_live u hu)
        (validJumpForest_jump_depth_lt valid (ok.live_lt u hu) (by omega))
  · simpa only [selectAtDepth, ite_eq_right h, Stored.select, ok.parent_eq u hu] using
      And.intro (ok.parent_live u hu) (ok.parent_down u hu (by omega))

/-- The value evaluator replaces map composition by applying each selected map.
The recursive measure is the remaining distance to the requested depth. -/
def evalAtDepth {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    (d u : Nat) (hu : live u) (xs : Values) : Values × Nat :=
  if h : d < F.depthOf u then
    let mv := selectAtDepth F.depthOf d (ref u)
    let next := evalAtDepth valid ok d mv.dst
      (eval_selected_live_down valid ok hu h).1 (Map.eval mv.map xs)
    (next.1, 1 + next.2)
  else (xs, 0)
termination_by F.depthOf u - d
decreasing_by
  have hd := (eval_selected_live_down valid ok hu h).2
  omega

private theorem evalAtDepth_eq_foldAux {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live) (d : Nat) :
    ∀ (rem u : Nat) (hu : live u), F.depthOf u - d = rem →
      ∀ (budget steps : Nat) (acc : Map) (xs : Values), rem ≤ budget - steps →
        let ev := evalAtDepth valid ok d u hu (Map.eval acc xs)
        let folded := foldFusedAux F.depthOf ref d budget u acc steps
        ev.1 = Map.eval folded.composed xs ∧ steps + ev.2 = folded.steps := by
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
    intro u hu hRem budget steps acc xs hBudget
    let folded := foldFusedAux F.depthOf ref d budget u acc steps
    change (evalAtDepth valid ok d u hu (Map.eval acc xs)).1 = Map.eval folded.composed xs ∧
      steps + (evalAtDepth valid ok d u hu (Map.eval acc xs)).2 = folded.steps
    by_cases hCmp : d < F.depthOf u
    · let mv := selectAtDepth F.depthOf d (ref u)
      have hMove := eval_selected_live_down valid ok hu hCmp
      have hGuard : steps < budget ∧ d < F.depthOf u := ⟨by omega, hCmp⟩
      let rest := evalAtDepth valid ok d mv.dst hMove.1 (Map.eval mv.map (Map.eval acc xs))
      have hEval : evalAtDepth valid ok d u hu (Map.eval acc xs) = (rest.1, 1 + rest.2) := by
        rw [evalAtDepth.eq_1, dite_eq_left hCmp]
      have hFold : folded = foldFusedAux F.depthOf ref d budget mv.dst
          (Map.compose acc mv.map) (steps + 1) := by
        have hr := foldFusedAux_registers F.depthOf ref d budget ⟨u, acc, steps⟩
        change folded = _ at hr
        exact hr.trans (ite_eq_left hGuard)
      have hDown : F.depthOf mv.dst < F.depthOf u := hMove.2
      obtain ⟨hVal, hCost⟩ :=
        ih (F.depthOf mv.dst - d) (by omega) mv.dst hMove.1 rfl budget (steps + 1)
          (Map.compose acc mv.map) xs (by omega)
      rw [eval_compose] at hVal hCost
      change rest.1 = _ at hVal
      change steps + 1 + rest.2 = _ at hCost
      rw [hEval, hFold]
      exact ⟨hVal, by simpa only [Nat.add_assoc] using hCost⟩
    · have hFold : folded = ⟨u, acc, steps⟩ := by
        have hr := foldFusedAux_registers F.depthOf ref d budget ⟨u, acc, steps⟩
        change folded = _ at hr
        exact hr.trans (ite_eq_right (fun h => hCmp h.2))
      rw [evalAtDepth.eq_1, dite_eq_right hCmp, hFold]
      exact ⟨rfl, Nat.add_zero _⟩

theorem evalAtDepth_spec {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {u d : Nat} (hu : live u) (xs : Values) :
    evalAtDepth valid ok d u hu xs =
      (Map.eval (foldFused F ref u d).composed xs, (foldFused F ref u d).steps) := by
  obtain ⟨hVal, hSteps⟩ := evalAtDepth_eq_foldAux valid ok d
    (F.depthOf u - d) u hu rfl (F.depthOf u - d) 0 Map.identity xs (by omega)
  rw [Map.eval_identity] at hVal hSteps
  exact Prod.ext hVal (by simpa only [foldFused, Nat.zero_add] using hSteps)

theorem foldFused_step_values {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {u d : Nat} (hu : live u) (hCmp : d < F.depthOf u) (xs : Values) :
    let mv := selectAtDepth F.depthOf d (ref u)
    Map.eval (foldFused F ref u d).composed xs =
      Map.eval (foldFused F ref mv.dst d).composed (Map.eval mv.map xs) ∧
    (foldFused F ref u d).steps = 1 + (foldFused F ref mv.dst d).steps := by
  let mv := selectAtDepth F.depthOf d (ref u)
  have hn : live mv.dst := (eval_selected_live_down valid ok hu hCmp).1
  have he := evalAtDepth_spec valid ok hu (d := d) xs
  rw [evalAtDepth.eq_1, dite_eq_left hCmp] at he
  let next := evalAtDepth valid ok d mv.dst hn (Map.eval mv.map xs)
  change (next.1, 1 + next.2) = _ at he
  dsimp only [next] at he
  rw [evalAtDepth_spec valid ok hn] at he
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

theorem foldFused_stop_values {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {u d : Nat} (hu : live u) (hCmp : ¬ d < F.depthOf u) (xs : Values) :
    Map.eval (foldFused F ref u d).composed xs = xs ∧
      (foldFused F ref u d).steps = 0 := by
  have he := evalAtDepth_spec valid ok hu (d := d) xs
  rw [evalAtDepth.eq_1, dite_eq_right hCmp] at he
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

end PaperB.RamProgram.ExitSummaryBuild
