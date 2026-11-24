module

public import PaperB.ForestEmbeddingStep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Endpoint facts for the measured forest step and its installation. -/

set_option autoImplicit false

namespace EX24
namespace PreStep

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

noncomputable section

theorem occupied_depth_eq
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} (g : Grounded c F s.tables) (a : Fin F.size) :
    (selectors c s).depth a.val = F.depthOf a.val := by
  change (readRecordWords c.region s.tables.mem a.val).1.depth = F.depthOf a.val
  have hl := g.layout
  first
  | exact hl.slot_depth a.val a.isLt
  | exact hl.slot_depth a.isLt
  | exact hl.slot_depth (u := a.val) a.isLt
  | change readWord s.tables.mem (c.region.depthAddr a.val) = F.depthOf a.val
    first
    | exact hl.slot_depth a.val a.isLt
    | exact hl.slot_depth a.isLt
    | exact?

private theorem init_slot_val (a : Fin JumpForest.init.size) : a.val = 0 := by
  have ha := a.isLt
  change a.val < 1 at ha
  omega

/-- The initial occupied interval is the singleton containing the artificial root. -/
def initialUp (_ : Fin JumpForest.init.size) : Fin JumpForest.init.size :=
  ⟨0, by decide⟩

theorem initialUp_val (a : Fin JumpForest.init.size) :
    (initialUp a).val = JumpForest.init.parentOf a.val := by
  rw [init_slot_val a]
  rfl

/-- No vertex labels are required to be correct before the first head. -/
def initial_embedding
    {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    {mem : Array Nat} (layout : JumpWordLayout c.region JumpForest.init mem)
    (vertexCapacity : Nat) :
    Embedding c (initial c mem vertexCapacity) JumpForest.init rank
      initialUp (fun _ => False) := by
  have g : Grounded c JumpForest.init (initial c mem vertexCapacity).tables :=
    initial_grounded c layout rfl vertexCapacity
  refine
    { image := fun _ => (buildProperLossForest H rank).rootNode
      injective := ?_
      root_eq := fun _ => rfl
      label_lt := fun _ hv => hv.elim
      label_eq := fun _ hv => hv.elim
      depth_eq := ?_
      parent_eq := fun _ => (buildProperLossForest_parent_root H rank).symm
      back_eq := ?_ }
  · intro a b _
    exact Fin.ext ((init_slot_val a).trans (init_slot_val b).symm)
  · intro a
    rw [occupied_depth_eq g a, init_slot_val a, buildProperLossForest_depth_root] <;>
      rfl
  · intro a
    rw [init_slot_val a, buildProperLossForest_nodeKey?_root]
    exact g.zero

/-- An empty dictionary slot rules out the key in the entire old reverse table. -/
theorem empty_slot_key_absent
    {H : LabelledQuotient} {c : Config H} {F : JumpForest} {t : Tables H}
    (g : Grounded c F t) {q : CutPair H} {i : Nat}
    (hit : (PairLookup.lookup c.dict (c.code q)).1 = some i)
    (empty : t.slotAt i = 0) :
    ∀ (n : Nat), t.back[n]? ≠ some (some q) := by
  intro n hn
  obtain ⟨_, hn0, j, hj, hslot⟩ := g.backward n q hn
  have hji : j = i := Option.some.inj (hj.symm.trans hit)
  subst j
  exact hn0 (hslot.symm.trans empty)

/--
The `none` request keeps its measured parent. A `some q` request either
appends at the old size or selects the occupied dictionary slot for `q`.
The latter branch preserves the entire table, including the node's old parent.
-/
theorem step_install_cases
    {H : LabelledQuotient} {c : Config H} {s : State H} {F : JumpForest}
    {rank : Vertex H → Nat} {y : Vertex H} {xs : List (Vertex H)}
    {r : HeadResult H}
    (g : Grounded c F s.tables) (hstep : step c s rank y xs = some r) :
    r.measured.step.parent < F.size ∧
    (match r.measured.step.newPair with
    | none =>
        r.installed.allocated = false ∧
        r.installed.node = r.measured.step.parent ∧
        r.installed.tables = s.tables
    | some q =>
        ∃ i, (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
          ((r.installed.allocated = true ∧
            s.tables.slotAt i = 0 ∧
            r.installed.node = F.size ∧
            r.installed.tables.back[r.installed.node]? = some (some q) ∧
            (∀ (n : Nat), s.tables.back[n]? ≠ some (some q))) ∨
           (r.installed.allocated = false ∧
            s.tables.slotAt i ≠ 0 ∧
            r.installed.node = s.tables.slotAt i ∧
            r.installed.tables = s.tables ∧
            s.tables.back[r.installed.node]? = some (some q)))) := by
  have hinstall := (step_parts hstep).2.1
  have hp : r.measured.step.parent < s.tables.next := by
    by_cases h : r.measured.step.parent < s.tables.next
    · exact h
    · simp [install, h] at hinstall
  refine ⟨by simpa only [g.size_eq] using hp, ?_⟩
  cases hq : r.measured.step.newPair with
  | none =>
      simp only [install, if_pos hp, hq] at hinstall
      have he := Option.some.inj hinstall
      rw [← he]
      exact ⟨rfl, rfl, rfl⟩
  | some q =>
      cases hk : (PairLookup.lookup c.dict (c.code q)).1 with
      | none => simp [install, hp, hq, hk] at hinstall
      | some i =>
          obtain ⟨hi, hcode⟩ :=
            (PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted i).mp hk
          have hb : i < s.tables.slots.size := by
            simpa only [g.slot_size] using hi
          refine ⟨i, hk, ?_⟩
          by_cases hz : s.tables.slotAt i = 0
          · by_cases hn : s.tables.next < s.tables.back.size
            · simp [install, hp, hq, hk, hb, hz, hn] at hinstall
              left
              rw [← hinstall]
              refine ⟨rfl, hz, g.size_eq.symm, ?_, empty_slot_key_absent g hk hz⟩
              change
                (s.tables.back.set s.tables.next (some q) hn)[s.tables.next]? =
                  some (some q)
              have hidx : s.tables.next <
                  (s.tables.back.set s.tables.next (some q) hn).size := by
                simpa only [Array.size_set] using hn
              rw [getElem?_def, dif_pos hidx]
              first
              | simpa only [Array.getElem_set_same]
              | simp [Array.getElem_set, hn]
            · simp [install, hp, hq, hk, hb, hz, hn] at hinstall
          · simp [install, hp, hq, hk, hb, hz] at hinstall
            obtain ⟨q', hq', hback⟩ := g.forward i hz
            obtain ⟨_, hcode'⟩ :=
              (PairLookup.lookup_eq_some_iff c.dict (c.code q') c.sorted i).mp hq'
            have hsame : q' = q := c.code_inj (hcode'.symm.trans hcode)
            subst q'
            right
            rw [← hinstall]
            exact ⟨rfl, hz, rfl, rfl, hback⟩

section Endpoint

variable {H : LabelledQuotient} {c : Config H} {s : State H}
variable {F : JumpForest} {rank : Vertex H → Nat}
variable {up : Fin F.size → Fin F.size}
variable {y : Vertex H} {xs : List (Vertex H)} {r : HeadResult H}

/-- The selected key is the carried parent's key or the actual requested cut key. -/
def selectedEndpointKey
    (E : Embedding c s F rank up (fun v => rank v < rank y))
    (g : Grounded c F s.tables) (hstep : step c s rank y xs = some r) :
    Option (CutPair H) :=
  match r.measured.step.newPair with
  | none =>
      (buildProperLossForest H rank).nodeKey?
        (E.image ⟨r.measured.step.parent, (step_install_cases g hstep).1⟩)
  | some q => some q

theorem step_selected_key_facts
    (E : Embedding c s F rank up (fun v => rank v < rank y))
    (g : Grounded c F s.tables) (hstep : step c s rank y xs = some r) :
    r.state.tables.back[r.installed.node]? = some (selectedEndpointKey E g hstep) ∧
    (r.installed.allocated = true →
      r.installed.node = F.size ∧
      ∀ (n : Nat), s.tables.back[n]? ≠ some (selectedEndpointKey E g hstep)) ∧
    (r.installed.allocated = false →
      ∃ hn : r.installed.node < F.size,
        (buildProperLossForest H rank).nodeKey? (E.image ⟨r.installed.node, hn⟩) =
          selectedEndpointKey E g hstep) := by
  have hs := step_install_cases g hstep
  have spec := step_spec g hstep
  have hold (ha : r.installed.allocated = false)
      (hb : r.state.tables.back[r.installed.node]? = some (selectedEndpointKey E g hstep)) :
      ∃ hn : r.installed.node < F.size,
        (buildProperLossForest H rank).nodeKey? (E.image ⟨r.installed.node, hn⟩) =
          selectedEndpointKey E g hstep := by
    have hsize : r.state.tables.next = F.size := by
      rw [spec.2.1, g.size_eq]
      simp [Installed.delta, ha]
    have hn : r.installed.node < r.state.tables.next := spec.1.node_lt
    rw [hsize] at hn
    have hback := spec.1.old_back r.installed.node (by simpa only [g.size_eq] using hn)
    exact ⟨hn, Option.some.inj
      ((E.back_eq ⟨r.installed.node, hn⟩).symm.trans (hback.symm.trans hb))⟩
  have hsel := hs.2
  cases hq : r.measured.step.newPair with
  | none =>
      simp only [hq] at hsel
      obtain ⟨ha, hn, ht⟩ := hsel
      have hb : r.state.tables.back[r.installed.node]? =
          some (selectedEndpointKey E g hstep) := by
        change r.installed.tables.back[r.installed.node]? = _
        rw [ht, hn]
        simpa only [selectedEndpointKey, hq] using
          E.back_eq ⟨r.measured.step.parent, hs.1⟩
      refine ⟨hb, ?_, fun h => hold h hb⟩
      intro h
      rw [ha] at h
      cases h
  | some q =>
      simp only [hq] at hsel
      obtain ⟨i, _, hg | hr⟩ := hsel
      · obtain ⟨_, _, hn, hback, hfresh⟩ := hg
        have hb : r.state.tables.back[r.installed.node]? =
            some (selectedEndpointKey E g hstep) := by
          change r.installed.tables.back[r.installed.node]? = _
          simpa only [selectedEndpointKey, hq] using hback
        refine ⟨hb, ?_, fun h => hold h hb⟩
        intro _
        exact ⟨hn, by simpa only [selectedEndpointKey, hq] using hfresh⟩
      · obtain ⟨ha, _, _, ht, hback⟩ := hr
        have hb : r.state.tables.back[r.installed.node]? =
            some (selectedEndpointKey E g hstep) := by
          change r.installed.tables.back[r.installed.node]? = _
          rw [ht]
          simpa only [selectedEndpointKey, hq] using hback
        refine ⟨hb, ?_, fun h => hold h hb⟩
        intro h
        rw [ha] at h
        cases h

private theorem decode_request (V : Nat → List (CutPair H))
    (hstep : step c s rank y xs = some r) :
    decode V r.measured.step =
      V r.measured.step.parent ++ r.measured.step.newPair.toList := by
  rw [(step_parts hstep).1]
  by_cases hy : y = H.root
  · simp only [ForestHead.runHead, if_pos hy]
    exact decode_finish V 0 none
  · by_cases hr : H.hasQuotientArcBool H.root y = true
    · simp only [ForestHead.runHead, if_neg hy, if_pos hr]
      exact decode_finish V 0 none
    · cases hm : maxByRank rank (preds H y) with
      | none =>
          simp only [ForestHead.runHead, if_neg hy, if_neg hr, hm]
          exact decode_finish V 0 none
      | some m =>
          simp only [ForestHead.runHead, if_neg hy, if_neg hr, hm]
          exact decode_finish V
            (nodeAt (selectors c s) ((selectors c s).label m)
              (measuredLog (probe (selectors c s) xs m)
                ((selectors c s).depth ((selectors c s).label m) + 1)).cut)
            (candidatePairOfPreds H (preds H y))

private theorem getLast?_snoc {α : Type} (l : List α) (q : α) :
    (l ++ [q]).getLast? = some q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l => exact ih

private theorem take_length_snoc {α : Type} (l : List α) (q : α) :
    (l ++ [q]).take l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change a :: (l ++ [q]).take l.length = a :: l
      exact congrArg (List.cons a) ih

/-- The last key of a full canonical chain is the node's key. -/
private theorem canonical_chain_last
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (a : CanonNode H rank) :
    ((buildProperLossForest H rank).nodeChain a).getLast? =
      (buildProperLossForest H rank).nodeKey? a := by
  rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat]
  exact getLast?_parentKeyChain rankArc flat ((buildProperLossForest H rank).nodeKey? a)

/--
The endpoint inputs to `step_embedding_of_endpoint`, expressed using the
canonical label. On reuse, the endpoint is already in the old embedding;
only allocation identifies the measured parent with a new node's parent.
-/
structure StepEndpointFacts
    (E : Embedding c s F rank up (fun v => rank v < rank y))
    (r : HeadResult H) : Prop where
  parent_lt : r.measured.step.parent < F.size
  request_last :
    (decode (view E) r.measured.step).getLast? =
      (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y)
  selected_back :
    r.state.tables.back[r.installed.node]? =
      some ((buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y))
  allocated : r.installed.allocated = true →
    r.installed.node = F.size ∧
    (∀ (n : Nat), s.tables.back[n]? ≠
      some ((buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y))) ∧
    E.image ⟨r.measured.step.parent, parent_lt⟩ =
      (buildProperLossForest H rank).parent ((buildProperLossForest H rank).label y) ∧
    F.depthOf r.measured.step.parent + 1 =
      (buildProperLossForest H rank).depth ((buildProperLossForest H rank).label y)
  reused : r.installed.allocated = false →
    ∃ hn : r.installed.node < F.size,
      E.image ⟨r.installed.node, hn⟩ = (buildProperLossForest H rank).label y

/-- Use `later_head_semantics` for `sem`; no selection or freshness hypothesis is needed. -/
theorem step_endpoint_facts
    (E : Embedding c s F rank up (fun v => rank v < rank y))
    (g : Grounded c F s.tables) (hstep : step c s rank y xs = some r)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat) (L : CanonicalLaws H rank)
    (sem : decode (view E) r.measured.step = sweepChain H rank y) :
    StepEndpointFacts E r := by
  let C := buildProperLossForest H rank
  let z := C.label y
  have hs := step_install_cases g hstep
  let p : Fin F.size := ⟨r.measured.step.parent, hs.1⟩
  have hpview : view E r.measured.step.parent = C.nodeChain (E.image p) := by
    simp [view, hs.1]
    change C.nodeChain (E.image p) = C.nodeChain (E.image p)
    rfl
  have hdecode := decode_request (view E) hstep
  obtain ⟨hback, halloc, hold⟩ := step_selected_key_facts E g hstep
  have hrequest :
      (decode (view E) r.measured.step).getLast? = selectedEndpointKey E g hstep := by
    rw [hdecode]
    cases hq : r.measured.step.newPair with
    | none =>
        simp only [hq, Option.toList, List.append_nil, selectedEndpointKey]
        rw [hpview]
        exact canonical_chain_last rankArc flat (E.image p)
    | some q =>
        simpa only [hq, Option.toList, selectedEndpointKey] using
          getLast?_snoc (view E r.measured.step.parent) q
  have hsweep : sweepChain H rank y = C.nodeChain z :=
    buildProperLossForest_sweepChain_eq_nodeChain rankArc distinctRanks flat y
  have hlast : (decode (view E) r.measured.step).getLast? = C.nodeKey? z :=
    (congrArg (fun l : List (CutPair H) => l.getLast?) (sem.trans hsweep)).trans
      (canonical_chain_last rankArc flat z)
  have hkey : selectedEndpointKey E g hstep = C.nodeKey? z :=
    hrequest.symm.trans hlast
  refine ⟨hs.1, hlast, hback.trans (congrArg some hkey), ?_, ?_⟩
  · intro ha
    obtain ⟨hend, hfresh⟩ := halloc ha
    have hnew : ∃ q, r.measured.step.newPair = some q := by
      cases hq : r.measured.step.newPair with
      | none =>
          have hsel := hs.2
          simp only [hq] at hsel
          have hfalse := hsel.1
          rw [ha] at hfalse
          cases hfalse
      | some q => exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hnew
    have hchain : view E r.measured.step.parent ++ [q] = C.nodeChain z := by
      simpa only [hdecode, hq, Option.toList] using sem.trans hsweep
    have hparentChain : C.nodeChain (C.parent z) = C.nodeChain (E.image p) := calc
      _ = (C.nodeChain z).take ((C.nodeChain z).length - 1) := L.parent_take z
      _ = (view E r.measured.step.parent ++ [q]).take
            (view E r.measured.step.parent).length := by
              rw [← hchain]
              simp
      _ = view E r.measured.step.parent := take_length_snoc _ _
      _ = _ := hpview
    have hparent : E.image p = C.parent z := by
      apply buildProperLossForest_nodeKey?_inj H rank
      exact (canonical_chain_last rankArc flat (E.image p)).symm.trans
        ((congrArg (fun l : List (CutPair H) => l.getLast?) hparentChain.symm).trans
          (canonical_chain_last rankArc flat (C.parent z)))
    have hreal : C.nodeKey? z = some q := by
      simpa only [selectedEndpointKey, hq] using hkey.symm
    refine ⟨hend, ?_, hparent, ?_⟩
    · simpa only [hkey] using hfresh
    · calc
        F.depthOf r.measured.step.parent + 1 =
            (selectors c s).depth p.val + 1 :=
          congrArg (fun d : Nat => d + 1) (occupied_depth_eq g p).symm
        _ = C.depth (E.image p) + 1 :=
          congrArg (fun d : Nat => d + 1) (E.depth_eq p)
        _ = C.depth (C.parent z) + 1 := by rw [hparent]
        _ = C.depth z := (buildProperLossForest_depth_real rankArc flat hreal).symm
  · intro ha
    obtain ⟨hn, hk⟩ := hold ha
    exact ⟨hn, buildProperLossForest_nodeKey?_inj H rank (hk.trans hkey)⟩

end Endpoint
end

end PreStep
end EX24
