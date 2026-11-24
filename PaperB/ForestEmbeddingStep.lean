module

public import PaperB.ForestReady

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Place this after the supplied declarations in the same module.

This proves the endpoint-conditioned `Embedding` extension. The getter,
selection, and canonical endpoint equations not stated in the excerpt are
explicit hypotheses. In particular, `freshKey` is an allocation contract,
not a consequence of `InstallOK.old_back`. The proof does not assume that
the endpoint is the label of `y`: it derives that equality from
`runHead_semantics` (via `step_request_semantics`) and canonical key
injectivity.
-/

namespace EX24
namespace PreStep

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

theorem step_embedding_of_endpoint
    {H : LabelledQuotient}
    {c : Config H} {s : State H} {F F' : JumpForest}
    {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size}
    {up' : Fin F'.size → Fin F'.size}
    {y : Vertex H} {xs : List (Vertex H)} {r : HeadResult H}
    (E : Embedding c s F rank up (fun v => rank v < rank y))
    (g : Grounded c F s.tables)
    (hstep : step c s rank y xs = some r)
    (h0 : 0 < F.size)
    (forest_eq : F' =
      (if r.installed.allocated then F.appendLeaf r.measured.step.parent else F))
    (oldSize : s.tables.next = F.size)
    (newSize : F'.size = r.state.tables.next)
    (oldDepth : ∀ a : Fin F.size,
      (selectors c s).depth a.val = F.depthOf a.val)
    (newDepth : ∀ a : Fin F'.size,
      (selectors c r.state).depth a.val = F'.depthOf a.val)
    (oldParent : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (newParent : ∀ a : Fin F'.size, (up' a).val = F'.parentOf a.val)
    (z : CanonNode H rank) (k : Option (CutPair H))
    (zKey : (buildProperLossForest H rank).nodeKey? z = k)
    (selectedBack : r.state.tables.back[r.installed.node]? = some k)
    (freshKey : r.installed.allocated = true →
      ∀ n, n < F.size → s.tables.back[n]? ≠ some k)
    (parentBound : r.installed.allocated = true →
      r.measured.step.parent < F.size)
    (appendParentAtEnd : r.installed.allocated = true →
      (F.appendLeaf r.measured.step.parent).parentOf F.size =
        r.measured.step.parent)
    (appendDepthAtEnd : r.installed.allocated = true →
      (F.appendLeaf r.measured.step.parent).depthOf F.size =
        F.depthOf r.measured.step.parent + 1)
    (zParent : ∀ ha : r.installed.allocated = true,
      E.image ⟨r.measured.step.parent, parentBound ha⟩ =
        (buildProperLossForest H rank).parent z)
    (zDepth : r.installed.allocated = true →
      F.depthOf r.measured.step.parent + 1 =
        (buildProperLossForest H rank).depth z)
    (T : TestSpec y xs)
    (rootView : view E 0 = [])
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (readyY : ∀ m, y ≠ H.root → H.hasQuotientArcBool H.root y = false →
      maxByRank rank (preds H y) = some m →
      H.HasQuotientArc m y ∧ Ready (selectors c s) (view E) rank y m xs)
    (requestLast : (decode (view E) r.measured.step).getLast? = k)
    (canonicalLast : (sweepChain H rank y).getLast? =
      (buildProperLossForest H rank).nodeKey? ((buildProperLossForest H rank).label y)) :
    ∃ E' : Embedding c r.state F' rank up' (fun v => rank v < rank y ∨ v = y),
      (∀ (a : Fin F.size) (b : Fin F'.size), b.val = a.val → E'.image b = E.image a) ∧
      (∀ b : Fin F'.size, b.val = r.installed.node → E'.image b = z) := by
  have sem := step_request_semantics hstep (view E) T rootView rankArc readyY
  have zLabel : z = (buildProperLossForest H rank).label y := by
    apply buildProperLossForest_nodeKey?_inj H rank
    calc
      _ = k := zKey
      _ = (decode (view E) r.measured.step).getLast? := requestLast.symm
      _ = (sweepChain H rank y).getLast? :=
        congrArg (fun l : List (CutPair H) => l.getLast?) sem
      _ = _ := canonicalLast

  have spec := step_spec g hstep
  have ok := spec.1
  have size_eq : F'.size = F.size + r.installed.delta := by
    rw [newSize, spec.2.1, oldSize]
  have size_le : F.size ≤ F'.size := by omega
  have node_lt : r.installed.node < F'.size := by
    rw [newSize]
    exact ok.node_lt
  have back_old (n : Nat) (hn : n < F.size) :
      r.state.tables.back[n]? = s.tables.back[n]? :=
    ok.old_back n (by simpa only [oldSize] using hn)
  have write_y : (selectors c r.state).label y = r.installed.node := by
    change (r.labels[c.vertexIndex y]?).getD 0 = r.installed.node
    rw [(step_parts hstep).2.2.2 (c.vertexIndex y), if_pos rfl] <;> rfl

  have grown (ha : r.installed.allocated = true) :
      F' = F.appendLeaf r.measured.step.parent := by
    simpa [ha] using forest_eq
  have parent_old (n : Nat) (hn : n < F.size) :
      F'.parentOf n = F.parentOf n := by
    rw [forest_eq]
    split
    · exact parentOf_appendLeaf_old F _ hn
    · rfl
  have depth_old (n : Nat) (hn : n < F.size) :
      F'.depthOf n = F.depthOf n := by
    rw [forest_eq]
    split
    · exact depthOf_appendLeaf_old F _ hn
    · rfl

  have allocated_of_new (b : Fin F'.size) (hb : ¬ b.val < F.size) :
      r.installed.allocated = true := by
    cases ha : r.installed.allocated with
    | false =>
        have hd : r.installed.delta = 0 := by simp [Installed.delta, ha]
        have hl := b.isLt
        omega
    | true => rfl
  have index_new (b : Fin F'.size) (hb : ¬ b.val < F.size) :
      b.val = F.size := by
    have ha := allocated_of_new b hb
    have hd : r.installed.delta = 1 := by simp [Installed.delta, ha]
    have hl := b.isLt
    omega
  have node_at_end (ha : r.installed.allocated = true) :
      r.installed.node = F.size := by
    have hn : ¬ r.installed.node < F.size := by
      intro hl
      exact freshKey ha _ hl ((back_old _ hl).symm.trans selectedBack)
    exact index_new ⟨r.installed.node, node_lt⟩ hn
  have image_ne_z (a : Fin F.size) (ha : r.installed.allocated = true) :
      E.image a ≠ z := by
    intro he
    apply freshKey ha a.val a.isLt
    rw [E.back_eq a, he, zKey]

  let img : Fin F'.size → CanonNode H rank := fun b =>
    if hb : b.val < F.size then E.image ⟨b.val, hb⟩ else z
  have img_old (b : Fin F'.size) (hb : b.val < F.size) :
      img b = E.image ⟨b.val, hb⟩ := by
    simp only [img, dif_pos hb]
  have img_new (b : Fin F'.size) (hb : ¬ b.val < F.size) :
      img b = z := by
    simp only [img, dif_neg hb]
  have img_inj : Function.Injective img := by
    intro a b hab
    by_cases ha : a.val < F.size
    · by_cases hb : b.val < F.size
      · rw [img_old a ha, img_old b hb] at hab
        exact Fin.ext (congrArg (fun i : Fin F.size => i.val) (E.injective hab))
      · rw [img_old a ha, img_new b hb] at hab
        exact (image_ne_z ⟨a.val, ha⟩ (allocated_of_new b hb) hab).elim
    · by_cases hb : b.val < F.size
      · rw [img_new a ha, img_old b hb] at hab
        exact (image_ne_z ⟨b.val, hb⟩ (allocated_of_new a ha) hab.symm).elim
      · exact Fin.ext ((index_new a ha).trans (index_new b hb).symm)

  have img_installed (b : Fin F'.size) (hb : b.val = r.installed.node) :
      img b = z := by
    by_cases hl : b.val < F.size
    · rw [img_old b hl]
      apply buildProperLossForest_nodeKey?_inj H rank
      rw [zKey]
      have hnew : r.state.tables.back[b.val]? = some k := by
        rw [hb, selectedBack]
      exact Option.some.inj
        ((E.back_eq ⟨b.val, hl⟩).symm.trans ((back_old b.val hl).symm.trans hnew))
    · exact img_new b hl

  have labelBound : ∀ v, (rank v < rank y ∨ v = y) →
      (selectors c r.state).label v < F'.size := by
    intro v hv
    rcases hv with hv | hv
    · have hne : v ≠ y := by
        intro he
        subst v
        exact (Nat.lt_irrefl _) hv
      rw [previous_label hstep hne]
      exact Nat.lt_of_lt_of_le (E.label_lt v hv) size_le
    · subst v
      rw [write_y]
      exact node_lt

  let E' : Embedding c r.state F' rank up' (fun v => rank v < rank y ∨ v = y) := {
    image := img
    injective := img_inj
    root_eq := by
      intro h
      exact (img_old ⟨0, h⟩ h0).trans (E.root_eq h0)
    label_lt := labelBound
    label_eq := by
      intro v hv
      rcases hv with hv | hv
      · have hne : v ≠ y := by
          intro he
          subst v
          exact (Nat.lt_irrefl _) hv
        let b : Fin F'.size := ⟨(selectors c r.state).label v, labelBound v (Or.inl hv)⟩
        change img b = (buildProperLossForest H rank).label v
        have hval : b.val = (selectors c s).label v := previous_label hstep hne
        have hb : b.val < F.size := by rw [hval]; exact E.label_lt v hv
        exact (img_old b hb).trans
          ((congrArg E.image (Fin.ext hval)).trans (E.label_eq v hv))
      · subst v
        exact (img_installed _ write_y).trans zLabel
    depth_eq := by
      intro b
      by_cases hb : b.val < F.size
      · calc
          _ = F'.depthOf b.val := newDepth b
          _ = F.depthOf b.val := depth_old b.val hb
          _ = (selectors c s).depth b.val := (oldDepth ⟨b.val, hb⟩).symm
          _ = (buildProperLossForest H rank).depth (E.image ⟨b.val, hb⟩) :=
            E.depth_eq ⟨b.val, hb⟩
          _ = _ := congrArg ((buildProperLossForest H rank).depth) (img_old b hb).symm
      · have ha := allocated_of_new b hb
        calc
          _ = F'.depthOf b.val := newDepth b
          _ = (F.appendLeaf r.measured.step.parent).depthOf b.val :=
            congrArg (fun G : JumpForest => G.depthOf b.val) (grown ha)
          _ = (F.appendLeaf r.measured.step.parent).depthOf F.size :=
            congrArg (fun n => (F.appendLeaf r.measured.step.parent).depthOf n) (index_new b hb)
          _ = F.depthOf r.measured.step.parent + 1 := appendDepthAtEnd ha
          _ = (buildProperLossForest H rank).depth z := zDepth ha
          _ = _ := congrArg ((buildProperLossForest H rank).depth) (img_new b hb).symm
    parent_eq := by
      intro b
      by_cases hb : b.val < F.size
      · let a : Fin F.size := ⟨b.val, hb⟩
        have hpar : (up' b).val = (up a).val :=
          (newParent b).trans ((parent_old b.val hb).trans (oldParent a).symm)
        have hl : (up' b).val < F.size := by rw [hpar]; exact (up a).isLt
        calc
          img (up' b) = E.image ⟨(up' b).val, hl⟩ := img_old (up' b) hl
          _ = E.image (up a) := congrArg E.image (Fin.ext hpar)
          _ = (buildProperLossForest H rank).parent (E.image a) := E.parent_eq a
          _ = _ := congrArg ((buildProperLossForest H rank).parent) (img_old b hb).symm
      · have ha := allocated_of_new b hb
        have hpar : (up' b).val = r.measured.step.parent := calc
          _ = F'.parentOf b.val := newParent b
          _ = (F.appendLeaf r.measured.step.parent).parentOf b.val :=
            congrArg (fun G : JumpForest => G.parentOf b.val) (grown ha)
          _ = (F.appendLeaf r.measured.step.parent).parentOf F.size :=
            congrArg (fun n => (F.appendLeaf r.measured.step.parent).parentOf n)
              (index_new b hb)
          _ = _ := appendParentAtEnd ha
        have hl : (up' b).val < F.size := by rw [hpar]; exact parentBound ha
        calc
          img (up' b) = E.image ⟨(up' b).val, hl⟩ := img_old (up' b) hl
          _ = E.image ⟨r.measured.step.parent, parentBound ha⟩ :=
            congrArg E.image (Fin.ext hpar)
          _ = (buildProperLossForest H rank).parent z := zParent ha
          _ = _ := congrArg ((buildProperLossForest H rank).parent) (img_new b hb).symm
    back_eq := by
      intro b
      by_cases hb : b.val < F.size
      · rw [img_old b hb]
        exact (back_old b.val hb).trans (E.back_eq ⟨b.val, hb⟩)
      · have ha := allocated_of_new b hb
        have hval : b.val = r.installed.node := (index_new b hb).trans (node_at_end ha).symm
        rw [img_new b hb, hval, selectedBack, zKey]
  }
  refine ⟨E', ?_, ?_⟩
  · intro a b hval
    have hb : b.val < F.size := by rw [hval]; exact a.isLt
    exact (img_old b hb).trans (congrArg E.image (Fin.ext hval))
  · exact img_installed

end PreStep
end EX24
