module

public import PaperB.SiblingBlocks

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Finite sibling key indexing

Toolchain (`lean-toolchain`): `leanprover/lean4:v4.35.0-rc3`.

The encoder and decoder identify actual sibling block keys with positions
in `siblingBlockKeys`. No complexity claim is made.
-/

namespace PaperB.Digraph

private theorem nodup_fin_id_ofFn (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup := by
  change List.Pairwise (fun a b : Fin n => a ≠ b)
    (List.ofFn (fun i : Fin n => i))
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  have hval : i = j := by
    simpa only [List.getElem_ofFn] using
      (congrArg (fun a : Fin n => a.val) heq)
  exact (Nat.ne_of_lt hij) hval

private theorem nodup_filterMap_of_keyVal
    {α β : Type} {f : α → Option β} (keyVal : β → α)
    (hval : ∀ (a : α) (b : β), f a = some b → keyVal b = a)
    {xs : List α} (hxs : xs.Nodup) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons a tail ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hxs
      have htail : (tail.filterMap f).Nodup := ih hnodup
      cases hfa : f a with
      | none =>
          simpa only [List.filterMap_cons, hfa] using htail
      | some b =>
          simp only [List.filterMap_cons, hfa]
          apply List.nodup_cons.mpr
          refine ⟨?_, htail⟩
          intro hb
          obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
          have haa' : a = a' := (hval a b hfa).symm.trans (hval a' b hfa')
          exact hnot (haa'.symm ▸ ha')

/-- Each retained key has the original ID of the input that produced it. -/
theorem siblingBlockKeys_nodup
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) :
    (siblingBlockKeys g r d parent).Nodup := by
  classical
  unfold siblingBlockKeys
  refine nodup_filterMap_of_keyVal
    (fun key : SiblingBlockKey g r d parent => key.val)
    ?_ (nodup_fin_id_ofFn g.vertexCount)
  intro a key hsome
  by_cases ha : a = d ∨ (parent a = d ∧ a ≠ d ∧ g.InitiallyReachable r a)
  · rw [dite_eq_left ha] at hsome
    have hkey : (⟨a, ha⟩ : SiblingBlockKey g r d parent) = key :=
      Option.some.inj hsome
    exact (congrArg (fun k : SiblingBlockKey g r d parent => k.val) hkey).symm
  · rw [dite_eq_right ha] at hsome
    cases hsome

/-- Decode an index by looking up the key at that position. -/
noncomputable def decodeSiblingBlockKey
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (i : Fin (siblingBlockKeys g r d parent).length) :
    SiblingBlockKey g r d parent :=
  (siblingBlockKeys g r d parent).get i

private theorem exists_siblingBlockKey_index
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (key : SiblingBlockKey g r d parent) :
    ∃ i : Fin (siblingBlockKeys g r d parent).length,
      decodeSiblingBlockKey g r d parent i = key := by
  obtain ⟨i, hi, hkey⟩ :=
    List.mem_iff_getElem.mp (mem_siblingBlockKeys key)
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa only [decodeSiblingBlockKey, List.get_eq_getElem] using hkey

/-- Encode a key by choosing a position at which it occurs. -/
noncomputable def encodeSiblingBlockKey
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (key : SiblingBlockKey g r d parent) :
    Fin (siblingBlockKeys g r d parent).length :=
  Classical.choose (exists_siblingBlockKey_index g r d parent key)

@[simp] theorem decodeSiblingBlockKey_encodeSiblingBlockKey
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (key : SiblingBlockKey g r d parent) :
    decodeSiblingBlockKey g r d parent
      (encodeSiblingBlockKey g r d parent key) = key :=
  Classical.choose_spec (exists_siblingBlockKey_index g r d parent key)

@[simp] theorem encodeSiblingBlockKey_decodeSiblingBlockKey
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (i : Fin (siblingBlockKeys g r d parent).length) :
    encodeSiblingBlockKey g r d parent
      (decodeSiblingBlockKey g r d parent i) = i := by
  apply Fin.ext
  apply (siblingBlockKeys_nodup g r d parent).eq_of_getElem_eq
    (encodeSiblingBlockKey g r d parent (decodeSiblingBlockKey g r d parent i)).isLt
    i.isLt
  simpa only [decodeSiblingBlockKey, List.get_eq_getElem] using
    (decodeSiblingBlockKey_encodeSiblingBlockKey g r d parent
      (decodeSiblingBlockKey g r d parent i))

end PaperB.Digraph
