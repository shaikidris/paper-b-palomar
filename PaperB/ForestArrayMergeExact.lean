module

public import PaperB.ForestArrayMerge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
open PairLookup
open PaperB.PairDictionary.ArrayMerge
namespace ArrayMergeExact
open PaperB.PairLookup.KeyMerge

def leftSlice {k} (p : Plan k) (a : Array Key) (h : a.size = 2*k) : List Key :=
  List.ofFn fun i : Fin p.leftLen => readLeft p a h i.val i.isLt
def rightSlice {k} (p : Plan k) (a : Array Key) (h : a.size = 2*k) : List Key :=
  List.ofFn fun j : Fin p.rightLen => readRight p a h j.val j.isLt

private theorem ltSelf (x : Key) : ¬ lexLess x x := by
  rcases x with ⟨a,b⟩
  simp [lexLess]
private theorem ltTrans {x y z : Key} (h : lexLess x y) (g : lexLess y z) :
    lexLess x z := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩; rcases z with ⟨e,f⟩
  simp [lexLess] at * <;> omega
private theorem tieEq {x y : Key} (h : ¬ lexLess x y) (g : ¬ lexLess y x) :
    x = y := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  change ¬ (a < c ∨ (a = c ∧ b < d)) at h
  change ¬ (c < a ∨ (c = a ∧ d < b)) at g
  have he : a = c ∧ b = d := by omega
  rcases he with ⟨rfl,rfl⟩
  rfl

private theorem incExt {l r : List Key} (hl : Increasing l) (hr : Increasing r)
    (hm : ∀ z : Key, z ∈ l ↔ z ∈ r) : l = r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons y ys => simpa using (hm y).mpr (by simp)
  | cons x xs ih =>
    cases r with
    | nil => simpa using (hm x).mp (by simp)
    | cons y ys =>
      have e : x = y := by
        by_cases h : x = y
        · exact h
        · have hx : x ∈ ys := by simpa [h] using (hm x).mp (by simp)
          have hy : y ∈ xs := by simpa [Ne.symm h] using (hm y).mpr (by simp)
          exact (ltSelf x (ltTrans (hl.head y hy) (hr.head x hx))).elim
      subst y
      apply congrArg (List.cons x)
      apply ih
      · exact hl.tail
      · exact hr.tail
      · intro z
        by_cases h : z = x
        · subst z
          have hx : x ∉ xs := fun hz => ltSelf x (hl.head x hz)
          have hy : x ∉ ys := fun hz => ltSelf x (hr.head x hz)
          simp [hx, hy]
        · simpa only [List.mem_cons, h, false_or] using hm z

private theorem emitEq {l r l' r' : List Key} {x : Key}
    (hl : Increasing l) (hr : Increasing r) (hl' : Increasing l') (hr' : Increasing r')
    (hmin : ∀ z : Key, z ∈ l' ∨ z ∈ r' → lexLess x z)
    (hm : ∀ z : Key, (z ∈ l ∨ z ∈ r) ↔ (z = x ∨ z ∈ l' ∨ z ∈ r')) :
    (KeyMerge.merge l r).keys = x :: (KeyMerge.merge l' r').keys := by
  have s := merge_spec hl' hr'
  apply incExt (merge_spec hl hr).increasing
  · exact .cons (fun z hz => hmin z ((s.mem_iff z).mp hz)) s.increasing
  · intro z
    simpa only [List.mem_cons, (merge_spec hl hr).mem_iff, s.mem_iff] using hm z

private theorem belowRun {x y : Key} {ys : List Key} (h : lexLess x y)
    (hy : Increasing (y :: ys)) (z : Key) (hz : z ∈ y :: ys) : lexLess x z := by
  rcases List.mem_cons.mp hz with rfl | hz
  · exact h
  · exact ltTrans h (hy.head z hz)

private theorem incDrop {l : List Key} (h : Increasing l) (n : Nat) :
    Increasing (l.drop n) := by
  induction h generalizing n with
  | nil => simpa using Increasing.nil
  | cons hx ht ih =>
    cases n with
    | zero => exact .cons hx ht
    | succ n => exact ih n

private theorem view {n : Nat} (f : Fin n → Key) {i : Nat} (hi : i < n) :
    (List.ofFn f).drop i = f ⟨i, hi⟩ :: (List.ofFn f).drop (i+1) := by
  have hb : i < (List.ofFn f).length := by simpa using hi
  simpa only [List.getElem_ofFn] using List.drop_eq_getElem_cons hb

private theorem dropEnd {n : Nat} (f : Fin n → Key) : (List.ofFn f).drop n = [] := by
  simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))

private theorem choiceKeys {k} {p : Plan k} {orig a : Array Key} {i j w i' j' r c dr dc}
    {xs : List Key} {x : Key} {ha : a.size = 2*k} (h : orig.size = 2*k)
    (t : Trace p orig a i j w xs r c) (hl : Increasing (leftSlice p orig h))
    (hr : Increasing (rightSlice p orig h)) (ch : Choice p a ha i j i' j' x dr dc) :
    (KeyMerge.merge ((leftSlice p orig h).drop i) ((rightSlice p orig h).drop j)).keys =
      x :: (KeyMerge.merge ((leftSlice p orig h).drop i') ((rightSlice p orig h).drop j')).keys := by
  have L (hi : i < p.leftLen) :
      (leftSlice p orig h).drop i = readLeft p a ha i hi :: (leftSlice p orig h).drop (i+1) := by
    have hq : p.leftBase + i < k := by have := p.separated; have := p.rightFits; omega
    have e : readLeft p a ha i hi = readLeft p orig h i hi := t.sourceUnchanged h _ hq
    rw [e]; exact view _ hi
  have R (hj : j < p.rightLen) :
      (rightSlice p orig h).drop j = readRight p a ha j hj :: (rightSlice p orig h).drop (j+1) := by
    have hq : p.rightBase + j < k := by have := p.rightFits; omega
    have e : readRight p a ha j hj = readRight p orig h j hj := t.sourceUnchanged h _ hq
    rw [e]; exact view _ hj
  have il := incDrop hl i
  have ir := incDrop hr j
  cases ch with
  | leftOnly hi hj =>
    have e : (rightSlice p orig h).drop j = [] := by rw [hj]; exact dropEnd _
    rw [L hi] at il ⊢
    rw [e] at ir ⊢
    refine emitEq il ir (incDrop hl _) ir (fun z hz => il.head z (by simpa using hz)) ?_
    intro z
    simp [List.mem_cons] <;> grind
  | rightOnly hi hj =>
    have e : (leftSlice p orig h).drop i = [] := by rw [hi]; exact dropEnd _
    rw [e] at il ⊢
    rw [R hj] at ir ⊢
    refine emitEq il ir il (incDrop hr _) (fun z hz => ir.head z (by simpa using hz)) ?_
    intro z
    simp [List.mem_cons] <;> grind
  | leftFirst hi hj hlt =>
    rw [L hi] at il ⊢
    rw [R hj] at ir ⊢
    refine emitEq il ir (incDrop hl _) ir (fun z hz => hz.elim (il.head z) (belowRun hlt ir z)) ?_
    intro z
    simp [List.mem_cons] <;> grind
  | rightFirst hi hj _ hlt =>
    rw [L hi] at il ⊢
    rw [R hj] at ir ⊢
    refine emitEq il ir il (incDrop hr _) (fun z hz => hz.elim (belowRun hlt il z) (ir.head z)) ?_
    intro z
    simp [List.mem_cons] <;> grind
  | tie hi hj h₁ h₂ =>
    rw [L hi] at il ⊢
    rw [R hj, ← tieEq h₁ h₂] at ir ⊢
    refine emitEq il ir (incDrop hl _) (incDrop hr _) (fun z hz => hz.elim (il.head z) (ir.head z)) ?_
    intro z
    simp [List.mem_cons] <;> grind

theorem runPacked_exact {k} (p : Plan k) (orig : Array Key) (h : orig.size = 2*k)
    (hl : Increasing (leftSlice p orig h)) (hr : Increasing (rightSlice p orig h)) :
    ∃ r c, Trace p orig (runPacked p orig h).bank p.leftLen p.rightLen (runPacked p orig h).count
      (KeyMerge.merge (leftSlice p orig h) (rightSlice p orig h)).keys r c := by
  obtain ⟨xs, r, c, t, _⟩ := (runPacked p orig h).certified
  have inv {a i j w ys nr nc} (s : Trace p orig a i j w ys nr nc) :
      ys ++ (KeyMerge.merge ((leftSlice p orig h).drop i) ((rightSlice p orig h).drop j)).keys =
        (KeyMerge.merge (leftSlice p orig h) (rightSlice p orig h)).keys := by
    induction s with
    | nil => simp
    | snoc s step ih =>
      cases step
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        ← choiceKeys h s hl hr (by assumption)] using ih
  have e : xs = (KeyMerge.merge (leftSlice p orig h) (rightSlice p orig h)).keys := by
    simpa only [leftSlice, rightSlice, dropEnd, show (KeyMerge.merge [] []).keys = [] from rfl,
      List.append_nil] using inv t
  exact ⟨r, c, e ▸ t⟩

end ArrayMergeExact
end PaperB
