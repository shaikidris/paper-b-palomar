module

public import PaperB.StaticHeavyLCA
public import PaperB.HeavyChild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace StaticHeadSweep

open PaperB.LabelledQuotient ForestHeavyPath

universe u

/-- Vertex IDs are physical array indices. The length proof is erased. -/
structure Slots (N : Nat) (β : Type u) where
  data : Array β
  len : data.size = N

namespace Slots

variable {N : Nat} {β : Type u}

def read (a : Slots N β) (i : Fin N) : β :=
  a.data[i.val]'(by simpa only [a.len] using i.isLt)

def write (a : Slots N β) (i : Fin N) (x : β) : Slots N β :=
  let hi : i.val < a.data.size := by simpa only [a.len] using i.isLt
  ⟨a.data.set i.val x hi, by simpa using a.len⟩

def fill (N : Nat) (x : β) : Slots N β :=
  ⟨Array.replicate N x, by simp⟩

@[simp] theorem read_write_same (a : Slots N β) (i : Fin N) (x : β) :
    (a.write i x).read i = x := by
  simp [read, write]

theorem read_write_other (a : Slots N β) (i j : Fin N) (x : β)
    (h : j ≠ i) : (a.write i x).read j = a.read j := by
  have hji : j.val ≠ i.val := fun e => h (Fin.ext e)
  have hij : i.val ≠ j.val := Ne.symm hji
  simp [read, write, Array.getElem_set, hij]

end Slots

/-- The heavy-child column is already packed. A sweep step does not run
    `heavyChild` or enumerate children. -/
structure Packed (N : Nat) where
  root : Fin N
  parent : Slots N (Fin N)
  depth : Slots N Nat
  heavy : Slots N (Option (Fin N))
  size : Slots N Nat

structure State (N : Nat) where
  heads : Slots N (Fin N)
  writes : Nat

variable {N : Nat}

abbrev Inherits (p : Packed N) (b : Fin N) : Prop :=
  b ≠ p.root ∧ p.heavy.read (p.parent.read b) = some b

def nextHead (p : Packed N) (a : Slots N (Fin N)) (b : Fin N) : Fin N :=
  if Inherits p b then a.read (p.parent.read b) else b

def step (p : Packed N) (s : State N) (b : Fin N) : State N :=
  let h := nextHead p s.heads b
  ⟨s.heads.write b h, s.writes + 1⟩

def initial (p : Packed N) : State N :=
  ⟨Slots.fill N p.root, 0⟩

def sweep (p : Packed N) (xs : List (Fin N)) : State N :=
  xs.foldl (step p) (initial p)

def preorder (p : Packed N) : List (Fin N) :=
  dfsPreorder p.root p.parent.read p.depth.read

def build (p : Packed N) : State N :=
  sweep p (preorder p)

@[simp] theorem step_read_same (p : Packed N) (s : State N) (b : Fin N) :
    (step p s b).heads.read b = nextHead p s.heads b := by
  simp [step]

theorem step_read_other (p : Packed N) (s : State N) (b v : Fin N)
    (h : v ≠ b) : (step p s b).heads.read v = s.heads.read v :=
  Slots.read_write_other s.heads b v _ h

theorem fold_preserves_unwritten (p : Packed N) (v : Fin N)
    (xs : List (Fin N)) (s : State N) (hv : v ∉ xs) :
    (xs.foldl (step p) s).heads.read v = s.heads.read v := by
  induction xs generalizing s with
  | nil => rfl
  | cons b xs ih =>
      have hne : v ≠ b := fun e => hv (List.mem_cons.mpr (Or.inl e))
      have ht : v ∉ xs := fun h => hv (List.mem_cons.mpr (Or.inr h))
      change (xs.foldl (step p) (step p s b)).heads.read v = s.heads.read v
      rw [ih (step p s b) ht, step_read_other p s b v hne]

/-- At physical index `b.val`, the value left by the sweep is exactly the
    value written at `b`'s visit. The parent lookup is in the state *before*
    that visit. `pre.length` is the zero-based visit index. -/
theorem fold_read_at (p : Packed N) (s : State N)
    (pre post : List (Fin N)) (b : Fin N) (hb : b ∉ post) :
    ((pre ++ b :: post).foldl (step p) s).heads.read b =
      if Inherits p b then
        (pre.foldl (step p) s).heads.read (p.parent.read b)
      else b := by
  rw [List.foldl_append]
  change (post.foldl (step p) (step p (pre.foldl (step p) s) b)).heads.read b = _
  rw [fold_preserves_unwritten p b post _ hb, step_read_same]
  rfl

theorem fold_write_count (p : Packed N) (xs : List (Fin N)) (s : State N) :
    (xs.foldl (step p) s).writes = s.writes + xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons b xs ih =>
      change (xs.foldl (step p) (step p s b)).writes = s.writes + (xs.length + 1)
      rw [ih]
      change s.writes + 1 + xs.length = s.writes + (xs.length + 1)
      omega

private theorem split_mem {β : Type u} {b : β} (xs : List β)
    (h : b ∈ xs) : ∃ pre post, xs = pre ++ b :: post := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rcases List.mem_cons.mp h with e | h
      · subst x
        exact ⟨[], xs, rfl⟩
      · obtain ⟨pre, post, e⟩ := ih h
        exact ⟨x :: pre, post, congrArg (List.cons x) e⟩

private theorem length_le_of_cover {β : Type u} (xs ys : List β)
    (hx : xs.Nodup) (hc : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons b xs ih =>
      obtain ⟨l, r, rfl⟩ := split_mem ys (hc b (by simp))
      have hn := List.nodup_cons.mp hx
      have ht : ∀ x ∈ xs, x ∈ l ++ r := by
        intro x h
        rcases List.mem_append.mp (hc x (List.mem_cons.mpr (Or.inr h))) with hl | hr
        · exact List.mem_append.mpr (Or.inl hl)
        · rcases List.mem_cons.mp hr with e | hr
          · subst x
            exact (hn.1 h).elim
          · exact List.mem_append.mpr (Or.inr hr)
      have hle := ih (l ++ r) hn.2 ht
      simp only [List.length_append, List.length_cons] at hle ⊢
      omega

private theorem not_mem_right {β : Type u} {a : β} (l r : List β)
    (hn : (l ++ r).Nodup) (ha : a ∈ l) : a ∉ r := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      have ht : (x :: (l ++ r)).Nodup := hn
      rcases List.mem_cons.mp ha with e | ha
      · subst x
        intro hr
        exact (List.nodup_cons.mp ht).1 (List.mem_append.mpr (Or.inr hr))
      · exact ih (List.nodup_cons.mp ht).2 ha

private inductive Before {β : Type u} (a b : β) : List β → Prop where
  | here {xs} : b ∈ xs → Before a b (a :: xs)
  | there {x xs} : Before a b xs → Before a b (x :: xs)

private theorem before_mem_right {β : Type u} {a b : β} {xs : List β}
    (h : Before a b xs) : b ∈ xs := by
  induction h with
  | here h => exact List.mem_cons.mpr (Or.inr h)
  | there _ ih => exact List.mem_cons.mpr (Or.inr ih)

private theorem before_append {β : Type u} {a b : β} {xs : List β}
    (h : Before a b xs) (r : List β) : Before a b (xs ++ r) := by
  induction h with
  | here h => exact .here (List.mem_append.mpr (Or.inl h))
  | there _ ih => exact .there ih

private theorem before_prepend {β : Type u} {a b : β} {xs : List β}
    (l : List β) (h : Before a b xs) : Before a b (l ++ xs) := by
  induction l with
  | nil => exact h
  | cons _ _ ih => exact .there ih

private theorem before_mem_prefix {β : Type u} {a b : β} (l r : List β)
    (hn : (l ++ b :: r).Nodup) (h : Before a b (l ++ b :: r)) : a ∈ l := by
  induction l with
  | nil =>
      have hn' : (b :: r).Nodup := hn
      change Before a b (b :: r) at h
      have hb := (List.nodup_cons.mp hn').1
      cases h with
      | here hm => exact (hb hm).elim
      | there ht => exact (hb (before_mem_right ht)).elim
  | cons x l ih =>
      have hn' : (x :: (l ++ b :: r)).Nodup := hn
      change Before a b (x :: (l ++ b :: r)) at h
      cases h with
      | here _ => exact List.mem_cons.mpr (Or.inl rfl)
      | there ht => exact List.mem_cons.mpr (Or.inr (ih (List.nodup_cons.mp hn').2 ht))

abbrev TreeOK (p : Packed N) :=
  ValidDepthTree p.root p.parent.read p.depth.read

private theorem in_parent_bucket (p : Packed N) {b : Fin N} (hb : b ≠ p.root) :
    b ∈ bucketChildren p.root p.parent.read (p.parent.read b) := by
  rw [LabelledQuotient.mem_bucketChildren_iff]
  simp [hb]

theorem preorder_nodup (p : Packed N) (ht : TreeOK p) : (preorder p).Nodup :=
  nodup_dfsPreorder ht

theorem mem_preorder (p : Packed N) (ht : TreeOK p) (b : Fin N) :
    b ∈ preorder p := by
  obtain ⟨l, r, hs⟩ := exists_split_dfsPreorder ht b
  have hb : b ∈ dfsSubtree p.root p.parent.read p.depth.read b := by
    rw [dfsSubtree_unfold ht b]
    simp
  unfold preorder
  rw [hs]
  simp [hb]

/-- The predecessor needed by a step is in the actual DFS prefix,
    not just somewhere earlier in a depth-sorted surrogate. -/
theorem parent_mem_prefix (p : Packed N) (ht : TreeOK p)
    {l r : List (Fin N)} {b : Fin N}
    (hs : preorder p = l ++ b :: r) (hb : b ≠ p.root) :
    p.parent.read b ∈ l := by
  have hc := in_parent_bucket p hb
  have hself : b ∈ dfsSubtree p.root p.parent.read p.depth.read b := by
    rw [dfsSubtree_unfold ht b]
    simp
  have hsub : Before (p.parent.read b) b
      (dfsSubtree p.root p.parent.read p.depth.read (p.parent.read b)) := by
    rw [dfsSubtree_unfold ht (p.parent.read b)]
    apply Before.here
    have hblock (cs : List (Fin N)) (hm : b ∈ cs) :
        b ∈ concatMapList (dfsSubtree p.root p.parent.read p.depth.read) cs := by
      induction cs with
      | nil => simp at hm
      | cons c cs ih =>
          change b ∈ dfsSubtree p.root p.parent.read p.depth.read c ++
            concatMapList (dfsSubtree p.root p.parent.read p.depth.read) cs
          rcases List.mem_cons.mp hm with he | htail
          · subst c
            exact List.mem_append.mpr (Or.inl hself)
          · exact List.mem_append.mpr (Or.inr (ih htail))
    exact hblock _ hc
  have hall : Before (p.parent.read b) b (preorder p) := by
    obtain ⟨pre, post, hp⟩ := exists_split_dfsPreorder ht (p.parent.read b)
    unfold preorder
    rw [hp]
    simpa only [List.append_assoc] using before_prepend pre (before_append hsub post)
  have hn := preorder_nodup p ht
  rw [hs] at hn hall
  exact before_mem_prefix l r hn hall

theorem build_write_count (p : Packed N) (ht : TreeOK p) : (build p).writes = N := by
  have hf : (List.finRange N).Nodup := by
    first | exact List.nodup_finRange N | simpa | exact?
  have hm : ∀ b : Fin N, b ∈ List.finRange N := by
    intro b
    first | exact List.mem_finRange b | simpa | exact?
  have hlen : (preorder p).length = N := by
    have h₁ := length_le_of_cover (preorder p) (List.finRange N)
      (preorder_nodup p ht) (fun b _ => hm b)
    have h₂ := length_le_of_cover (List.finRange N) (preorder p)
      hf (fun b _ => mem_preorder p ht b)
    simpa using Nat.le_antisymm h₁ h₂
  simpa [build, sweep, initial, hlen] using
    fold_write_count p (preorder p) (initial p)

/-- Both the old-parent lookup and the fresh-head case, specialized to
    any visit in the executable constructor. -/
theorem build_read_at (p : Packed N) (ht : TreeOK p)
    {l r : List (Fin N)} {b : Fin N} (hs : preorder p = l ++ b :: r) :
    (build p).heads.read b =
      if Inherits p b then (sweep p l).heads.read (p.parent.read b) else b := by
  have hn := preorder_nodup p ht
  rw [hs] at hn
  have hb : b ∉ r := by
    clear hs
    induction l with
    | nil => exact (List.nodup_cons.mp hn).1
    | cons x l ih =>
        have hn' : (x :: (l ++ b :: r)).Nodup := hn
        exact ih (List.nodup_cons.mp hn').2
  unfold build
  rw [hs]
  exact fold_read_at p (initial p) l r b hb

theorem build_read_eq (p : Packed N) (ht : TreeOK p) (b : Fin N) :
    (build p).heads.read b =
      if Inherits p b then (build p).heads.read (p.parent.read b) else b := by
  obtain ⟨l, r, hs⟩ := split_mem (preorder p) (mem_preorder p ht b)
  rw [build_read_at p ht hs]
  by_cases hb : Inherits p b
  · simp only [ite_eq_left hb]
    have hp := parent_mem_prefix p ht hs hb.1
    have hn := preorder_nodup p ht
    rw [hs] at hn
    have hnot := not_mem_right l (b :: r) hn hp
    unfold build sweep
    rw [hs, List.foldl_append, fold_preserves_unwritten p _ _ _ hnot]
  · simp [hb]

private def Ready (p : Packed N) (seen xs : List (Fin N)) : Prop :=
  ∀ l b r, xs = l ++ b :: r → Inherits p b →
    p.parent.read b ∈ seen ∨ p.parent.read b ∈ l

/-- At every prefix, all written indices satisfy `Q`. In the inheriting
    branch the parent index is already written, so no initial fill value
    is used as an inherited head. -/
private theorem fold_good (p : Packed N) (Q : Fin N → Fin N → Prop)
    (fresh : ∀ b, ¬ Inherits p b → Q b b)
    (extend : ∀ b a, Inherits p b → Q (p.parent.read b) a → Q b a)
    (xs : List (Fin N)) :
    ∀ (seen : List (Fin N)) (s : State N), xs.Nodup →
      (∀ b ∈ xs, b ∉ seen) → Ready p seen xs →
      (∀ b ∈ seen, Q b (s.heads.read b)) →
      ∀ b, b ∈ seen ∨ b ∈ xs → Q b ((xs.foldl (step p) s).heads.read b) := by
  induction xs with
  | nil =>
      intro seen s _ _ _ hq b hb
      exact hq b (hb.resolve_right (by simp))
  | cons v xs ih =>
      intro seen s hn hd hr hq b hb
      have hn' := List.nodup_cons.mp hn
      have hv : v ∉ seen := hd v (by simp)
      have hd' : ∀ x ∈ xs, x ∉ v :: seen := by
        intro x hx hh
        rcases List.mem_cons.mp hh with e | hh
        · subst x
          exact hn'.1 hx
        · exact hd x (List.mem_cons.mpr (Or.inr hx)) hh
      have hr' : Ready p (v :: seen) xs := by
        intro l x r hs hh
        have he : v :: xs = (v :: l) ++ x :: r := congrArg (List.cons v) hs
        rcases hr (v :: l) x r he hh with hm | hm
        · exact Or.inl (List.mem_cons.mpr (Or.inr hm))
        · rcases List.mem_cons.mp hm with e | hm
          · exact Or.inl (List.mem_cons.mpr (Or.inl e))
          · exact Or.inr hm
      have hq' : ∀ x ∈ v :: seen, Q x ((step p s v).heads.read x) := by
        intro x hx
        rcases List.mem_cons.mp hx with e | hx
        · subst x
          rw [step_read_same]
          by_cases hh : Inherits p v
          · have hm := (hr [] v xs rfl hh).resolve_right (by simp)
            simpa only [nextHead, ite_eq_left hh] using
              extend v _ hh (hq _ hm)
          · simpa only [nextHead, ite_eq_right hh] using fresh v hh
        · have hne : x ≠ v := fun e => hv (e ▸ hx)
          rw [step_read_other p s v x hne]
          exact hq x hx
      have hb' : b ∈ v :: seen ∨ b ∈ xs := by
        rcases hb with hb | hb
        · exact Or.inl (List.mem_cons.mpr (Or.inr hb))
        · rcases List.mem_cons.mp hb with e | hb
          · exact Or.inl (List.mem_cons.mpr (Or.inl e))
          · exact Or.inr hb
      exact ih (v :: seen) (step p s v) hn'.2 hd' hr' hq' b hb'

def tables (p : Packed N) : EX16.Tables (Fin N) where
  root := p.root
  parent := p.parent.read
  depth := p.depth.read
  heavy := p.heavy.read
  head := (build p).heads.read
  size := p.size.read

private theorem head_facts (p : Packed N) (ht : TreeOK p) (b : Fin N) :
    EX16.HeavyPath (tables p) ((tables p).head b) b ∧
      EX16.Top (tables p) ((tables p).head b) := by
  let Q : Fin N → Fin N → Prop := fun v a =>
    EX16.HeavyPath (tables p) a v ∧ EX16.Top (tables p) a
  have hf : ∀ v, ¬ Inherits p v → Q v v := by
    intro v hv
    constructor
    · exact EX16.Path.refl
    · intro hn hh
      exact hv ⟨hn, hh⟩
  have he : ∀ v a, Inherits p v → Q (p.parent.read v) a → Q v a := by
    intro v a hv ha
    constructor
    · change EX16.HeavyPath (tables p) a v
      exact EX16.Path.step hv.1 hv.2 ha.1
    · exact ha.2
  have hr : Ready p [] (preorder p) := by
    intro l v r hs hv
    exact Or.inr (parent_mem_prefix p ht hs hv.1)
  exact fold_good p Q hf he (preorder p) [] (initial p)
    (preorder_nodup p ht) (by simp) hr (by simp) b
    (Or.inr (mem_preorder p ht b))

abbrev SizesOK (p : Packed N) :=
  ∀ v, p.size.read v = subtreeSize p.root p.parent.read p.depth.read v

abbrev HeavyOK (p : Packed N) :=
  ∀ v, p.heavy.read v = heavyChild p.root p.parent.read p.size.read v

/-- Exact maximality transfers to the packed heavy-child column. -/
theorem packed_heavy_maximal (p : Packed N) (hh : HeavyOK p)
    {u v c : Fin N} (hv : p.heavy.read u = some v)
    (hc : c ∈ bucketChildren p.root p.parent.read u) :
    p.size.read c ≤ p.size.read v := by
  have hselected : heavyChild p.root p.parent.read p.size.read u = some v :=
    (hh u).symm.trans hv
  exact ForestHeavyPath.heavyChild_maximal hselected hc

private theorem packed_light_halves (p : Packed N) (ht : TreeOK p)
    (hs : SizesOK p) (hh : HeavyOK p) (b : Fin N) (hb : b ≠ p.root)
    (hl : p.heavy.read (p.parent.read b) ≠ some b) :
    2 * p.size.read b < p.size.read (p.parent.read b) := by
  have hc := in_parent_bucket p hb
  have hl' : heavyChild p.root p.parent.read p.size.read (p.parent.read b) ≠ some b := by
    rw [← hh (p.parent.read b)]
    exact hl
  have hedge : IsLightEdge p.root p.parent.read p.size.read (p.parent.read b) b := by
    first
    | exact ⟨hc, hl'⟩
    | constructor <;> solve_by_elim [hc, hb, hl', And.intro, Eq.refl]
    | unfold IsLightEdge
      solve_by_elim [hc, hb, hl', And.intro, Eq.refl]
  exact ForestHeavyPath.light_edge_halves ht hs hedge

theorem valid (p : Packed N) (ht : TreeOK p) (hs : SizesOK p) (hh : HeavyOK p) :
    EX16.Valid (tables p) := by
  exact {
    depth_root := ht.depth_root
    depth_step := by
      intro b hb
      change p.depth.read (p.parent.read b) + 1 = p.depth.read b
      first
      | have hd := ht.depth_step b hb
        omega
      | have hd := ht.depth_step hb
        omega
    size_pos := by
      intro b
      change 0 < p.size.read b
      rw [hs b]
      unfold subtreeSize
      rw [dfsSubtree_unfold ht b]
      simp
    size_step := by
      intro b hb
      change p.size.read b ≤ p.size.read (p.parent.read b)
      rw [hs b, hs (p.parent.read b)]
      exact Nat.le_of_lt (ForestHeavyPath.child_size_lt ht (in_parent_bucket p hb))
    light_halves := by
      intro b hb hl
      exact packed_light_halves p ht hs hh b hb hl
    head_path := fun b => (head_facts p ht b).1
    head_top := fun b => (head_facts p ht b).2
  }

end StaticHeadSweep
end PaperB
