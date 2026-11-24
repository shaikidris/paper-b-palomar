module

public import PaperB.StaticTreeReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.DenseQuotientRows

open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath

variable {N : Nat}

/-!
`ofBuckets` is the indexing pass. It can consume the buckets already retained
by `PackedStaticLayout`; it does not run the packed layout, the heavy sweep,
or arc routing. `build` is the convenience entry point for an unbucketed input.

There is one row per ordinary ID, in ordinary ID order. Slot zero is the
quotient root. The remaining slots are the existing ordinary child bucket,
in bucket order. A child emission writes both its forward cell and its
inverse local slot. The directory stores (prefix offset, row length).

The list models below occur only in correctness proofs. In particular,
neither direction of the local index uses `encodeSiblingBlockKey`.
-/

abbrev Key (N : Nat) := Sum (Fin N) (Fin N)

inductive Cell (N : Nat) where
  | root (id : Fin N)
  | child (id : Fin N) (localSlot : Nat)

def Cell.key : Cell N → Key N
  | .root d => .inl d
  | .child c _ => .inr c

def Occurs (g : ChildLists N) (u : Fin N) : Key N → Prop
  | .inl d => d = u
  | .inr c => c ∈ g.get u

abbrev Occurrence (g : ChildLists N) (u : Fin N) :=
  {k : Key N // Occurs g u k}

private theorem elems_eq (n : Nat) :
    finElems n = List.ofFn (fun i : Fin n => i) := by
  first
  | apply List.ext_getElem
    · simp [finElems]
    · intro i hi hj
      apply Fin.ext
      first
      | simp [finElems]
        done
      | simp [finElems, List.getElem_attach]
        done
      | simp [finElems, List.getElem_pmap]
        done
    done
  | have hfilter (xs : List Nat) (hxs : ∀ i ∈ xs, i < n) :
        xs.filterMap (fun i => if h : i < n then some (⟨i, h⟩ : Fin n) else none) =
          xs.pmap (fun i h => (⟨i, h⟩ : Fin n)) hxs := by
      induction xs with
      | nil => rfl
      | cons i xs ih =>
          have hi : i < n := hxs i (by simp)
          have ht : ∀ j ∈ xs, j < n := fun j hj =>
            hxs j (List.mem_cons.mpr (Or.inr hj))
          simp only [List.filterMap_cons, dif_pos hi, List.pmap]
          rw [ih ht]
    unfold finElems
    rw [hfilter (List.range n) (fun i hi => List.mem_range.mp hi)]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      apply Fin.ext
      first
      | simp
        done
      | simp [List.getElem_pmap]
  | induction n with
    | zero => rfl
    | succ n ih =>
        simp [finElems, List.ofFn_succ, ih, Function.comp_def]
        apply congrArg (fun f : Fin n → Fin (n + 1) => List.ofFn f)
        funext i
        apply Fin.ext
        rfl

private theorem elems_length (n : Nat) : (finElems n).length = n := by
  simp [elems_eq]

private theorem elems_at (u : Fin N) : (finElems N)[u.val]? = some u := by
  rw [elems_eq, List.getElem?_eq_getElem (by simp)]
  simp

private theorem elems_nodup (n : Nat) : (finElems n).Nodup := by
  rw [elems_eq, List.nodup_iff_pairwise_ne]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have he' : i = j := by
    simpa only [List.getElem_ofFn] using congrArg Fin.val he
  exact (Nat.ne_of_lt hij) he'

private theorem bucket_mem (root : Fin N) (parent : Fin N → Fin N)
    (u c : Fin N) :
    c ∈ bucketChildren root parent u ↔ c ≠ root ∧ parent c = u := by
  exact mem_bucketChildren_iff root parent u c

private theorem bucket_nodup (root : Fin N) (parent : Fin N → Fin N)
    (u : Fin N) : (bucketChildren root parent u).Nodup := by
  first
  | exact nodup_bucketChildren root parent u
  | exact bucketChildren_nodup root parent u
  | exact pairwise_bucketChildren root parent u
  | exact bucketChildren_pairwise root parent u
  | have hn := elems_nodup N
    unfold bucketChildren
    first | rw [List.nodup_reverse] | skip
    generalize finElems N = us at hn ⊢
    generalize he : (fun _ : Fin N => ([] : List (Fin N))) = b
    have hb : ∀ q, (b q).Nodup := by
      rw [← he]
      simp
    have hf : ∀ d ∈ us, ∀ q, d ∉ b q := by
      rw [← he]
      simp
    clear he
    induction us generalizing b with
    | nil => exact hb u
    | cons c cs ih =>
        obtain ⟨hc, hcs⟩ := List.nodup_cons.mp hn
        have hnew (q : Fin N) : c ∉ b q := hf c (by simp) q
        have ht (d : Fin N) (hd : d ∈ cs) (q : Fin N) : d ∉ b q :=
          hf d (List.mem_cons.mpr (Or.inr hd)) q
        have hne (d : Fin N) (hd : d ∈ cs) : d ≠ c := by
          intro h
          subst d
          exact hc hd
        have hp (q : Fin N) : (c :: b q).Nodup :=
          List.nodup_cons.mpr ⟨hnew q, hb q⟩
        have ha (q : Fin N) : (b q ++ [c]).Nodup := by
          change (b q ++ [c]).Pairwise (· ≠ ·)
          rw [List.pairwise_append]
          refine ⟨hb q, by simp, ?_⟩
          intro d hd e he
          have h : e = c := by simpa using he
          subst e
          intro h
          subst d
          exact hnew q hd
        have hfp (d : Fin N) (hd : d ∈ cs) (q : Fin N) : d ∉ c :: b q := by
          intro hm
          rcases List.mem_cons.mp hm with hm | hm
          · exact hne d hd hm
          · exact ht d hd q hm
        have hfa (d : Fin N) (hd : d ∈ cs) (q : Fin N) : d ∉ b q ++ [c] := by
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact ht d hd q hm
          · exact hne d hd (by simpa using hm)
        first
        | simp only [bucketPassAux]
        | conv =>
            arg 1
            whnf
        (first | split | skip) <;> apply ih
        all_goals
          first
          | exact hcs
          | exact hb
          | exact ht
          | intro q
            first
            | split
            | change List.Nodup (ite _ _ _)
              split
            | change List.Nodup (dite _ _ _)
              split
            | simp only [Function.update]
              split
            all_goals first | exact hb _ | exact hp _ | exact ha _
          | intro d hd q
            first
            | split
            | change d ∉ (ite _ (_ : List (Fin N)) _)
              split
            | change d ∉ (dite _ (_ : _ → List (Fin N)) _)
              split
            | simp only [Function.update]
              split
            all_goals first | exact ht d hd _ | exact hfp d hd _ | exact hfa d hd _

private def childSpec : Nat → List (Fin N) → List (Cell N)
  | _, [] => []
  | j, c :: cs => .child c j :: childSpec (j + 1) cs

private def rowSpec (g : ChildLists N) (u : Fin N) : List (Cell N) :=
  .root u :: childSpec 1 (g.get u)

private def flatSpec (g : ChildLists N) : List (Fin N) → List (Cell N)
  | [] => []
  | u :: us => rowSpec g u ++ flatSpec g us

private def directorySpec (g : ChildLists N) :
    Nat → List (Fin N) → List (Nat × Nat)
  | _, [] => []
  | p, u :: us =>
      (p, (rowSpec g u).length) ::
        directorySpec g (p + (rowSpec g u).length) us

private theorem childSpec_length (j : Nat) (cs : List (Fin N)) :
    (childSpec j cs).length = cs.length := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp [childSpec, ih]

private theorem childSpec_at (cs : List (Fin N)) (j i : Nat)
    (hi : i < cs.length) :
    (childSpec j cs)[i]? = some (.child cs[i] (j + i)) := by
  induction cs generalizing j i with
  | nil => simp at hi
  | cons c cs ih =>
      cases i with
      | zero => simp [childSpec]
      | succ i =>
          have h : i < cs.length := by simpa using hi
          simpa [childSpec, Nat.succ_eq_add_one, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using ih (j + 1) i h

private theorem childSpec_mem {cs : List (Fin N)} {j k : Nat} {c : Fin N}
    (h : Cell.child c k ∈ childSpec j cs) : c ∈ cs := by
  induction cs generalizing j with
  | nil => simp [childSpec] at h
  | cons d cs ih =>
      simp only [childSpec, List.mem_cons] at h ⊢
      rcases h with h | h
      · cases h
        exact Or.inl rfl
      · exact Or.inr (ih h)

private theorem rowSpec_length (g : ChildLists N) (u : Fin N) :
    (rowSpec g u).length = (g.get u).length + 1 := by
  simp [rowSpec, childSpec_length]

private theorem rowSpec_succ (g : ChildLists N) (u : Fin N) (j : Nat)
    (hj : j < (g.get u).length) :
    (rowSpec g u)[j + 1]? = some (.child (g.get u)[j] (j + 1)) := by
  simpa [rowSpec, Nat.add_comm 1 j] using childSpec_at (g.get u) 1 j hj

private theorem rowSpec_child_mem {g : ChildLists N} {u c : Fin N} {j : Nat}
    (h : Cell.child c j ∈ rowSpec g u) : c ∈ g.get u := by
  have h' : Cell.child c j ∈ childSpec 1 (g.get u) := by
    simpa [rowSpec] using h
  exact childSpec_mem h'

private theorem directorySpec_length (g : ChildLists N) (p : Nat)
    (us : List (Fin N)) : (directorySpec g p us).length = us.length := by
  induction us generalizing p with
  | nil => rfl
  | cons u us ih => simp [directorySpec, ih]

private theorem flatSpec_length (g : ChildLists N) (us : List (Fin N)) :
    (flatSpec g us).length = us.length + sumBucketLengths (fun u => g.get u) us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      simp [flatSpec, rowSpec_length, sumBucketLengths, ih] <;> omega

private def store (a : Slots N Nat) (c : Fin N) (j : Nat) : Slots N Nat := by
  rcases a with ⟨a, ha⟩
  have hc : c.val < a.size := by rw [ha]; exact c.isLt
  exact ⟨a.set c.val j hc, by simpa using ha⟩

private theorem store_same (a : Slots N Nat) (c : Fin N) (j : Nat) :
    (store a c j).read c = j := by
  cases a
  simp [store, Slots.read]

private theorem store_other (a : Slots N Nat) (c d : Fin N) (j : Nat)
    (h : d ≠ c) : (store a c j).read d = a.read d := by
  have hv : d.val ≠ c.val := fun e => h (Fin.ext e)
  cases a
  simp [store, Slots.read, Array.getElem_set, Ne.symm hv]

private structure Buffer (N : Nat) where
  cells : Array (Cell N)
  pos : Slots N Nat

private def pushRoot (b : Buffer N) (u : Fin N) : Buffer N :=
  match b with
  | ⟨a, p⟩ => ⟨a.push (.root u), p⟩

private def pushChild (b : Buffer N) (c : Fin N) (j : Nat) : Buffer N :=
  match b with
  | ⟨a, p⟩ => ⟨a.push (.child c j), store p c j⟩

private def emit : List (Fin N) → Nat → Buffer N → Buffer N
  | [], _, b => b
  | c :: cs, j, b => emit cs (j + 1) (pushChild b c j)

private structure Raw (N : Nat) where
  buf : Buffer N
  dirs : Array (Nat × Nat)

private def initial (n : Nat) : Raw n :=
  ⟨⟨#[], Slots.fill n 0⟩, #[]⟩

private def step (g : ChildLists N) (s : Raw N) (u : Fin N) : Raw N :=
  match s with
  | ⟨b, ds⟩ =>
      let p := b.cells.size
      let b' := emit (g.get u) 1 (pushRoot b u)
      let len := b'.cells.size - p
      ⟨b', ds.push (p, len)⟩

private def scan (g : ChildLists N) : List (Fin N) → Raw N → Raw N
  | [], s => s
  | u :: us, s => scan g us (step g s u)

private theorem pushRoot_cells (b : Buffer N) (u : Fin N) :
    (pushRoot b u).cells.toList = b.cells.toList ++ [.root u] := by
  cases b
  simp [pushRoot]

private theorem pushChild_cells (b : Buffer N) (c : Fin N) (j : Nat) :
    (pushChild b c j).cells.toList = b.cells.toList ++ [.child c j] := by
  cases b
  simp [pushChild]

private theorem pushRoot_pos (b : Buffer N) (u : Fin N) :
    (pushRoot b u).pos = b.pos := by
  cases b
  rfl

private theorem pushChild_pos (b : Buffer N) (c : Fin N) (j : Nat) :
    (pushChild b c j).pos = store b.pos c j := by
  cases b
  rfl

private theorem emit_cells (cs : List (Fin N)) (j : Nat) (b : Buffer N) :
    (emit cs j b).cells.toList = b.cells.toList ++ childSpec j cs := by
  induction cs generalizing j b with
  | nil => simp [emit, childSpec]
  | cons c cs ih =>
      simp [emit, ih, pushChild_cells, childSpec, List.append_assoc]

private theorem step_cells (g : ChildLists N) (s : Raw N) (u : Fin N) :
    (step g s u).buf.cells.toList = s.buf.cells.toList ++ rowSpec g u := by
  cases s
  simp [step, emit_cells, pushRoot_cells, rowSpec, List.append_assoc]

private theorem step_size (g : ChildLists N) (s : Raw N) (u : Fin N) :
    (step g s u).buf.cells.size = s.buf.cells.size + (rowSpec g u).length := by
  simpa using congrArg List.length (step_cells g s u)

private theorem step_dirs (g : ChildLists N) (s : Raw N) (u : Fin N) :
    (step g s u).dirs.toList =
      s.dirs.toList ++ [(s.buf.cells.size, (rowSpec g u).length)] := by
  have hs : (step g s u).buf.cells.size - s.buf.cells.size =
      (rowSpec g u).length := by rw [step_size]; omega
  have hd : (step g s u).dirs =
      s.dirs.push (s.buf.cells.size, (step g s u).buf.cells.size - s.buf.cells.size) := by
    cases s
    rfl
  rw [hd, hs]
  simp

private theorem scan_cells (g : ChildLists N) (us : List (Fin N)) (s : Raw N) :
    (scan g us s).buf.cells.toList = s.buf.cells.toList ++ flatSpec g us := by
  induction us generalizing s with
  | nil => simp [scan, flatSpec]
  | cons u us ih => simp [scan, ih, step_cells, flatSpec, List.append_assoc]

private theorem scan_dirs (g : ChildLists N) (us : List (Fin N)) (s : Raw N) :
    (scan g us s).dirs.toList =
      s.dirs.toList ++ directorySpec g s.buf.cells.size us := by
  induction us generalizing s with
  | nil => simp [scan, directorySpec]
  | cons u us ih =>
      simp [scan, ih, step_dirs, step_size, directorySpec, List.append_assoc]

private def Agrees (b : Buffer N) : Prop :=
  ∀ c j, Cell.child c j ∈ b.cells.toList → b.pos.read c = j

private def Fresh (b : Buffer N) (cs : List (Fin N)) : Prop :=
  ∀ c ∈ cs, ∀ j, Cell.child c j ∉ b.cells.toList

private theorem pushChild_agrees (b : Buffer N) (c : Fin N) (j : Nat)
    (ha : Agrees b) (hf : ∀ k, Cell.child c k ∉ b.cells.toList) :
    Agrees (pushChild b c j) := by
  intro d k h
  rw [pushChild_cells, List.mem_append] at h
  rw [pushChild_pos]
  rcases h with h | h
  · have hn : d ≠ c := by
      intro e
      subst d
      exact hf k h
    exact (store_other b.pos c d j hn).trans (ha d k h)
  · have he : Cell.child d k = Cell.child c j := by simpa using h
    cases he
    exact store_same b.pos c j

private theorem emit_agrees (cs : List (Fin N)) (j : Nat) (b : Buffer N)
    (ha : Agrees b) (hf : Fresh b cs) (hn : cs.Nodup) :
    Agrees (emit cs j b) := by
  induction cs generalizing j b with
  | nil => exact ha
  | cons c cs ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      have hc : ∀ k, Cell.child c k ∉ b.cells.toList :=
        hf c (List.mem_cons.mpr (Or.inl rfl))
      change Agrees (emit cs (j + 1) (pushChild b c j))
      apply ih (j + 1) (pushChild b c j) (pushChild_agrees b c j ha hc) _ htail
      intro d hd k hm
      rw [pushChild_cells, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hf d (List.mem_cons.mpr (Or.inr hd)) k hm
      · have he : Cell.child d k = Cell.child c j := by simpa using hm
        cases he
        exact hnot hd

private theorem step_agrees (g : ChildLists N) (s : Raw N) (u : Fin N)
    (ha : Agrees s.buf) (hf : Fresh s.buf (g.get u)) (hn : (g.get u).Nodup) :
    Agrees (step g s u).buf := by
  have hr : Agrees (pushRoot s.buf u) := by
    intro c j h
    rw [pushRoot_pos]
    apply ha c j
    simpa [pushRoot_cells] using h
  have hfr : Fresh (pushRoot s.buf u) (g.get u) := by
    intro c hc j h
    exact hf c hc j (by simpa [pushRoot_cells] using h)
  have hb : (step g s u).buf = emit (g.get u) 1 (pushRoot s.buf u) := by
    cases s
    rfl
  rw [hb]
  exact emit_agrees _ _ _ hr hfr hn

private theorem scan_agrees (g : ChildLists N) (parent : Fin N → Fin N)
    (hp : ∀ u c, c ∈ g.get u → parent c = u)
    (hb : ∀ u, (g.get u).Nodup)
    (us : List (Fin N)) (s : Raw N) (hn : us.Nodup) (ha : Agrees s.buf)
    (hf : ∀ u ∈ us, Fresh s.buf (g.get u)) :
    Agrees (scan g us s).buf := by
  induction us generalizing s with
  | nil => exact ha
  | cons u us ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      have hu := hf u (List.mem_cons.mpr (Or.inl rfl))
      change Agrees (scan g us (step g s u)).buf
      apply ih (step g s u) htail (step_agrees g s u ha hu (hb u))
      intro v hv c hc j hm
      rw [step_cells, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hf v (List.mem_cons.mpr (Or.inr hv)) c hc j hm
      · have he : u = v := (hp u c (rowSpec_child_mem hm)).symm.trans (hp v c hc)
        exact hnot (he.symm ▸ hv)

structure Layout (g : ChildLists N) where
  cells : Array (Cell N)
  directory : Array (Nat × Nat)
  directory_size : directory.size = N
  localPos : Slots N Nat
  cells_exact : cells.toList = flatSpec g (finElems N)
  directory_exact : directory.toList = directorySpec g 0 (finElems N)
  pos_exact : ∀ c j, Cell.child c j ∈ cells.toList → localPos.read c = j

/-- One outer pass over the retained buckets and one visit to each child
record. The old flat buffer is not retained when emitting the next row. -/
def ofBuckets (root : Fin N) (parent : Fin N → Fin N) (g : ChildLists N)
    (hg : ∀ u, g.get u = bucketChildren root parent u) : Layout g :=
  let s := scan g (finElems N) (initial N)
  have hd : s.dirs.toList = directorySpec g 0 (finElems N) := by
    simpa [s, initial] using scan_dirs g (finElems N) (initial N)
  { cells := s.buf.cells
    directory := s.dirs
    directory_size := by
      simpa [directorySpec_length, elems_length] using congrArg List.length hd
    localPos := s.buf.pos
    cells_exact := by
      simpa [s, initial] using scan_cells g (finElems N) (initial N)
    directory_exact := hd
    pos_exact := by
      have hp (u c : Fin N) (hc : c ∈ g.get u) : parent c = u := by
        rw [hg u] at hc
        exact ((bucket_mem root parent u c).mp hc).2
      have hn (u : Fin N) : (g.get u).Nodup := by
        rw [hg u]
        exact bucket_nodup root parent u
      have ha : Agrees (initial N).buf := by
        intro c j h
        simp [initial] at h
      have hf : ∀ u ∈ finElems N, Fresh (initial N).buf (g.get u) := by
        intro u hu c hc j h
        simp [initial] at h
      exact scan_agrees g parent hp hn (finElems N) (initial N)
        (elems_nodup N) ha hf }

/-- Bucketing is only needed here if the caller does not already have it.
For a retained packed layout, call `ofBuckets` with `buckets` and `bucket_read`. -/
def build (x : PackedStaticLayout.Input N) :
    Layout (bucketChildLists x.root x.parent.read) :=
  ofBuckets x.root x.parent.read (bucketChildLists x.root x.parent.read)
    (bucketChildLists_get x.root x.parent.read)

private theorem array_at {α : Type} (a : Array α) (i : Nat) (hi : i < a.size) :
    a.toList[i]? = some a[i] := by
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp

private theorem array_mem {α : Type} (a : Array α) (i : Nat) (hi : i < a.size) :
    a[i] ∈ a.toList :=
  List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩

private theorem model_at (g : ChildLists N) (us : List (Fin N))
    (pre : List (Cell N)) (i : Nat) (u : Fin N) (hu : us[i]? = some u) :
    ∃ p, (directorySpec g pre.length us)[i]? = some (p, (rowSpec g u).length) ∧
      p = pre.length + (flatSpec g (us.take i)).length ∧
      p + (rowSpec g u).length ≤ (pre ++ flatSpec g us).length ∧
      ∀ j, j < (rowSpec g u).length →
        (pre ++ flatSpec g us)[p + j]? = (rowSpec g u)[j]? := by
  induction us generalizing pre i with
  | nil => simp at hu
  | cons v vs ih =>
      cases i with
      | zero =>
          have he : v = u := by simpa using hu
          subst v
          refine ⟨pre.length, rfl, by simp [flatSpec], by simp [flatSpec], ?_⟩
          intro j hj
          change (pre ++ (rowSpec g u ++ flatSpec g vs))[pre.length + j]? = _
          rw [List.getElem?_append_right (by omega)]
          have hs : pre.length + j - pre.length = j := by omega
          rw [hs, List.getElem?_append_left hj]
      | succ i =>
          have hv : vs[i]? = some u := by simpa using hu
          obtain ⟨p, hd, hp, hb, ha⟩ := ih (pre ++ rowSpec g v) i hv
          refine ⟨p, ?_, ?_, ?_, ?_⟩
          · simpa [directorySpec, List.length_append] using hd
          · simpa [flatSpec, List.length_append, Nat.add_assoc] using hp
          · simpa [flatSpec, List.append_assoc] using hb
          · intro j hj
            simpa [flatSpec, List.append_assoc] using ha j hj

namespace Layout

variable {g : ChildLists N}

private def descriptor (r : Layout g) (u : Fin N) : Nat × Nat :=
  r.directory[u.val]'(by rw [r.directory_size]; exact u.isLt)

def start (r : Layout g) (u : Fin N) : Nat := (r.descriptor u).1

def length (r : Layout g) (u : Fin N) : Nat := (r.descriptor u).2

private theorem row_info (r : Layout g) (u : Fin N) :
    r.length u = (rowSpec g u).length ∧
    r.start u = (flatSpec g ((finElems N).take u.val)).length ∧
    r.start u + r.length u ≤ r.cells.size ∧
    ∀ j, j < r.length u →
      r.cells.toList[r.start u + j]? = (rowSpec g u)[j]? := by
  obtain ⟨p, hd, hp, hb, ha⟩ := model_at g (finElems N) [] u.val u (elems_at u)
  have hdir : r.directory.toList[u.val]? = some (r.descriptor u) :=
    array_at r.directory u.val (by rw [r.directory_size]; exact u.isLt)
  rw [r.directory_exact] at hdir
  have hpair : r.descriptor u = (p, (rowSpec g u).length) :=
    Option.some.inj (hdir.symm.trans hd)
  have hs : r.start u = p := congrArg Prod.fst hpair
  have hl : r.length u = (rowSpec g u).length := congrArg Prod.snd hpair
  refine ⟨hl, ?_, ?_, ?_⟩
  · rw [hs]
    simpa using hp
  · rw [hs, hl]
    have h : p + (rowSpec g u).length ≤ r.cells.toList.length := by
      rw [r.cells_exact]
      simpa using hb
    simpa using h
  · intro j hj
    rw [hs, r.cells_exact]
    simpa using ha j (hl ▸ hj)

theorem length_exact (r : Layout g) (u : Fin N) :
    r.length u = (g.get u).length + 1 :=
  (r.row_info u).1.trans (rowSpec_length g u)

private theorem root_lt (r : Layout g) (u : Fin N) : 0 < r.length u := by
  rw [r.length_exact]
  omega

private theorem cell_bound (r : Layout g) (u : Fin N) (i : Fin (r.length u)) :
    r.start u + i.val < r.cells.size := by
  have hb := (r.row_info u).2.2.1
  have hi := i.isLt
  omega

def cell (r : Layout g) (u : Fin N) (i : Fin (r.length u)) : Cell N :=
  r.cells[r.start u + i.val]'(r.cell_bound u i)

/-- A forward lookup is a directory read and a flat-cell read. -/
def key (r : Layout g) (u : Fin N) (i : Fin (r.length u)) : Key N :=
  (r.cell u i).key

private theorem read_spec (r : Layout g) (u : Fin N) (i : Fin (r.length u)) :
    (rowSpec g u)[i.val]? = some (r.cell u i) :=
  ((r.row_info u).2.2.2 i.val i.isLt).symm.trans
    (array_at r.cells _ (r.cell_bound u i))

private theorem cell_cases (r : Layout g) (u : Fin N) (i : Fin (r.length u)) :
    (i.val = 0 ∧ r.cell u i = .root u) ∨
      ∃ c, r.cell u i = .child c i.val ∧ c ∈ g.get u := by
  have hr := r.read_spec u i
  generalize hk : i.val = k at hr ⊢
  have hi : k < (g.get u).length + 1 := by
    rw [← r.length_exact u, ← hk]
    exact i.isLt
  cases k with
  | zero =>
      have hh : some (Cell.root u) = some (r.cell u i) := by
        simpa [rowSpec] using hr
      exact Or.inl ⟨rfl, (Option.some.inj hh).symm⟩
  | succ j =>
      have hj : j < (g.get u).length := by omega
      refine Or.inr ⟨(g.get u)[j], Option.some.inj (hr.symm.trans
        (rowSpec_succ g u j hj)), ?_⟩
      exact List.mem_iff_getElem.mpr ⟨j, hj, rfl⟩

private theorem cell_zero (r : Layout g) (u : Fin N) :
    r.cell u ⟨0, r.root_lt u⟩ = .root u := by
  have h := r.read_spec u ⟨0, r.root_lt u⟩
  have hh : some (.root u) = some (r.cell u ⟨0, r.root_lt u⟩) := by
    simpa [rowSpec] using h
  exact (Option.some.inj hh).symm

private theorem succ_lt (r : Layout g) (u : Fin N) (j : Nat)
    (hj : j < (g.get u).length) : j + 1 < r.length u := by
  rw [r.length_exact]
  omega

private theorem cell_succ (r : Layout g) (u : Fin N) (j : Nat)
    (hj : j < (g.get u).length) :
    r.cell u ⟨j + 1, r.succ_lt u j hj⟩ = .child (g.get u)[j] (j + 1) := by
  exact Option.some.inj ((r.read_spec u ⟨j + 1, r.succ_lt u j hj⟩).symm.trans
    (rowSpec_succ g u j hj))

theorem key_zero (r : Layout g) (u : Fin N) :
    r.key u ⟨0, r.root_lt u⟩ = .inl u := by
  simp [key, r.cell_zero, Cell.key]

/-- Ordered grouping specification: child slot `j + 1` is bucket entry `j`.
The bucket access in this statement is not performed by `key`. -/
theorem key_succ (r : Layout g) (u : Fin N) (j : Nat)
    (hj : j < (g.get u).length) :
    r.key u ⟨j + 1, r.succ_lt u j hj⟩ = .inr (g.get u)[j] := by
  simp [key, r.cell_succ u j hj, Cell.key]

theorem key_is_root_iff (r : Layout g) (u d : Fin N) (i : Fin (r.length u)) :
    r.key u i = .inl d ↔ i.val = 0 ∧ d = u := by
  constructor
  · intro h
    rcases r.cell_cases u i with ⟨hz, hr⟩ | ⟨c, hc, _⟩
    · have he : (Sum.inl u : Key N) = Sum.inl d := by
        simpa only [key, hr, Cell.key] using h
      exact ⟨hz, (Sum.inl.inj he).symm⟩
    · simp [key, hc, Cell.key] at h
  · rintro ⟨hz, hd⟩
    subst d
    have hi : i = (⟨0, r.root_lt u⟩ : Fin (r.length u)) := Fin.ext hz
    exact (congrArg (r.key u) hi).trans (r.key_zero u)

def decode (r : Layout g) (u : Fin N) (i : Fin (r.length u)) : Occurrence g u :=
  ⟨r.key u i, by
    rcases r.cell_cases u i with ⟨_, h⟩ | ⟨c, h, hc⟩
    · simp [key, h, Cell.key, Occurs]
    · simpa [key, h, Cell.key, Occurs] using hc⟩

private theorem child_pos (r : Layout g) (u c : Fin N) (i : Fin (r.length u))
    (hc : r.cell u i = .child c i.val) : r.localPos.read c = i.val := by
  apply r.pos_exact c i.val
  rw [← hc]
  exact array_mem r.cells _ (r.cell_bound u i)

private def rank (r : Layout g) : Key N → Nat
  | .inl _ => 0
  | .inr c => r.localPos.read c

private theorem rank_lt (r : Layout g) (u : Fin N) (k : Occurrence g u) :
    r.rank k.val < r.length u := by
  rcases k with ⟨k, hk⟩
  cases k with
  | inl d => exact r.root_lt u
  | inr c =>
      change c ∈ g.get u at hk
      obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hk
      let i : Fin (r.length u) := ⟨j + 1, r.succ_lt u j hj⟩
      have h : r.cell u i = .child c i.val :=
        (r.cell_succ u j hj).trans (congrArg (fun d : Fin N => Cell.child d (j + 1)) he)
      change r.localPos.read c < r.length u
      calc
        r.localPos.read c = i.val := r.child_pos u c i h
        _ < r.length u := i.isLt

/-- Inverse lookup: slot zero for the root, one scattered-slot read for a
child. The membership certificate and the Fin bound are erased. -/
def encode (r : Layout g) (u : Fin N) (k : Occurrence g u) : Fin (r.length u) :=
  ⟨r.rank k.val, r.rank_lt u k⟩

@[simp] theorem encode_decode (r : Layout g) (u : Fin N) (i : Fin (r.length u)) :
    r.encode u (r.decode u i) = i := by
  apply Fin.ext
  change r.rank ((r.cell u i).key) = i.val
  rcases r.cell_cases u i with ⟨hz, hr⟩ | ⟨c, hc, _⟩
  · simp [hr, Cell.key, rank, hz]
  · simpa [hc, Cell.key, rank] using r.child_pos u c i hc

private theorem decode_surjective (r : Layout g) (u : Fin N) (k : Occurrence g u) :
    ∃ i, r.decode u i = k := by
  rcases k with ⟨k, hk⟩
  cases k with
  | inl d =>
      change d = u at hk
      subst d
      exact ⟨⟨0, r.root_lt u⟩, Subtype.ext (r.key_zero u)⟩
  | inr c =>
      change c ∈ g.get u at hk
      obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hk
      refine ⟨⟨j + 1, r.succ_lt u j hj⟩, Subtype.ext ?_⟩
      change r.key u ⟨j + 1, r.succ_lt u j hj⟩ = .inr c
      rw [r.key_succ u j hj, he]

@[simp] theorem decode_encode (r : Layout g) (u : Fin N) (k : Occurrence g u) :
    r.decode u (r.encode u k) = k := by
  obtain ⟨i, hi⟩ := r.decode_surjective u k
  rw [← hi, r.encode_decode]

theorem occurs_iff (r : Layout g) (u : Fin N) (k : Key N) :
    (∃ i : Fin (r.length u), r.key u i = k) ↔ Occurs g u k := by
  constructor
  · rintro ⟨i, rfl⟩
    exact (r.decode u i).property
  · intro hk
    exact ⟨r.encode u ⟨k, hk⟩, congrArg Subtype.val (r.decode_encode u ⟨k, hk⟩)⟩

theorem key_injective (r : Layout g) (u : Fin N)
    {i j : Fin (r.length u)} (h : r.key u i = r.key u j) : i = j := by
  have hd : r.decode u i = r.decode u j := Subtype.ext h
  simpa only [r.encode_decode] using congrArg (r.encode u) hd

theorem ordinary_child_iff (r : Layout g) (root : Fin N)
    (parent : Fin N → Fin N) (hg : ∀ u, g.get u = bucketChildren root parent u)
    (u c : Fin N) :
    (∃ i : Fin (r.length u), r.key u i = .inr c) ↔ c ≠ root ∧ parent c = u := by
  rw [r.occurs_iff]
  change c ∈ g.get u ↔ _
  rw [hg u]
  exact bucket_mem root parent u c

private theorem sum_lengths_on (r : Layout g) (us : List (Fin N)) :
    (us.map r.length).sum = (flatSpec g us).length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      simp [flatSpec, (r.row_info u).1, ih]

theorem start_eq_prefix (r : Layout g) (u : Fin N) :
    r.start u = (((finElems N).take u.val).map r.length).sum :=
  (r.row_info u).2.1.trans (r.sum_lengths_on ((finElems N).take u.val)).symm

theorem sum_lengths_eq_storage (r : Layout g) :
    ((finElems N).map r.length).sum = r.cells.size := by
  have h := r.sum_lengths_on (finElems N)
  rw [← r.cells_exact] at h
  simpa using h

/-- The scan visits `N` rows and `N - 1` child records. It emits one
directory entry per row, one cell per root or child, and makes exactly
one inverse-slot write per child. The latter is the single `store` call
in each nonempty `emit` step. -/
theorem child_visits (root : Fin N) (parent : Fin N → Fin N)
    (hg : ∀ u, g.get u = bucketChildren root parent u) :
    sumBucketLengths (fun u => g.get u) (finElems N) = N - 1 := by
  rw [show (fun u => g.get u) = bucketChildren root parent from funext hg]
  exact total_bucketChildren_edges root parent

theorem sum_lengths_exact (r : Layout g) (root : Fin N)
    (parent : Fin N → Fin N) (hg : ∀ u, g.get u = bucketChildren root parent u) :
    ((finElems N).map r.length).sum = N + (N - 1) := by
  rw [r.sum_lengths_on, flatSpec_length, elems_length, child_visits root parent hg]

theorem storage_le (r : Layout g) (root : Fin N)
    (parent : Fin N → Fin N) (hg : ∀ u, g.get u = bucketChildren root parent u) :
    r.cells.size ≤ 2 * N := by
  rw [← r.sum_lengths_eq_storage, r.sum_lengths_exact root parent hg]
  omega

end Layout
end PaperB.DenseQuotientRows
