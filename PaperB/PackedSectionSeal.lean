module

public import PaperB.PackedSliceRebase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PairLookup.ColumnReduction.EX52Seal

abbrev Bank (bits : Nat) := Array (ScalarWord bits)

variable {bits : Nat}

def cells : List (Bank bits) → Nat
  | [] => 0
  | b :: bs => b.size + cells bs

theorem cells_eq_sum (bs : List (Bank bits)) :
    cells bs = (bs.map (fun b => b.size)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [cells, ih]

/-- Also defined at `q = bs.length`, where this is the terminal offset. -/
def offset : List (Bank bits) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | b :: bs, q + 1 => b.size + offset bs q

theorem block_end (bs : List (Bank bits)) (q : Nat)
    (hq : q < bs.length) :
    offset bs q + (bs[q]'hq).size ≤ cells bs := by
  induction bs generalizing q with
  | nil => simp at hq
  | cons b bs ih =>
    cases q with
    | zero => simp [offset, cells] <;> omega
    | succ q =>
      have hq' : q < bs.length := by simpa using hq
      have he := ih q hq'
      change b.size + offset bs q + (bs[q]'hq').size ≤ b.size + cells bs
      omega

theorem offset_end (bs : List (Bank bits)) :
    offset bs bs.length = cells bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [offset, cells, ih]

structure Packed (bits : Nat) where
  header : Bank bits
  data : Bank bits

@[inline] def Packed.start (p : Packed bits) (q : Nat)
    (hq : q < p.header.size) : Nat :=
  (p.header[q]'hq).val

@[inline] def Packed.read (p : Packed bits) (q i : Nat)
    (hq : q < p.header.size) (hi : p.start q hq + i < p.data.size) :
    ScalarWord bits :=
  p.data[p.start q hq + i]'hi

/-- One header push per section, including an empty section, and one
terminal push. The second component is temporary, not part of `Packed`. -/
private def scan (bs : List (Bank bits)) (s : Nat) (a : Bank bits)
    (h : s + cells bs < 2 ^ bits) : Bank bits × Nat :=
  match bs with
  | [] => (a.push ⟨s, by simpa [cells] using h⟩, s)
  | b :: rest =>
    scan rest (s + b.size)
      (a.push ⟨s, by omega⟩)
      (by simpa [cells, Nat.add_assoc] using h)

/-- The only payload writer. A cell step does one input word load and one
push into the same global accumulator. A section step does neither.
The capacity is reserved before entering this loop. -/
private def fill (fuel : Nat) (bs : List (Bank bits)) (j : Nat)
    (out : Bank bits) : Bank bits :=
  match fuel with
  | 0 => out
  | k + 1 =>
    match bs with
    | [] => out
    | b :: rest =>
      if hj : j < b.size then
        fill k bs (j + 1) (out.push (b[j]'hj))
      else
        fill k rest 0 out

private def scan0 (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    Bank bits × Nat :=
  scan bs 0 #[] (by simpa using h)

/-- No input blocks, list spine, work counters, or scan state are returned. -/
def serialize (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) : Packed bits :=
  let r := scan0 bs h
  ⟨r.1, fill (r.1.size - 1 + r.2) bs 0 (Array.emptyWithCapacity r.2)⟩

/- The following lists are specifications only; `serialize` does not build them. -/

private def heads (bs : List (Bank bits)) (s : Nat) : List Nat :=
  match bs with
  | [] => [s]
  | b :: rest => s :: heads rest (s + b.size)

@[simp] private theorem heads_length (bs : List (Bank bits)) (s : Nat) :
    (heads bs s).length = bs.length + 1 := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => simp [heads, ih]

private theorem heads_at (bs : List (Bank bits)) (s q : Nat)
    (hq : q ≤ bs.length) :
    (heads bs s)[q]'(by rw [heads_length]; omega) = s + offset bs q := by
  induction bs generalizing s q with
  | nil =>
    have e : q = 0 := by simpa using hq
    subst q
    rfl
  | cons b bs ih =>
    cases q with
    | zero => rfl
    | succ q =>
      have hq' : q ≤ bs.length := by simpa using hq
      have hp : q < (heads bs (s + b.size)).length := by
        rw [heads_length]
        omega
      change (heads bs (s + b.size))[q]'hp = s + (b.size + offset bs q)
      exact (ih (s + b.size) q hq').trans (Nat.add_assoc _ _ _)

private theorem scan_spec (bs : List (Bank bits)) (s : Nat)
    (a : Bank bits) (h : s + cells bs < 2 ^ bits) :
    (scan bs s a h).1.toList.map (fun w => w.val) =
      a.toList.map (fun w => w.val) ++ heads bs s ∧
    (scan bs s a h).2 = s + cells bs := by
  induction bs generalizing s a with
  | nil => simp [scan, heads, cells, Array.toList_push]
  | cons b bs ih =>
    have hs : s < 2 ^ bits := by omega
    have ht : s + b.size + cells bs < 2 ^ bits := by
      simpa [cells, Nat.add_assoc] using h
    simpa [scan, heads, cells, Array.toList_push, List.append_assoc,
      Nat.add_assoc] using ih (s + b.size) (a.push ⟨s, hs⟩) ht

private def flat : List (Bank bits) → List (ScalarWord bits)
  | [] => []
  | b :: bs => b.toList ++ flat bs

@[simp] private theorem flat_length (bs : List (Bank bits)) :
    (flat bs).length = cells bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [flat, cells, ih]

private def pending : List (Bank bits) → Nat → List (ScalarWord bits)
  | [], _ => []
  | b :: bs, j => b.toList.drop j ++ flat bs

@[simp] private theorem pending_zero (bs : List (Bank bits)) :
    pending bs 0 = flat bs := by
  cases bs <;> rfl

private def headSize : List (Bank bits) → Nat
  | [] => 0
  | b :: _ => b.size

private theorem drop_step {α : Type} (l : List α) (j : Nat)
    (h : j < l.length) :
    l.drop j = (l[j]'h) :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at h
  | cons x l ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj : j < l.length := by simpa using h
      simpa using ih j hj

private theorem drop_done {α : Type} (l : List α) (j : Nat)
    (h : l.length ≤ j) : l.drop j = [] := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons x l ih =>
    cases j with
    | zero => simp at h
    | succ j =>
      have hj : l.length ≤ j := by simpa using h
      simpa using ih j hj

private theorem pending_step (b : Bank bits) (bs : List (Bank bits))
    (j : Nat) (hj : j < b.size) :
    pending (b :: bs) j = (b[j]'hj) :: pending (b :: bs) (j + 1) := by
  have hj' : j < b.toList.length := by simpa using hj
  simp only [pending]
  rw [drop_step b.toList j hj']
  simp

private theorem pending_done (b : Bank bits) (bs : List (Bank bits)) :
    pending (b :: bs) b.size = pending bs 0 := by
  have h : b.toList.length ≤ b.size := by simp
  rw [pending, drop_done b.toList b.size h]
  simp

/-- Proof-only trace of the actual loop. The last indices count cell steps
(one payload read and one data write each) and section steps, respectively.
`word` bounds the source index and destination cursor; `section` requires
the local cursor to be exactly at the endpoint, even for an empty block. -/
inductive CopySteps (cap : Nat) :
    Nat → List (Bank bits) → Nat → Bank bits → Bank bits → Nat → Nat → Prop
  | stop (j : Nat) (out : Bank bits) (bound : out.size ≤ cap) :
      CopySteps cap 0 [] j out out 0 0
  | word {k j w r : Nat} {b : Bank bits} {bs : List (Bank bits)}
      {out dst : Bank bits} (hj : j < b.size) (room : out.size < cap)
      (tail : CopySteps cap k (b :: bs) (j + 1) (out.push (b[j]'hj)) dst w r) :
      CopySteps cap (k + 1) (b :: bs) j out dst (w + 1) r
  | section {k w r : Nat} {b : Bank bits} {bs : List (Bank bits)}
      {out dst : Bank bits} (tail : CopySteps cap k bs 0 out dst w r) :
      CopySteps cap (k + 1) (b :: bs) b.size out dst w (r + 1)

private theorem fill_spec (cap fuel : Nat) (bs : List (Bank bits))
    (j : Nat) (out : Bank bits)
    (hf : fuel = bs.length + (pending bs j).length)
    (hc : out.size + (pending bs j).length = cap)
    (hj : j ≤ headSize bs) :
    CopySteps cap fuel bs j out (fill fuel bs j out)
      (pending bs j).length bs.length ∧
    (fill fuel bs j out).toList = out.toList ++ pending bs j := by
  induction fuel generalizing bs j out with
  | zero =>
    cases bs with
    | nil =>
      have ho : out.size = cap := by simpa [pending] using hc
      simpa [fill, pending] using
        (show CopySteps cap 0 [] j out out 0 0 ∧ out.toList = out.toList
         from ⟨CopySteps.stop j out (Nat.le_of_eq ho), rfl⟩)
    | cons b bs =>
      simp only [List.length_cons] at hf
      omega
  | succ k ih =>
    cases bs with
    | nil => simp [pending] at hf
    | cons b bs =>
      change j ≤ b.size at hj
      by_cases hlt : j < b.size
      · have e := pending_step b bs j hlt
        have el := congrArg List.length e
        simp only [List.length_cons] at el
        have hf' : k = (b :: bs).length + (pending (b :: bs) (j + 1)).length := by
          omega
        have hc' : (out.push (b[j]'hlt)).size +
            (pending (b :: bs) (j + 1)).length = cap := by
          simp only [Array.size_push]
          omega
        have hj' : j + 1 ≤ headSize (b :: bs) := by
          change j + 1 ≤ b.size
          omega
        obtain ⟨tr, eq⟩ := ih (b :: bs) (j + 1) (out.push (b[j]'hlt)) hf' hc' hj'
        simp only [fill, dif_pos hlt, e, List.length_cons]
        refine ⟨CopySteps.word hlt (by omega) tr, ?_⟩
        simpa [Array.toList_push, List.append_assoc] using eq
      · have he : j = b.size := by omega
        subst j
        have e := pending_done b bs
        have el := congrArg List.length e
        simp only [List.length_cons] at hf
        have hf' : k = bs.length + (pending bs 0).length := by omega
        have hc' : out.size + (pending bs 0).length = cap := by omega
        obtain ⟨tr, eq⟩ := ih bs 0 out hf' hc' (Nat.zero_le _)
        simp only [fill, dif_neg hlt, e, List.length_cons]
        exact ⟨CopySteps.section tr, eq⟩

@[simp] private theorem empty_list (n : Nat) :
    (Array.emptyWithCapacity n : Bank bits).toList = [] := rfl

@[simp] private theorem empty_size (n : Nat) :
    (Array.emptyWithCapacity n : Bank bits).size = 0 := rfl

private theorem seal_models (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    (serialize bs h).header.toList.map (fun w => w.val) = heads bs 0 ∧
    (serialize bs h).data.toList = flat bs ∧
    CopySteps (cells bs) (bs.length + cells bs) bs 0
      (Array.emptyWithCapacity (cells bs)) (serialize bs h).data (cells bs) bs.length := by
  have hs : (scan0 bs h).1.toList.map (fun w => w.val) = heads bs 0 ∧
      (scan0 bs h).2 = cells bs := by
    simpa [scan0] using scan_spec bs 0 #[] (by simpa using h)
  have hn : (scan0 bs h).1.size = bs.length + 1 := by
    simpa using congrArg List.length hs.1
  have hf : (scan0 bs h).1.size - 1 + (scan0 bs h).2 =
      bs.length + (pending bs 0).length := by simp [hn, hs.2]
  have hc : (Array.emptyWithCapacity (scan0 bs h).2 : Bank bits).size +
      (pending bs 0).length = cells bs := by simp
  obtain ⟨tr, eq⟩ := fill_spec (cells bs)
    ((scan0 bs h).1.size - 1 + (scan0 bs h).2) bs 0
    (Array.emptyWithCapacity (scan0 bs h).2) hf hc (Nat.zero_le _)
  refine ⟨hs.1, ?_, ?_⟩
  · simpa [serialize] using eq
  · simpa [serialize, hn, hs.2] using tr

/-- In the source-level RAM count: `cells bs` payload loads and data pushes,
and `bs.length` section advances. Each nonterminal writer step checks one
block size. The header scan reads one block size per section and pushes
`bs.length + 1` words. These are not counts of Lean runtime instructions. -/
theorem seal_copy_steps (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    CopySteps (cells bs) (bs.length + cells bs) bs 0
      (Array.emptyWithCapacity (cells bs)) (serialize bs h).data (cells bs) bs.length :=
  (seal_models bs h).2.2

theorem seal_header_size (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    (serialize bs h).header.size = bs.length + 1 := by
  simpa using congrArg List.length (seal_models bs h).1

theorem seal_data_size (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    (serialize bs h).data.size = cells bs := by
  simpa using congrArg List.length (seal_models bs h).2.1

theorem header_bound (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q ≤ bs.length) : q < (serialize bs h).header.size := by
  rw [seal_header_size]
  omega

private theorem list_at_eq {α : Type} {l r : List α} (e : l = r)
    {i : Nat} (hl : i < l.length) (hr : i < r.length) :
    l[i]'hl = r[i]'hr := by
  subst r
  rfl

private theorem list_index_eq {α : Type} (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (e : i = j) :
    l[i]'hi = l[j]'hj := by
  subst j
  rfl

theorem seal_start (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q ≤ bs.length) :
    (serialize bs h).start q (header_bound bs h q hq) = offset bs q := by
  have hl : q < ((serialize bs h).header.toList.map (fun w => w.val)).length := by
    simpa using header_bound bs h q hq
  have hr : q < (heads bs 0).length := by rw [heads_length]; omega
  have e := list_at_eq (seal_models bs h).1 hl hr
  simpa only [Packed.start, List.getElem_map, Array.getElem_toList, Nat.zero_add]
    using e.trans (heads_at bs 0 q hq)

private theorem flat_bound (bs : List (Bank bits)) (q : Nat)
    (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    offset bs q + i < (flat bs).length := by
  have h := block_end bs q hq
  rw [flat_length]
  omega

private theorem flat_at (bs : List (Bank bits)) (q : Nat)
    (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    (flat bs)[offset bs q + i]'(flat_bound bs q hq i hi) = (bs[q]'hq)[i]'hi := by
  induction bs generalizing q with
  | nil => simp at hq
  | cons b bs ih =>
    cases q with
    | zero =>
      change i < b.size at hi
      have hl : i < b.toList.length := by simpa using hi
      have ha : i < (b.toList ++ flat bs).length := by simp <;> omega
      simp only [flat, offset, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem_append_left hl] <;> simp
    | succ q =>
      have hq' : q < bs.length := by simpa using hq
      have hi' : i < (bs[q]'hq').size := hi
      have hb := flat_bound bs q hq' i hi'
      have ha : b.size + offset bs q + i < (b.toList ++ flat bs).length := by
        rw [List.length_append, Array.length_toList]
        omega
      have ht : b.toList.length ≤ b.size + offset bs q + i := by
        simp <;> omega
      have e : b.size + offset bs q + i - b.toList.length = offset bs q + i := by
        simp <;> omega
      change (b.toList ++ flat bs)[b.size + offset bs q + i]'ha =
        (bs[q]'hq')[i]'hi'
      rw [List.getElem_append_right ht]
      exact (list_index_eq (flat bs) (by rw [e]; exact hb) hb e).trans (ih q hq' hi')

theorem read_bound (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    (serialize bs h).start q (header_bound bs h q (Nat.le_of_lt hq)) + i <
      (serialize bs h).data.size := by
  rw [seal_start bs h q (Nat.le_of_lt hq), seal_data_size]
  have hb := block_end bs q hq
  omega

/-- The lookup does not consult `bs`: one header load, one address addition,
and one payload load. The proof arguments erase. -/
theorem seal_read (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    (serialize bs h).read q i (header_bound bs h q (Nat.le_of_lt hq))
      (read_bound bs h q hq i hi) = (bs[q]'hq)[i]'hi := by
  let a := (serialize bs h).start q (header_bound bs h q (Nat.le_of_lt hq)) + i
  have ea : a = offset bs q + i := by
    dsimp only [a]
    rw [seal_start bs h q (Nat.le_of_lt hq)]
  have hl : a < (serialize bs h).data.toList.length := by
    simpa only [Array.length_toList, a] using read_bound bs h q hq i hi
  have hr : a < (flat bs).length := by
    rw [ea]
    exact flat_bound bs q hq i hi
  have e₁ := list_at_eq (seal_models bs h).2.1 hl hr
  have e₂ := list_index_eq (flat bs) hr (flat_bound bs q hq i hi) ea
  simpa only [Packed.read, Array.getElem_toList, a] using
    e₁.trans (e₂.trans (flat_at bs q hq i hi))

/-- EX5.2 placement uses the actual header entry, not a recomputed prefix
sum. The full block endpoint is valid even when the block is empty. -/
theorem seal_placement (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q < bs.length) :
    SlicePlacement (bs[q]'hq) (serialize bs h).data
      ((serialize bs h).start q (header_bound bs h q (Nat.le_of_lt hq))) := by
  have he := seal_start bs h q (Nat.le_of_lt hq)
  have hb := block_end bs q hq
  refine ⟨by omega, ?_, ?_⟩
  · rw [seal_data_size]
    omega
  · intro i hi
    exact (seal_read bs h q hq i hi).symm

/-- Bind `packed := serialize bs h` once at the call site. Rebasing uses the old
slice metadata and the packed header word; this placement proof is erased. -/
theorem seal_rebase_get (bs : List (Bank bits)) (h : cells bs < 2 ^ bits)
    (q : Nat) (hq : q < bs.length) (p : Slice (bs[q]'hq))
    (i : Nat) (hi : i < p.len) :
    (rebaseSlice p (seal_placement bs h q hq)).get i hi = p.get i hi :=
  rebaseSlice_get p (seal_placement bs h q hq) i hi

end PaperB.PairLookup.ColumnReduction.EX52Seal
