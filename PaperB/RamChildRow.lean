module

public import PaperB.StaticChildLookup
public import PaperB.RamSearchCorrect

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram.Predecessor.ChildRow
open PaperB.Machine (Word)

open PaperB.StaticChildLookup
  (Child childAt Contains Valid entry_strict lookup lookup_some_iff lookup_none_iff)

universe u v

private abbrev domainOf {A : Type u} {B : Sort v} (_ : A → B) : Type u := A

/-- The actual input type of the scalar worker, taken from its `Slice` API. -/
abbrev EntryInput {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) : Type :=
  domainOf (Slice (bits := bits) (cap := cap) (hcap := hcap))

/--
A compiled view of an original-dominator child row. `input.words` is the
sealed entry column. The other two sealed columns have the same capacity
and use the base and length in `entries`; they have no independent offsets.
-/
structure RowView {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (input : EntryInput hcap) where
  entries : Slice (bits := bits) (cap := cap) (hcap := hcap) input
  stops : Array (Word bits)
  childIds : Array (Word bits)
  stops_size : stops.size = cap
  childIds_size : childIds.size = cap

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {input : EntryInput hcap}

namespace RowView

private theorem address_lt (v : RowView hcap input) {i : Nat}
    (hi : i < v.entries.len) : v.entries.base.val + i < cap :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) v.entries.within

def stopAt (v : RowView hcap input) (i : Nat) (hi : i < v.entries.len) : Nat :=
  (v.stops[v.entries.base.val + i]'(by
    rw [v.stops_size]
    exact address_lt v hi)).val

def idAt (v : RowView hcap input) (i : Nat) (hi : i < v.entries.len) : Nat :=
  (v.childIds[v.entries.base.val + i]'(by
    rw [v.childIds_size]
    exact address_lt v hi)).val

def readAt (v : RowView hcap input) (i : Nat) (hi : i < v.entries.len) :
    Child Nat where
  id := v.idAt i hi
  entry := (v.entries.get i hi).val
  stop := v.stopAt i hi

/--
The after-worker reader. Zero has no candidate; a positive count selects
index `count - 1`. Charge three column reads for an in-bounds candidate,
even when the interval test rejects it. No proof row is read.
-/
def finish (v : RowView hcap input) (rank : Nat) :
    Nat → Option (Child Nat) × Nat
  | 0 => (none, 0)
  | i + 1 =>
      if hi : i < v.entries.len then
        let c := v.readAt i hi
        ((if c.entry ≤ rank ∧ rank < c.stop then some c else none), 3)
      else
        (none, 0)

theorem finish_reads_le (v : RowView hcap input) (rank count : Nat) :
    (v.finish rank count).2 ≤ 3 := by
  cases count with
  | zero => simp [finish]
  | succ i =>
    by_cases hi : i < v.entries.len <;> simp [finish, hi]

end RowView

/-- The logical row is used only in proofs, never to build the RAM input. -/
structure RowAgreement (v : RowView hcap input) (row : Array (Child Nat)) :
    Prop where
  valid : Valid row
  len_eq : v.entries.len = row.size
  columns : ∀ (i : Nat) (hi : i < v.entries.len) (hr : i < row.size),
    (v.entries.get i hi).val = (childAt row ⟨i, hr⟩).entry ∧
    v.stopAt i hi = (childAt row ⟨i, hr⟩).stop ∧
    v.idAt i hi = (childAt row ⟨i, hr⟩).id

variable {v : RowView hcap input} {row : Array (Child Nat)}

theorem RowAgreement.sorted (a : RowAgreement v row) : v.entries.Sorted := by
  intro i j hi hj hij
  have hir : i < row.size := by simpa only [a.len_eq] using hi
  have hjr : j < row.size := by simpa only [a.len_eq] using hj
  rw [(a.columns i hi hir).1, (a.columns j hj hjr).1]
  by_cases h : i = j
  · subst j
    exact Nat.le_refl _
  · exact Nat.le_of_lt
      (entry_strict a.valid ⟨i, hir⟩ ⟨j, hjr⟩ (by change i < j; omega))

theorem RowAgreement.readAt_eq (a : RowAgreement v row)
    (i : Nat) (hi : i < v.entries.len) (hr : i < row.size) :
    v.readAt i hi = childAt row ⟨i, hr⟩ := by
  obtain ⟨he, hs, hd⟩ := a.columns i hi hr
  simp only [RowView.readAt, he, hs, hd] <;>
    cases childAt row ⟨i, hr⟩ <;> rfl

/-- The worker's lower register is a count, not a zero-based child index. -/
theorem RowAgreement.cut (a : RowAgreement v row) {key : Word bits}
    {count : Nat} (answer : Answer v.entries key count) :
    count ≤ v.entries.len ∧
      ∀ i : Fin row.size, (childAt row i).entry ≤ key.val ↔ i.val < count := by
  obtain ⟨hb, hlo, hhi⟩ := answer
  refine ⟨hb, ?_⟩
  intro i
  have hi : i.val < v.entries.len := by
    rw [a.len_eq]
    exact i.isLt
  have he : (v.entries.get i.val hi).val = (childAt row i).entry :=
    (a.columns i.val hi i.isLt).1
  constructor
  · intro hle
    by_cases h : i.val < count
    · exact h
    · have hgt := hhi i.val hi (by omega)
      rw [he] at hgt
      omega
  · intro h
    have hle := hlo i.val hi h
    rwa [he] at hle

/-- Disjointness forces any containing interval to be the last qualifying entry. -/
private theorem count_of_contains (valid : Valid row) {rank count : Nat}
    (hb : count ≤ row.size)
    (cut : ∀ i : Fin row.size, (childAt row i).entry ≤ rank ↔ i.val < count)
    (i : Fin row.size) (hit : Contains (childAt row i) rank) :
    count = i.val + 1 := by
  have hi := (cut i).mp hit.1
  let j : Fin row.size := ⟨count - 1, by omega⟩
  have hj : j.val = count - 1 := rfl
  have hje := (cut j).mpr (by omega)
  by_cases hij : i.val < j.val
  · have hsep := valid.2 i j hij
    have hstop := hit.2
    omega
  · omega

/-- The physical reader agrees with lookup before encoding `none` as zero. -/
theorem RowAgreement.finish_correct (a : RowAgreement v row) {key : Word bits}
    {count : Nat} (answer : Answer v.entries key count) :
    (v.finish key.val count).1 = lookup row key.val := by
  obtain ⟨hb, cut⟩ := a.cut answer
  cases count with
  | zero =>
    have hn : lookup row key.val = none :=
      (lookup_none_iff a.valid key.val).2 (by
        rintro ⟨i, hit⟩
        have hi := (cut i).mp hit.1
        omega)
    simpa only [RowView.finish] using hn.symm
  | succ j =>
    have hj : j < v.entries.len := by omega
    have hjr : j < row.size := by simpa only [a.len_eq] using hj
    let i : Fin row.size := ⟨j, hjr⟩
    have hread : v.readAt j hj = childAt row i := a.readAt_eq j hj hjr
    have hfinish :
        (v.finish key.val (j + 1)).1 =
          (if (childAt row i).entry ≤ key.val ∧ key.val < (childAt row i).stop
           then some (childAt row i) else none) := by
      simp only [RowView.finish, dif_pos hj, hread]
    rw [hfinish]
    by_cases hm : (childAt row i).entry ≤ key.val ∧ key.val < (childAt row i).stop
    · rw [if_pos hm]
      exact ((lookup_some_iff a.valid key.val (childAt row i)).2
        ⟨i, rfl, hm⟩).symm
    · rw [if_neg hm]
      apply Eq.symm
      apply (lookup_none_iff a.valid key.val).2
      rintro ⟨k, hk⟩
      have hbr : j + 1 ≤ row.size := by simpa only [a.len_eq] using hb
      have heq : j + 1 = k.val + 1 :=
        count_of_contains a.valid hbr cut k hk
      have hki : k = i := Fin.ext (by change k.val = j; omega)
      apply hm
      simpa only [hki, Contains] using hk

/-- The numeric convention at the call boundary. -/
def encode : Option (Child Nat) → Nat
  | none => 0
  | some c => c.id

def workerBudget (len : Nat) : Nat :=
  11 * (Nat.log2 (len + 1) + 1)

structure CallResult where
  count : Nat
  childId : Nat
  cost : Nat

/--
Run the existing scalar RAM program on the supplied entry input, then read
the candidate from the sealed columns. Cost is executed RAM instructions
plus after-worker column reads. The reader itself is not lowered to ROM here.
-/
def execute (v : RowView hcap input) (key : Word bits) : Option CallResult :=
  match run (worker hcap) input (workerBudget v.entries.len)
      (init v.entries key) with
  | none => none
  | some r =>
    let count := lower r.finalState
    let f := v.finish key.val count
    some ⟨count, encode f.1, r.executed + f.2⟩

theorem execute_correct (a : RowAgreement v row) (key : Word bits) :
    ∃ r out,
      run (worker hcap) input (workerBudget v.entries.len)
        (init v.entries key) = some r ∧
      Answer v.entries key (lower r.finalState) ∧
      r.finalState.data = #[] ∧
      execute v key = some out ∧
      out.count = lower r.finalState ∧
      out.count ≤ v.entries.len ∧
      (∀ i : Fin row.size, (childAt row i).entry ≤ key.val ↔ i.val < out.count) ∧
      (v.finish key.val out.count).1 = lookup row key.val ∧
      out.childId = encode (lookup row key.val) ∧
      out.cost = r.executed + (v.finish key.val out.count).2 ∧
      out.cost ≤ 11 * Nat.log2 (v.entries.len + 1) + 14 := by
  obtain ⟨r, hr, ha, hd, hsteps⟩ := worker_correct v.entries key a.sorted
  have hrun :
      run (worker hcap) input (workerBudget v.entries.len)
        (init v.entries key) = some r := hr
  obtain ⟨hb, hcut⟩ := a.cut ha
  let f := v.finish key.val (lower r.finalState)
  have hfinish : f.1 = lookup row key.val := a.finish_correct ha
  let out : CallResult := ⟨lower r.finalState, encode f.1, r.executed + f.2⟩
  have hexec : execute v key = some out := by
    simp only [execute, hrun, out, f]
  have hreads : f.2 ≤ 3 := v.finish_reads_le key.val (lower r.finalState)
  have hworker : r.executed ≤ 11 * (Nat.log2 (v.entries.len + 1) + 1) := hsteps
  have hcost : out.cost ≤ 11 * Nat.log2 (v.entries.len + 1) + 14 := by
    change r.executed + f.2 ≤ 11 * Nat.log2 (v.entries.len + 1) + 14
    omega
  exact ⟨r, out, hrun, ha, hd, hexec, rfl, hb, hcut, hfinish,
    congrArg encode hfinish, rfl, hcost⟩

end PaperB.RamProgram.Predecessor.ChildRow
