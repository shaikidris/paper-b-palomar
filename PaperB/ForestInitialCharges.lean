module

public import PaperB.ForestPackedOrderedReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace EX24.PreparedSweep

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient
open PaperB.Jumps EX24.PreStep
open ForestDictionary

/-- `initial` retains the supplied memory and allocates the other three arrays. -/
theorem initial_array_sizes {H : LabelledQuotient} (c : Config H)
    (mem : Array Nat) (vertexCapacity : Nat) :
    (initial c mem vertexCapacity).tables.mem.size = mem.size ∧
    (initial c mem vertexCapacity).tables.slots.size = c.dict.size ∧
    (initial c mem vertexCapacity).tables.back.size = c.region.maxNodes + 1 ∧
    (initial c mem vertexCapacity).labels.size = vertexCapacity := by
  simp [initial]

/-- The existing root-image charge counts the zero-fill and one write. -/
theorem allocated_initCharge (n : Nat) :
    ConcreteInit.initCharge n = (1 + 3 * (n + 1)) + 1 :=
  (ConcreteInit.exact_init_charges n).2.2.2

/-- Follow the original accumulator through the successful recursive calls.
The witness is the accumulator in the empty-row branch. -/
theorem foldRowsAux_reverse_input {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows : List (Row H)} {s out : State H}
    {rev log : Log H}
    (h : foldRowsAux c rank rows s rev = some (out, log)) :
    ∃ acc : Log H,
      foldRowsAux c rank [] out acc = some (out, log) ∧
      acc.length = rev.length + rows.length := by
  induction rows generalizing s out rev log with
  | nil =>
    change some (s, rev.reverse) = some (out, log) at h
    have hs : s = out := congrArg Prod.fst (Option.some.inj h)
    subst s
    exact ⟨rev, h, by simp⟩
  | cons row rows ih =>
    cases hr : stepPrepared c s rank row.head row.tests with
    | none => simp [foldRowsAux, hr] at h
    | some r =>
      have ht : foldRowsAux c rank rows r.state
          (Event.ofResult row.head r :: rev) = some (out, log) := by
        simpa only [foldRowsAux, hr] using h
      obtain ⟨acc, hacc, hlen⟩ :=
        ih (s := r.state) (out := out)
          (rev := Event.ofResult row.head r :: rev) (log := log) ht
      refine ⟨acc, hacc, ?_⟩
      simp only [List.length_cons] at hlen ⊢
      omega

/-- For `orderedRows`, the row-count premise is `by simp [orderedRows]`. -/
theorem fromRoot_order_log_length {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {mem : Array Nat} {vertexCapacity : Nat}
    {rows : List (Row H)} {out : State H} {log : Log H}
    (hrows : rows.length = H.vertexCount)
    (h : fromRoot c rank mem vertexCapacity rows = some (out, log)) :
    log.length = H.vertexCount := by
  change foldRowsAux c rank rows (initial c mem vertexCapacity) [] =
    some (out, log) at h
  obtain ⟨acc, hacc, hlen⟩ := foldRowsAux_reverse_input h
  change some (out, acc.reverse) = some (out, log) at hacc
  have he : acc.reverse = log := congrArg Prod.snd (Option.some.inj hacc)
  rw [← he, List.length_reverse]
  simpa only [List.length_nil, Nat.zero_add, hrows] using hlen

/-- The final reversal of this successful call consumes exactly one entry per vertex. -/
theorem fromRoot_order_reverse_input {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {mem : Array Nat} {vertexCapacity : Nat}
    {rows : List (Row H)} {out : State H} {log : Log H}
    (hrows : rows.length = H.vertexCount)
    (h : fromRoot c rank mem vertexCapacity rows = some (out, log)) :
    ∃ acc : Log H,
      foldRowsAux c rank [] out acc = some (out, log) ∧
      log = acc.reverse ∧ acc.length = H.vertexCount := by
  have hlen := fromRoot_order_log_length hrows h
  change foldRowsAux c rank rows (initial c mem vertexCapacity) [] =
    some (out, log) at h
  obtain ⟨acc, hacc, _⟩ := foldRowsAux_reverse_input h
  have hb := hacc
  change some (out, acc.reverse) = some (out, log) at hb
  have he : log = acc.reverse := (congrArg Prod.snd (Option.some.inj hb)).symm
  exact ⟨acc, hacc, he, by simpa only [he, List.length_reverse] using hlen⟩

theorem preparedCollectCostTrace_lengths {H : LabelledQuotient}
    {p : ForestDictionary.Rows H} {code : CutPair H → Key}
    {ys : List (Vertex H)} {xs : List Key} {visits emits : Nat}
    (t : PreparedCollectCostTrace p code ys xs visits emits) :
    visits = ys.length ∧ emits = xs.length := by
  induction t with
  | nil => exact ⟨rfl, rfl⟩
  | skip _ _ ih =>
    exact ⟨congrArg (fun n : Nat => n + 1) ih.1, ih.2⟩
  | emit _ _ ih =>
    exact ⟨congrArg (fun n : Nat => n + 1) ih.1,
      congrArg (fun n : Nat => n + 1) ih.2⟩

/-- The collect trace counts the vertex enumeration and the returned list,
not auxiliary workspace. -/
theorem collect_trace_counts {H : LabelledQuotient}
    {p : ForestDictionary.Rows H} {code : CutPair H → Key}
    {visits emits : Nat}
    (t : PreparedCollectCostTrace p code (List.finRange H.vertexCount)
      (ForestDictionary.collect p code) visits emits) :
    visits = H.vertexCount ∧ emits = (ForestDictionary.collect p code).length := by
  obtain ⟨hv, he⟩ := preparedCollectCostTrace_lengths t
  exact ⟨by simpa only [List.length_finRange] using hv, he⟩

end EX24.PreparedSweep
