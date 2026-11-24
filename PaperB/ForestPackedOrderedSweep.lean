module

public import PaperB.ForestFixedBankSortToll
public import PaperB.ForestActualFull
public import PaperB.ForestFixedBankSortExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestDictionary

open PaperB.LabelledQuotient PaperB.ForestHead
open PaperB.PairLookup PaperB.PairLookup.KeyMerge PaperB.PairDictionary.FixedBank

private def initialBanks (xs : List Key) : Array Key :=
  let bank0 := xs.toArray
  bank0 ++ Array.replicate bank0.size (0, 0)

/-- Allocate the two-bank destination once, without growing the source
array by appending a separately allocated padding bank. -/
private def initialBanksReserved (xs : List Key) : Array Key :=
  let input := xs.toArray
  Array.ofFn fun i : Fin (input.size + input.size) =>
    if h : i.val < input.size then input[i.val]'h else (0, 0)

@[csimp] private theorem initialBanks_csimp : @initialBanks = @initialBanksReserved := by
  funext xs
  unfold initialBanks initialBanksReserved
  dsimp only
  apply Array.ext
  · simp
  · intro i old new
    by_cases h : i < xs.toArray.size
    · rw [Array.getElem_append_left h, Array.getElem_ofFn]
      simp only [dite_eq_left h]
    · rw [Array.getElem_append_right (Nat.le_of_not_gt h), Array.getElem_ofFn]
      simp only [Array.getElem_replicate, dite_eq_right h]

private theorem initialBanks_size (xs : List Key) :
    (initialBanks xs).size = 2 * xs.length := by
  simp [initialBanks] <;> omega

private theorem initialKeys (xs : List Key) :
    keysAt (initialBanks xs) (initialBanks_size xs) false 0 xs.length (by simp) =
      xs := by
  apply List.ext_getElem
  · simp [keysAt]
  · intro i hi hj
    have hsize := initialBanks_size xs
    simp only [keysAt, List.getElem_ofFn]
    change (initialBanks xs)[0 + (0 + i)]'(by omega) = xs[i]
    simp only [Nat.zero_add, initialBanks]
    rw [Array.getElem_append_left] <;> simp [*]

private theorem extractKeys {k : Nat} (a : Array Key) (ha : a.size = 2 * k)
    (n : Nat) (hn : n ≤ k) :
    (a.extract 0 n).toList = keysAt a ha false 0 n (by simpa using hn) := by
  have hs : (a.extract 0 n).size = n := by
    simp only [Array.size_extract, Nat.sub_zero]
    omega
  apply List.ext_getElem
  · simp only [keysAt, List.length_ofFn, Array.length_toList, hs]
  · intro i hi hj
    have hin : i < n := by simpa only [Array.length_toList, hs] using hi
    simp only [Array.getElem_toList, Array.getElem_extract, keysAt, List.getElem_ofFn]
    change _ = a[0 + (0 + i)]'(by omega)
    simp

private def packedKeys (xs : List Key) : Array Key :=
  let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
  out.bank.extract 0 out.count

private theorem packedKeys_spec (xs : List Key) :
    Increasing (packedKeys xs).toList ∧
      ∀ z : Key, z ∈ (packedKeys xs).toList ↔ z ∈ xs := by
  let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
  have he : (packedKeys xs).toList = out.keys :=
    extractKeys out.bank out.size_eq out.count out.count_le
  have h := runPacked_spec xs.length false (initialBanks xs) (initialBanks_size xs)
  rw [he]
  exact ⟨h.1, fun z => (h.2 z).trans (by rw [initialKeys xs])⟩

private theorem key_irrefl (x : Key) : ¬ lexLess x x := by
  rcases x with ⟨a, b⟩
  change ¬ (a < a ∨ (a = a ∧ b < b))
  omega

-- Equal support forces equal heads, then equal tail support.
private theorem increasing_unique {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys)
    (hm : ∀ k : Key, k ∈ xs ↔ k ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h := (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
      simp at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
      simp at h
    | cons y ys =>
      have he : x = y := by
        by_cases h : x = y
        · exact h
        · have hxy := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
          have hyx := (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
          have hxr := (List.mem_cons.mp hxy).resolve_left h
          have hyr := (List.mem_cons.mp hyx).resolve_left (fun e => h e.symm)
          exact False.elim (key_irrefl x
            (lexLess_trans (hx.head y hyr) (hy.head x hxr)))
      subst y
      apply congrArg (List.cons x)
      apply ih hx.tail hy.tail
      intro k
      by_cases hk : k = x
      · subst k
        have hnx : x ∉ xs := fun h => key_irrefl x (hx.head x h)
        have hny : x ∉ ys := fun h => key_irrefl x (hy.head x h)
        simp [hnx, hny]
      · simpa only [List.mem_cons, hk, false_or] using hm k

private theorem packedKeys_eq (xs : List Key) :
    packedKeys xs = KeyMerge.dictionary xs := by
  have hp := packedKeys_spec xs
  have hr := KeyMerge.build_spec xs
  have he := increasing_unique hp.1 hr.increasing
    (fun k => (hp.2 k).trans (hr.mem_iff k).symm)
  simpa [KeyMerge.dictionary] using congrArg (fun l : List Key => l.toArray) he

/-- Collect once, sort in the two banks, and extract the occupied output prefix. -/
def packedDictionary {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) : Array Key :=
  packedKeys (collect p code)

theorem packedDictionary_eq {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    packedDictionary p code = dictionary p code :=
  packedKeys_eq (collect p code)

theorem packedDictionary_spec {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    StrictSorted (packedDictionary p code) ∧
      (∀ k : Key, k ∈ (packedDictionary p code).toList ↔
        ∃ (y : Vertex H) (q : CutPair H),
          preparedKey H (p.row y) = some q ∧ code q = k) ∧
      (packedDictionary p code).size ≤ H.vertexCount := by
  rw [packedDictionary_eq]
  exact dictionary_spec p code

-- Insert after `packedDictionary`, inside `PaperB.ForestDictionary`.

private theorem packedConstruction_succ_le_pow (n : Nat) :
    n + 1 ≤ (2 : Nat) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

open PaperB.PairDictionary in
/-- Space accounting for the packed construction starting from the collected list.
Here `k` is the number of collected keys before deduplication, and `H.vertexCount`
is the input bound. `peak` counts simultaneously live sorting frames, not total calls.

The sum charges the input list, both setup arrays, the common bank, and the
returned slice, even if their lifetimes do not overlap. The initial and outgoing
bank states describe one logical `2 * k`-cell region in this accounting.
`frameCells` is a fixed charge per live frame; taking it to be one gives
coefficient seven. This is a source-level logical-cell bound, not a bound on
collection workspace, runtime heap or stack usage, or copying cost. -/
theorem packedDictionary_construction_space {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) (frameCells : Nat) :
    let xs := collect p code
    let k := xs.length
    let bank0 := xs.toArray
    let zeros : Array Key := Array.replicate bank0.size (0, 0)
    let bank := initialBanks xs
    let out := runPacked k false bank (initialBanks_size xs)
    xs.length ≤ H.vertexCount ∧
      bank0.size = k ∧
      zeros.size = k ∧
      bank = bank0 ++ zeros ∧
      bank.size = 2 * k ∧
      out.bank.size = 2 * k ∧
      packedDictionary p code = out.bank.extract 0 out.count ∧
      (packedDictionary p code).size = out.count ∧
      (packedDictionary p code).size ≤ k ∧
      ∃ peak : Nat,
        Calls (ceilBinaryLog k) (PaperB.PairLookup.KeyMerge.Workspace.Span.root k) peak ∧
        peak ≤ ceilBinaryLog k + 1 ∧
        xs.length + bank0.size + zeros.size + bank.size +
          (packedDictionary p code).size + frameCells * peak ≤
          (6 + frameCells) * (H.vertexCount + 1) := by
  intro xs k bank0 zeros bank out
  have hinput : xs.length ≤ H.vertexCount := collect_length_le p code
  have hkN : k ≤ H.vertexCount := hinput
  have hfirst : bank0.size = k := by
    change xs.toArray.size = xs.length
    simp
  have hzeros : zeros.size = k := by
    change (Array.replicate bank0.size ((0, 0) : Key)).size = k
    simpa only [Array.size_replicate] using hfirst
  have hsetup : bank = bank0 ++ zeros := rfl
  have hbank : bank.size = 2 * k := initialBanks_size xs
  have hout : out.bank.size = 2 * k := out.size_eq
  have hcount : out.count ≤ k := out.count_le
  have hresult : packedDictionary p code = out.bank.extract 0 out.count := rfl
  have hslice : (packedDictionary p code).size = out.count := by
    rw [hresult]
    simp only [Array.size_extract, Nat.sub_zero]
    omega
  have hsliceLe : (packedDictionary p code).size ≤ k := by
    rw [hslice]
    exact hcount
  obtain ⟨peak, hcalls, hpeak⟩ :=
    runPacked_live_frames k false bank (initialBanks_size xs)
  have hlog : ceilBinaryLog k ≤ k :=
    (ceilBinaryLog_le_iff k k).mpr
      (Nat.le_trans (Nat.le_succ k) (packedConstruction_succ_le_pow k))
  have hpeakN : peak ≤ H.vertexCount + 1 := by
    omega
  have hdata :
      xs.length + bank0.size + zeros.size + bank.size +
        (packedDictionary p code).size ≤ 6 * (H.vertexCount + 1) := by
    rw [hfirst, hzeros, hbank]
    omega
  have htotal :
      xs.length + bank0.size + zeros.size + bank.size +
        (packedDictionary p code).size + frameCells * peak ≤
        (6 + frameCells) * (H.vertexCount + 1) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add hdata (Nat.mul_le_mul_left frameCells hpeakN)
  exact ⟨hinput, hfirst, hzeros, hsetup, hbank, hout, hresult, hslice,
    hsliceLe, peak, hcalls, hpeak, htotal⟩


end PaperB.ForestDictionary

namespace EX24.PreparedSweep

open PaperB EX24.PreStep PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open PaperB.PairLookup

private def orderedWith {H : LabelledQuotient} (large : 3 ≤ H.vertexCount)
    (d : Array Key) (hd : StrictSorted d) : Config H :=
  let base : Config H :=
    { region := ConcreteInit.region H.vertexCount
      dict := d
      sorted := hd
      code := orderedPairCode
      code_inj := by
        intro a b h
        rcases a with ⟨a₁, a₂, _, _, _⟩
        rcases b with ⟨b₁, b₂, _, _, _⟩
        have h₁ : a₁ = b₁ := Fin.ext (congrArg Prod.fst h)
        have h₂ : a₂ = b₂ := Fin.ext (congrArg Prod.snd h)
        subst b₁
        subst b₂
        rfl
      vertexIndex := Fin.val
      vertexIndex_inj := fun h => Fin.ext h
      zeroKey := SmallQuotient.sentinelDefaultCutPair H large
      atDepth := fun _ _ _ _ => 0
      ancestor := fun _ _ _ _ => false }
  base.usePackedWords

private theorem orderedWith_congr {H : LabelledQuotient}
    (large : 3 ≤ H.vertexCount) {d e : Array Key}
    (hd : StrictSorted d) (he : StrictSorted e) (h : d = e) :
    orderedWith large d hd = orderedWith large e he := by
  cases h
  rfl

def packedOrderedConfig {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) : Config H :=
  orderedWith large (ForestDictionary.packedDictionary p orderedPairCode)
    (ForestDictionary.packedDictionary_spec p orderedPairCode).1

theorem packedOrderedConfig_eq {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) :
    packedOrderedConfig p large = orderedConfig p large :=
  orderedWith_congr large
    (ForestDictionary.packedDictionary_spec p orderedPairCode).1
    (ForestDictionary.dictionary_spec p orderedPairCode).1
    (ForestDictionary.packedDictionary_eq p orderedPairCode)

def runOrderedPacked {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount) :
    Option (State H × Log H) :=
  fromRoot (packedOrderedConfig p large) rank
    (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    (orderedRows p data size_data)

theorem runOrderedPacked_eq {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount) :
    runOrderedPacked p data size_data rank large = runOrdered p data size_data rank large := by
  simp only [runOrderedPacked, runOrdered, packedOrderedConfig_eq]

end EX24.PreparedSweep



namespace PaperB.ForestDictionary

open PaperB.LabelledQuotient PaperB.ForestHead
open PaperB.PairLookup PaperB.PairLookup.KeyMerge PaperB.PairDictionary.FixedBank
open PaperB.PairLookup.KeyMerge.Workspace (Span)

/-- One visit for each original prepared row, including rows producing no key,
and one emission for each key collected. The indices record the input vertices,
the emitted keys, the visit count, and the emission count. -/
inductive PreparedCollectCostTrace {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    List (Vertex H) → List Key → Nat → Nat → Prop where
  | nil : PreparedCollectCostTrace p code [] [] 0 0
  | skip {y : Vertex H} {ys : List (Vertex H)} {xs : List Key} {v k : Nat}
      (h : preparedKey H (p.row y) = none) :
      PreparedCollectCostTrace p code ys xs v k →
      PreparedCollectCostTrace p code (y :: ys) xs (v + 1) k
  | emit {y : Vertex H} {ys : List (Vertex H)} {xs : List Key}
      {v k : Nat} {q : CutPair H}
      (h : preparedKey H (p.row y) = some q) :
      PreparedCollectCostTrace p code ys xs v k →
      PreparedCollectCostTrace p code (y :: ys) (code q :: xs) (v + 1) (k + 1)

private theorem preparedCollectCostTrace {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) (ys : List (Vertex H)) :
    PreparedCollectCostTrace p code ys (collectFrom p code ys)
      ys.length (collectFrom p code ys).length := by
  induction ys with
  | nil => exact PreparedCollectCostTrace.nil
  | cons y ys ih =>
    cases h : preparedKey H (p.row y) with
    | none =>
      simpa [collectFrom, List.filterMap, h] using
        (PreparedCollectCostTrace.skip (p := p) (code := code) h ih)
    | some q =>
      simpa [collectFrom, List.filterMap, h] using
        (PreparedCollectCostTrace.emit (p := p) (code := code) h ih)

private theorem fullSpanCostWitness {k : Nat} (fuel : Nat) (s : Span k)
    (dst : Bool) (a : Array Key) (ha : a.size = 2 * k)
    (hw : s.width ≤ 2 ^ fuel) (hfull : s.width = k) :
    let out := runSpan fuel s dst a ha hw
    ∃ (s' : Span k) (cost : Nat), s'.width = k ∧ k ≤ 2 ^ fuel ∧
      SpanCostTrace fuel s' dst a out.bank out.count cost := by
  obtain ⟨cost, t⟩ := runSpan_costTrace fuel s dst a ha hw
  exact ⟨s, cost, hfull, hfull ▸ hw, t⟩

private theorem packedFullSpanCostWitness (k : Nat) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) :
    let out := runPacked k dst a ha
    ∃ (s : Span k) (cost : Nat), s.width = k ∧ k ≤ 2 ^ ceilBinaryLog k ∧
      SpanCostTrace (ceilBinaryLog k) s dst a out.bank out.count cost := by
  unfold runPacked
  apply fullSpanCostWitness
  rfl

private theorem packedWidth_le_pow (n : Nat) : n ≤ 2 ^ ceilBinaryLog n := by
  obtain ⟨_, _, _, h, _⟩ := packedFullSpanCostWitness n false
    (Array.replicate (2 * n) ((0, 0) : Key)) (by simp)
  exact h

private theorem packedTwoPow_mono {i j : Nat} (h : i ≤ j) :
    2 ^ i ≤ 2 ^ j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rw [Nat.pow_succ]
    omega

/-- Bound the existing physical trace by any depth budget sufficient for its
width. This does not change the fuel or the bank operations of the traced run. -/
private theorem packedSpanCost_bound_at {k fuel : Nat} {s : Span k} {dst : Bool}
    {a b : Array Key} {w cost : Nat}
    (t : SpanCostTrace fuel s dst a b w cost) (L : Nat)
    (hw : s.width ≤ 2 ^ L) :
    cost ≤ 6 * s.width * (L + 1) + (if s.width = 0 then 1 else 0) := by
  induction t generalizing L with
  | @leaf fuel s dst a ha hw' hs =>
    by_cases hz : s.width = 0
    · simp [hz]
    · have hp : 0 < s.width := by omega
      simp only [ite_eq_right hz, ite_eq_left hp, Nat.add_zero]
      rw [Nat.mul_add (6 * s.width) L 1, Nat.mul_one]
      omega
  | @fork n s dst a lb rb b lc rc w cl cr rd cp xs hs hl hr hrb
      left right t _charge _actual ihl ihr =>
    cases L with
    | zero =>
      change s.width ≤ 1 at hw
      omega
    | succ L =>
      have hb : s.width ≤ 2 ^ L * 2 := by
        simpa only [Nat.pow_succ] using hw
      have hwl : s.left.width ≤ 2 ^ L := by
        change s.width / 2 ≤ 2 ^ L
        omega
      have hwr : s.right.width ≤ 2 ^ L := by
        change s.width - s.width / 2 ≤ 2 ^ L
        omega
      have hleft : s.left.width ≠ 0 := by
        change s.width / 2 ≠ 0
        omega
      have hright : s.right.width ≠ 0 := by
        change s.width - s.width / 2 ≠ 0
        omega
      have hsum : s.left.width + s.right.width = s.width := by
        change s.width / 2 + (s.width - s.width / 2) = s.width
        omega
      have hcl := ihl L hwl
      have hcr := ihr L hwr
      simp only [ite_eq_right hleft, ite_eq_right hright, Nat.add_zero] at hcl hcr
      have hadd :
          6 * s.left.width * (L + 1) + 6 * s.right.width * (L + 1) =
            6 * s.width * (L + 1) := by
        rw [← Nat.add_mul, ← Nat.mul_add, hsum]
      have hchildren : cl + cr ≤ 6 * s.width * (L + 1) := by
        rw [← hadd]
        exact Nat.add_le_add hcl hcr
      obtain ⟨_, hrd, hcp, _, _⟩ := t.accounting
      have hfit : w ≤ s.width := t.fits
      have hmerge : rd + cp + w ≤ 5 * s.width := by omega
      simp only [ite_eq_right (show s.width ≠ 0 by omega), Nat.add_zero]
      rw [Nat.mul_add (6 * s.width) (L + 1) 1, Nat.mul_one]
      omega

/-- The non-sort portion of the local construction toll.

* Each enumerated vertex pays one enumeration unit and one prepared-row visit.
* Each collected key pays one emission unit and one list-length visit.
* Each logical array destination pays one allocation unit per actual key
  slot: the `toArray` input, the replicated padding, the protected two-bank
  array, and the compact extract.
* A key occupies two modeled words. `toArray`, the bank append, and the
  compact extract pay two word reads and two word writes per copied key.
  `replicate` pays two word writes per initialized key.

Allocation here is a charge on the sizes of the concrete array values, not
on allocator capacity or backing-store copies. -/
def packedDictionaryNonSortToll (visits : Nat) (xs : List Key) (d : Array Key) :
    Nat :=
  let input := xs.toArray
  let padding : Array Key := Array.replicate input.size (0, 0)
  let banks := initialBanks xs
  2 * visits + 2 * xs.length +
    (input.size + padding.size + banks.size + d.size) +
    (4 * input.size + 2 * padding.size + 4 * banks.size + 4 * d.size)

theorem packedDictionaryNonSortToll_eq (visits : Nat) (xs : List Key)
    (d : Array Key) :
    packedDictionaryNonSortToll visits xs d =
      2 * visits + 20 * xs.length + 5 * d.size := by
  simp [packedDictionaryNonSortToll, initialBanks_size] <;> omega

/-- A local certificate for the actual packed dictionary construction. The
sort tally is exactly the `SpanCostTrace` tally: a unit per sort frame, a
key read and write at each positive leaf, and the checked merge head reads,
key comparisons, and output key writes. A zero-width leaf pays only its
frame unit.

Scope note for the unpublished proof: these are logical action and slot
charges, not a Lean runtime or whole-sweep bound. The prepared rows and
encoder are supplied; the visit and emission units do not analyze the
internals of row access, `preparedKey`, or `code`. The trace does not price
address and cursor arithmetic, reference counting, dynamic capacity, or
backing-store copies. It does not include sweep initialization or execution. -/
structure PackedDictionaryConstructionTrace {H : LabelledQuotient}
    (p : Rows H) (code : CutPair H → Key) (d : Array Key)
    (sortCost total : Nat) : Prop where
  collection :
    PreparedCollectCostTrace p code (List.finRange H.vertexCount)
      (collect p code) H.vertexCount (collect p code).length
  sort :
    let xs := collect p code
    let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
    ∃ s : Span xs.length, s.width = xs.length ∧
      SpanCostTrace (ceilBinaryLog xs.length) s false (initialBanks xs)
        out.bank out.count sortCost
  compact :
    let xs := collect p code
    let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
    d = out.bank.extract 0 out.count ∧ d.size = out.count ∧ out.count ≤ xs.length
  tally :
    total = packedDictionaryNonSortToll H.vertexCount (collect p code) d + sortCost

theorem packedDictionary_construction_trace {H : LabelledQuotient}
    (p : Rows H) (code : CutPair H → Key) :
    ∃ sortCost total,
      PackedDictionaryConstructionTrace p code (packedDictionary p code)
        sortCost total := by
  let xs := collect p code
  let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
  obtain ⟨s, sortCost, hs, _, ht⟩ :=
    packedFullSpanCostWitness xs.length false (initialBanks xs) (initialBanks_size xs)
  have hsize : (out.bank.extract 0 out.count).size = out.count := by
    have hb := out.size_eq
    have hc : out.count ≤ xs.length := out.count_le
    simp only [Array.size_extract, Nat.sub_zero]
    omega
  refine ⟨sortCost,
    packedDictionaryNonSortToll H.vertexCount xs (packedDictionary p code) + sortCost,
    ?_⟩
  refine ⟨?_, ⟨s, hs, ht⟩, ⟨rfl, hsize, out.count_le⟩, rfl⟩
  simpa [collect] using
    (preparedCollectCostTrace p code (List.finRange H.vertexCount))

/-- The only additive charge is the empty sort frame when no keys are
collected. This form also applies when the vertex count is zero. -/
theorem PackedDictionaryConstructionTrace.bound_with_empty
    {H : LabelledQuotient} {p : Rows H} {code : CutPair H → Key}
    {d : Array Key} {sortCost total : Nat}
    (t : PackedDictionaryConstructionTrace p code d sortCost total)
    (L : Nat) (hL : ceilBinaryLog H.vertexCount ≤ L) :
    total ≤ 33 * H.vertexCount * (L + 1) +
      (if (collect p code).length = 0 then 1 else 0) := by
  have hK := collect_length_le p code
  have hd : d.size ≤ (collect p code).length :=
    Nat.le_trans (Nat.le_of_eq t.compact.2.1) t.compact.2.2
  obtain ⟨s, hs, ht⟩ := t.sort
  have hw : s.width ≤ 2 ^ L := by
    rw [hs]
    exact Nat.le_trans hK
      (Nat.le_trans (packedWidth_le_pow H.vertexCount) (packedTwoPow_mono hL))
  have hsort := packedSpanCost_bound_at ht L hw
  rw [hs] at hsort
  have hmul :=
    Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul_left 6 hK)
  have hsort' :
      sortCost ≤ 6 * H.vertexCount * (L + 1) +
        (if (collect p code).length = 0 then 1 else 0) := by
    omega
  have hns :
      packedDictionaryNonSortToll H.vertexCount (collect p code) d ≤
        27 * H.vertexCount := by
    rw [packedDictionaryNonSortToll_eq]
    omega
  have hns' :
      packedDictionaryNonSortToll H.vertexCount (collect p code) d ≤
        27 * H.vertexCount * (L + 1) := by
    rw [Nat.mul_add (27 * H.vertexCount) L 1, Nat.mul_one]
    omega
  rw [Nat.mul_assoc 6 H.vertexCount (L + 1)] at hsort'
  rw [Nat.mul_assoc 27 H.vertexCount (L + 1)] at hns'
  rw [t.tally, Nat.mul_assoc 33 H.vertexCount (L + 1)]
  omega

theorem packedDictionary_construction_budget {H : LabelledQuotient}
    (p : Rows H) (code : CutPair H → Key) (L : Nat)
    (hL : ceilBinaryLog H.vertexCount ≤ L) (hpos : 0 < H.vertexCount) :
    ∃ sortCost total,
      PackedDictionaryConstructionTrace p code (packedDictionary p code)
        sortCost total ∧ total ≤ 34 * H.vertexCount * (L + 1) := by
  obtain ⟨sortCost, total, t⟩ := packedDictionary_construction_trace p code
  refine ⟨sortCost, total, t, ?_⟩
  have hb := t.bound_with_empty L hL
  have hframe : (if (collect p code).length = 0 then 1 else 0) ≤ 1 := by
    split <;> omega
  have hunit : 1 ≤ H.vertexCount * (L + 1) := by
    rw [Nat.mul_add H.vertexCount L 1, Nat.mul_one]
    omega
  rw [Nat.mul_assoc 33 H.vertexCount (L + 1)] at hb
  rw [Nat.mul_assoc 34 H.vertexCount (L + 1)]
  omega

end PaperB.ForestDictionary

namespace EX24.PreparedSweep

open PaperB EX24.PreStep PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open PaperB.PairLookup PaperB.PairLookup.KeyMerge

/-- The budget applies to the dictionary installed by `packedOrderedConfig`,
without replacing it by the extensionally equal list-built dictionary. -/
theorem packedOrderedConfig_dictionary_construction_budget {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) (L : Nat)
    (hL : ceilBinaryLog H.vertexCount ≤ L) :
    ∃ sortCost total,
      ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
        (packedOrderedConfig p large).dict sortCost total ∧
      total ≤ 34 * H.vertexCount * (L + 1) := by
  have hd : (packedOrderedConfig p large).dict =
      ForestDictionary.packedDictionary p orderedPairCode := rfl
  rw [hd]
  exact ForestDictionary.packedDictionary_construction_budget
    p orderedPairCode L hL (by omega)

end EX24.PreparedSweep
