module

public import PaperB.RamForestDictSort
public import PaperB.RamLinkedReturn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.Sweep

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.DepthSeek
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.ForestHead (Vertex TestSpec)
open PaperB.ForestDictionary (Rows packedDictionary packedDictionary_spec dictionary dictionary_spec)
open PaperB.ForestSlimIndex
open PaperB.PairLookup (Key)
open PaperB.RetainedProperLoss (WordColumns packWordColumns BackWords packBackWords encodeBackPair)
open PaperB.EX24.FinalDFS (packedInput nodeCount nodeCount_eq_next packedInput_parent packedInput_root)
open _root_.EX24 (Config Grounded)
open _root_.EX24.PreStep (climb Embedding)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedPairCode orderedConfig orderedRows)
open PaperB.ForestHead (preparedKey)
open PaperB.ForestDictionary (packedDictionary_eq)
open _root_.EX24 (initial initial_grounded)
open _root_.EX24.PreStep (initialUp initial_embedding boundedJumpParent)
open PaperB.Machine

/-! ### Constants, register & scratch layout, and general mathematical lemmas -/

abbrev rPtr : Fin 15 := registers.ptr
abbrev rStack : Fin 15 := registers.stackBase
abbrev rRem : Fin 15 := registers.remain
abbrev rChild : Fin 15 := registers.childBase
abbrev rVal : Fin 15 := registers.value
abbrev rOne : Fin 15 := registers.one
abbrev rTmp : Fin 15 := registers.tmp
abbrev rZero : Fin 15 := registers.zero
abbrev rCmd : Fin 15 := cmd
abbrev rCnt : Fin 15 := count
abbrev rClk : Fin 15 := clk
abbrev rTin : Fin 15 := tinBase
abbrev rTout : Fin 15 := toutBase
abbrev rOff : Fin 15 := offsetBase
abbrev rChB : Fin 15 := childrenBase

abbrev slN : Nat := 0
abbrev slRoot : Nat := 1
abbrev slNext : Nat := 2
abbrev slDictBase : Nat := 3
abbrev slDictCnt : Nat := 4
abbrev slDictSnd : Nat := 5
abbrev slDictSlots : Nat := 6
abbrev slJumpBase : Nat := 7
abbrev slBackFst : Nat := 8
abbrev slBackSnd : Nat := 9
abbrev slLabels : Nat := 10
abbrev slParents : Nat := 11
abbrev slOrder : Nat := 12
abbrev slRanks : Nat := 13
abbrev slRowStart : Nat := 14
abbrev slRowEnd : Nat := 15
abbrev slPredBuf : Nat := 16
abbrev slSource : Nat := 17
abbrev slIdx : Nat := 18
abbrev slY : Nat := 19
abbrev slRowLo : Nat := 20
abbrev slRowHi : Nat := 21
abbrev slMNode : Nat := 22
abbrev slLoBS : Nat := 23
abbrev slHiBS : Nat := 24
abbrev slMidBS : Nat := 25
abbrev slAncNode : Nat := 26
abbrev slPredJ : Nat := 27
abbrev slKeyFst : Nat := 28
abbrev slKeySnd : Nat := 29

theorem scratch_lt_orderBase {n m sl : Nat} (hn : 3 ≤ n) (hsl : sl < 30) :
    sl < orderBase n m := by
  unfold orderBase stampsBase indegBase csrArenaWords
  omega

theorem vertexCount_lt_two_pow_L (n : Nat) :
    n + 1 < 2 ^ OracleContract.L n := by
  have h : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) := by
    exact (Nat.log2_lt (by omega : n + 1 ≠ 0)).mp (Nat.lt_succ_self _)
  simpa only [OracleContract.L] using h

theorem vertexCount_add2_le_two_pow_L_succ (n : Nat) :
    n + 2 ≤ 2 ^ (OracleContract.L n + 1) := by
  have h := vertexCount_lt_two_pow_L n
  rw [Nat.pow_succ]
  omega

theorem strictSorted_list_unique :
    ∀ (xs ys : List Key),
      PairLookup.StrictSorted xs.toArray →
      PairLookup.StrictSorted ys.toArray →
      (∀ k : Key, k ∈ xs ↔ k ∈ ys) → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ hm
    cases ys with
    | nil => rfl
    | cons y _ =>
      have hy := (hm y).mpr List.mem_cons_self
      simp at hy
  | cons x xs ih =>
    intro ys hxs hys hm
    cases ys with
    | nil =>
      have hx := (hm x).mp List.mem_cons_self
      simp at hx
    | cons y ys =>
      have hxTail : PairLookup.StrictSorted xs.toArray := fun i j hi hj hij => by
        have hi' : i + 1 < (x :: xs).toArray.size := by simp at hi ⊢; omega
        have hj' : j + 1 < (x :: xs).toArray.size := by simp at hj ⊢; omega
        exact hxs (i + 1) (j + 1) hi' hj' (Nat.succ_lt_succ hij)
      have hyTail : PairLookup.StrictSorted ys.toArray := fun i j hi hj hij => by
        have hi' : i + 1 < (y :: ys).toArray.size := by simp at hi ⊢; omega
        have hj' : j + 1 < (y :: ys).toArray.size := by simp at hj ⊢; omega
        exact hys (i + 1) (j + 1) hi' hj' (Nat.succ_lt_succ hij)
      have hxHead : ∀ z ∈ xs, PairLookup.lexLess x z := fun z hz => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        have hi' : i + 1 < (x :: xs).toArray.size := by simp; omega
        exact hxs 0 (i + 1) (by simp) hi' (Nat.zero_lt_succ i)
      have hyHead : ∀ z ∈ ys, PairLookup.lexLess y z := fun z hz => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        have hi' : i + 1 < (y :: ys).toArray.size := by simp; omega
        exact hys 0 (i + 1) (by simp) hi' (Nat.zero_lt_succ i)
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hm y).mpr List.mem_cons_self) with he | hyt
        · exact he.symm
        · rcases List.mem_cons.mp ((hm x).mp List.mem_cons_self) with he | hxt
          · exact he
          · exact False.elim (PairLookup.lexLess_irrefl x
              (PairLookup.lexLess_trans (hxHead y hyt) (hyHead x hxt)))
      subst hxy
      apply congrArg (List.cons x)
      apply ih ys hxTail hyTail
      intro z
      by_cases hz : z = x
      · subst z
        have hnx : x ∉ xs := fun h => PairLookup.lexLess_irrefl x (hxHead x h)
        have hny : x ∉ ys := fun h => PairLookup.lexLess_irrefl x (hyHead x h)
        simp [hnx, hny]
      · simpa only [List.mem_cons, hz, false_or] using hm z

theorem strictSorted_array_eq (a1 a2 : Array Key)
    (hs1 : PairLookup.StrictSorted a1) (hs2 : PairLookup.StrictSorted a2)
    (hmem : ∀ k : Key, k ∈ a1.toList ↔ k ∈ a2.toList) : a1 = a2 := by
  have h1 : PairLookup.StrictSorted a1.toList.toArray := by simpa using hs1
  have h2 : PairLookup.StrictSorted a2.toList.toArray := by simpa using hs2
  have hlist := strictSorted_list_unique a1.toList a2.toList h1 h2 hmem
  apply Array.ext
  · simpa using congrArg List.length hlist
  · intro i hi1 hi2
    have hopt := congrArg (fun l : List Key => l[i]?) hlist
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hi1,
        Array.getElem?_toList, Array.getElem?_eq_getElem hi2] at hopt
    exact Option.some.inj hopt

theorem orderedDictionary_eq (H : LabelledQuotient)
    (rows1 rows2 : Rows H) :
    dictionary rows1 orderedPairCode = dictionary rows2 orderedPairCode := by
  have h1 := dictionary_spec rows1 orderedPairCode
  have h2 := dictionary_spec rows2 orderedPairCode
  apply strictSorted_array_eq _ _ h1.1 h2.1
  intro k
  rw [h1.2.1 k, h2.2.1 k]
  constructor <;> rintro ⟨y, q, hq1, hq2⟩
  · refine ⟨y, q, ?_, hq2⟩
    rw [PaperB.ForestHead.preparedKey_eq_candidate y (rows2.row y) (rows2.spec y),
        ← PaperB.ForestHead.preparedKey_eq_candidate y (rows1.row y) (rows1.spec y)]
    exact hq1
  · refine ⟨y, q, ?_, hq2⟩
    rw [PaperB.ForestHead.preparedKey_eq_candidate y (rows1.row y) (rows1.spec y),
        ← PaperB.ForestHead.preparedKey_eq_candidate y (rows2.row y) (rows2.spec y)]
    exact hq1

theorem packedDictionary_eq_dictionary (H : LabelledQuotient)
    (rows1 rows2 : Rows H) :
    packedDictionary rows1 orderedPairCode = dictionary rows2 orderedPairCode := by
  have h1 := packedDictionary_spec rows1 orderedPairCode
  have h2 := dictionary_spec rows2 orderedPairCode
  apply strictSorted_array_eq _ _ h1.1 h2.1
  intro k
  rw [h1.2.1 k, h2.2.1 k]
  constructor <;> rintro ⟨y, q, hq1, hq2⟩
  · refine ⟨y, q, ?_, hq2⟩
    rw [PaperB.ForestHead.preparedKey_eq_candidate y (rows2.row y) (rows2.spec y),
        ← PaperB.ForestHead.preparedKey_eq_candidate y (rows1.row y) (rows1.spec y)]
    exact hq1
  · refine ⟨y, q, ?_, hq2⟩
    rw [PaperB.ForestHead.preparedKey_eq_candidate y (rows1.row y) (rows1.spec y),
        ← PaperB.ForestHead.preparedKey_eq_candidate y (rows2.row y) (rows2.spec y)]
    exact hq1

theorem config_ext {H : LabelledQuotient}
    {r1 r2} {d1 d2 : Array Key} {s1 s2} {c1 c2 : CutPair H → Key}
    {ci1 ci2} {v1 v2 : Vertex H → Nat} {vi1 vi2} {z1 z2 : CutPair H}
    {ad1 ad2 anc1 anc2}
    (hr : r1 = r2) (hd : d1 = d2) (hc : c1 = c2) (hv : v1 = v2) (hz : z1 = z2)
    (had : ad1 = ad2) (hanc : anc1 = anc2) :
    (Config.mk r1 d1 s1 c1 ci1 v1 vi1 z1 ad1 anc1 : Config H) =
    Config.mk r2 d2 s2 c2 ci2 v2 vi2 z2 ad2 anc2 := by
  subst hr hd hc hv hz had hanc; rfl

theorem orderedConfig_eq_of_rows {H : LabelledQuotient}
    (rows1 rows2 : Rows H) (large : 3 ≤ H.vertexCount) :
    orderedConfig rows1 large = orderedConfig rows2 large := by
  unfold orderedConfig
  congr 1
  exact config_ext rfl (orderedDictionary_eq H rows1 rows2) rfl rfl rfl rfl rfl

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length := by
  intro l1
  induction l1 with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro l2 hnd hsub
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l2 := hsub a List.mem_cons_self
    have hlen := ih (l2.erase a) hnd.2 (fun x hx => by
      have hx2 : x ∈ l2 := hsub x (List.mem_cons_of_mem a hx)
      have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.mpr hx2)
    have her : (l2.erase a).length + 1 = l2.length := by
      have := List.length_erase_of_mem ha
      have hpos : 0 < l2.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

theorem sum_filter_finRange {α : Type} {n : Nat} (f : α → Fin n) (xs : List α) :
    ((List.finRange n).map (fun y => (xs.filter (fun x => decide (f x = y))).length)).sum =
      xs.length := by
  induction xs with
  | nil =>
    have hz : ∀ ys : List (Fin n), (ys.map (fun _ => 0)).sum = 0 := by
      intro ys; induction ys <;> simp [*]
    simpa using hz (List.finRange n)
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    have hstep : ((List.finRange n).map (fun y =>
        ((if decide (f x = y) = true then x :: xs.filter (fun z => decide (f z = y))
          else xs.filter (fun z => decide (f z = y))).length))).sum =
        ((List.finRange n).map (fun y => (xs.filter (fun z => decide (f z = y))).length)).sum + 1 := by
      have hpoint : ∀ ys : List (Fin n), ys.Nodup →
          (ys.map (fun y => (if decide (f x = y) = true
            then (xs.filter (fun z => decide (f z = y))).length + 1
            else (xs.filter (fun z => decide (f z = y))).length))).sum =
          (ys.map (fun y => (xs.filter (fun z => decide (f z = y))).length)).sum +
            (if f x ∈ ys then 1 else 0) := by
        intro ys hnd
        induction ys with
        | nil => simp
        | cons y ys ihy =>
          rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.sum_cons, ihy hnd.2, List.mem_cons]
          by_cases he : f x = y
          · have hnot : y ∉ ys := he ▸ hnd.1
            simp only [he, decide_true, ↓reduceIte, hnot, or_false]
            omega
          · simp only [he, decide_eq_true_eq, ↓reduceIte, false_or]
            omega
      have hmap : (List.finRange n).map (fun y =>
          (if decide (f x = y) = true then x :: xs.filter (fun z => decide (f z = y))
           else xs.filter (fun z => decide (f z = y))).length) =
          (List.finRange n).map (fun y =>
            if decide (f x = y) = true
            then (xs.filter (fun z => decide (f z = y))).length + 1
            else (xs.filter (fun z => decide (f z = y))).length) := by
        refine List.map_congr_left (fun y _ => ?_)
        split <;> simp
      rw [hmap, hpoint (List.finRange n) (List.nodup_finRange n)]
      simp
    rw [hstep, ih]

theorem row_length_sum_le_arcCount (H : LabelledQuotient) (rows : Rows H) :
    ((List.finRange H.vertexCount).map (fun y => (rows.row y).length)).sum ≤ H.arcCount := by
  let p := PaperB.ForestIncomingRaw.prepare H
  have hsub : ∀ y : Vertex H, (rows.row y).length ≤
      ((PaperB.ForestIncomingRaw.row H p y).map Prod.fst).length := by
    intro y
    apply nodup_length_le_of_subset _ _ (rows.spec y).nodup
    intro u hu
    have harc : H.HasQuotientArc u y := ((rows.spec y).cover u).mp hu
    obtain ⟨a, haMem, haHead⟩ := harc
    have hmemRow := (PaperB.ForestIncomingRaw.mem_row H u y a).mpr ⟨haMem, haHead⟩
    exact List.mem_map.mpr ⟨(u, a), hmemRow, rfl⟩
  have hsum1 : ((List.finRange H.vertexCount).map (fun y => (rows.row y).length)).sum ≤
      ((List.finRange H.vertexCount).map (fun y =>
        (PaperB.ForestIncomingRaw.row H p y).length)).sum := by
    have hle : ∀ l : List (Vertex H),
        (l.map (fun y => (rows.row y).length)).sum ≤
        (l.map (fun y => (PaperB.ForestIncomingRaw.row H p y).length)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons y ys ih =>
        simp only [List.map_cons, List.sum_cons]
        have hy := hsub y
        rw [List.length_map] at hy
        omega
    exact hle (List.finRange H.vertexCount)
  have hsum2 : ((List.finRange H.vertexCount).map (fun y =>
      (PaperB.ForestIncomingRaw.row H p y).length)).sum = H.arcCount := by
    have hcongr : (List.finRange H.vertexCount).map (fun y =>
        (PaperB.ForestIncomingRaw.row H p y).length) =
        (List.finRange H.vertexCount).map (fun y =>
          ((PaperB.ForestIncomingRaw.supplied H).filter (fun e =>
            decide (PaperB.ForestIncomingRaw.arcHead e.2 = y))).length) := by
      refine List.map_congr_left (fun y _ => ?_)
      rw [PaperB.ForestIncomingRaw.row_eq]
    rw [hcongr, sum_filter_finRange (fun e => PaperB.ForestIncomingRaw.arcHead e.2)
      (PaperB.ForestIncomingRaw.supplied H), PaperB.ForestIncomingRaw.length_supplied,
      PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
  omega

theorem row_length_sum_order (H : LabelledQuotient) (rows : Rows H)
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (nodup : order.toList.Nodup) :
    ((List.finRange H.vertexCount).map (fun i =>
      (rows.row (orderedVertexAt order size_order i)).length)).sum ≤ H.arcCount := by
  have hof : List.ofFn (fun i : Fin H.vertexCount => (rows.row (orderedVertexAt order size_order i)).length) =
      order.toList.map (fun y => (rows.row y).length) := by
    apply List.ext_getElem
    · simp [size_order]
    · intro k hk1 hk2
      simp [orderedVertexAt]
  have hperm : ∀ l1 l2 : List (Vertex H), l1.Nodup → (∀ x ∈ l1, x ∈ l2) →
      ∀ f : Vertex H → Nat, (l1.map f).sum ≤ (l2.map f).sum := by
    intro l1
    induction l1 with
    | nil => intro _ _ _ _; simp
    | cons a t ih =>
      intro l2 hnd hsub f
      rw [List.nodup_cons] at hnd
      have ha : a ∈ l2 := hsub a List.mem_cons_self
      have hih := ih (l2.erase a) hnd.2 (fun x hx => by
        have hx2 := hsub x (List.mem_cons_of_mem a hx)
        exact List.mem_erase_of_ne (fun he : x = a => hnd.1 (he ▸ hx)) |>.mpr hx2) f
      have her : (l2.map f).sum = f a + ((l2.erase a).map f).sum := by
        clear hih hnd hsub
        induction l2 with
        | nil => simp at ha
        | cons b bs ihb =>
          simp only [List.mem_cons] at ha
          by_cases hab : b = a
          · subst hab; simp [List.erase_cons_head]
          · have hbs : a ∈ bs := ha.elim (fun h => absurd h.symm hab) id
            rw [List.erase_cons]
            split
            · next he => exact absurd (eq_of_beq he) hab
            · simp only [List.map_cons, List.sum_cons]
              rw [ihb hbs]; omega
      simp only [List.map_cons, List.sum_cons, her]
      omega
  have hm1 : ((List.finRange H.vertexCount).map (fun i =>
      (rows.row (orderedVertexAt order size_order i)).length)).sum =
      (order.toList.map (fun y => (rows.row y).length)).sum := by
    rw [← hof]
    congr 1
    exact List.ext_getElem (by simp) (fun k hk1 hk2 => by simp)
  rw [hm1]
  have hle := hperm order.toList (List.finRange H.vertexCount) nodup (fun x _ => List.mem_finRange x)
    (fun y => (rows.row y).length)
  exact Nat.le_trans hle (row_length_sum_le_arcCount H rows)

/-! ### Reusable low-level step helpers for 15-register word-RAM -/

section StepHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

theorem array_set_congr {α : Type} {a b : Array α} {i j : Nat} {v w : α}
    (ha : i < a.size) (hb : j < b.size) (hab : a = b) (hij : i = j) (hvw : v = w) :
    a.set i v ha = b.set j w hb := by
  subst hab; subst hij; subst hvw; rfl

def putReg (s : State L) (d : Fin 15) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

theorem reg_putReg (s : State L) (d r : Fin 15) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, Ne.symm hv]

theorem step_imm_at {code : Program L} {input : Input L} {s : State L}
    {d : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {d src : Fin 15}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d (reg s src), ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then
      some (Transition.next (putReg s d (reg s src))) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

theorem step_add15_at {code : Program L} {input : Input L} {s : State L}
    {d lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.add d lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = add (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_add_at (input := input) hf hn

theorem step_sub15_at {code : Program L} {input : Input L} {s : State L}
    {d lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.sub d lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = sub (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_sub_at (input := input) hf hn

theorem step_shr15_at {code : Program L} {input : Input L} {s : State L}
    {d src : Fin 15}
    (hf : code[s.pc]? = some (.shr1 d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      (reg t d).val = (reg s src).val / 2 ∧
      (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_shr1_at (input := input) hf hn

theorem step_loadInput_at {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d addr)) (hn : s.pc + 1 < code.size)
    (hw' : input.words[(reg s addr).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  refine ⟨putReg s d w, ?_, rfl, ?_, ?_, rfl⟩
  · unfold step
    rw [hf]
    change (input.words[(reg s addr).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw']
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

theorem step_loadData_at' {code : Program L} {input : Input L} {s : State L}
    {d addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData d addr))
    (hn : s.pc + 1 < code.size)
    (_inBounds : (reg s addr).val < workCap)
    (hread : s.data[(reg s addr).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadData_at (input := input) hf hread hn

theorem step_storeData_at {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin 15}
    (hf : code[s.pc]? = some (.storeData addr src)) (hn : s.pc + 1 < code.size)
    (hbound : (reg s addr).val < workCap) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      t.data = s.data.set (reg s addr).val (reg s src)
        (by simpa only [s.data_size] using hbound) ∧
      (∀ r : Fin 15, reg t r = reg s r) := by
  have ha : (reg s addr).val < s.data.size := by simpa only [s.data_size] using hbound
  let t : State L :=
    { s with
      data := s.data.set (reg s addr).val (reg s src) ha
      pc := s.pc + 1
      data_size := by simp only [Array.size_set, s.data_size] }
  refine ⟨t, ?_, rfl, rfl, fun _ => rfl⟩
  unfold step
  rw [hf]
  change (if h : (reg s addr).val < s.data.size then
    if s.pc + 1 < code.size then some (Transition.next _) else none else none) = _
  rw [dite_eq_left ha, ite_eq_left hn]

theorem step_branchLt_true {code : Program L} {input : Input L} {s : State L}
    {x y : Fin 15} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (hlt : (reg s x).val < (reg s y).val) (hyes : yesPC < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = yesPC ∧
      (∀ r : Fin 15, reg t r = reg s r) ∧ t.data = s.data := by
  have hc : ltb (reg s x) (reg s y) = true := (PaperB.WordOps.ltb_eq_true _ _).mpr hlt
  refine ⟨{ s with pc := yesPC }, ?_, rfl, fun _ => rfl, rfl⟩
  simpa only [hc, ite_true] using
    step_branchLt_at (input := input) hf (by rw [hc]; exact hyes)

theorem step_branchLt_false {code : Program L} {input : Input L} {s : State L}
    {x y : Fin 15} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (hle : (reg s y).val ≤ (reg s x).val) (hno : noPC < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = noPC ∧
      (∀ r : Fin 15, reg t r = reg s r) ∧ t.data = s.data := by
  have hc : ltb (reg s x) (reg s y) = false := by
    cases h : ltb (reg s x) (reg s y) with
    | false => rfl
    | true =>
      have hlt := (PaperB.WordOps.ltb_eq_true _ _).mp h
      omega
  refine ⟨{ s with pc := noPC }, ?_, rfl, fun _ => rfl, rfl⟩
  simpa only [hc, Bool.false_eq_true, ite_false] using
    step_branchLt_at (input := input) hf (by rw [hc]; exact hno)

theorem immLoad_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp dst : Fin 15} {slot : Word bits} {w : Word bits}
    (_hne : tmp ≠ dst)
    (f0 : code[entry]? = some (.imm tmp slot))
    (f1 : code[entry + 1]? = some (.loadData dst tmp))
    (pc : s.pc = entry) (next : entry + 2 < code.size)
    (hb : slot.val < workCap) (atMem : s.data[slot.val]? = some w) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ tmp → r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_imm_at (input := input) (pc ▸ f0) (by omega)
  have hat1 : s1.data[(reg s1 tmp).val]? = some w := by rw [d1, r1]; exact atMem
  obtain ⟨s2, st1, pc2, r2, k2, d2⟩ := step_loadData_at' (input := input)
    (pc1 ▸ pc ▸ f1) (by omega) (by rw [r1]; exact hb) hat1
  exact ⟨s2, .cons st0 (.cons st1 (.zero _)), by omega, r2,
    fun r h1 h2 => (k2 r h2).trans (k1 r h1), d2.trans d1⟩

theorem immStore_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp src : Fin 15} {slot : Word bits}
    (f0 : code[entry]? = some (.imm tmp slot))
    (f1 : code[entry + 1]? = some (.storeData tmp src))
    (pc : s.pc = entry) (next : entry + 2 < code.size)
    (hb : slot.val < workCap) (hne : src ≠ tmp) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set slot.val (reg s src) (by simpa only [s.data_size] using hb) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg s r) := by
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_imm_at (input := input) (pc ▸ f0) (by omega)
  obtain ⟨s2, st1, pc2, d2, k2⟩ := step_storeData_at (input := input)
    (pc1 ▸ pc ▸ f1) (by omega) (by rw [r1]; exact hb)
  refine ⟨s2, .cons st0 (.cons st1 (.zero _)), by omega, ?_, fun r hr => (k2 r).trans (k1 r hr)⟩
  rw [d2]
  exact array_set_congr (a := s1.data) (b := s.data) (v := reg s1 src) (w := reg s src)
    (by rw [s1.data_size, r1]; exact hb) (by simpa only [s.data_size] using hb)
    d1 (congrArg Fin.val r1) (k1 src hne)

theorem loadAtOffset_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp dst base idx : Fin 15} {w : Word bits}
    (f0 : code[entry]? = some (.add tmp base idx))
    (f1 : code[entry + 1]? = some (.loadData dst tmp))
    (pc : s.pc = entry) (next : entry + 2 < code.size)
    (hb : (reg s base).val + (reg s idx).val < workCap)
    (atMem : s.data[(reg s base).val + (reg s idx).val]? = some w) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ tmp → r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_add15_at (input := input) (pc ▸ f0) (by omega)
  have hlt : (reg s base).val + (reg s idx).val < 2 ^ bits := Nat.lt_of_lt_of_le hb hw
  have rv1 : (reg s1 tmp).val = (reg s base).val + (reg s idx).val := by
    rw [r1, PaperB.WordOps.add_no_wrap _ _ hlt]
  have hat1 : s1.data[(reg s1 tmp).val]? = some w := by rw [d1, rv1]; exact atMem
  obtain ⟨s2, st1, pc2, r2, k2, d2⟩ := step_loadData_at' (input := input)
    (pc1 ▸ pc ▸ f1) (by omega) (by rw [rv1]; exact hb) hat1
  exact ⟨s2, .cons st0 (.cons st1 (.zero _)), by omega, r2,
    fun r h1 h2 => (k2 r h2).trans (k1 r h1), d2.trans d1⟩

theorem storeAtOffset_steps {code : Program L} {input : Input L} {s : State L}
    {entry : Nat} {tmp base idx src : Fin 15}
    (f0 : code[entry]? = some (.add tmp base idx))
    (f1 : code[entry + 1]? = some (.storeData tmp src))
    (pc : s.pc = entry) (next : entry + 2 < code.size)
    (hsrc : src ≠ tmp)
    (hb : (reg s base).val + (reg s idx).val < workCap) :
    ∃ t : State L, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set ((reg s base).val + (reg s idx).val) (reg s src)
        (by simpa only [s.data_size] using hb) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg s r) := by
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_add15_at (input := input) (pc ▸ f0) (by omega)
  have hlt : (reg s base).val + (reg s idx).val < 2 ^ bits := Nat.lt_of_lt_of_le hb hw
  have rv1 : (reg s1 tmp).val = (reg s base).val + (reg s idx).val := by
    rw [r1, PaperB.WordOps.add_no_wrap _ _ hlt]
  obtain ⟨s2, st1, pc2, d2, k2⟩ := step_storeData_at (input := input)
    (pc1 ▸ pc ▸ f1) (by omega) (by rw [rv1]; exact hb)
  refine ⟨s2, .cons st0 (.cons st1 (.zero _)), by omega, ?_, fun r hr => (k2 r).trans (k1 r hr)⟩
  rw [d2]
  exact array_set_congr (a := s1.data) (b := s.data) (v := reg s1 src) (w := reg s src)
    (by rw [s1.data_size, rv1]; exact hb) (by simpa only [s.data_size] using hb) d1 rv1 (k1 src hsrc)

end StepHelpers

/-! ### Reuse of `depthLookupProgram` via relocation and `measuredSearch` alignment -/

section DepthLookupReuse

def mapHaltToGoto {bits : Nat} (entry ret : Nat) (op : Instr bits 15) : Instr bits 15 :=
  match op with
  | .halt => .goto ret
  | _ => relocateInstr entry op

theorem nonHalt_mapHaltToGoto {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (entry ret : Nat) (op : Instr bits 15) :
    @nonHalt bits (layout bits inputCap workCap hi hw) (mapHaltToGoto entry ret op) = true := by
  cases op <;> rfl

def relocatedSubroutine {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (prog : Program (layout bits inputCap workCap hi hw)) (entry ret : Nat) :
    List (Instr bits 15) :=
  prog.toList.map (mapHaltToGoto entry ret)

theorem relocatedSubroutine_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (prog : Program (layout bits inputCap workCap hi hw)) (entry ret : Nat) :
    (relocatedSubroutine prog entry ret).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold relocatedSubroutine
  rw [List.all_map]
  simp only [List.all_eq_true, Function.comp_def, nonHalt_mapHaltToGoto, implies_true]

theorem linked_return_of_halt_map {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code linked : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {r : Result (layout bits inputCap workCap hi hw)}
    {fuel entry ret : Nat}
    (hRun : run code input fuel s = some r)
    (placed : ∀ i op, code[i]? = some op →
      linked[entry + i]? = some (mapHaltToGoto entry ret op))
    (target : ret < linked.size) :
    Steps linked input r.executed (relocateStatePC entry s) { r.finalState with pc := ret } := by
  refine linked_return_of_run_multi (ret := fun _ => ret) hRun ?_ ?_
  · intro i op hop hne
    have hmap : mapHaltToGoto entry ret op = relocateInstr entry op := by
      cases op <;> first | exact (hne rfl).elim | rfl
    simpa only [hmap] using placed i op hop
  · intro i hi'
    exact ⟨by simpa only [mapHaltToGoto] using placed i Instr.halt hi', target⟩

theorem relocate_depthLookup {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {base target u nodes exponent entry ret : Nat}
    {F : JumpForest} (s : State (layout bits inputCap workCap hi hw))
    (pc : s.pc = entry)
    (retBound : ret < code.size)
    (placed : Placed code entry
      (relocatedSubroutine (depthLookupProgram (hi := hi) (hw := hw)) entry ret))
    (parameters : Fixed base target s)
    (words : Records base F s.data) (uFit : u < F.size)
    (node : (reg s registers.ptr).val = u)
    (fits : F.numInserted ≤ nodes)
    (power : nodes + 2 ≤ 2 ^ exponent) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ work : Nat,
      work ≤ 60 * exponent + 7 ∧
      Steps code input work s t ∧
      t.pc = ret ∧
      (reg t registers.ptr).val = F.ancestorAtDepth u target ∧
      t.data = s.data := by
  let s0 : State (layout bits inputCap workCap hi hw) :=
    { regs := s.regs, data := s.data, pc := 0, regs_size := s.regs_size, data_size := s.data_size }
  have fixed0 : Fixed base target s0 :=
    ⟨parameters.parent, parameters.depth, parameters.jump, parameters.targetVal, parameters.zero⟩
  obtain ⟨t0, _, work, hbound, hrun, hanc, hdata, _, _⟩ :=
    run_depth_lookup input (base := base) (target := target) (u := u) s0
      fixed0 words uFit node nodes exponent fits power
  have hmap : ∀ i op, (depthLookupProgram (hi := hi) (hw := hw))[i]? = some op →
      code[entry + i]? = some (mapHaltToGoto entry ret op) := by
    intro i op hi'
    have hl : (depthLookupProgram (hi := hi) (hw := hw)).toList[i]? = some op := by
      simpa using hi'
    have hi'' : (relocatedSubroutine (depthLookupProgram (hi := hi) (hw := hw)) entry ret)[i]? =
        some (mapHaltToGoto entry ret op) := by
      unfold relocatedSubroutine
      rw [List.getElem?_map, hl]
      rfl
    exact placed i _ hi''
  have hrel := linked_return_of_halt_map hrun hmap retBound
  have hs0 : relocateStatePC entry (Phase.initial s0) = s := by
    cases s
    simp only [relocateStatePC, Phase.initial, s0]
    exact congrArg (State.mk _ _ · _ _) pc.symm
  rw [hs0] at hrel
  exact ⟨{ t0 with pc := ret }, work, hbound, hrel, rfl, hanc, hdata⟩

theorem measuredSearch_while
    (p : Nat → PaperB.ForestHead.Probe) :
    ∀ fuel lo hi : Nat,
      lo < hi → hi - lo ≤ 2 ^ fuel →
      (PaperB.ForestHead.measuredSearch p fuel lo hi).cut =
        if hi ≤ lo + 1 then lo
        else
          let mid := lo + (hi - lo) / 2
          if (p mid).ok then (PaperB.ForestHead.measuredSearch p (fuel - 1) mid hi).cut
          else (PaperB.ForestHead.measuredSearch p (fuel - 1) lo mid).cut := by
  intro fuel
  cases fuel with
  | zero =>
    intro lo hi hlt hle
    have hle1 : hi ≤ lo + 1 := by omega
    simp [PaperB.ForestHead.measuredSearch, hle1]
  | succ f =>
    intro lo hi _ _
    simp only [PaperB.ForestHead.measuredSearch, Nat.add_sub_cancel]
    by_cases h : hi ≤ lo + 1
    · simp [h]
    · simp only [h, ↓reduceIte]
      by_cases hp : (p (lo + (hi - lo) / 2)).ok = true
      · simp [hp, PaperB.ForestHead.addProbe]
      · simp [hp, PaperB.ForestHead.addProbe]

end DepthLookupReuse

/-! ### Small-constant loader (`immNat`) and Stage 2b Sweep Invariant & Init Phase -/

def immNatAux {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) :
    Nat → Nat → List (Instr bits 15)
  | 0, k => if hk : k < 8 then [.imm dst ⟨k, by omega⟩] else [.imm dst ⟨0, by omega⟩]
  | fuel + 1, k =>
    if hk : k < 8 then [.imm dst ⟨k, by omega⟩]
    else if k % 2 = 0 then immNatAux h8 dst one fuel (k / 2) ++ [.add dst dst dst]
    else immNatAux h8 dst one fuel (k / 2) ++ [.add dst dst dst, .add dst dst one]

def immNat {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) (k : Nat) :
    List (Instr bits 15) :=
  immNatAux h8 dst one 5 k

theorem immNatAux_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) :
    ∀ fuel k : Nat,
      (immNatAux h8 dst one fuel k).all
        (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    unfold immNatAux
    by_cases hk : k < 8 <;> simp only [hk, ↓reduceDIte] <;> rfl
  | succ f ih =>
    intro k
    unfold immNatAux
    by_cases hk : k < 8
    · simp only [hk, ↓reduceDIte]; rfl
    · simp only [hk, ↓reduceDIte]
      by_cases he : k % 2 = 0
      · simp only [he, ↓reduceIte, List.all_append, ih (k / 2), List.all_cons, List.all_nil]; rfl
      · simp only [he, ↓reduceIte, List.all_append, ih (k / 2),
          List.all_cons, List.all_nil]; rfl

theorem immNat_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) (k : Nat) :
    (immNat h8 dst one k).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true :=
  immNatAux_nonHalt h8 dst one 5 k

theorem immNatAux_succ {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) (f k : Nat) :
    immNatAux h8 dst one (f + 1) k =
      if hk : k < 8 then [.imm dst ⟨k, Nat.lt_of_lt_of_le hk h8⟩]
      else if k % 2 = 0 then immNatAux h8 dst one f (k / 2) ++ [.add dst dst dst]
      else immNatAux h8 dst one f (k / 2) ++ [.add dst dst dst, .add dst dst one] := rfl

theorem immNatAux_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {dst one : Fin 15} (hne : dst ≠ one) :
    ∀ fuel k : Nat, k < 2 ^ (fuel + 3) → k < 2 ^ bits →
      ∀ {entry : Nat} {s : State (layout bits inputCap workCap hi hw)},
        s.pc = entry →
        Placed code entry (immNatAux h8 dst one fuel k) →
        entry + (immNatAux h8 dst one fuel k).length < code.size →
        (reg s one).val = 1 →
        ∃ t : State (layout bits inputCap workCap hi hw),
          Steps code input (immNatAux h8 dst one fuel k).length s t ∧
          t.pc = entry + (immNatAux h8 dst one fuel k).length ∧
          (reg t dst).val = k ∧
          (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧
          t.data = s.data := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk8 hk entry s hpc hpl hsz _
    have hk8' : k < 8 := by simpa using hk8
    have heq : immNatAux h8 dst one 0 k = [.imm dst ⟨k, Nat.lt_of_lt_of_le hk8' h8⟩] := by
      unfold immNatAux; simp [hk8']
    have hlen1 : (immNatAux h8 dst one 0 k).length = 1 := by simp [heq]
    have f0 : code[s.pc]? = some (.imm dst ⟨k, Nat.lt_of_lt_of_le hk8' h8⟩) := by
      rw [hpc]; exact hpl 0 _ (by rw [heq]; rfl)
    obtain ⟨t, st, tpc, r, keep, dt⟩ :=
      step_imm_at (input := input) f0 (by rw [hpc]; omega)
    exact ⟨t, hlen1 ▸ .cons st (.zero _), by rw [tpc, hpc, hlen1], congrArg Fin.val r, keep, dt⟩
  | succ f ih =>
    intro k hpow hk entry s hpc hpl hsz hone
    by_cases hk8 : k < 8
    · have heq : immNatAux h8 dst one (f + 1) k = [.imm dst ⟨k, Nat.lt_of_lt_of_le hk8 h8⟩] := by
        rw [immNatAux_succ, dite_eq_left hk8]
      have hlen1 : (immNatAux h8 dst one (f + 1) k).length = 1 := by simp [heq]
      have f0 : code[s.pc]? = some (.imm dst ⟨k, Nat.lt_of_lt_of_le hk8 h8⟩) := by
        rw [hpc]; exact hpl 0 _ (by rw [heq]; rfl)
      obtain ⟨t, st, tpc, r, keep, dt⟩ :=
        step_imm_at (input := input) f0 (by rw [hpc]; omega)
      have hst : Steps code input (immNatAux h8 dst one (f + 1) k).length s t := by
        rw [hlen1]; exact .cons st (.zero _)
      exact ⟨t, hst, by rw [tpc, hpc, hlen1], congrArg Fin.val r, keep, dt⟩
    · have hdivPow : k / 2 < 2 ^ (f + 3) := by
        rw [show f + 1 + 3 = (f + 3) + 1 by omega, Nat.pow_succ] at hpow
        omega
      have hdivFit : k / 2 < 2 ^ bits := Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) hk
      by_cases heven : k % 2 = 0
      · have heq : immNatAux h8 dst one (f + 1) k =
            immNatAux h8 dst one f (k / 2) ++ [.add dst dst dst] := by
          rw [immNatAux_succ, dite_eq_right hk8, ite_eq_left heven]
        have hpl1 : Placed code entry (immNatAux h8 dst one f (k / 2)) := by
          intro i op hi'
          have hlt' : i < (immNatAux h8 dst one f (k / 2)).length :=
            (List.getElem?_eq_some_iff.mp hi').1
          exact hpl i op (by rw [heq, List.getElem?_append_left hlt']; exact hi')
        have hlenEq : (immNatAux h8 dst one (f + 1) k).length =
            (immNatAux h8 dst one f (k / 2)).length + 1 := by simp [heq]
        obtain ⟨s1, st1, pc1, r1, keep1, dt1⟩ :=
          ih (k / 2) hdivPow hdivFit hpc hpl1 (by rw [hlenEq] at hsz; omega) hone
        have fadd : code[s1.pc]? = some (.add dst dst dst) := by
          rw [pc1]
          exact hpl (immNatAux h8 dst one f (k / 2)).length _
            (by rw [heq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
        obtain ⟨s2, st2, pc2, r2, keep2, dt2⟩ :=
          step_add15_at (input := input) fadd (by rw [pc1]; rw [hlenEq] at hsz; omega)
        have r2v : (reg s2 dst).val = k := by
          rw [r2, PaperB.WordOps.add_no_wrap _ _ (by rw [r1]; omega), r1]; omega
        have hst : Steps code input (immNatAux h8 dst one (f + 1) k).length s s2 := by
          rw [hlenEq]; exact st1.append (.cons st2 (.zero _))
        exact ⟨s2, hst, by rw [pc2, pc1, hlenEq]; omega,
          r2v, fun r hr => (keep2 r hr).trans (keep1 r hr), dt2.trans dt1⟩
      · have heq : immNatAux h8 dst one (f + 1) k =
            immNatAux h8 dst one f (k / 2) ++ [.add dst dst dst, .add dst dst one] := by
          rw [immNatAux_succ, dite_eq_right hk8, ite_eq_right heven]
        have hpl1 : Placed code entry (immNatAux h8 dst one f (k / 2)) := by
          intro i op hi'
          have hlt' : i < (immNatAux h8 dst one f (k / 2)).length :=
            (List.getElem?_eq_some_iff.mp hi').1
          exact hpl i op (by rw [heq, List.getElem?_append_left hlt']; exact hi')
        have hlenEq : (immNatAux h8 dst one (f + 1) k).length =
            (immNatAux h8 dst one f (k / 2)).length + 2 := by simp [heq]
        obtain ⟨s1, st1, pc1, r1, keep1, dt1⟩ :=
          ih (k / 2) hdivPow hdivFit hpc hpl1 (by rw [hlenEq] at hsz; omega) hone
        have fadd1 : code[s1.pc]? = some (.add dst dst dst) := by
          rw [pc1]
          exact hpl (immNatAux h8 dst one f (k / 2)).length _
            (by rw [heq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
        obtain ⟨s2, st2, pc2, r2, keep2, dt2⟩ :=
          step_add15_at (input := input) fadd1 (by rw [pc1]; rw [hlenEq] at hsz; omega)
        have fadd2 : code[s2.pc]? = some (.add dst dst one) := by
          rw [pc2, pc1]
          exact hpl ((immNatAux h8 dst one f (k / 2)).length + 1) _
            (by
              rw [heq, List.getElem?_append_right (Nat.le_succ _)]
              have hs : (immNatAux h8 dst one f (k / 2)).length + 1 -
                  (immNatAux h8 dst one f (k / 2)).length = 1 := by omega
              rw [hs]; rfl)
        obtain ⟨s3, st3, pc3, r3, keep3, dt3⟩ :=
          step_add15_at (input := input) fadd2 (by rw [pc2, pc1]; rw [hlenEq] at hsz; omega)
        have hone2 : (reg s2 one).val = 1 := by rw [keep2 _ hne.symm, keep1 _ hne.symm, hone]
        have r2v : (reg s2 dst).val = 2 * (k / 2) := by
          rw [r2, PaperB.WordOps.add_no_wrap _ _ (by rw [r1]; omega), r1]; omega
        have r3v : (reg s3 dst).val = k := by
          rw [r3, PaperB.WordOps.add_no_wrap _ _ (by rw [r2v, hone2]; omega), r2v, hone2]; omega
        exact ⟨s3, hlenEq ▸ st1.append (.cons st2 (.cons st3 (.zero _))),
          by rw [pc3, pc2, pc1, hlenEq]; omega,
          r3v, fun r hr => (keep3 r hr).trans ((keep2 r hr).trans (keep1 r hr)), dt3.trans (dt2.trans dt1)⟩

theorem immNat_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {dst one : Fin 15} (hne : dst ≠ one)
    (k : Nat) (hk256 : k < 256) (hk : k < 2 ^ bits)
    {entry : Nat} {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = entry)
    (hpl : Placed code entry (immNat h8 dst one k))
    (hsz : entry + (immNat h8 dst one k).length < code.size)
    (hone : (reg s one).val = 1) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (immNat h8 dst one k).length s t ∧
      t.pc = entry + (immNat h8 dst one k).length ∧
      (reg t dst).val = k ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data :=
  immNatAux_steps h8 hne 5 k hk256 hk hpc hpl hsz hone

def mkPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (body : List (Instr bits 15))
    (allNonHalt : body.all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true) :
    Phase (layout bits inputCap workCap hi hw) :=
  Phase.ofLast (body ++ [Instr.halt]).toArray body.length
    (by simp)
    (by simp)
    (by simpa [List.take_left] using allNonHalt)

theorem word_mem_eq_of_map_val {bits : Nat} {x : Option (Word bits)} {v : Nat}
    (h : x.map Fin.val = some v) : ∃ w : Word bits, x = some w ∧ w.val = v := by
  cases x with
  | none => cases h
  | some w => exact ⟨w, rfl, Option.some.inj h⟩

/-- Shared invariant across the entire Stage 2b forest sweep (`0 ≤ idx ≤ H.vertexCount`). -/
structure SweepInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (F : JumpForest)
    (sRef : _root_.EX24.State H) (idx : Nat) (s : State (layout bits inputCap workCap hi hw)) : Prop where
  idxLe : idx ≤ H.vertexCount
  sRefLabelsSize : sRef.labels.size = H.vertexCount
  sRefNextLe : sRef.tables.next ≤ idx + 1
  labelsLt : ∀ v : Vertex H, sRef.labelAt v.val < sRef.tables.next
  backPos : ∀ k, 0 < k → k < sRef.tables.next → ∃ q, sRef.tables.back[k]? = some (some q)
  grounded : Grounded (orderedConfig dictRows large) F sRef.tables
  stage1 : Stage1Output H s order size_order rank rows
  -- Constants and base pointers in scratch slots `0..18`
  slNVal : (s.data[slN]?).map Fin.val = some H.vertexCount
  slRootVal : (s.data[slRoot]?).map Fin.val = some H.root.val
  slNextVal : (s.data[slNext]?).map Fin.val = some sRef.tables.next
  slDictBaseVal : (s.data[slDictBase]?).map Fin.val = some (dictBase H.vertexCount H.arcCount)
  slDictCntVal : (s.data[slDictCnt]?).map Fin.val = some (orderedConfig dictRows large).dict.size
  slDictSndVal : (s.data[slDictSnd]?).map Fin.val =
    some (dictBase H.vertexCount H.arcCount + 1 + (orderedConfig dictRows large).dict.size)
  slDictSlotsVal : (s.data[slDictSlots]?).map Fin.val =
    some (dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size)
  slJumpVal : (s.data[slJumpBase]?).map Fin.val = some (jumpBase H.vertexCount H.arcCount)
  slBackFstVal : (s.data[slBackFst]?).map Fin.val = some (backFstBase H.vertexCount H.arcCount)
  slBackSndVal : (s.data[slBackSnd]?).map Fin.val = some (backSndBase H.vertexCount H.arcCount)
  slLabelsVal : (s.data[slLabels]?).map Fin.val = some (labelsBase H.vertexCount H.arcCount)
  slParentsVal : (s.data[slParents]?).map Fin.val = some (parentsBase H.vertexCount H.arcCount)
  slOrderVal : (s.data[slOrder]?).map Fin.val = some (orderBase H.vertexCount H.arcCount)
  slRanksVal : (s.data[slRanks]?).map Fin.val = some (ranksBase H.vertexCount H.arcCount)
  slRowStartVal : (s.data[slRowStart]?).map Fin.val = some (rowStartBase H.vertexCount H.arcCount)
  slRowEndVal : (s.data[slRowEnd]?).map Fin.val = some (rowEndBase H.vertexCount H.arcCount)
  slPredBufVal : (s.data[slPredBuf]?).map Fin.val = some (predBufBase H.vertexCount H.arcCount)
  slSourceVal : (s.data[slSource]?).map Fin.val = some (sourceBase H.vertexCount H.arcCount)
  slIdxVal : (s.data[slIdx]?).map Fin.val = some idx
  -- Mutable forest & dictionary banks
  records : Records (jumpBase H.vertexCount H.arcCount) F s.data
  dictHeader : (s.data[dictBase H.vertexCount H.arcCount]?).map Fin.val =
    some (orderedConfig dictRows large).dict.size
  dictKeys : ∀ i (hi' : i < (orderedConfig dictRows large).dict.size),
    (s.data[dictBase H.vertexCount H.arcCount + 1 + i]?).map Fin.val =
      some ((orderedConfig dictRows large).dict[i]'hi').1 ∧
    (s.data[dictBase H.vertexCount H.arcCount + 1 +
      (orderedConfig dictRows large).dict.size + i]?).map Fin.val =
      some ((orderedConfig dictRows large).dict[i]'hi').2
  dictSlots : ∀ i (_ : i < (orderedConfig dictRows large).dict.size),
    (s.data[dictBase H.vertexCount H.arcCount + 1 +
      2 * (orderedConfig dictRows large).dict.size + i]?).map Fin.val =
      some (sRef.tables.slotAt i)
  backMem : ∀ k ≤ H.vertexCount,
    (s.data[backFstBase H.vertexCount H.arcCount + k]?).map Fin.val =
      some (encodeBackPair (sRef.tables.back[k]?.join)).1 ∧
    (s.data[backSndBase H.vertexCount H.arcCount + k]?).map Fin.val =
      some (encodeBackPair (sRef.tables.back[k]?.join)).2
  labelsMem : ∀ v : Vertex H,
    (s.data[labelsBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
      some (sRef.labelAt v.val)
  parentsMem : ∀ u < F.size,
    (s.data[parentsBase H.vertexCount H.arcCount + u]?).map Fin.val = some (F.parentOf u)


/-! ### Shared scratch, phase, and invariant helpers extracted from SweepInit/Loop -/

def sweepInitStoreScratch {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (sl : Nat) (src : Fin 15) :
    List (Instr bits 15) :=
  immNat h8 rTmp rOne sl ++ [.storeData rTmp src]

theorem sweepInitStoreScratch_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (sl : Nat) (src : Fin 15) :
    (sweepInitStoreScratch h8 sl src).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [sweepInitStoreScratch, List.all_append, immNat_nonHalt, nonHalt]


def isNonHaltBool {bits : Nat} : Instr bits 15 → Bool
  | .halt => false
  | _ => true

theorem all_nonHalt_eq_isNonHaltBool {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (l : List (Instr bits 15)) :
    l.all (@nonHalt bits (layout bits inputCap workCap hi hw)) = l.all isNonHaltBool := by
  induction l with
  | nil => rfl
  | cons op rest ih =>
    have hop : @nonHalt bits (layout bits inputCap workCap hi hw) op = isNonHaltBool op := by
      cases op <;> rfl
    simp only [List.all_cons, hop, ih]

theorem list_all_append_true {α : Type} {p : α → Bool} {a b : List α}
    (ha : a.all p = true) (hb : b.all p = true) : (a ++ b).all p = true := by
  simp [ha, hb]

theorem list_all_cons_true {α : Type} {p : α → Bool} {a : α} {b : List α}
    (ha : p a = true) (hb : b.all p = true) : (a :: b).all p = true := by
  simp [ha, hb]


theorem slice_get_val_eq {bits : Nat} {xs : Array (Word bits)}
    (sl : PaperB.PairLookup.ColumnReduction.Slice xs) (i idx : Nat)
    (hi : i < sl.len) (hidx : idx < xs.size) (heq : sl.base.val + i = idx) :
    (sl.get i hi).val = (xs[idx]'hidx).val := by
  unfold PaperB.PairLookup.ColumnReduction.Slice.get
  subst heq
  rfl

theorem secondSlice_base {bits : Nat} {xs : Array (Word bits)} (v : FlatPairDictionary.Valid xs) :
    (FlatPairDictionary.secondSlice xs v).base.val = 1 + FlatPairDictionary.rowCount xs := rfl

theorem slotSlice_base {bits : Nat} {xs : Array (Word bits)} (v : FlatPairDictionary.Valid xs) :
    (FlatPairDictionary.slotSlice xs v).base.val = 1 + 2 * FlatPairDictionary.rowCount xs := by
  unfold FlatPairDictionary.slotSlice FlatPairDictionary.slotBase FlatPairDictionary.secondBase
  change 1 + FlatPairDictionary.rowCount xs + FlatPairDictionary.rowCount xs = _
  omega

theorem dict_size_le (H : LabelledQuotient) (rows : Rows H)
    (large : 3 ≤ H.vertexCount) :
    (orderedConfig rows large).dict.size ≤ H.vertexCount := by
  have hs := orderedConfig rows large |>.sorted
  have hspec := PaperB.ForestDictionary.dictionary_spec rows orderedPairCode
  have hnd : (orderedConfig rows large).dict.toList.Nodup := by
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij => ?_)
    have hlt := hs i j (by simpa using hi) (by simpa using hj) hij
    intro heq
    have heq' : (orderedConfig rows large).dict[i] = (orderedConfig rows large).dict[j] := heq
    rw [heq'] at hlt
    exact PaperB.PairLookup.lexLess_irrefl _ hlt
  let cands : List PaperB.PairLookup.Key :=
    (List.finRange H.vertexCount).filterMap
      (fun (y : Vertex H) => (preparedKey H (rows.row y)).map orderedPairCode)
  have hsub : ∀ k ∈ (orderedConfig rows large).dict.toList, k ∈ cands := by
    intro k hk
    have hk' : k ∈ (PaperB.ForestDictionary.dictionary rows orderedPairCode).toList := hk
    rw [hspec.2.1 k] at hk'
    obtain ⟨y, q, hq1, hq2⟩ := hk'
    refine List.mem_filterMap.mpr ⟨y, List.mem_finRange y, ?_⟩
    rw [hq1, Option.map_some, hq2]
  have hle := nodup_length_le_of_subset _ cands hnd hsub
  have hcands : cands.length ≤ (List.finRange H.vertexCount).length := by
    dsimp only [cands]
    exact List.length_filterMap_le _ _
  have hfr : (List.finRange H.vertexCount).length = H.vertexCount := List.length_finRange
  have hsize : (orderedConfig rows large).dict.size = (orderedConfig rows large).dict.toList.length :=
    (Array.length_toList).symm
  omega


theorem placed_fetch {bits : Nat} {L : Layout bits}
    {code : Program L} {s : State L} {entry i : Nat}
    {l : List (Instr bits L.registerCount)} {op : Instr bits L.registerCount}
    (hpl : Placed code entry l) (hi : l[i]? = some op) (hpc : s.pc = entry + i) :
    code[s.pc]? = some op := by
  rw [hpc]; exact hpl i op hi

theorem placed_append_left {bits : Nat} {L : Layout bits}
    {code : Program L} {entry : Nat} {a b : List (Instr bits L.registerCount)}
    (h : Placed code entry (a ++ b)) : Placed code entry a := by
  intro i op hi
  have hlt : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
  exact h i op (by rw [List.getElem?_append_left hlt]; exact hi)

theorem placed_append_right {bits : Nat} {L : Layout bits}
    {code : Program L} {entry : Nat} {a b : List (Instr bits L.registerCount)}
    (h : Placed code entry (a ++ b)) : Placed code (entry + a.length) b := by
  intro i op hi
  have h' := h (a.length + i) op (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hi)
  rwa [← Nat.add_assoc] at h'

theorem placed_of_phase_body {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (body : List (Instr bits 15))
    (allNH : body.all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true) :
    Placed (mkPhase (hi := hi) (hw := hw) body allNH).code 0 body := by
  intro i op hbi
  have hlt : i < body.length := (List.getElem?_eq_some_iff.mp hbi).1
  change (body ++ [Instr.halt]).toArray[0 + i]? = some op
  rw [Nat.zero_add, ← Array.getElem?_toList]
  change (body ++ [Instr.halt])[i]? = some op
  rw [List.getElem?_append_left hlt]
  exact hbi

theorem array_set_getElem?_same {α : Type} (a : Array α) (i : Nat)
    (hi : i < a.size) (v : α) : (a.set i v hi)[i]? = some v := by
  rw [Array.getElem?_eq_getElem (by simpa only [Array.size_set] using hi), Array.getElem_set_self]

theorem array_set_getElem?_ne {α : Type} (a : Array α) (i j : Nat)
    (hi : i < a.size) (v : α) (hne : j ≠ i) : (a.set i v hi)[j]? = a[j]? := by
  rw [Array.getElem?_set_ne hi (Ne.symm hne)]

theorem sweepInitStoreScratch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {entry : Nat} (sl : Nat) (src : Fin 15) (hsrc : src ≠ rTmp)
    (hsl256 : sl < 256) (hslCap : sl < workCap)
    (hpc : s.pc = entry)
    (hpl : Placed code entry (sweepInitStoreScratch h8 sl src))
    (hsz : entry + (sweepInitStoreScratch h8 sl src).length < code.size)
    (hone : (reg s rOne).val = 1) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (sweepInitStoreScratch h8 sl src).length s t ∧
      t.pc = entry + (sweepInitStoreScratch h8 sl src).length ∧
      (t.data[sl]?).map Fin.val = some (reg s src).val ∧
      (∀ j, j ≠ sl → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ rTmp → reg t r = reg s r) := by
  have hlen : (sweepInitStoreScratch (bits := bits) h8 sl src).length =
      (immNat h8 rTmp rOne sl).length + 1 := by simp [sweepInitStoreScratch]
  have hplImm : Placed code entry (immNat h8 rTmp rOne sl) :=
    placed_append_left hpl
  obtain ⟨s1, st1, pc1, rtmp1, keep1, dt1⟩ :=
    immNat_steps h8 (show rTmp ≠ rOne by decide) sl hsl256
      (Nat.lt_of_lt_of_le hslCap hw) hpc hplImm (by rw [hlen] at hsz; omega) hone
  have fstore : code[s1.pc]? = some (.storeData rTmp src) := by
    rw [pc1]
    exact hpl (immNat h8 rTmp rOne sl).length _
      (by simp [sweepInitStoreScratch])
  have hlt1 : (reg s1 rTmp).val < workCap := by rw [rtmp1]; exact hslCap
  obtain ⟨s2, st2, pc2, d2, keep2⟩ :=
    step_storeData_at (input := input) fstore (by rw [pc1]; rw [hlen] at hsz; omega) hlt1
  have hlt1' : (reg s1 rTmp).val < s1.data.size := by rw [s1.data_size]; exact hlt1
  have hstep : Steps code input (sweepInitStoreScratch (bits := bits) h8 sl src).length s s2 := by
    rw [hlen]; exact st1.append (.cons st2 (.zero _))
  refine ⟨s2, hstep, by rw [pc2, pc1, hlen]; omega, ?_, ?_, fun r hr => (keep2 r).trans (keep1 r hr)⟩
  · rw [d2, show sl = (reg s1 rTmp).val from rtmp1.symm, array_set_getElem?_same,
        Option.map_some, keep1 src hsrc]
  · intro j hj
    rw [d2, array_set_getElem?_ne _ _ _ hlt1' _ (by rw [rtmp1]; exact hj), dt1]

theorem immNat_length_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) :
    ∀ fuel k : Nat, (immNatAux h8 dst one fuel k).length ≤ 2 * fuel + 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    unfold immNatAux
    by_cases hk : k < 8 <;> simp [hk]
  | succ f ih =>
    intro k
    unfold immNatAux
    by_cases hk : k < 8
    · simp [hk]
    · by_cases he : k % 2 = 0 <;> simp [hk, he] <;> have := ih (k / 2) <;> omega


theorem scratch_lt_workCap17 {n m workCap : Nat}
    (hWork : rawWorkCap n m ≤ workCap) {sl : Nat} (hsl : sl < 17) :
    sl < workCap := by
  have : 32 * n + 7 * m + 17 ≤ workCap := hWork
  omega

theorem scratch_lt_workCap30 {n m workCap : Nat}
    (hWork : rawWorkCap n m ≤ workCap) (hn : 3 ≤ n) {sl : Nat} (hsl : sl < 30) :
    sl < workCap := by
  have : 32 * n + 7 * m + 17 ≤ workCap := hWork
  omega


theorem stage1_frame_data {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    {s t : State (layout bits inputCap workCap hi hw)}
    (hs : Stage1Output H s order size_order rank rows)
    (hPres : ∀ j, orderBase H.vertexCount H.arcCount ≤ j ∧
      j < candFstABase H.vertexCount H.arcCount → t.data[j]? = s.data[j]?) :
    Stage1Output H t order size_order rank rows := by
  refine ⟨hs.nodup, hs.covers, hs.topo, hs.rank_at, hs.rank_increasing, hs.rank_arc, ?_, ?_, ?_⟩
  · intro i
    rw [hPres _ ⟨by simp only [orderBase, stampsBase, indegBase, csrArenaWords]; omega,
      by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega⟩]
    exact hs.order_mem i
  · intro v
    rw [hPres _ ⟨by simp only [ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega,
      by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase]; omega⟩]
    exact hs.ranks_mem v
  · intro y
    obtain ⟨lo, hi', hlo, hhi, h1, h2, h3, h4⟩ := hs.rows_mem y
    refine ⟨lo, hi', ?_, ?_, h1, h2, h3, ?_⟩
    · rw [hPres _ ⟨by simp only [rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega,
        by simp only [candFstABase, predBufBase, rowEndBase, rowStartBase]; omega⟩]; exact hlo
    · rw [hPres _ ⟨by simp only [rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega,
        by simp only [candFstABase, predBufBase, rowEndBase]; omega⟩]; exact hhi
    · intro j
      rw [hPres _ ⟨by simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega,
        by have := j.isLt; simp only [candFstABase, predBufBase]; omega⟩]
      exact h4 j


section SweepLoopMath

open PaperB.ForestHead _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

def loadScratch {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst : Fin 15) (sl : Nat) :
    List (Instr bits 15) :=
  immNat h8 rTmp rOne sl ++ [.loadData dst rTmp]

theorem loadScratch_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (dst : Fin 15) (sl : Nat) :
    (loadScratch h8 dst sl).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [loadScratch, List.all_append, immNat_nonHalt, nonHalt]

theorem loadScratch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry : Nat} (dst : Fin 15) (sl : Nat)
    (hsl : sl < workCap) (hSlFit : sl < 32)
    (_hdr : dst ≠ rTmp) (hro : rTmp ≠ rOne)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = entry) (hpl : Placed code entry (loadScratch h8 dst sl))
    (hsz : entry + (loadScratch h8 dst sl).length < code.size)
    (hone : (reg s rOne).val = 1)
    {v : Word bits} (hv : s.data[sl]? = some v) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (loadScratch h8 dst sl).length s t ∧
      t.pc = entry + (loadScratch h8 dst sl).length ∧
      reg t dst = v ∧
      t.data = s.data ∧
      ∀ r, r ≠ dst → r ≠ rTmp → reg t r = reg s r := by
  have hl : (loadScratch h8 dst sl).length = (immNat h8 rTmp rOne sl).length + 1 := by
    simp [loadScratch]
  have hplI : Placed code entry (immNat h8 rTmp rOne sl) := placed_append_left hpl
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
    immNat_steps h8 hro sl (by omega) (Nat.lt_of_lt_of_le hsl hw) hpc hplI (by rw [hl] at hsz; omega) hone
  have hf : code[s1.pc]? = some (.loadData dst rTmp) :=
    placed_fetch (op := .loadData dst rTmp) hpl (i := (immNat h8 rTmp rOne sl).length)
      (by simp [loadScratch]) pc1
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ :=
    step_loadData_at' (input := input) (s := s1) hf (by rw [pc1, Nat.add_assoc, ← hl]; exact hsz)
      (by rw [r1]; exact hsl) (by rw [d1, r1]; exact hv)
  refine ⟨s2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact st1.append (.cons st2 (.zero _))
  · rw [pc2, pc1, hl, Nat.add_assoc]
  · exact r2
  · exact d2.trans d1
  · intro r hr1 hr2
    exact (k2 r hr1).trans (k1 r hr2)

theorem loadScratch_length_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst : Fin 15) (sl : Nat) :
    (loadScratch h8 dst sl).length ≤ 12 := by
  simp only [loadScratch, List.length_append, List.length_cons, List.length_nil]
  change (immNatAux h8 rTmp rOne 5 sl).length + 1 ≤ 12
  have := immNat_length_le h8 rTmp rOne 5 sl
  omega

theorem storeScratch_length_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (sl : Nat) (src : Fin 15) :
    (sweepInitStoreScratch h8 sl src).length ≤ 12 := by
  simp only [sweepInitStoreScratch, List.length_append, List.length_cons, List.length_nil]
  change (immNatAux h8 rTmp rOne 5 sl).length + 1 ≤ 12
  have := immNat_length_le h8 rTmp rOne 5 sl
  omega

theorem SweepInv.of_scratch19 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s t : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx s)
    (hPres : ∀ j, j < 19 ∨ 30 ≤ j → t.data[j]? = s.data[j]?) :
    SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx t := by
  have hScr : ∀ sl, sl < 19 → t.data[sl]? = s.data[sl]? := fun sl hsl => hPres sl (Or.inl hsl)
  have hHigh : ∀ j, orderBase H.vertexCount H.arcCount ≤ j → t.data[j]? = s.data[j]? := fun j hj =>
    hPres j (Or.inr (by
      have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by omega)
      omega))
  have hBaseLe : ∀ j, jumpBase H.vertexCount H.arcCount ≤ j → orderBase H.vertexCount H.arcCount ≤ j := by
    intro j hj
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at hj ⊢
    omega
  have hDictLe : ∀ j, dictBase H.vertexCount H.arcCount ≤ j → orderBase H.vertexCount H.arcCount ≤ j := by
    intro j hj
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at hj ⊢
    omega
  refine
    { idxLe := inv.idxLe
      sRefLabelsSize := inv.sRefLabelsSize
      sRefNextLe := inv.sRefNextLe
      labelsLt := inv.labelsLt
      backPos := inv.backPos
      grounded := inv.grounded
      stage1 := stage1_frame_data inv.stage1 (fun j ⟨h1, _⟩ => hHigh j h1)
      slNVal := by rw [hScr _ (by decide)]; exact inv.slNVal
      slRootVal := by rw [hScr _ (by decide)]; exact inv.slRootVal
      slNextVal := by rw [hScr _ (by decide)]; exact inv.slNextVal
      slDictBaseVal := by rw [hScr _ (by decide)]; exact inv.slDictBaseVal
      slDictCntVal := by rw [hScr _ (by decide)]; exact inv.slDictCntVal
      slDictSndVal := by rw [hScr _ (by decide)]; exact inv.slDictSndVal
      slDictSlotsVal := by rw [hScr _ (by decide)]; exact inv.slDictSlotsVal
      slJumpVal := by rw [hScr _ (by decide)]; exact inv.slJumpVal
      slBackFstVal := by rw [hScr _ (by decide)]; exact inv.slBackFstVal
      slBackSndVal := by rw [hScr _ (by decide)]; exact inv.slBackSndVal
      slLabelsVal := by rw [hScr _ (by decide)]; exact inv.slLabelsVal
      slParentsVal := by rw [hScr _ (by decide)]; exact inv.slParentsVal
      slOrderVal := by rw [hScr _ (by decide)]; exact inv.slOrderVal
      slRanksVal := by rw [hScr _ (by decide)]; exact inv.slRanksVal
      slRowStartVal := by rw [hScr _ (by decide)]; exact inv.slRowStartVal
      slRowEndVal := by rw [hScr _ (by decide)]; exact inv.slRowEndVal
      slPredBufVal := by rw [hScr _ (by decide)]; exact inv.slPredBufVal
      slSourceVal := by rw [hScr _ (by decide)]; exact inv.slSourceVal
      slIdxVal := by rw [hScr _ (by decide)]; exact inv.slIdxVal
      records := by
        refine ⟨inv.records.valid, ?_, ?_, ?_, ?_⟩
        · rw [t.data_size, ← s.data_size]; exact inv.records.fit
        · intro u hu; rw [hHigh _ (hBaseLe _ (by omega))]; exact inv.records.parent u hu
        · intro u hu; rw [hHigh _ (hBaseLe _ (by omega))]; exact inv.records.depth u hu
        · intro u hu; rw [hHigh _ (hBaseLe _ (by omega))]; exact inv.records.jump u hu
      dictHeader := by rw [hHigh _ (hDictLe _ (by omega))]; exact inv.dictHeader
      dictKeys := fun i hi' => ⟨by rw [hHigh _ (hDictLe _ (by omega))]; exact (inv.dictKeys i hi').1,
                                by rw [hHigh _ (hDictLe _ (by omega))]; exact (inv.dictKeys i hi').2⟩
      dictSlots := fun i hi' => by rw [hHigh _ (hDictLe _ (by omega))]; exact inv.dictSlots i hi'
      backMem := fun k hk =>
        ⟨by rw [hHigh _ (hBaseLe _ (by simp only [backFstBase]; omega))]; exact (inv.backMem k hk).1,
         by rw [hHigh _ (hBaseLe _ (by simp only [backSndBase, backFstBase]; omega))]; exact (inv.backMem k hk).2⟩
      labelsMem := fun v => by
        rw [hHigh _ (hBaseLe _ (by simp only [labelsBase, backSndBase, backFstBase]; omega))]
        exact inv.labelsMem v
      parentsMem := fun u hu => by
        rw [hHigh _ (hBaseLe _ (by simp only [parentsBase, labelsBase, backSndBase, backFstBase]; omega))]
        exact inv.parentsMem u hu }

theorem stepPrepared_eq_of_testSpec {H : LabelledQuotient}
    (c : Config H) (s : _root_.EX24.State H) (rank : Vertex H → Nat)
    (y : Vertex H) (xs1 xs2 : List (Vertex H))
    (T1 : TestSpec y xs1) (T2 : TestSpec y xs2)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b)
    {r1 : HeadResult H} (h1 : stepPrepared c s rank y xs1 = some r1) :
    ∃ r2 : HeadResult H,
      stepPrepared c s rank y xs2 = some r2 ∧
      r2.state = r1.state ∧
      r2.measured.step = r1.measured.step ∧
      r2.installed.node = r1.installed.node ∧
      r2.installed.allocated = r1.installed.allocated := by
  have hp1 : _root_.EX24.step c s rank y xs1 = some r1 := by
    rwa [← stepPrepared_eq_step c s rank y xs1 T1 inj]
  obtain ⟨hm1, hi1, _, hlab1⟩ := step_parts hp1
  have hProbeOk : ∀ m d,
      (probe (selectors c s) xs1 m d).ok = (probe (selectors c s) xs2 m d).ok := by
    intro m d
    by_cases hz : d = 0
    · simp [probe, hz]
    by_cases hd : d ≤ (selectors c s).depth ((selectors c s).label m)
    · simp only [probe, ite_eq_right hz, ite_eq_left hd]
      have hiff : (scan (raw (selectors c s) ((selectors c s).atDepth ((selectors c s).label m) d)
            ((selectors c s).key ((selectors c s).atDepth ((selectors c s).label m) d))) xs1).ok = true ↔
          (scan (raw (selectors c s) ((selectors c s).atDepth ((selectors c s).label m) d)
            ((selectors c s).key ((selectors c s).atDepth ((selectors c s).label m) d))) xs2).ok = true := by
        rw [scan_ok, scan_ok]
        constructor <;> intro h u hu
        · exact h u ((T1.cover u).mpr ((T2.cover u).mp hu))
        · exact h u ((T2.cover u).mpr ((T1.cover u).mp hu))
      cases hA : (scan _ xs1).ok <;> cases hB : (scan _ xs2).ok <;> simp_all
    · simp [probe, hz, hd]
  have hStepEq : (runHead (selectors c s) rank y xs2).step =
      (runHead (selectors c s) rank y xs1).step := by
    by_cases hy : y = H.root
    · simp [runHead, hy]
    · by_cases hhr : H.hasQuotientArcBool H.root y = true
      · simp [runHead, hy, hhr]
      · have hhrf : H.hasQuotientArcBool H.root y = false := Bool.eq_false_iff.mpr hhr
        cases hmax : maxByRank rank (preds H y) with
        | none => simp [runHead, hy, hhrf, hmax]
        | some m =>
          have hCut : (measuredLog (probe (selectors c s) xs2 m)
              ((selectors c s).depth ((selectors c s).label m) + 1)).cut =
            (measuredLog (probe (selectors c s) xs1 m)
              ((selectors c s).depth ((selectors c s).label m) + 1)).cut := by
            have p1 := congrArg Prod.fst (measuredLog_project (probe (selectors c s) xs1 m)
              ((selectors c s).depth ((selectors c s).label m) + 1))
            have p2 := congrArg Prod.fst (measuredLog_project (probe (selectors c s) xs2 m)
              ((selectors c s).depth ((selectors c s).label m) + 1))
            dsimp only at p1 p2
            rw [p1, p2]
            have hfn : (fun d => (probe (selectors c s) xs2 m d).ok) =
                (fun d => (probe (selectors c s) xs1 m d).ok) := funext fun d => (hProbeOk m d).symm
            rw [hfn]
          simp [runHead, hy, hhrf, hmax, active, hCut]
  have hyBound : c.vertexIndex y < s.labels.size := by
    by_cases hy : c.vertexIndex y < s.labels.size
    · exact hy
    · simp [_root_.EX24.step, hy] at hp1
  have hInst : install c s.tables (runHead (selectors c s) rank y xs2).step = some r1.installed := by
    rw [hStepEq, ← hm1]; exact hi1
  let r2 : HeadResult H := ⟨runHead (selectors c s) rank y xs2, r1.installed,
    s.labels.set (c.vertexIndex y) r1.installed.node hyBound⟩
  have hlabEq : r2.labels = r1.labels := by
    apply Array.ext
    · simp only [r2, Array.size_set]; exact (step_parts hp1).2.2.1.symm
    · intro j hj1 hj2
      have h1' := hlab1 j
      have h2' : r2.labels[j]? = if j = c.vertexIndex y then some r1.installed.node else s.labels[j]? := by
        by_cases hj : j = c.vertexIndex y <;> simp [r2, getElem?_def, Array.getElem_set, hj, hyBound, Ne.symm]
      have hopt : (some r2.labels[j] : Option Nat) = some r1.labels[j] := by
        rw [← getElem?_pos r2.labels j hj1, ← getElem?_pos r1.labels j hj2, h2', h1']
      exact Option.some.inj hopt
  refine ⟨r2, ?_, ?_, ?_, rfl, rfl⟩
  · rw [stepPrepared_eq_step c s rank y xs2 T2 inj]
    simp [_root_.EX24.step, hyBound, hInst, r2]
  · change ({ tables := r1.installed.tables, labels := r2.labels } : _root_.EX24.State H) = r1.state
    rw [hlabEq]
    cases r1; rfl
  · exact hStepEq.trans (congrArg Measured.step hm1).symm

theorem orderedRows_drop_uncons {H : LabelledQuotient} (dictRows : Rows H)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    {sRef out : _root_.EX24.State H} {log : Log H} {idx : Nat}
    (hidx : idx < H.vertexCount)
    (ht : Trace (orderedConfig dictRows large) rank sRef
      ((orderedRows dictRows order size_order).drop idx) out log) :
    let y := orderedVertexAt order size_order ⟨idx, hidx⟩
    ∃ rStep : HeadResult H, ∃ tail : Log H,
      stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep ∧
      Trace (orderedConfig dictRows large) rank rStep.state
        ((orderedRows dictRows order size_order).drop (idx + 1)) out tail := by
  have hDrop : (orderedRows dictRows order size_order).drop idx =
      ⟨orderedVertexAt order size_order ⟨idx, hidx⟩,
        dictRows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)⟩ ::
      (orderedRows dictRows order size_order).drop (idx + 1) := by
    have hlen : idx < (orderedRows dictRows order size_order).length := by
      simp [orderedRows, hidx]
    have helem : (orderedRows dictRows order size_order)[idx]'hlen =
        ⟨orderedVertexAt order size_order ⟨idx, hidx⟩,
          dictRows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)⟩ := by
      simp [orderedRows]; rfl
    rw [← helem]
    exact List.drop_eq_getElem_cons hlen
  rw [hDrop] at ht
  cases ht with
  | cons hs htail => exact ⟨_, _, hs, htail⟩

theorem validJumpForest_depthOf_jump_le {F : JumpForest} (hF : ValidJumpForest F) :
    ∀ {u : Nat}, u < F.size → F.depthOf (F.jumpOf u) ≤ F.depthOf u := by
  let ⟨_, inv⟩ := hF.exists_forestInvariant
  intro u hu
  refine Nat.strongRecOn (motive := fun w => w < F.size → F.depthOf (F.jumpOf w) ≤ F.depthOf w)
    u ?_ hu
  intro w ih hw
  by_cases hPos : 0 < w
  · have specW := inv.nodes w hw
    have hpLt : F.parentOf w < w := specW.pos_parent_lt hPos
    have hpSz : F.parentOf w < F.size := specW.parent_lt_size
    have hdepW : F.depthOf w = F.depthOf (F.parentOf w) + 1 := specW.pos_depth hPos
    rcases specW.pos_jump_cases hPos with hj | hj
    · rw [hj, hdepW]; omega
    · have haLt : F.jumpOf (F.parentOf w) < F.size := hF.jumpOf_lt_size hpSz
      have h1 := ih (F.parentOf w) hpLt hpSz
      have h2 : F.jumpOf (F.parentOf w) ≤ F.parentOf w := by
        by_cases hpp : 0 < F.parentOf w
        · have hjl := (inv.nodes (F.parentOf w) hpSz).pos_jump_le_parent hpp
          have hpl := (inv.nodes (F.parentOf w) hpSz).pos_parent_lt hpp
          omega
        · have hp0 : F.parentOf w = 0 := by omega
          rw [hp0, inv.root_jump]; omega
      have h3 : F.depthOf (F.jumpOf (F.jumpOf (F.parentOf w))) ≤ F.depthOf (F.jumpOf (F.parentOf w)) := by
        by_cases hpa : F.jumpOf (F.parentOf w) < w
        · exact ih _ hpa haLt
        · omega
      rw [hj, hdepW]; omega
  · have hw0 : w = 0 := by omega
    rw [hw0, inv.root_jump]; exact Nat.le_refl _

theorem distinctRanks_of_stage1 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} {s : State (layout bits inputCap workCap hi hw)}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    (st : Stage1Output H s order size_order rank rows) :
    ∀ {a b : Vertex H}, rank a = rank b → a = b := by
  intro a b hab
  obtain ⟨ia, hia⟩ := st.covers a
  obtain ⟨ib, hib⟩ := st.covers b
  have hij : ia.val = ib.val := by
    by_cases hlt : ia.val < ib.val
    · have h := st.rank_increasing ia ib hlt
      rw [hia, hib] at h; omega
    · by_cases hgt : ib.val < ia.val
      · have h := st.rank_increasing ib ia hgt
        rw [hib, hia] at h; omega
      · omega
  exact hia.symm.trans ((congrArg (orderedVertexAt order size_order) (Fin.ext hij)).trans hib)

theorem SweepInv.advance_keep {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s t : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx s)
    (hidx : idx < H.vertexCount)
    (y : Vertex H)
    {rStep : HeadResult H}
    (hStep : stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep)
    (hNoAlloc : rStep.installed.allocated = false)
    (hLab : (t.data[labelsBase H.vertexCount H.arcCount + y.val]?).map Fin.val =
      some rStep.installed.node)
    (hIdx : (t.data[slIdx]?).map Fin.val = some (idx + 1))
    (hPres : ∀ j, (19 ≤ j ∧ j < 30) ∨ j = slIdx ∨
      j = labelsBase H.vertexCount H.arcCount + y.val ∨
      t.data[j]? = s.data[j]?) :
    SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F rStep.state (idx + 1) t := by
  let c := orderedConfig dictRows large
  have inj : ∀ a b : Vertex H, rank a = rank b → a = b := fun a b h => distinctRanks_of_stage1 inv.stage1 h
  obtain ⟨_, hInst, hLabSz, hLabAt⟩ := prepared_parts (row := ⟨y, dictRows.row y⟩) (dictRows.spec y) inj hStep
  have hOk := install_spec inv.grounded hInst
  have hTabEq : rStep.installed.tables = sRef.tables := hOk.no_allocation hNoAlloc
  have hStEq : rStep.state.tables = sRef.tables := hTabEq
  have hNextEq : rStep.state.tables.next = sRef.tables.next := congrArg Tables.next hTabEq
  have hPre : ∀ j, j ≠ slIdx → j ≠ labelsBase H.vertexCount H.arcCount + y.val →
      (j < 19 ∨ 30 ≤ j) → t.data[j]? = s.data[j]? := by
    intro j hj1 hj2 hj3
    rcases hPres j with h | h | h | h
    · omega
    · exact absurd h hj1
    · exact absurd h hj2
    · exact h
  have hScrNe : ∀ sl, sl < 19 → sl ≠ slIdx →
      t.data[sl]? = s.data[sl]? := fun sl hsl hne => by
    apply hPre sl hne
    · simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
        candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
        stampsBase, indegBase, csrArenaWords]
      omega
    · exact Or.inl hsl
  have hHighNe : ∀ j, orderBase H.vertexCount H.arcCount ≤ j →
      j ≠ labelsBase H.vertexCount H.arcCount + y.val → t.data[j]? = s.data[j]? := fun j hj hne =>
    hPre j (by
      have hsi : slIdx = 18 := rfl
      have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by omega)
      omega) hne (Or.inr (by
      have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by omega)
      omega))
  have hOrderLtLab : ∀ j, j < candFstABase H.vertexCount H.arcCount →
      j ≠ labelsBase H.vertexCount H.arcCount + y.val := fun j hj => by
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase] at hj ⊢; omega
  have hDictLtLab : ∀ j, j < jumpBase H.vertexCount H.arcCount →
      j ≠ labelsBase H.vertexCount H.arcCount + y.val := fun j hj => by
    simp only [labelsBase, backSndBase, backFstBase, jumpBase] at hj ⊢; omega
  have hJumpLtLab : ∀ u k, u < F.size → k < 3 →
      jumpBase H.vertexCount H.arcCount + 3 * u + k ≠ labelsBase H.vertexCount H.arcCount + y.val :=
    fun u k hu hk => by
      have hFsz : F.size ≤ H.vertexCount + 1 := by
        rw [inv.grounded.size_eq]; exact Nat.le_trans inv.sRefNextLe (by omega)
      simp only [labelsBase, backSndBase, backFstBase]
      omega
  have hBackLtLab : ∀ k, k ≤ H.vertexCount →
      backFstBase H.vertexCount H.arcCount + k ≠ labelsBase H.vertexCount H.arcCount + y.val ∧
      backSndBase H.vertexCount H.arcCount + k ≠ labelsBase H.vertexCount H.arcCount + y.val := fun k hk => by
    simp only [labelsBase, backSndBase]; omega
  have hParNeLab : ∀ u, parentsBase H.vertexCount H.arcCount + u ≠
      labelsBase H.vertexCount H.arcCount + y.val := fun u => by
    have := y.isLt; simp only [parentsBase]; omega
  have hBaseLe : ∀ j, dictBase H.vertexCount H.arcCount ≤ j → orderBase H.vertexCount H.arcCount ≤ j := by
    intro j hj
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at hj ⊢; omega
  refine
    { idxLe := by omega
      sRefLabelsSize := by change rStep.labels.size = H.vertexCount; rw [hLabSz, inv.sRefLabelsSize]
      sRefNextLe := by
        rw [hNextEq]
        have := inv.sRefNextLe
        change sRef.tables.next ≤ idx + 1 at this
        omega
      labelsLt := fun v => by
        rw [hNextEq]
        change (rStep.labels[v.val]?).getD 0 < sRef.tables.next
        rw [hLabAt v.val]
        by_cases hv : v.val = y.val
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte, Option.getD_some]
          rw [← hNextEq]
          exact hOk.node_lt
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte]
          exact inv.labelsLt v
      backPos := fun k hk1 hk2 => by rw [hStEq]; exact inv.backPos k hk1 (by rw [← hNextEq]; exact hk2)
      grounded := by rw [hStEq]; exact inv.grounded
      stage1 := stage1_frame_data inv.stage1 (fun j ⟨h1, h2⟩ => hHighNe j h1 (hOrderLtLab j h2))
      slNVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slNVal
      slRootVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slRootVal
      slNextVal := by rw [hNextEq, hScrNe _ (by decide) (by decide)]; exact inv.slNextVal
      slDictBaseVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slDictBaseVal
      slDictCntVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slDictCntVal
      slDictSndVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slDictSndVal
      slDictSlotsVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slDictSlotsVal
      slJumpVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slJumpVal
      slBackFstVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slBackFstVal
      slBackSndVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slBackSndVal
      slLabelsVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slLabelsVal
      slParentsVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slParentsVal
      slOrderVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slOrderVal
      slRanksVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slRanksVal
      slRowStartVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slRowStartVal
      slRowEndVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slRowEndVal
      slPredBufVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slPredBufVal
      slSourceVal := by rw [hScrNe _ (by decide) (by decide)]; exact inv.slSourceVal
      slIdxVal := hIdx
      records := by
        refine ⟨inv.records.valid, ?_, ?_, ?_, ?_⟩
        · rw [t.data_size, ← s.data_size]; exact inv.records.fit
        · intro u hu
          rw [hHighNe _ (hBaseLe _ (by simp only [jumpBase]; omega)) (by have := hJumpLtLab u 0 hu (by omega); omega)]
          exact inv.records.parent u hu
        · intro u hu
          rw [hHighNe _ (hBaseLe _ (by simp only [jumpBase]; omega)) (by have := hJumpLtLab u 1 hu (by omega); omega)]
          exact inv.records.depth u hu
        · intro u hu
          rw [hHighNe _ (hBaseLe _ (by simp only [jumpBase]; omega)) (by have := hJumpLtLab u 2 hu (by omega); omega)]
          exact inv.records.jump u hu
      dictHeader := by
        rw [hHighNe _ (hBaseLe _ (Nat.le_refl _)) (hDictLtLab _ (by simp only [jumpBase, dictBase]; omega))]
        exact inv.dictHeader
      dictKeys := fun i hi' =>
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' (dict_size_le H dictRows large)
        have hds := dict_size_le H dictRows large
        ⟨by rw [hHighNe _ (hBaseLe _ (by omega)) (hDictLtLab _ (by simp only [jumpBase, dictBase]; omega))]
            exact (inv.dictKeys i hi').1,
         by rw [hHighNe _ (hBaseLe _ (by omega)) (hDictLtLab _ (by simp only [jumpBase, dictBase]; omega))]
            exact (inv.dictKeys i hi').2⟩
      dictSlots := fun i hi' => by
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' (dict_size_le H dictRows large)
        have hds := dict_size_le H dictRows large
        rw [hStEq, hHighNe _ (hBaseLe _ (by omega)) (hDictLtLab _ (by simp only [jumpBase, dictBase]; omega))]
        exact inv.dictSlots i hi'
      backMem := fun k hk => by
        rw [hStEq]
        exact
          ⟨by rw [hHighNe _ (hBaseLe _ (by simp only [backFstBase, jumpBase]; omega)) (hBackLtLab k hk).1]
              exact (inv.backMem k hk).1,
           by rw [hHighNe _ (hBaseLe _ (by simp only [backSndBase, backFstBase, jumpBase]; omega)) (hBackLtLab k hk).2]
              exact (inv.backMem k hk).2⟩
      labelsMem := fun v => by
        change (t.data[labelsBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
          some ((rStep.labels[v.val]?).getD 0)
        rw [hLabAt v.val]
        by_cases hv : v.val = y.val
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte, Option.getD_some]
          exact hLab
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte]
          rw [hHighNe _ (hBaseLe _ (by simp only [labelsBase, backSndBase, backFstBase, jumpBase]; omega))
            (by omega)]
          exact inv.labelsMem v
      parentsMem := fun u hu => by
        rw [hHighNe _ (hBaseLe _ (by simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase]; omega))
          (hParNeLab u)]
        exact inv.parentsMem u hu }

theorem SweepInv.advance_grow {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s t : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx s)
    (hidx : idx < H.vertexCount)
    (y : Vertex H)
    {rStep : HeadResult H}
    (hStep : stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep)
    (hAlloc : rStep.installed.allocated = true)
    {q : CutPair H} {slotIdx : Nat}
    (hq : rStep.measured.step.newPair = some q)
    (hhit : (PairLookup.lookup (orderedConfig dictRows large).dict
      ((orderedConfig dictRows large).code q)).1 = some slotIdx)
    (hSlotFit : slotIdx < (orderedConfig dictRows large).dict.size)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hNextVal : (t.data[slNext]?).map Fin.val = some (sRef.tables.next + 1))
    (hIdxVal : (t.data[slIdx]?).map Fin.val = some (idx + 1))
    (hJ0 : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0]?).map Fin.val =
      some rStep.measured.step.parent)
    (hJ1 : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1]?).map Fin.val =
      some (F.depthOf rStep.measured.step.parent + 1))
    (hJ2 : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2]?).map Fin.val =
      some (F.mkAppendedRecord rStep.measured.step.parent).jump)
    (hSlotW : (t.data[dictBase H.vertexCount H.arcCount + 1 +
      2 * (orderedConfig dictRows large).dict.size + slotIdx]?).map Fin.val = some sRef.tables.next)
    (hBFW : (t.data[backFstBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val =
      some (q.fst.val + 1))
    (hBSW : (t.data[backSndBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val =
      some q.snd.val)
    (hLabW : (t.data[labelsBase H.vertexCount H.arcCount + y.val]?).map Fin.val =
      some sRef.tables.next)
    (hParW : (t.data[parentsBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val =
      some rStep.measured.step.parent)
    (hPres : ∀ j, (19 ≤ j ∧ j < 30) ∨
      j = slNext ∨ j = slIdx ∨
      j = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0 ∨
      j = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1 ∨
      j = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2 ∨
      j = dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx ∨
      j = backFstBase H.vertexCount H.arcCount + sRef.tables.next ∨
      j = backSndBase H.vertexCount H.arcCount + sRef.tables.next ∨
      j = labelsBase H.vertexCount H.arcCount + y.val ∨
      j = parentsBase H.vertexCount H.arcCount + sRef.tables.next ∨
      t.data[j]? = s.data[j]?) :
    SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      (F.appendLeaf rStep.measured.step.parent) rStep.state (idx + 1) t := by
  let c := orderedConfig dictRows large
  let next := sRef.tables.next
  let p := rStep.measured.step.parent
  let F' := F.appendLeaf p
  have inj : ∀ a b : Vertex H, rank a = rank b → a = b := fun a b h => distinctRanks_of_stage1 inv.stage1 h
  obtain ⟨_, hInst, hLabSz, hLabAt⟩ := prepared_parts (row := ⟨y, dictRows.row y⟩) (dictRows.spec y) inj hStep
  have hOk := install_spec inv.grounded hInst
  have hG' : Grounded c F' rStep.state.tables := by
    dsimp only [c, F', p]
    have hg := hOk.grounded
    rw [ite_eq_left hAlloc] at hg
    exact hg
  have hDelta : rStep.installed.delta = 1 := by simp [Installed.delta, hAlloc]
  have hNextEq : rStep.state.tables.next = next + 1 := by
    change rStep.installed.tables.next = sRef.tables.next + 1
    rw [hOk.next_eq, hDelta]
  have hSizeEq : F.size = next := inv.grounded.size_eq
  have hFPos : 0 < F.size := by
    cases inv.records.valid <;> simp [JumpForest.init, JumpForest.size, JumpForest.appendLeaf]
  have hNextPos : 0 < next := by rw [← hSizeEq]; exact hFPos
  have hNextLeN : next ≤ H.vertexCount := by exact Nat.le_trans inv.sRefNextLe (by omega)
  have hpLt : p < F.size := by
    rw [hSizeEq]
    by_cases hp : rStep.measured.step.parent < sRef.tables.next
    · exact hp
    · simp [install, hp] at hInst
  have hDictLeN : (orderedConfig dictRows large).dict.size ≤ H.vertexCount := dict_size_le H dictRows large
  have hOrdLtD : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount := by
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
  have hDLtJ : dictBase H.vertexCount H.arcCount + 1 + 3 * H.vertexCount ≤
      jumpBase H.vertexCount H.arcCount := by simp only [jumpBase]; omega
  have hJLtBF : jumpBase H.vertexCount H.arcCount + 3 * (H.vertexCount + 1) ≤
      backFstBase H.vertexCount H.arcCount := by simp only [backFstBase]; omega
  have hBFLtBS : backFstBase H.vertexCount H.arcCount + (H.vertexCount + 1) ≤
      backSndBase H.vertexCount H.arcCount := by simp only [backSndBase]; omega
  have hBSLtLab : backSndBase H.vertexCount H.arcCount + (H.vertexCount + 1) ≤
      labelsBase H.vertexCount H.arcCount := by simp only [labelsBase]; omega
  have hLabLtPar : labelsBase H.vertexCount H.arcCount + H.vertexCount ≤
      parentsBase H.vertexCount H.arcCount := by simp only [parentsBase]; omega
  have hyLt : y.val < H.vertexCount := y.isLt
  have hPre : ∀ j, j ≠ slNext → j ≠ slIdx →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 0 →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 1 →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 2 →
      j ≠ dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx →
      j ≠ backFstBase H.vertexCount H.arcCount + next →
      j ≠ backSndBase H.vertexCount H.arcCount + next →
      j ≠ labelsBase H.vertexCount H.arcCount + y.val →
      j ≠ parentsBase H.vertexCount H.arcCount + next →
      (j < 19 ∨ 30 ≤ j) → t.data[j]? = s.data[j]? := by
    intro j a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hB
    rcases hPres j with h | h | h | h | h | h | h | h | h | h | h | h
    · omega
    · exact absurd h a1
    · exact absurd h a2
    · exact absurd h a3
    · exact absurd h a4
    · exact absurd h a5
    · exact absurd h a6
    · exact absurd h a7
    · exact absurd h a8
    · exact absurd h a9
    · exact absurd h a10
    · exact h
  have hScrNe : ∀ sl, sl < 19 → sl ≠ slNext → sl ≠ slIdx → t.data[sl]? = s.data[sl]? := by
    intro sl hsl h1 h2
    have hL : 19 ≤ dictBase H.vertexCount H.arcCount := by
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
        rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    have hJ : dictBase H.vertexCount H.arcCount ≤ jumpBase H.vertexCount H.arcCount := by
      simp only [jumpBase]; omega
    have hBF : jumpBase H.vertexCount H.arcCount ≤ backFstBase H.vertexCount H.arcCount := by
      simp only [backFstBase]; omega
    have hBS : backFstBase H.vertexCount H.arcCount ≤ backSndBase H.vertexCount H.arcCount := by
      simp only [backSndBase]; omega
    have hLab : backSndBase H.vertexCount H.arcCount ≤ labelsBase H.vertexCount H.arcCount := by
      simp only [labelsBase]; omega
    have hPar : labelsBase H.vertexCount H.arcCount ≤ parentsBase H.vertexCount H.arcCount := by
      simp only [parentsBase]; omega
    exact hPre sl h1 h2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl hsl)
  have hHighNe : ∀ j, orderBase H.vertexCount H.arcCount ≤ j →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 0 →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 1 →
      j ≠ jumpBase H.vertexCount H.arcCount + 3 * next + 2 →
      j ≠ dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx →
      j ≠ backFstBase H.vertexCount H.arcCount + next →
      j ≠ backSndBase H.vertexCount H.arcCount + next →
      j ≠ labelsBase H.vertexCount H.arcCount + y.val →
      j ≠ parentsBase H.vertexCount H.arcCount + next →
      t.data[j]? = s.data[j]? := by
    intro j hj b3 b4 b5 b6 b7 b8 b9 b10
    have h30 : 30 ≤ j := by
      have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by omega)
      omega
    exact hPre j (by unfold slNext; omega) (by unfold slIdx; omega) b3 b4 b5 b6 b7 b8 b9 b10 (Or.inr h30)
  have hOrderPres : ∀ j, orderBase H.vertexCount H.arcCount ≤ j →
      j < candFstABase H.vertexCount H.arcCount → t.data[j]? = s.data[j]? := by
    intro j hj1 hj2
    have hB : candFstABase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount := by
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase]; omega
    have hJ : dictBase H.vertexCount H.arcCount ≤ jumpBase H.vertexCount H.arcCount := by
      simp only [jumpBase]; omega
    have hBF : jumpBase H.vertexCount H.arcCount ≤ backFstBase H.vertexCount H.arcCount := by
      simp only [backFstBase]; omega
    have hBS : backFstBase H.vertexCount H.arcCount ≤ backSndBase H.vertexCount H.arcCount := by
      simp only [backSndBase]; omega
    have hLab : backSndBase H.vertexCount H.arcCount ≤ labelsBase H.vertexCount H.arcCount := by
      simp only [labelsBase]; omega
    have hPar : labelsBase H.vertexCount H.arcCount ≤ parentsBase H.vertexCount H.arcCount := by
      simp only [parentsBase]; omega
    exact hHighNe j hj1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hDictKeyPres : ∀ j, dictBase H.vertexCount H.arcCount ≤ j →
      j ≤ dictBase H.vertexCount H.arcCount + 2 * (orderedConfig dictRows large).dict.size → t.data[j]? = s.data[j]? := by
    intro j hj1 hj2
    have hOrd : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount := by
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
    have hJ : dictBase H.vertexCount H.arcCount + 1 + 3 * H.vertexCount = jumpBase H.vertexCount H.arcCount := by
      simp only [jumpBase]; omega
    have hBF : jumpBase H.vertexCount H.arcCount ≤ backFstBase H.vertexCount H.arcCount := by
      simp only [backFstBase]; omega
    have hBS : backFstBase H.vertexCount H.arcCount ≤ backSndBase H.vertexCount H.arcCount := by
      simp only [backSndBase]; omega
    have hLab : backSndBase H.vertexCount H.arcCount ≤ labelsBase H.vertexCount H.arcCount := by
      simp only [labelsBase]; omega
    have hPar : labelsBase H.vertexCount H.arcCount ≤ parentsBase H.vertexCount H.arcCount := by
      simp only [parentsBase]; omega
    exact hHighNe j (Nat.le_trans hOrd hj1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hSel := hOk.selection
  simp only [Selection, hq] at hSel
  obtain ⟨slotIdx', hhit', hSlotAt', hNodeNe0, hBackAt', hAllocIff⟩ := hSel
  have hSlotEq : slotIdx' = slotIdx := Option.some.inj (hhit'.symm.trans hhit)
  subst slotIdx'
  have hZero : sRef.tables.slotAt slotIdx = 0 := hAllocIff.mp hAlloc
  have hNodeEq : rStep.installed.node = next := by
    have hle : rStep.installed.node ≤ next := by
      have := hOk.node_lt; change rStep.installed.node < rStep.state.tables.next at this
      rw [hNextEq] at this; omega
    by_cases hlt : rStep.installed.node < next
    · have hbOld : sRef.tables.back[rStep.installed.node]? = some (some q) := by
        rw [← hOk.old_back _ hlt]; exact hBackAt'
      obtain ⟨_, _, j, hj, hjs⟩ := inv.grounded.backward _ _ hbOld
      have hej : j = slotIdx := Option.some.inj (hj.symm.trans hhit)
      subst j
      exact absurd (hjs.symm.trans hZero) hNodeNe0
    · omega
  have hBackRange : ∀ {F0 : JumpForest} (t0 : Tables H) (_ : Grounded c F0 t0),
      ∀ k ≤ H.vertexCount, t0.next ≤ k → t0.back[k]? = some none := by
    intro F0 t0 gt k hk hge
    have hkSz : k < t0.back.size := by
      rw [gt.back_size]
      change k < (PaperB.Jumps.ConcreteInit.region H.vertexCount).maxNodes + 1
      simp only [PaperB.Jumps.ConcreteInit.region]; omega
    have hw := getElem?_pos t0.back k hkSz
    cases hbk : t0.back[k] with
    | none => simpa [hbk] using hw
    | some q' =>
      have := (gt.backward k q' (by simpa [hbk] using hw)).1
      omega
  refine
    { idxLe := by omega
      sRefLabelsSize := by change rStep.labels.size = H.vertexCount; rw [hLabSz, inv.sRefLabelsSize]
      sRefNextLe := by
        rw [hNextEq]
        have := inv.sRefNextLe
        change sRef.tables.next ≤ idx + 1 at this
        omega
      labelsLt := fun v => by
        rw [hNextEq]
        change (rStep.labels[v.val]?).getD 0 < next + 1
        rw [hLabAt v.val]
        by_cases hv : v.val = y.val
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte, Option.getD_some, hNodeEq]
          omega
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte]
          exact Nat.lt_of_lt_of_le (inv.labelsLt v) (Nat.le_succ _)
      backPos := fun k hk1 hk2 => by
        rw [hNextEq] at hk2
        by_cases hkn : k = next
        · subst k
          exact ⟨q, by
            change rStep.installed.tables.back[next]? = some (some q)
            simpa [hNodeEq] using hBackAt'⟩
        · have hkLt : k < next := by omega
          have := hOk.old_back k hkLt
          change rStep.installed.tables.back[k]? = sRef.tables.back[k]? at this
          change ∃ q, rStep.installed.tables.back[k]? = some (some q)
          rw [this]
          exact inv.backPos k hk1 hkLt
      grounded := hG'
      stage1 := stage1_frame_data inv.stage1 (fun j ⟨h1, h2⟩ => hOrderPres j h1 h2)
      slNVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slNVal
      slRootVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slRootVal
      slNextVal := by rw [hNextEq]; exact hNextVal
      slDictBaseVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slDictBaseVal
      slDictCntVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slDictCntVal
      slDictSndVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slDictSndVal
      slDictSlotsVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slDictSlotsVal
      slJumpVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slJumpVal
      slBackFstVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slBackFstVal
      slBackSndVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slBackSndVal
      slLabelsVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slLabelsVal
      slParentsVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slParentsVal
      slOrderVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slOrderVal
      slRanksVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slRanksVal
      slRowStartVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slRowStartVal
      slRowEndVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slRowEndVal
      slPredBufVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slPredBufVal
      slSourceVal := by rw [hScrNe _ (by decide) (by decide) (by decide)]; exact inv.slSourceVal
      slIdxVal := hIdxVal
      records := by
        have hrecNew : (F.appendLeaf p).recordAt next = F.mkAppendedRecord p := by
          rw [← hSizeEq]; exact recordAt_appendLeaf_new F p
        refine ⟨ValidJumpForest.appendLeaf inv.records.valid hpLt, ?_, ?_, ?_, ?_⟩
        · rw [t.data_size, F.size_appendLeaf p, hSizeEq]
          have hC : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hWork
          simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase,
            candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase,
            indegBase, csrArenaWords] at hC ⊢
          omega
        · intro u hu
          rw [F.size_appendLeaf p, hSizeEq] at hu
          by_cases hun : u = next
          · subst u
            have hpNew : (F.appendLeaf p).parentOf next = p := by
              unfold JumpForest.parentOf; rw [hrecNew]; rfl
            rw [hpNew]
            exact hJ0
          · have huLt : u < F.size := by rw [hSizeEq]; omega
            have huNext : u < next := hSizeEq ▸ huLt
            rw [parentOf_appendLeaf_old F p huLt,
              hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact inv.records.parent u huLt
        · intro u hu
          rw [F.size_appendLeaf p, hSizeEq] at hu
          by_cases hun : u = next
          · subst u
            have hdNew : (F.appendLeaf p).depthOf next = F.depthOf p + 1 := by
              unfold JumpForest.depthOf; rw [hrecNew]; rfl
            rw [hdNew, show jumpBase H.vertexCount H.arcCount + 1 + 3 * next =
              jumpBase H.vertexCount H.arcCount + 3 * next + 1 by omega]
            exact hJ1
          · have huLt : u < F.size := by rw [hSizeEq]; omega
            have huNext : u < next := hSizeEq ▸ huLt
            rw [depthOf_appendLeaf_old F p huLt,
              hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact inv.records.depth u huLt
        · intro u hu
          rw [F.size_appendLeaf p, hSizeEq] at hu
          by_cases hun : u = next
          · subst u
            have hjNew : (F.appendLeaf p).jumpOf next = (F.mkAppendedRecord p).jump := by
              unfold JumpForest.jumpOf; rw [hrecNew]
            rw [hjNew, show jumpBase H.vertexCount H.arcCount + 2 + 3 * next =
              jumpBase H.vertexCount H.arcCount + 3 * next + 2 by omega]
            exact hJ2
          · have huLt : u < F.size := by rw [hSizeEq]; omega
            have huNext : u < next := hSizeEq ▸ huLt
            rw [jumpOf_appendLeaf_old F p huLt,
              hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact inv.records.jump u huLt
      dictHeader := by
        rw [hDictKeyPres _ (Nat.le_refl _) (by omega)]
        exact inv.dictHeader
      dictKeys := fun i hi' =>
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' hDictLeN
        ⟨by rw [hDictKeyPres _ (by omega) (by omega)]; exact (inv.dictKeys i hi').1,
         by rw [hDictKeyPres _ (by omega) (by omega)]; exact (inv.dictKeys i hi').2⟩
      dictSlots := fun i hi' => by
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' hDictLeN
        by_cases he : i = slotIdx
        · subst i
          change _ = some (rStep.installed.tables.slotAt slotIdx)
          have hSt : rStep.installed.tables.slotAt slotIdx = next := by
            rw [hSlotAt', hNodeEq]
          rw [hSt]
          exact hSlotW
        · have hOld : rStep.state.tables.slotAt i = sRef.tables.slotAt i := by
            by_cases hnz : sRef.tables.slotAt i = 0
            · by_cases hnz' : rStep.installed.tables.slotAt i = 0
              · change rStep.installed.tables.slotAt i = _; rw [hnz', hnz]
              · obtain ⟨q', hq', hbq'⟩ := hG'.forward i hnz'
                have hlt : rStep.installed.tables.slotAt i < rStep.state.tables.next :=
                  (hG'.backward _ q' hbq').1
                rw [hNextEq] at hlt
                by_cases hsn : rStep.installed.tables.slotAt i = next
                · have hqEq : q' = q := Option.some.inj (Option.some.inj (hbq'.symm.trans (by
                    change rStep.installed.tables.back[rStep.installed.tables.slotAt i]? = some (some q)
                    rw [hsn]; simpa [hNodeEq] using hBackAt')))
                  subst q'
                  exact absurd (Option.some.inj (hq'.symm.trans hhit)) he
                · have hlt' : rStep.installed.tables.slotAt i < next := by omega
                  have hbOld : sRef.tables.back[rStep.installed.tables.slotAt i]? = some (some q') := by
                    rw [← hOk.old_back _ hlt']; exact hbq'
                  obtain ⟨_, _, j, hj, hjs⟩ := inv.grounded.backward _ q' hbOld
                  have hji : j = i := Option.some.inj (hj.symm.trans hq')
                  subst j
                  exact absurd (hjs.symm.trans hnz) hnz'
            · exact hOk.old_slot i hnz
          rw [hOld, hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact inv.dictSlots i hi'
      backMem := fun k hk => by
        by_cases hkn : k = next
        · subst k
          have hBack : rStep.state.tables.back[next]? = some (some q) := by
            change rStep.installed.tables.back[next]? = some (some q)
            simpa [hNodeEq] using hBackAt'
          rw [hBack]
          exact ⟨hBFW, hBSW⟩
        · have hOldB : rStep.state.tables.back[k]? = sRef.tables.back[k]? := by
            by_cases hklt : k < next
            · exact hOk.old_back k hklt
            · have hge1 : next + 1 ≤ k := by omega
              rw [hBackRange rStep.state.tables hG' k hk (by rw [hNextEq]; exact hge1),
                  hBackRange sRef.tables inv.grounded k hk (by omega)]
          rw [hOldB]
          constructor
          · rw [hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact (inv.backMem k hk).1
          · rw [hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact (inv.backMem k hk).2
      labelsMem := fun v => by
        change (t.data[labelsBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
          some ((rStep.labels[v.val]?).getD 0)
        rw [hLabAt v.val]
        by_cases hv : v.val = y.val
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte, Option.getD_some, hNodeEq]
          exact hLabW
        · simp only [orderedConfig, Config.usePackedWords, hv, ↓reduceIte]
          have hvLt : v.val < H.vertexCount := v.isLt
          rw [hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact inv.labelsMem v
      parentsMem := fun u hu => by
        rw [JumpForest.size_appendLeaf, hSizeEq] at hu
        have hrecNew : (F.appendLeaf p).recordAt next = F.mkAppendedRecord p := by
          rw [← hSizeEq]; exact recordAt_appendLeaf_new F p
        by_cases hun : u = next
        · subst u
          have hpNew : (F.appendLeaf p).parentOf next = p := by
            unfold JumpForest.parentOf; rw [hrecNew]; rfl
          change Option.map Fin.val t.data[parentsBase H.vertexCount H.arcCount + next]? =
            some ((F.appendLeaf p).parentOf next)
          rw [hpNew]
          exact hParW
        · have huLt : u < F.size := by rw [hSizeEq]; omega
          have huNext : u < next := hSizeEq ▸ huLt
          change Option.map Fin.val t.data[parentsBase H.vertexCount H.arcCount + u]? =
            some ((F.appendLeaf p).parentOf u)
          rw [parentOf_appendLeaf_old F p huLt,
            hHighNe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact inv.parentsMem u huLt }

end SweepLoopMath

theorem placed_slice {bits : Nat} {L : Layout bits}
    {code : Program L} {entry : Nat} {a b : List (Instr bits L.registerCount)}
    (h : Placed code entry (a ++ b)) :
    Placed code entry a ∧ Placed code (entry + a.length) b :=
  ⟨placed_append_left h, placed_append_right h⟩

theorem step_loadData_reg {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {dst addrReg : Fin 15} {v : Nat}
    (hf : code[s.pc]? = some (.loadData dst addrReg))
    (hpc : s.pc + 1 < code.size)
    (haddr : (reg s addrReg).val < workCap)
    (hmem : (s.data[(reg s addrReg).val]?).map Fin.val = some v) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      step code input s = some (.next t) ∧
      t.pc = s.pc + 1 ∧
      (reg t dst).val = v ∧
      (∀ r, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  obtain ⟨w, hwMem, hwVal⟩ := word_mem_eq_of_map_val hmem
  obtain ⟨t, st, pc, rd, k, d⟩ := step_loadData_at' hf hpc haddr hwMem
  exact ⟨t, st, pc, by rw [rd, hwVal], k, d⟩

theorem step_storeData_val {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {addrReg src : Fin 15}
    (hf : code[s.pc]? = some (.storeData addrReg src))
    (hpc : s.pc + 1 < code.size)
    (haddr : (reg s addrReg).val < workCap) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      step code input s = some (.next t) ∧
      t.pc = s.pc + 1 ∧
      (t.data[(reg s addrReg).val]?).map Fin.val = some (reg s src).val ∧
      (∀ j, j ≠ (reg s addrReg).val → t.data[j]? = s.data[j]?) ∧
      (∀ r, reg t r = reg s r) := by
  obtain ⟨t, st, pc, dt, k⟩ := step_storeData_at hf hpc haddr
  have hset : (t.data[(reg s addrReg).val]?).map Fin.val = some (reg s src).val := by
    rw [dt, Array.getElem?_set_self (by rw [s.data_size]; exact haddr)]
    rfl
  have hfr : ∀ j, j ≠ (reg s addrReg).val → t.data[j]? = s.data[j]? := fun j hj => by
    rw [dt]; exact array_set_getElem?_ne _ _ _ _ _ hj
  exact ⟨t, st, pc, hset, hfr, k⟩

theorem placed_right_eq {bits : Nat} {L : Layout bits}
    {code : Program L} {entry entry' : Nat} {a b : List (Instr bits L.registerCount)}
    (h : Placed code entry (a ++ b)) (he : entry' = entry + a.length) :
    Placed code entry' b :=
  he ▸ placed_append_right h

theorem ite_true_branch {P : Prop} [hdec : Decidable P] {A B : Prop} (h : P) (ha : A) :
    if P then A else B :=
  match hdec with
  | isTrue _ => ha
  | isFalse hn => False.elim (hn h)

theorem ite_false_branch {P : Prop} [hdec : Decidable P] {A B : Prop} (h : ¬ P) (hb : B) :
    if P then A else B :=
  match hdec with
  | isTrue hp => False.elim (h hp)
  | isFalse _ => hb

theorem ite_elim_true {P : Prop} [hdec : Decidable P] {A B : Prop} (h : P)
    (hab : if P then A else B) : A :=
  match hdec, hab with
  | isTrue _, ha => ha
  | isFalse hn, _ => False.elim (hn h)

theorem ite_elim_false {P : Prop} [hdec : Decidable P] {A B : Prop} (h : ¬ P)
    (hab : if P then A else B) : B :=
  match hdec, hab with
  | isTrue hp, _ => False.elim (h hp)
  | isFalse _, hb => hb

theorem loadScratch_val_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry : Nat} (dst : Fin 15) (sl : Nat)
    (hsl : sl < workCap) (hSlFit : sl < 256)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = entry) (hpl : Placed code entry (loadScratch h8 dst sl))
    (hsz : entry + (loadScratch h8 dst sl).length < code.size)
    (hone : (reg s rOne).val = 1)
    {v : Nat} (hv : (s.data[sl]?).map Fin.val = some v) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (loadScratch h8 dst sl).length s t ∧
      t.pc = entry + (loadScratch h8 dst sl).length ∧
      (reg t dst).val = v ∧
      t.data = s.data ∧
      ∀ r, r ≠ dst → r ≠ rTmp → reg t r = reg s r := by
  have hl : (loadScratch h8 dst sl).length = (immNat h8 rTmp rOne sl).length + 1 := by
    simp [loadScratch]
  have hplI : Placed code entry (immNat h8 rTmp rOne sl) := placed_append_left hpl
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
    immNat_steps h8 (by decide) sl hSlFit (Nat.lt_of_lt_of_le hsl hw) hpc hplI (by rw [hl] at hsz; omega) hone
  have hf : code[s1.pc]? = some (.loadData dst rTmp) :=
    placed_fetch (op := .loadData dst rTmp) hpl (i := (immNat h8 rTmp rOne sl).length)
      (by simp [loadScratch]) pc1
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ :=
    step_loadData_reg hf (by rw [pc1, Nat.add_assoc, ← hl]; exact hsz)
      (by rw [r1]; exact hsl) (by rw [d1, r1]; exact hv)
  refine ⟨s2, ?_, ?_, r2, d2.trans d1, fun r hr1 hr2 => (k2 r hr1).trans (k1 r hr2)⟩
  · rw [hl]; exact st1.append (.cons st2 (.zero _))
  · rw [pc2, pc1, hl, Nat.add_assoc]

theorem storeScratch_val_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry : Nat} (sl : Nat) (src : Fin 15)
    (hSlFit : sl < 256) (hso : src ≠ rTmp)
    (hsl : sl < workCap)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = entry) (hpl : Placed code entry (sweepInitStoreScratch h8 sl src))
    (hsz : entry + (sweepInitStoreScratch h8 sl src).length < code.size)
    (hone : (reg s rOne).val = 1) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (sweepInitStoreScratch h8 sl src).length s t ∧
      t.pc = entry + (sweepInitStoreScratch h8 sl src).length ∧
      (t.data[sl]?).map Fin.val = some (reg s src).val ∧
      (∀ j, j ≠ sl → t.data[j]? = s.data[j]?) ∧
      ∀ r, r ≠ rTmp → reg t r = reg s r :=
  sweepInitStoreScratch_steps h8 sl src hso hSlFit hsl hpc hpl hsz hone


theorem sub_val_exact {bits : Nat} {x y : Word bits} (h : y.val ≤ x.val) :
    (WordOps.sub x y).val = x.val - y.val := by
  rw [WordOps.sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt)

theorem sweepInitStoreScratch_length_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (sl : Nat) (src : Fin 15) :
    (sweepInitStoreScratch h8 sl src).length ≤ 12 := by
  simp only [sweepInitStoreScratch, immNat, List.length_append, List.length_cons, List.length_nil]
  have := immNat_length_le h8 rTmp rOne 5 sl
  omega


theorem storeData_getElem?_ne {α : Type} {a : Array α} {p w : Nat} {v : α} {hp : p < a.size}
    (tData : Array α) (hd : tData = a.set p v hp) (hne : p ≠ w) : tData[w]? = a[w]? := by
  rw [hd, Array.getElem?_set_ne hp hne]


end PaperB.RamForestProgram.Sweep
