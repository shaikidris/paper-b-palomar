module

public import PaperB.RamProgram
public import PaperB.StaticHeavyLCA

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX53

open PaperB.Machine (Word)
open PaperB.RamProgram

set_option maxHeartbeats 2000000

abbrev layout (bits cap : Nat) (fit : cap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, cap, 0, fit, Nat.zero_le _⟩

abbrev R := Fin 16
abbrev Bank (bits : Nat) := R → Word bits

abbrev rx : R := ⟨0, by decide⟩
private abbrev ry : R := ⟨1, by decide⟩
private abbrev bh : R := ⟨2, by decide⟩
private abbrev bp : R := ⟨3, by decide⟩
private abbrev bd : R := ⟨4, by decide⟩
private abbrev ru : R := ⟨5, by decide⟩
private abbrev rv : R := ⟨6, by decide⟩
private abbrev ra : R := ⟨7, by decide⟩
private abbrev rb : R := ⟨8, by decide⟩
private abbrev rz : R := ⟨9, by decide⟩

variable {bits cap n : Nat} {fit : cap ≤ 2 ^ bits}

def program (fit : cap ≤ 2 ^ bits) : Program (layout bits cap fit) :=
  #[
    .add bh bh rz, .loadInput bh bh,       -- 0: header: head base
    .add bp bp rz, .loadInput bp bp,       -- 2: header: parent base
    .add bd bd rz, .loadInput bd bd,       -- 4: header: depth base
    .add ru bh rx, .loadInput ru ru,       -- 6: head[x]
    .add rv bh ry, .loadInput rv rv,       -- 8: head[y]
    .branchLt ru rv 11 12,                 -- 10
    .goto 13,                             -- 11: balance the two tests
    .branchLt rv ru 13 18,                 -- 12
    .add ra bd ru, .loadInput ra ra,       -- 13: depth[head[x]]
    .add rb bd rv, .loadInput rb rb,       -- 15: depth[head[y]]
    .branchLt ra rb 26 23,                 -- 17: ties jump left
    .add ra bd ry, .loadInput ra ra,       -- 18: depth[y]
    .add rb bd rx, .loadInput rb rb,       -- 20: depth[x]
    .branchLt ra rb 30 29,                 -- 22: ties return x
    .add rx bp ru, .loadInput rx rx,       -- 23: x := parent[head[x]]
    .goto 6,                              -- 25
    .add ry bp rv, .loadInput ry ry,       -- 26: y := parent[head[y]]
    .goto 6,                              -- 28
    .goto 31,                             -- 29: x is already the answer
    .mov rx ry,                           -- 30
    .halt                                -- 31
  ]

private theorem program_bound (fit : cap ≤ 2 ^ bits) {p : Nat} (h : p < 32) :
    p < (program fit).size := by
  change p < 32
  exact h
def vertexWord (fit : n ≤ 2 ^ bits) (v : Fin n) : Word bits :=
  ⟨v.val, Nat.lt_of_lt_of_le v.isLt fit⟩

/-- A contract on raw cells, not on the outcome of any RAM instruction.
    A successful raw lookup also witnesses the bound for its address. -/
structure Packed (input : Input (layout bits cap fit))
    (T : _root_.EX16.Tables (Fin n)) where
  idsFit : n ≤ 2 ^ bits
  headersFit : 3 ≤ cap
  depthFits : ∀ v, T.depth v < 2 ^ bits
  headBase : Word bits
  parentBase : Word bits
  depthBase : Word bits
  headHeader : input.words[0]? = some headBase
  parentHeader : input.words[1]? = some parentBase
  depthHeader : input.words[2]? = some depthBase
  headCell : ∀ v, input.words[headBase.val + v.val]? =
    some (vertexWord idsFit (T.head v))
  parentCell : ∀ v, input.words[parentBase.val + v.val]? =
    some (vertexWord idsFit (T.parent v))
  depthCell : ∀ v, input.words[depthBase.val + v.val]? =
    some (⟨T.depth v, depthFits v⟩ : Word bits)

variable {input : Input (layout bits cap fit)}
variable {T : _root_.EX16.Tables (Fin n)}

abbrev Packed.node (P : Packed input T) (v : Fin n) : Word bits :=
  vertexWord P.idsFit v

abbrev Packed.dep (P : Packed input T) (v : Fin n) : Word bits :=
  ⟨T.depth v, P.depthFits v⟩

def At (s : State (layout bits cap fit)) (pc : Nat) (f : Bank bits) : Prop :=
  s.pc = pc ∧ ∀ r : R, reg s r = f r

def Live (P : Packed input T) (f : Bank bits) (x y : Fin n) : Prop :=
  f rx = P.node x ∧ f ry = P.node y ∧
  f bh = P.headBase ∧ f bp = P.parentBase ∧ f bd = P.depthBase

private def put (f : Bank bits) (d : R) (w : Word bits) : Bank bits :=
  fun r => if r = d then w else f r

private def heads (f : Bank bits) (u v : Word bits) : Bank bits :=
  put (put f ru u) rv v

private def depths (f : Bank bits) (u v : Word bits) : Bank bits :=
  put (put f ra u) rb v

private theorem put_same (f : Bank bits) (d : R) (w : Word bits) :
    put f d w d = w :=
  ite_eq_left (show d = d from rfl)

private theorem put_other {r d : R} (f : Bank bits) (w : Word bits) (h : r ≠ d) :
    put f d w r = f r :=
  ite_eq_right h

private theorem pairAt {pc : Nat} {d b i : R}
    (h₀ : (program fit)[pc]? = some (.add d b i))
    (h₁ : (program fit)[pc + 1]? = some (.loadInput d d)) :
    Placed (program fit) pc (indexedInputRead d b i) := by
  intro j op hj
  cases j with
  | zero =>
    have e : Instr.add d b i = op := by
      simpa [indexedInputRead] using hj
    subst op
    exact h₀
  | succ j =>
    cases j with
    | zero =>
      have e : Instr.loadInput d d = op := by
        simpa [indexedInputRead] using hj
      subst op
      exact h₁
    | succ j =>
      simp [indexedInputRead] at hj

private theorem readAt {s : State (layout bits cap fit)} {pc : Nat}
    {f : Bank bits} {d b i : R} {w : Word bits}
    (placed : Placed (program fit) pc (indexedInputRead d b i))
    (hs : At s pc f) (exit : pc + 2 < (program fit).size)
    (cell : input.words[(f b).val + (f i).val]? = some w) :
    ∃ t, Steps (program fit) input 2 s t ∧ At t (pc + 2) (put f d w) := by
  have bound : (reg s b).val + (reg s i).val < cap := by
    rw [hs.2 b, hs.2 i]
    by_cases h : (f b).val + (f i).val < cap
    · exact h
    · have hn : ¬ (f b).val + (f i).val < input.words.size := by
        simpa only [input.size_eq] using h
      simp [getElem?_def, hn] at cell
  obtain ⟨t, ht, hpc, hval, keep, _⟩ :=
    indexedInputRead_steps (input := input) placed hs.1 exit bound
  rw [hs.2 b, hs.2 i, cell] at hval
  refine ⟨t, ht, hpc, ?_⟩
  intro r
  by_cases e : r = d
  · subst r
    rw [put_same]
    exact Option.some.inj hval
  · rw [put_other _ _ e, keep r e, hs.2 r]

private theorem gotoAt {s : State (layout bits cap fit)} {pc target : Nat}
    {f : Bank bits}
    (fetch : (program fit)[pc]? = some (.goto target))
    (hs : At s pc f) (ok : target < (program fit).size) :
    ∃ t, Steps (program fit) input 1 s t ∧ At t target f := by
  have hf : (program fit)[s.pc]? = some (.goto target) := by
    rw [hs.1]
    exact fetch
  have h := step_goto_at (input := input) (s := s) hf ok
  refine ⟨{ s with pc := target }, Steps.cons h (Steps.zero _), rfl, ?_⟩
  intro r
  change reg s r = f r
  exact hs.2 r

private theorem branchAt {s : State (layout bits cap fit)} {pc yes no target : Nat}
    {f : Bank bits} {a b : R}
    (fetch : (program fit)[pc]? = some (.branchLt a b yes no))
    (hs : At s pc f)
    (choose : (if PaperB.WordOps.ltb (f a) (f b) then yes else no) = target)
    (ok : target < (program fit).size) :
    ∃ t, Steps (program fit) input 1 s t ∧ At t target f := by
  have hf : (program fit)[s.pc]? = some (.branchLt a b yes no) := by
    rw [hs.1]
    exact fetch
  have hc :
      (if PaperB.WordOps.ltb (reg s a) (reg s b) then yes else no) = target := by
    rw [hs.2 a, hs.2 b]
    exact choose
  have h := step_branchLt_at (input := input) (s := s) hf (by rw [hc]; exact ok)
  rw [hc] at h
  refine ⟨{ s with pc := target }, Steps.cons h (Steps.zero _), rfl, ?_⟩
  intro r
  change reg s r = f r
  exact hs.2 r

/-- The only non-indexed register write in the worker. The explicit state
    below is definitionally the state built by `step` for `.mov`. -/
private theorem moveAt {s : State (layout bits cap fit)} {pc : Nat}
    {f : Bank bits} {d a : R}
    (fetch : (program fit)[pc]? = some (.mov d a))
    (hs : At s pc f) (ok : pc + 1 < (program fit).size) :
    ∃ t, Steps (program fit) input 1 s t ∧ At t (pc + 1) (put f d (f a)) := by
  have hf : (program fit)[s.pc]? = some (.mov d a) := by
    rw [hs.1]
    exact fetch
  have hd : d.val < s.regs.size := by
    rw [s.regs_size]
    exact d.isLt
  let t : State (layout bits cap fit) :=
    { s with
      regs := s.regs.set d.val (reg s a) hd
      pc := s.pc + 1
      regs_size := by simp only [Array.size_set, s.regs_size] }
  have hn : s.pc + 1 < (program fit).size := by
    rw [hs.1]
    exact ok
  have h : step (program fit) input s = some (PaperB.RamProgram.Transition.next t) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < (program fit).size then
      some (PaperB.RamProgram.Transition.next t) else none) =
        some (PaperB.RamProgram.Transition.next t)
    exact ite_eq_left hn
  refine ⟨t, Steps.cons h (Steps.zero t), ?_, ?_⟩
  · change s.pc + 1 = pc + 1
    rw [hs.1]
  · intro r
    have hr : r.val < s.regs.size := by
      rw [s.regs_size]
      exact r.isLt
    have old : s.regs[r.val]'hr = f r := by
      change reg s r = f r
      exact hs.2 r
    change (s.regs.set d.val (reg s a) hd)[r.val]'(by
      simpa only [Array.size_set] using hr) = put f d (f a) r
    by_cases e : r = d
    · subst r
      rw [put_same, Array.getElem_set]
      split
      · exact hs.2 a
      · rename_i hne
        exact (hne rfl).elim
    · have ev : r.val ≠ d.val := fun hval => e (Fin.ext hval)
      rw [put_other _ _ e, Array.getElem_set]
      split
      · rename_i he
        first | exact (ev he).elim | exact (ev he.symm).elim
      · exact old

private def headerWord (P : Packed input T) (i : Fin 3) : Word bits :=
  ⟨i.val, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le i.isLt P.headersFit) fit⟩

private def entryBank (P : Packed input T) (x y : Fin n) : Bank bits :=
  put (put (put (put (fun _ => headerWord P ⟨0, by decide⟩)
    rx (P.node x)) ry (P.node y))
    bp (headerWord P ⟨1, by decide⟩)) bd (headerWord P ⟨2, by decide⟩)

def initial (P : Packed input T) (x y : Fin n) : State (layout bits cap fit) where
  regs := Array.ofFn (entryBank P x y)
  data := #[]
  pc := 0
  regs_size := by simp
  data_size := rfl

private theorem boot (P : Packed input T) (x y : Fin n) :
    ∃ t f, Steps (program fit) input 6 (initial P x y) t ∧
      At t 6 f ∧ Live P f x y := by
  let f := entryBank P x y
  let g := put f bh P.headBase
  let j := put g bp P.parentBase
  have h₀ : At (initial P x y) 0 f := by
    refine ⟨rfl, ?_⟩
    intro r
    change (Array.ofFn f)[r.val]'(by simpa using r.isLt) = f r
    simp
  have e₀ : (f bh).val + (f rz).val = 0 := rfl
  have e₁ : (g bp).val + (g rz).val = 1 := rfl
  have e₂ : (j bd).val + (j rz).val = 2 := rfl
  obtain ⟨u, hsu, hu⟩ := readAt (pc := 0) (d := bh) (b := bh) (i := rz)
    (pairAt rfl rfl) h₀ (program_bound fit (by decide)) (by rw [e₀]; exact P.headHeader)
  have hu' : At u 2 g := hu
  obtain ⟨v, huv, hv⟩ := readAt (pc := 2) (d := bp) (b := bp) (i := rz)
    (pairAt rfl rfl) hu' (program_bound fit (by decide)) (by rw [e₁]; exact P.parentHeader)
  have hv' : At v 4 j := hv
  obtain ⟨t, hvt, ht⟩ := readAt (pc := 4) (d := bd) (b := bd) (i := rz)
    (pairAt rfl rfl) hv' (program_bound fit (by decide)) (by rw [e₂]; exact P.depthHeader)
  refine ⟨t, _, (hsu.append huv).append hvt, ht, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem headBlock (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    (hs : At s 6 f) (live : Live P f x y) :
    ∃ t, Steps (program fit) input 6 s t ∧
      At t (if T.head x = T.head y then 18 else 13)
        (heads f (P.node (T.head x)) (P.node (T.head y))) := by
  rcases live with ⟨fx, fy, fh, _, _⟩
  obtain ⟨u, hsu, hu⟩ := readAt (pc := 6) (d := ru) (b := bh) (i := rx)
    (pairAt rfl rfl) hs (program_bound fit (by decide)) (w := P.node (T.head x)) (by
      rw [fh, fx]
      exact P.headCell x)
  obtain ⟨v, huv, hv⟩ := readAt (pc := 8) (d := rv) (b := bh) (i := ry)
    (pairAt rfl rfl) hu (program_bound fit (by decide)) (w := P.node (T.head y)) (by
      rw [put_other _ _ (show bh ≠ ru by decide),
        put_other _ _ (show ry ≠ ru by decide), fh, fy]
      exact P.headCell y)
  let g := heads f (P.node (T.head x)) (P.node (T.head y))
  have hv' : At v 10 g := hv
  have gu : g ru = P.node (T.head x) := rfl
  have gv : g rv = P.node (T.head y) := rfl
  by_cases xy : (T.head x).val < (T.head y).val
  · have ne : T.head x ≠ T.head y := by
      intro e
      rw [e] at xy
      omega
    rw [ite_eq_right ne]
    obtain ⟨w, hvw, hw⟩ := branchAt (input := input) (a := ru) (b := rv)
      (yes := 11) (no := 12) (target := 11) rfl hv' (by
        simp [gu, gv, PaperB.WordOps.ltb, vertexWord, xy]) (program_bound fit (by decide))
    obtain ⟨t, hwt, ht⟩ := gotoAt (input := input) (target := 13)
      rfl hw (program_bound fit (by decide))
    exact ⟨t, ((hsu.append huv).append hvw).append hwt, ht⟩
  · obtain ⟨w, hvw, hw⟩ := branchAt (input := input) (a := ru) (b := rv)
      (yes := 11) (no := 12) (target := 12) rfl hv' (by
        simp [gu, gv, PaperB.WordOps.ltb, vertexWord, xy]) (program_bound fit (by decide))
    by_cases yx : (T.head y).val < (T.head x).val
    · have ne : T.head x ≠ T.head y := by
        intro e
        rw [e] at yx
        omega
      rw [ite_eq_right ne]
      obtain ⟨t, hwt, ht⟩ := branchAt (input := input) (a := rv) (b := ru)
        (yes := 13) (no := 18) (target := 13) rfl hw (by
          simp [gu, gv, PaperB.WordOps.ltb, vertexWord, yx]) (program_bound fit (by decide))
      exact ⟨t, ((hsu.append huv).append hvw).append hwt, ht⟩
    · have eq : T.head x = T.head y := Fin.ext (by omega)
      rw [ite_eq_left eq]
      obtain ⟨t, hwt, ht⟩ := branchAt (input := input) (a := rv) (b := ru)
        (yes := 13) (no := 18) (target := 18) rfl hw (by
          simp [gu, gv, PaperB.WordOps.ltb, vertexWord, yx]) (program_bound fit (by decide))
      exact ⟨t, ((hsu.append huv).append hvw).append hwt, ht⟩

private theorem depthBlock (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {pc yes no target : Nat}
    {i j : R} {x y : Fin n}
    (hs : At s pc f) (base : f bd = P.depthBase)
    (ix : f i = P.node x) (jy : f j = P.node y) (j_ne : j ≠ ra)
    (p₀ : Placed (program fit) pc (indexedInputRead ra bd i))
    (p₁ : Placed (program fit) (pc + 2) (indexedInputRead rb bd j))
    (fetch : (program fit)[pc + 2 + 2]? = some (.branchLt ra rb yes no))
    (ok₀ : pc + 2 < (program fit).size)
    (ok₁ : pc + 2 + 2 < (program fit).size)
    (ok₂ : target < (program fit).size)
    (choose : (if T.depth x < T.depth y then yes else no) = target) :
    ∃ t, Steps (program fit) input 5 s t ∧
      At t target (depths f (P.dep x) (P.dep y)) := by
  obtain ⟨u, hsu, hu⟩ := readAt p₀ hs ok₀ (w := P.dep x) (by
    rw [base, ix]
    exact P.depthCell x)
  obtain ⟨v, huv, hv⟩ := readAt p₁ hu ok₁ (w := P.dep y) (by
    rw [put_other _ _ (show bd ≠ ra by decide), put_other _ _ j_ne, base, jy]
    exact P.depthCell y)
  have hv' : At v (pc + 2 + 2) (depths f (P.dep x) (P.dep y)) := hv
  have va : depths f (P.dep x) (P.dep y) ra = P.dep x := rfl
  have vb : depths f (P.dep x) (P.dep y) rb = P.dep y := rfl
  obtain ⟨t, hvt, ht⟩ := branchAt (input := input) fetch hv' (by
    rw [va, vb]
    simpa [PaperB.WordOps.ltb, Packed.dep] using choose) ok₂
  exact ⟨t, (hsu.append huv).append hvt, ht⟩

private abbrev afterHeads (P : Packed input T) (f : Bank bits) (x y : Fin n) :=
  heads f (P.node (T.head x)) (P.node (T.head y))

private abbrev jumpBank (P : Packed input T) (f : Bank bits) (x y : Fin n) :=
  depths (afterHeads P f x y) (P.dep (T.head x)) (P.dep (T.head y))

private abbrev stopBank (P : Packed input T) (f : Bank bits) (x y : Fin n) :=
  depths (afterHeads P f x y) (P.dep y) (P.dep x)

private theorem unequalPrefix (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    {target : Nat} (hs : At s 6 f) (live : Live P f x y)
    (ne : T.head x ≠ T.head y) (ok : target < (program fit).size)
    (choose : (if T.depth (T.head x) < T.depth (T.head y) then 26 else 23) =
      target) :
    ∃ t, Steps (program fit) input 11 s t ∧ At t target (jumpBank P f x y) := by
  obtain ⟨u, hsu, hu⟩ := headBlock P hs live
  have hu' : At u 13 (afterHeads P f x y) := by
    simpa only [ite_eq_right ne] using hu
  have base : afterHeads P f x y bd = P.depthBase := live.2.2.2.2
  have ix : afterHeads P f x y ru = P.node (T.head x) := rfl
  have jy : afterHeads P f x y rv = P.node (T.head y) := rfl
  obtain ⟨t, hut, ht⟩ := depthBlock P (yes := 26) (no := 23)
    (i := ru) (j := rv) hu' base ix jy (by decide)
    (pairAt rfl rfl) (pairAt rfl rfl) rfl
    (program_bound fit (by decide)) (program_bound fit (by decide)) ok choose
  exact ⟨t, hsu.append hut, ht⟩

private theorem equalPrefix (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    {target : Nat} (hs : At s 6 f) (live : Live P f x y)
    (eq : T.head x = T.head y) (ok : target < (program fit).size)
    (choose : (if T.depth y < T.depth x then 30 else 29) = target) :
    ∃ t, Steps (program fit) input 11 s t ∧ At t target (stopBank P f x y) := by
  obtain ⟨u, hsu, hu⟩ := headBlock P hs live
  have hu' : At u 18 (afterHeads P f x y) := by
    simpa only [ite_eq_left eq] using hu
  rcases live with ⟨fx, fy, _, _, fd⟩
  have base : afterHeads P f x y bd = P.depthBase := fd
  have iy : afterHeads P f x y ry = P.node y := fy
  have jx : afterHeads P f x y rx = P.node x := fx
  obtain ⟨t, hut, ht⟩ := depthBlock P (yes := 30) (no := 29)
    (i := ry) (j := rx) hu' base iy jx (by decide)
    (pairAt rfl rfl) (pairAt rfl rfl) rfl
    (program_bound fit (by decide)) (program_bound fit (by decide)) ok choose
  exact ⟨t, hsu.append hut, ht⟩

/-- The premises and updated endpoint are those of `Execution.jumpLeft`. -/
theorem jumpLeftSteps (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    (ne : T.head x ≠ T.head y) (le : T.depth (T.head y) ≤ T.depth (T.head x))
    (hs : At s 6 f) (live : Live P f x y) :
    ∃ t g, Steps (program fit) input 14 s t ∧ At t 6 g ∧
      Live P g (T.parent (T.head x)) y := by
  obtain ⟨u, hsu, hu⟩ := unequalPrefix P (target := 23) hs live ne
    (program_bound fit (by decide)) (ite_eq_right (Nat.not_lt.mpr le))
  rcases live with ⟨_, fy, fh, fp, fd⟩
  have base : jumpBank P f x y bp = P.parentBase := fp
  have idx : jumpBank P f x y ru = P.node (T.head x) := rfl
  obtain ⟨v, huv, hv⟩ := readAt (pc := 23) (d := rx) (b := bp) (i := ru)
    (pairAt rfl rfl) hu (program_bound fit (by decide)) (w := P.node (T.parent (T.head x))) (by
      rw [base, idx]
      exact P.parentCell (T.head x))
  obtain ⟨t, hvt, ht⟩ := gotoAt (input := input) (target := 6)
    rfl hv (program_bound fit (by decide))
  refine ⟨t, _, (hsu.append huv).append hvt, ht, ?_⟩
  exact ⟨rfl, fy, fh, fp, fd⟩

/-- The premises and updated endpoint are those of `Execution.jumpRight`. -/
theorem jumpRightSteps (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    (ne : T.head x ≠ T.head y) (lt : T.depth (T.head x) < T.depth (T.head y))
    (hs : At s 6 f) (live : Live P f x y) :
    ∃ t g, Steps (program fit) input 14 s t ∧ At t 6 g ∧
      Live P g x (T.parent (T.head y)) := by
  obtain ⟨u, hsu, hu⟩ := unequalPrefix P (target := 26) hs live ne
    (program_bound fit (by decide)) (ite_eq_left lt)
  rcases live with ⟨fx, _, fh, fp, fd⟩
  have base : jumpBank P f x y bp = P.parentBase := fp
  have idx : jumpBank P f x y rv = P.node (T.head y) := rfl
  obtain ⟨v, huv, hv⟩ := readAt (pc := 26) (d := ry) (b := bp) (i := rv)
    (pairAt rfl rfl) hu (program_bound fit (by decide)) (w := P.node (T.parent (T.head y))) (by
      rw [base, idx]
      exact P.parentCell (T.head y))
  obtain ⟨t, hvt, ht⟩ := gotoAt (input := input) (target := 6)
    rfl hv (program_bound fit (by decide))
  refine ⟨t, _, (hsu.append huv).append hvt, ht, ?_⟩
  exact ⟨fx, rfl, fh, fp, fd⟩

private theorem haltAt31 {s : State (layout bits cap fit)} {f : Bank bits}
    (hs : At s 31 f) : step (program fit) input s = some (.halted s) := by
  apply step_halt_at
  rw [hs.1] <;> rfl

theorem stopLeftSteps (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    (eq : T.head x = T.head y) (le : T.depth x ≤ T.depth y)
    (hs : At s 6 f) (live : Live P f x y) :
    ∃ t, Steps (program fit) input 12 s t ∧
      step (program fit) input t = some (.halted t) ∧ reg t rx = P.node x := by
  obtain ⟨u, hsu, hu⟩ := equalPrefix P (target := 29) hs live eq
    (program_bound fit (by decide)) (ite_eq_right (Nat.not_lt.mpr le))
  obtain ⟨t, hut, ht⟩ := gotoAt (input := input) (target := 31)
    rfl hu (program_bound fit (by decide))
  refine ⟨t, hsu.append hut, haltAt31 ht, ?_⟩
  rw [ht.2 rx]
  exact live.1

theorem stopRightSteps (P : Packed input T)
    {s : State (layout bits cap fit)} {f : Bank bits} {x y : Fin n}
    (eq : T.head x = T.head y) (lt : T.depth y < T.depth x)
    (hs : At s 6 f) (live : Live P f x y) :
    ∃ t, Steps (program fit) input 12 s t ∧
      step (program fit) input t = some (.halted t) ∧ reg t rx = P.node y := by
  obtain ⟨u, hsu, hu⟩ := equalPrefix P (target := 30) hs live eq
    (program_bound fit (by decide)) (ite_eq_left lt)
  obtain ⟨t, hut, ht⟩ := moveAt (input := input) (d := rx) (a := ry)
    rfl hu (program_bound fit (by decide))
  refine ⟨t, hsu.append hut, haltAt31 ht, ?_⟩
  rw [ht.2 rx]
  exact live.2.1

private theorem prependJump {s u t : State (layout bits cap fit)} {k : Nat}
    (first : Steps (program fit) input 14 s u)
    (rest : Steps (program fit) input (14 * k + 12) u t) :
    Steps (program fit) input (14 * (k + 1) + 12) s t := by
  have e : 14 + (14 * k + 12) = 14 * (k + 1) + 12 := by omega
  rw [← e]
  exact first.append rest

private theorem simulate (P : Packed input T) {x y a : Fin n} {k : Nat}
    (trace : _root_.EX16.Execution T x y a k) :
    ∀ (s : State (layout bits cap fit)) (f : Bank bits),
      At s 6 f → Live P f x y →
      ∃ t, Steps (program fit) input (14 * k + 12) s t ∧
        step (program fit) input t = some (.halted t) ∧ reg t rx = P.node a := by
  induction trace with
  | stopLeft eq le =>
    intro s f hs live
    exact stopLeftSteps P eq le hs live
  | stopRight eq lt =>
    intro s f hs live
    exact stopRightSteps P eq lt hs live
  | jumpLeft ne le _ ih =>
    intro s f hs live
    obtain ⟨u, g, hsu, hu, lu⟩ := jumpLeftSteps P ne le hs live
    obtain ⟨t, hut, halt, ans⟩ := ih u g hu lu
    exact ⟨t, prependJump hsu hut, halt, ans⟩
  | jumpRight ne lt _ ih =>
    intro s f hs live
    obtain ⟨u, g, hsu, hu, lu⟩ := jumpRightSteps P ne lt hs live
    obtain ⟨t, hut, halt, ans⟩ := ih u g hu lu
    exact ⟨t, prependJump hsu hut, halt, ans⟩

/-- Exact instruction count, including boot and the halt instruction.
    In particular, the public `EX16.lca` result's `trace` can be used here
    without unfolding its runner or accessing any private definition. -/
theorem runWorker (P : Packed input T) {x y a : Fin n} {k : Nat}
    (trace : _root_.EX16.Execution T x y a k) :
    ∃ r, run (program fit) input (14 * k + 19) (initial P x y) = some r ∧
      r.executed = 14 * k + 19 ∧ reg r.finalState rx = P.node a := by
  obtain ⟨u, f, hboot, hu, live⟩ := boot P x y
  obtain ⟨t, hworker, halt, ans⟩ := simulate P trace u f hu live
  have h := (hboot.append hworker).halts halt
  have e : 6 + (14 * k + 12) + 1 = 14 * k + 19 := by omega
  rw [e] at h
  exact ⟨⟨t, 14 * k + 19⟩, h, rfl, ans⟩

end PaperB.EX53
