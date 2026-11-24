module

public import PaperB.CommonAncestorSearch
public import PaperB.Jumps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.JumpForestCommonAncestor

def sharedDepth (F : JumpForest) (u v : Nat) : Nat :=
  min (F.depthOf u) (F.depthOf v)

private theorem shared_left (F : JumpForest) (u v : Nat) :
    sharedDepth F u v ≤ F.depthOf u :=
  Nat.min_le_left _ _

private theorem shared_right (F : JumpForest) (u v : Nat) :
    sharedDepth F u v ≤ F.depthOf v :=
  Nat.min_le_right _ _

private theorem le_shared {F : JumpForest} {u v d : Nat}
    (hu : d ≤ F.depthOf u) (hv : d ≤ F.depthOf v) :
    d ≤ sharedDepth F u v := by
  by_cases h : F.depthOf u ≤ F.depthOf v
  · simpa only [sharedDepth, Nat.min_eq_left h] using hu
  · have h' : F.depthOf v ≤ F.depthOf u := by omega
    simpa only [sharedDepth, Nat.min_eq_right h'] using hv

theorem root_agreement {F : JumpForest} (hF : ValidJumpForest F)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size) :
    F.ancestorAtDepth u 0 = F.ancestorAtDepth v 0 := by
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  obtain ⟨hU, _, hUd⟩ := hF.ancestorAtDepth_spec hu (Nat.zero_le _)
  obtain ⟨hV, _, hVd⟩ := hF.ancestorAtDepth_spec hv (Nat.zero_le _)
  exact ((inv.depth_eq_zero_iff hU).mp hUd).trans
    ((inv.depth_eq_zero_iff hV).mp hVd).symm

/-- Go to depth `a` from the shared ancestor at depth `b`, then use
ancestor uniqueness on each of the two original paths. -/
theorem agreement_downward {F : JumpForest} (hF : ValidJumpForest F)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ sharedDepth F u v)
    (heq : F.ancestorAtDepth u b = F.ancestorAtDepth v b) :
    F.ancestorAtDepth u a = F.ancestorAtDepth v a := by
  have hbu := Nat.le_trans hb (shared_left F u v)
  have hbv := Nat.le_trans hb (shared_right F u v)
  obtain ⟨hw, hwu, hwd⟩ := hF.ancestorAtDepth_spec hu hbu
  have hwv : IsAncestor F (F.ancestorAtDepth u b) v := by
    rw [heq]
    exact (hF.ancestorAtDepth_spec hv hbv).2.1
  have haw : a ≤ F.depthOf (F.ancestorAtDepth u b) := by
    rw [hwd]
    exact hab
  obtain ⟨_, hzw, hzd⟩ := hF.ancestorAtDepth_spec hw haw
  have hzu := (hF.ancestorAtDepth_unique hu (Nat.le_trans hab hbu)).mp
    ⟨IsAncestor.trans hzw hwu, hzd⟩
  have hzv := (hF.ancestorAtDepth_unique hv (Nat.le_trans hab hbv)).mp
    ⟨IsAncestor.trans hzw hwv, hzd⟩
  exact hzu.symm.trans hzv

def cut (F : JumpForest) (u v : Nat) : Nat :=
  (CommonAncestorSearch.run (sharedDepth F u v)
    (F.ancestorAtDepth u) (F.ancestorAtDepth v)).1

/-- Result vertex and checked search probe count. -/
def query (F : JumpForest) (u v : Nat) : Nat × Nat :=
  CommonAncestorSearch.lca (sharedDepth F u v)
    (F.ancestorAtDepth u) (F.ancestorAtDepth v)

theorem cut_spec {F : JumpForest} (hF : ValidJumpForest F)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size) :
    cut F u v ≤ sharedDepth F u v ∧
      F.ancestorAtDepth u (cut F u v) = F.ancestorAtDepth v (cut F u v) ∧
      ∀ d : Nat, d ≤ sharedDepth F u v →
        (F.ancestorAtDepth u d = F.ancestorAtDepth v d ↔ d ≤ cut F u v) :=
  CommonAncestorSearch.run_spec (sharedDepth F u v)
    (F.ancestorAtDepth u) (F.ancestorAtDepth v)
    (root_agreement hF hu hv) (agreement_downward hF hu hv)

theorem query_vertex (F : JumpForest) (u v : Nat) :
    (query F u v).1 = F.ancestorAtDepth u (cut F u v) :=
  rfl

theorem query_depth {F : JumpForest} (hF : ValidJumpForest F)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size) :
    F.depthOf (query F u v).1 = cut F u v := by
  rw [query_vertex]
  exact (hF.ancestorAtDepth_spec hu
    (Nat.le_trans (cut_spec hF hu hv).1 (shared_left F u v))).2.2

private theorem ancestor_depth_le {F : JumpForest} (hF : ValidJumpForest F)
    {a x : Nat} (hx : x < F.size) (ha : IsAncestor F a x) :
    F.depthOf a ≤ F.depthOf x := by
  obtain ⟨k, hk⟩ := ha
  rw [← hk, hF.depth_iterParent hx k]
  exact Nat.sub_le _ _

/-- The result is a common ancestor, and its inclusive ancestors are
exactly the common ancestors of the inputs. In particular, this is
greatest under ancestry, not merely maximal by depth. -/
theorem query_exact {F : JumpForest} (hF : ValidJumpForest F)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size) :
    (query F u v).1 < F.size ∧
      IsAncestor F (query F u v).1 u ∧
      IsAncestor F (query F u v).1 v ∧
      ∀ a : Nat, (IsAncestor F a u ∧ IsAncestor F a v) ↔
        IsAncestor F a (query F u v).1 := by
  obtain ⟨hc, heq, hclass⟩ := cut_spec hF hu hv
  obtain ⟨hw, hwu, hwd⟩ :=
    hF.ancestorAtDepth_spec hu (Nat.le_trans hc (shared_left F u v))
  have hwv : IsAncestor F (F.ancestorAtDepth u (cut F u v)) v := by
    rw [heq]
    exact (hF.ancestorAtDepth_spec hv (Nat.le_trans hc (shared_right F u v))).2.1
  rw [query_vertex]
  refine ⟨hw, hwu, hwv, ?_⟩
  intro a
  constructor
  · rintro ⟨hau, hav⟩
    have hdu := ancestor_depth_le hF hu hau
    have hdv := ancestor_depth_le hF hv hav
    have hAu := (hF.ancestorAtDepth_unique hu hdu).mp ⟨hau, rfl⟩
    have hAv := (hF.ancestorAtDepth_unique hv hdv).mp ⟨hav, rfl⟩
    have hdc := (hclass (F.depthOf a) (le_shared hdu hdv)).mp
      (hAu.symm.trans hAv)
    have hdw : F.depthOf a ≤ F.depthOf (F.ancestorAtDepth u (cut F u v)) := by
      rw [hwd]
      exact hdc
    obtain ⟨_, hzw, hzd⟩ := hF.ancestorAtDepth_spec hw hdw
    have hZu := (hF.ancestorAtDepth_unique hu hdu).mp
      ⟨IsAncestor.trans hzw hwu, hzd⟩
    have haZ := hAu.trans hZu.symm
    rwa [← haZ] at hzw
  · intro haw
    exact ⟨IsAncestor.trans haw hwu, IsAncestor.trans haw hwv⟩

theorem query_count_le (F : JumpForest) (u v : Nat) :
    (query F u v).2 ≤ Nat.log2 (sharedDepth F u v + 1) + 1 := by
  simpa only [query, CommonAncestorSearch.lca] using
    (CommonAncestorSearch.run_count_le (sharedDepth F u v)
      (F.ancestorAtDepth u) (F.ancestorAtDepth v))

/-! The executable query uses only the region, array, and two node IDs. -/

def wordGetter (R : JumpWordRegion) (mem : Array Nat) (u d : Nat) : Nat :=
  (ancestorAtDepthWords R mem u d).1

def wordSharedDepth (R : JumpWordRegion) (mem : Array Nat) (u v : Nat) : Nat :=
  min (readRecordWords R mem u).1.depth (readRecordWords R mem v).1.depth

def wordQuery (R : JumpWordRegion) (mem : Array Nat) (u v : Nat) : Nat × Nat :=
  CommonAncestorSearch.lca (wordSharedDepth R mem u v)
    (wordGetter R mem u) (wordGetter R mem v)

theorem wordQuery_refines {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u v n L : Nat}
    (hu : u < F.size) (hv : v < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L) :
    wordQuery R mem u v = query F u v := by
  have hdu : (readRecordWords R mem u).1.depth = F.depthOf u :=
    congrArg (fun r => r.depth) (readRecordWords_spec hLay hu).1
  have hdv : (readRecordWords R mem v).1.depth = F.depthOf v :=
    congrArg (fun r => r.depth) (readRecordWords_spec hLay hv).1
  have hgu : wordGetter R mem u = F.ancestorAtDepth u := by
    funext d
    exact (ancestorAtDepthWords_spec hLay hu hn hL d).1
  have hgv : wordGetter R mem v = F.ancestorAtDepth v := by
    funext d
    exact (ancestorAtDepthWords_spec hLay hv hn hL d).1
  simp only [wordQuery, wordSharedDepth, query, sharedDepth, hdu, hdv, hgu, hgv]

theorem wordQuery_exact {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u v n L : Nat}
    (hu : u < F.size) (hv : v < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L) :
    (wordQuery R mem u v).1 < F.size ∧
      IsAncestor F (wordQuery R mem u v).1 u ∧
      IsAncestor F (wordQuery R mem u v).1 v ∧
      ∀ a : Nat, (IsAncestor F a u ∧ IsAncestor F a v) ↔
        IsAncestor F a (wordQuery R mem u v).1 := by
  rw [wordQuery_refines hLay hu hv hn hL]
  exact query_exact hLay.valid hu hv

theorem word_accesses_in_region
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u v n L : Nat}
    (hu : u < F.size) (hv : v < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L) :
    AllAccessesInRegion R.baseAddr R.endAddr (readRecordWords R mem u).2 ∧
      AllAccessesInRegion R.baseAddr R.endAddr (readRecordWords R mem v).2 ∧
      (∀ d : Nat, AllAccessesInRegion R.baseAddr R.endAddr
        (ancestorAtDepthWords R mem u d).2) ∧
      (∀ d : Nat, AllAccessesInRegion R.baseAddr R.endAddr
        (ancestorAtDepthWords R mem v d).2) :=
  ⟨(readRecordWords_spec hLay hu).2.2, (readRecordWords_spec hLay hv).2.2,
    fun d => (ancestorAtDepthWords_spec hLay hu hn hL d).2.2.2,
    fun d => (ancestorAtDepthWords_spec hLay hv hn hL d).2.2.2⟩

/-! Old base nodes: parent and depth records suffice. Jump pointers need
not be assumed equal, because each valid forest's getter is unique. -/

private theorem old_iterParent {F G : JumpForest} (hF : ValidJumpForest F)
    (hParent : ∀ x, x < F.size → G.parentOf x = F.parentOf x)
    (k : Nat) {x : Nat} (hx : x < F.size) :
    G.iterParent k x = F.iterParent k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      change G.iterParent k (G.parentOf x) = F.iterParent k (F.parentOf x)
      rw [hParent x hx]
      exact ih (x := F.parentOf x) (hF.parentOf_lt_size hx)

theorem old_getter {F G : JumpForest}
    (hF : ValidJumpForest F) (hG : ValidJumpForest G)
    (hSize : F.size ≤ G.size)
    (hParent : ∀ x, x < F.size → G.parentOf x = F.parentOf x)
    (hDepth : ∀ x, x < F.size → G.depthOf x = F.depthOf x)
    {x : Nat} (hx : x < F.size) :
    G.ancestorAtDepth x = F.ancestorAtDepth x := by
  funext d
  by_cases hd : d ≤ F.depthOf x
  · obtain ⟨ha, ⟨k, hk⟩, had⟩ := hF.ancestorAtDepth_spec hx hd
    have hdG : d ≤ G.depthOf x := by simpa only [hDepth x hx] using hd
    exact ((hG.ancestorAtDepth_unique (Nat.lt_of_lt_of_le hx hSize) hdG).mp
      ⟨⟨k, (old_iterParent hF hParent k hx).trans hk⟩,
        (hDepth _ ha).trans had⟩).symm
  · have hdF : F.depthOf x ≤ d := by omega
    have hdG : G.depthOf x ≤ d := by simpa only [hDepth x hx] using hdF
    first
    | rw [ancestorAtDepth_of_ge G hdG, ancestorAtDepth_of_ge F hdF]
    | rw [JumpForest.ancestorAtDepth_of_ge G hdG,
          JumpForest.ancestorAtDepth_of_ge F hdF]

/-- Both the vertex and the search probe count are preserved. -/
theorem old_query {F G : JumpForest}
    (hF : ValidJumpForest F) (hG : ValidJumpForest G)
    (hSize : F.size ≤ G.size)
    (hParent : ∀ x, x < F.size → G.parentOf x = F.parentOf x)
    (hDepth : ∀ x, x < F.size → G.depthOf x = F.depthOf x)
    {u v : Nat} (hu : u < F.size) (hv : v < F.size) :
    query G u v = query F u v := by
  simp only [query, sharedDepth, hDepth u hu, hDepth v hv,
    old_getter hF hG hSize hParent hDepth hu,
    old_getter hF hG hSize hParent hDepth hv]

theorem old_wordQuery
    {R S : JumpWordRegion} {F G : JumpForest} {mem mem' : Array Nat}
    (hOld : JumpWordLayout R F mem) (hNew : JumpWordLayout S G mem')
    (hSize : F.size ≤ G.size)
    (hParent : ∀ x, x < F.size → G.parentOf x = F.parentOf x)
    (hDepth : ∀ x, x < F.size → G.depthOf x = F.depthOf x)
    {u v n L : Nat} (hu : u < F.size) (hv : v < F.size)
    (hnOld : F.numInserted ≤ n) (hnNew : G.numInserted ≤ n)
    (hL : n + 2 ≤ 2 ^ L) :
    wordQuery S mem' u v = wordQuery R mem u v := by
  rw [wordQuery_refines hNew (Nat.lt_of_lt_of_le hu hSize)
        (Nat.lt_of_lt_of_le hv hSize) hnNew hL,
      wordQuery_refines hOld hu hv hnOld hL]
  exact old_query hOld.valid hNew.valid hSize hParent hDepth hu hv

/-! Read and operation charges. A getter control unit covers a record
visit, including its constant local work. A probe control unit covers
the search comparison and interval update. Endpoint setup and final
dispatch each have one control unit in addition to their stated reads. -/

def evalCharge (p : Nat) : Nat := 2 * p + 1

def getterReadBound (L : Nat) : Nat := 1 + 3 * (6 * L + 1)

def getterOpBound (L : Nat) : Nat := getterReadBound L + (6 * L + 1)

def readCharge (L p : Nat) : Nat :=
  6 + p * (getterReadBound L + getterReadBound L) + getterReadBound L

def operationCharge (L p : Nat) : Nat :=
  7 + p * (1 + getterOpBound L + getterOpBound L) + (1 + getterOpBound L)

def getterReads (R : JumpWordRegion) (mem : Array Nat) (u d : Nat) : Nat :=
  (ancestorAtDepthWords R mem u d).2.length

def getterOps (R : JumpWordRegion) (mem : Array Nat) (u d : Nat) : Nat :=
  let reads := getterReads R mem u d
  reads + reads / 3

theorem getter_charges_le
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u n L : Nat} (hu : u < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L) (d : Nat) :
    getterReads R mem u d ≤ getterReadBound L ∧
      getterOps R mem u d ≤ getterOpBound L := by
  have he : getterReads R mem u d = 3 * (F.traceReadOps u d).length :=
    (ancestorAtDepthWords_spec hLay hu hn hL d).2.1
  have ht := traceReadOps_length_le hLay.valid hu hn hL d
  have hr : getterReads R mem u d ≤ getterReadBound L :=
    (ancestorAtDepthWords_spec hLay hu hn hL d).2.2.1
  have hVisits : getterReads R mem u d / 3 = (F.traceReadOps u d).length := by
    omega
  refine ⟨hr, ?_⟩
  change getterReads R mem u d + getterReads R mem u d / 3 ≤
    getterReadBound L + (6 * L + 1)
  rw [hVisits]
  exact Nat.add_le_add hr ht

def sumCharge (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => f d + sumCharge f ds

private theorem sumCharge_le {f : Nat → Nat} {B : Nat}
    (hf : ∀ d, f d ≤ B) (ds : List Nat) :
    sumCharge f ds ≤ ds.length * B := by
  induction ds with
  | nil => simp [sumCharge]
  | cons d ds ih =>
      change f d + sumCharge f ds ≤ (ds.length + 1) * B
      rw [Nat.add_mul, Nat.one_mul]
      have hd := hf d
      omega

/-- Charge both getters at a real probe, neither at the sentinel, and
one getter at the final depth. The schedule is only used for accounting. -/
def bill (extra : Nat) (cost : Nat → Nat → Nat)
    (m u v setup finalDepth : Nat) (ds : List Nat) : Nat :=
  setup + sumCharge
    (fun d => extra + (if d ≤ m then cost u d + cost v d else 0)) ds +
    (extra + cost u finalDepth)

private theorem bill_le {extra : Nat} {cost : Nat → Nat → Nat}
    {m u v setup finalDepth H B : Nat} (ds : List Nat)
    (hSetup : setup ≤ H) (hu : ∀ d, cost u d ≤ B) (hv : ∀ d, cost v d ≤ B) :
    bill extra cost m u v setup finalDepth ds ≤
      H + ds.length * (extra + B + B) + (extra + B) := by
  have hp (d : Nat) :
      extra + (if d ≤ m then cost u d + cost v d else 0) ≤ extra + B + B := by
    by_cases hd : d ≤ m
    · rw [ite_eq_left hd]
      have hU := hu d
      have hV := hv d
      omega
    · rw [ite_eq_right hd]
      omega
  have hs := sumCharge_le hp ds
  have hf := hu finalDepth
  unfold bill
  omega

def setupReads (R : JumpWordRegion) (mem : Array Nat) (u v : Nat) : Nat :=
  (readRecordWords R mem u).2.length + (readRecordWords R mem v).2.length

def wordReadBill (R : JumpWordRegion) (mem : Array Nat)
    (u v finalDepth : Nat) (ds : List Nat) : Nat :=
  bill 0 (getterReads R mem) (wordSharedDepth R mem u v)
    u v (setupReads R mem u v) finalDepth ds

def wordOpBill (R : JumpWordRegion) (mem : Array Nat)
    (u v finalDepth : Nat) (ds : List Nat) : Nat :=
  bill 1 (getterOps R mem) (wordSharedDepth R mem u v)
    u v (setupReads R mem u v + 1) finalDepth ds

theorem word_bills_le
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u v n L : Nat}
    (hu : u < F.size) (hv : v < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (finalDepth : Nat) (ds : List Nat) :
    wordReadBill R mem u v finalDepth ds ≤ readCharge L ds.length ∧
      wordOpBill R mem u v finalDepth ds ≤ operationCharge L ds.length := by
  have hs : setupReads R mem u v = 6 := by
    simp only [setupReads, (readRecordWords_spec hLay hu).2.1,
      (readRecordWords_spec hLay hv).2.1]
  constructor
  · have h := bill_le (extra := 0) (m := wordSharedDepth R mem u v)
      (finalDepth := finalDepth) ds (Nat.le_of_eq hs)
      (fun d => (getter_charges_le hLay hu hn hL d).1)
      (fun d => (getter_charges_le hLay hv hn hL d).1)
    simpa only [wordReadBill, readCharge, Nat.zero_add] using h
  · have hs' : setupReads R mem u v + 1 ≤ 7 := by omega
    exact bill_le (extra := 1) (m := wordSharedDepth R mem u v)
      (finalDepth := finalDepth) ds hs'
      (fun d => (getter_charges_le hLay hu hn hL d).2)
      (fun d => (getter_charges_le hLay hv hn hL d).2)

private theorem charge_mono {L p q : Nat} (h : p ≤ q) :
    readCharge L p ≤ readCharge L q ∧
      operationCharge L p ≤ operationCharge L q := by
  have hr := Nat.mul_le_mul_right (getterReadBound L + getterReadBound L) h
  have ho := Nat.mul_le_mul_right (1 + getterOpBound L + getterOpBound L) h
  unfold readCharge operationCharge
  exact ⟨by omega, by omega⟩

/-- The bills are bounded at the returned probe count, and the latter
charges are bounded at the checked logarithmic probe limit. The final
dispatch is one getter call, not one word read. -/
theorem word_query_charges
    {R : JumpWordRegion} {F : JumpForest} {mem : Array Nat}
    (hLay : JumpWordLayout R F mem) {u v n L : Nat}
    (hu : u < F.size) (hv : v < F.size)
    (hn : F.numInserted ≤ n) (hL : n + 2 ≤ 2 ^ L)
    (ds : List Nat) (hds : ds.length ≤ (wordQuery R mem u v).2) :
    let p := (wordQuery R mem u v).2
    let q := Nat.log2 (sharedDepth F u v + 1) + 1
    evalCharge p ≤ evalCharge q ∧
      wordReadBill R mem u v (cut F u v) ds ≤ readCharge L p ∧
      wordOpBill R mem u v (cut F u v) ds ≤ operationCharge L p ∧
      readCharge L p ≤ readCharge L q ∧
      operationCharge L p ≤ operationCharge L q := by
  dsimp only
  have hp : (wordQuery R mem u v).2 ≤ Nat.log2 (sharedDepth F u v + 1) + 1 := by
    rw [wordQuery_refines hLay hu hv hn hL]
    exact query_count_le F u v
  obtain ⟨hr, ho⟩ := word_bills_le hLay hu hv hn hL (cut F u v) ds
  obtain ⟨hr', ho'⟩ := charge_mono (L := L) hds
  obtain ⟨hr'', ho''⟩ := charge_mono (L := L) hp
  exact ⟨by unfold evalCharge; omega, Nat.le_trans hr hr', Nat.le_trans ho ho', hr'', ho''⟩

end PaperB.JumpForestCommonAncestor
