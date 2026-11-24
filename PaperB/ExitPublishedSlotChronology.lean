module

public import PaperB.ExitPhysicalPrefixLive

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open PaperB
open PaperB.Jumps
open EX24 EX24.PreStep EX24.PreparedSweep EX24.PreparedSweep.ChronologicalIndex

namespace PaperB.ExitPublishedSlotChronology

/-- Cut immediately after the publication, whether `e` allocates or reuses. -/
theorem splitAfterPublished
    {H : LabelledQuotient} {t out : Tables H}
    {pre post : Log H} {e : Event H}
    (run : SlotRun t (pre ++ e :: post) out) :
    ∃ mid, SlotRun t (pre ++ [e]) mid ∧ SlotRun mid post out ∧
      e.node < mid.next := by
  have run' : SlotRun t ((pre ++ [e]) ++ post) out := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using run
  obtain ⟨mid, hpre, hpost⟩ := SlotRun.splitAtPrefix run'
  have he : e ∈ pre ++ [e] :=
    List.mem_append.mpr (Or.inr (by simp))
  exact ⟨mid, hpre, hpost, hpre.node_lt e he⟩

/-- Every positive slot at most the published label already has its first
fresh creator by the end of the publishing event. -/
theorem firstCreationThroughPublished
    {H : LabelledQuotient} {t out : Tables H}
    {pre post : Log H} {e : Event H} {k : Nat}
    (run : SlotRun t (pre ++ e :: post) out)
    (hinit : t.next = 1) (hk : 0 < k) (hle : k ≤ e.node) :
    FirstCreation (pre ++ [e]) k := by
  obtain ⟨mid, hpre, _, he⟩ := splitAfterPublished run
  exact hpre.first k (by omega) (Nat.lt_of_le_of_lt hle he)

/-- The creator is in the prefix through `e`, and no fresh event in the
remaining log can create the same slot. -/
theorem scheduledThroughPublished
    {H : LabelledQuotient} {t out : Tables H}
    {pre post : Log H} {e : Event H} {k : Nat}
    (run : SlotRun t (pre ++ e :: post) out)
    (hinit : t.next = 1) (hk : 0 < k) (hle : k ≤ e.node) :
    ScheduledEarlier (pre ++ [e]) post k := by
  obtain ⟨mid, hpre, hpost, he⟩ := splitAfterPublished run
  have hlt : k < mid.next := Nat.lt_of_le_of_lt hle he
  obtain ⟨left, creator, between, hsplit, hnode, hfresh, hleft, hbetween⟩ :=
    hpre.first k (by omega) hlt
  refine ⟨left, creator, between, hsplit, hnode, hfresh, hleft, ?_⟩
  intro z hz hzk
  rcases List.mem_append.mp hz with hz | hz
  · exact hbetween z hz hzk
  · cases hzf : z.fresh with
    | false => rfl
    | true =>
      have hge := hpost.fresh_ge z hz hzf
      omega

/-- The cursor bound holds at any supplied later prefix state, not just
at the existential cut returned by `splitAfterPublished`. -/
theorem slotLtAtLaterPrefix
    {H : LabelledQuotient} {t atCall : Tables H}
    {pre gap : Log H} {e : Event H} {k : Nat}
    (hbefore : SlotRun t ((pre ++ [e]) ++ gap) atCall)
    (hle : k ≤ e.node) :
    k < atCall.next := by
  have he₀ : e ∈ pre ++ [e] :=
    List.mem_append.mpr (Or.inr (by simp))
  have he : e ∈ (pre ++ [e]) ++ gap :=
    List.mem_append.mpr (Or.inl he₀)
  exact Nat.lt_of_le_of_lt hle (hbefore.node_lt e he)

/-- `edge child parent` is an allowed physical parent step. Put any
forest-specific validity or bounds needed for that step in `edge`. -/
inductive PhysicalAncestor (edge : Nat → Nat → Prop) : Nat → Nat → Prop where
  | here (v : Nat) : PhysicalAncestor edge v v
  | up {v u k : Nat} :
      edge v u → PhysicalAncestor edge u k → PhysicalAncestor edge v k

/-- Instantiate `step_le` with the bounded jump-parent inequality.
For a valid `parentOf` step, strict decrease suffices via `Nat.le_of_lt`. -/
theorem PhysicalAncestor.leSource
    {edge : Nat → Nat → Prop} {source k : Nat}
    (path : PhysicalAncestor edge source k)
    (step_le : ∀ {v u}, edge v u → u ≤ v) :
    k ≤ source := by
  induction path with
  | here => exact Nat.le_refl _
  | up hedge _ ih => exact Nat.le_trans ih (step_le hedge)

theorem ancestorFirstCreationThroughPublished
    {H : LabelledQuotient} {t out : Tables H}
    {pre post : Log H} {e : Event H} {k : Nat}
    {edge : Nat → Nat → Prop}
    (run : SlotRun t (pre ++ e :: post) out)
    (hinit : t.next = 1) (hk : 0 < k)
    (path : PhysicalAncestor edge e.node k)
    (step_le : ∀ {v u}, edge v u → u ≤ v) :
    FirstCreation (pre ++ [e]) k :=
  firstCreationThroughPublished run hinit hk (path.leSource step_le)

private theorem freshDriverMemPrefix
    {H : LabelledQuotient} {pre rest : Log H}
    {driver : Event H} {k : Nat}
    (hs : ScheduledEarlier pre rest k)
    (hmem : driver ∈ pre ++ rest)
    (hfresh : driver.fresh = true) (hnode : driver.node = k) :
    driver ∈ pre := by
  obtain ⟨left, creator, between, hsplit, hn, hf, hb, hafter⟩ := hs
  rcases List.mem_append.mp hmem with hp | hr
  · exact hp
  · have hfalse := hafter driver (List.mem_append.mpr (Or.inr hr)) hnode
    simp [hfresh] at hfalse

/-- If compact coverage identifies a particular fresh event in the
physical log as the driver for `k`, that very event is before `row`.
The slot is also below the cursor of the supplied actual call state.

The forest-specific inputs are `path` and `step_le`; the compact
coverage inputs are `hdriverLog`, `hdriverFresh`, and `hdriverNode`. -/
theorem coveredAncestorDriverBeforeRow
    {H : LabelledQuotient} {t out atCall : Tables H}
    {pre gap tail : Log H} {e row driver : Event H} {k : Nat}
    {edge : Nat → Nat → Prop}
    (run : SlotRun t (pre ++ e :: (gap ++ row :: tail)) out)
    (hinit : t.next = 1)
    (hbefore : SlotRun t ((pre ++ [e]) ++ gap) atCall)
    (hk : 0 < k)
    (path : PhysicalAncestor edge e.node k)
    (step_le : ∀ {v u}, edge v u → u ≤ v)
    (hdriverLog : driver ∈ pre ++ e :: (gap ++ row :: tail))
    (hdriverFresh : driver.fresh = true) (hdriverNode : driver.node = k) :
    driver ∈ ((pre ++ [e]) ++ gap) ∧ k < atCall.next := by
  have hle := path.leSource step_le
  have hs := scheduledThroughPublished run hinit hk hle
  have hmem : driver ∈ (pre ++ [e]) ++ (gap ++ row :: tail) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append]
      using hdriverLog
  have hdriverPre := freshDriverMemPrefix hs hmem hdriverFresh hdriverNode
  exact ⟨List.mem_append.mpr (Or.inl hdriverPre), slotLtAtLaterPrefix hbefore hle⟩

end PaperB.ExitPublishedSlotChronology
