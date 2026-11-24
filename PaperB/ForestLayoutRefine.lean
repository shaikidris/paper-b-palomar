module

public import PaperB.ForestLayoutTrace
public import PaperB.ForestLayoutTreeCost

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

open PaperB.LabelledQuotient

variable {N : Nat}

private theorem fields_flatMap_congr {α β : Type}
    (xs : List α) (f h : α → List β)
    (heq : ∀ x ∈ xs, f x = h x) :
    xs.flatMap f = xs.flatMap h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := heq x (by simp)
    have ht := ih (fun y hy => heq y (by simp [hy]))
    simp only [List.flatMap_cons, hx, ht]

private theorem fields_flatMap_split {α β : Type}
    (f : α → List β) (xs : List α) (c : α) (hc : c ∈ xs) :
    ∃ p q, xs.flatMap f = p ++ f c ++ q := by
  induction xs with
  | nil => simp at hc
  | cons x xs ih =>
    rcases List.mem_cons.mp hc with he | hm
    · subst c
      exact ⟨[], xs.flatMap f, by simp [List.flatMap_cons]⟩
    · obtain ⟨p, q, hs⟩ := ih hm
      exact ⟨f x ++ p, q, by
        simp [List.flatMap_cons, hs, List.append_assoc]⟩

private def fields_traceFuel (g : ChildLists N) :
    Nat → Fin N → List (Command N)
  | 0, _ => []
  | k + 1, v =>
    .enter v :: ((g.get v).flatMap (fields_traceFuel g k) ++ [.exit v])

private theorem fields_traceFuel_agree (g : ChildLists N)
    (rank : Fin N → Nat)
    (hrank : ∀ v c, c ∈ g.get v → rank c < rank v) :
    ∀ k v l, rank v < k → rank v < l →
      fields_traceFuel g k v = fields_traceFuel g l v := by
  intro k
  induction k with
  | zero =>
    intro v l hk hl
    omega
  | succ k ih =>
    intro v l hk hl
    cases l with
    | zero => omega
    | succ l =>
      have hc : (g.get v).flatMap (fields_traceFuel g k) =
          (g.get v).flatMap (fields_traceFuel g l) := by
        apply fields_flatMap_congr
        intro c hm
        have h := hrank v c hm
        exact ih c l (by omega) (by omega)
      simp only [fields_traceFuel, hc]

/-- The event word of a subtree, defined without reading the layout state. -/
def dfsTrace (g : ChildLists N) (nodes : Fin N → List (Fin N))
    (v : Fin N) : List (Command N) :=
  fields_traceFuel g ((nodes v).length + 1) v

private def fields_vertex : Command N → Fin N
  | .enter v => v
  | .exit v => v

private def fields_hits {α : Type} [DecidableEq α] (key : α) : List α → Nat
  | [] => 0
  | x :: xs => (if x = key then 1 else 0) + fields_hits key xs

private theorem fields_hits_append {α : Type} [DecidableEq α]
    (key : α) (p q : List α) :
    fields_hits key (p ++ q) = fields_hits key p + fields_hits key q := by
  induction p with
  | nil => simp [fields_hits]
  | cons x xs ih => simp [fields_hits, ih, Nat.add_assoc]

private theorem fields_hits_zero {α : Type} [DecidableEq α]
    (key : α) (xs : List α) :
    fields_hits key xs = 0 ↔ key ∉ xs := by
  induction xs with
  | nil => simp [fields_hits]
  | cons x xs ih =>
    by_cases he : x = key
    · subst x
      simp [fields_hits]
    · simp [fields_hits, he, Ne.symm he, ih]

private theorem fields_hits_le_one {α : Type} [DecidableEq α]
    (key : α) (xs : List α) (h : xs.Pairwise (· ≠ ·)) :
    fields_hits key xs ≤ 1 := by
  induction xs with
  | nil => simp [fields_hits]
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    by_cases he : x = key
    · subst x
      have hz := (fields_hits_zero key xs).2 (fun hm => hhead key hm rfl)
      simp [fields_hits, hz]
    · simpa [fields_hits, he] using ih htail

private theorem fields_no_later_hit {α : Type} [DecidableEq α]
    (key : α) (p q : List α)
    (h : fields_hits key (p ++ (key :: q)) ≤ 1) :
    key ∉ q := by
  have hc : fields_hits key (key :: q) = 1 + fields_hits key q := by
    simp [fields_hits]
  rw [fields_hits_append, hc] at h
  exact (fields_hits_zero key q).1 (by omega)

private theorem fields_flatMap_facts (kids : List (Fin N))
    (tr : Fin N → List (Command N)) (nodes : Fin N → List (Fin N))
    (key : Command N)
    (h : ∀ c ∈ kids,
      eventVertices (tr c) = nodes c ∧
      (tr c).length = 2 * (nodes c).length ∧
      fields_hits key (tr c) = fields_hits (fields_vertex key) (nodes c)) :
    eventVertices (kids.flatMap tr) = kids.flatMap nodes ∧
    (kids.flatMap tr).length = 2 * (kids.flatMap nodes).length ∧
    fields_hits key (kids.flatMap tr) =
      fields_hits (fields_vertex key) (kids.flatMap nodes) := by
  induction kids with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨hp, hl, hh⟩ := h c (by simp)
    obtain ⟨hp', hl', hh'⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, eventVertices_append, hp, hp']
    · simp only [List.flatMap_cons, List.length_append, hl, hl', Nat.mul_add]
    · simp only [List.flatMap_cons, fields_hits_append, hh, hh']

section TraceFacts

variable (g : ChildLists N) (nodes : Fin N → List (Fin N))
variable (hnodes : ∀ v, nodes v = v :: (g.get v).flatMap nodes)

include hnodes

private theorem fields_child_shorter (v c : Fin N) (hc : c ∈ g.get v) :
    (nodes c).length < (nodes v).length := by
  obtain ⟨p, q, hs⟩ := fields_flatMap_split nodes (g.get v) c hc
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  rw [hnodes v, List.length_cons]
  omega

theorem dfsTrace_unfold (v : Fin N) :
    dfsTrace g nodes v =
      .enter v :: ((g.get v).flatMap (dfsTrace g nodes) ++ [.exit v]) := by
  have hc : (g.get v).flatMap (fields_traceFuel g (nodes v).length) =
      (g.get v).flatMap (dfsTrace g nodes) := by
    apply fields_flatMap_congr
    intro c hm
    change fields_traceFuel g (nodes v).length c =
      fields_traceFuel g ((nodes c).length + 1) c
    exact fields_traceFuel_agree g (fun a => (nodes a).length)
      (fields_child_shorter g nodes hnodes) _ c _
      (fields_child_shorter g nodes hnodes v c hm) (Nat.lt_succ_self _)
  change Command.enter v ::
      ((g.get v).flatMap (fields_traceFuel g (nodes v).length) ++
        [Command.exit v]) = _
  rw [hc]

private theorem fields_trace_facts (key : Command N) (v : Fin N) :
    eventVertices (dfsTrace g nodes v) = nodes v ∧
    (dfsTrace g nodes v).length = 2 * (nodes v).length ∧
    fields_hits key (dfsTrace g nodes v) =
      fields_hits (fields_vertex key) (nodes v) := by
  suffices h : ∀ k a, (nodes a).length < k →
      eventVertices (dfsTrace g nodes a) = nodes a ∧
      (dfsTrace g nodes a).length = 2 * (nodes a).length ∧
      fields_hits key (dfsTrace g nodes a) =
        fields_hits (fields_vertex key) (nodes a) by
    exact h _ v (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero =>
    intro a ha
    omega
  | succ k ih =>
    intro a ha
    obtain ⟨hp, hl, hh⟩ :=
      fields_flatMap_facts (g.get a) (dfsTrace g nodes) nodes key
        (fun c hc => ih c (by
          have hs := fields_child_shorter g nodes hnodes a c hc
          omega))
    rw [dfsTrace_unfold g nodes hnodes a, hnodes a]
    refine ⟨?_, ?_, ?_⟩
    · simp [eventVertices, eventVertices_append, hp]
    · simp only [List.length_cons, List.length_append, List.length_nil, hl]
      omega
    · change fields_hits key
          ([Command.enter a] ++ ((g.get a).flatMap (dfsTrace g nodes) ++ [Command.exit a])) =
        fields_hits (fields_vertex key) ([a] ++ (g.get a).flatMap nodes)
      cases key <;> rename_i b
      all_goals
        simp only [fields_vertex] at hh ⊢
        simp only [fields_hits_append, hh, fields_hits, fields_vertex]
        generalize fields_hits b ((g.get a).flatMap nodes) = t
        by_cases h : a = b
        · subst b
          simp <;> omega
        · simp [h] <;> omega

private theorem fields_trace_split (a v : Fin N) (ha : a ∈ nodes v) :
    ∃ p q, dfsTrace g nodes v = p ++ dfsTrace g nodes a ++ q := by
  suffices h : ∀ k u, (nodes u).length < k → a ∈ nodes u →
      ∃ p q, dfsTrace g nodes u = p ++ dfsTrace g nodes a ++ q by
    exact h _ v (Nat.lt_succ_self _) ha
  intro k
  induction k with
  | zero =>
    intro u hu hm
    omega
  | succ k ih =>
    intro u hu hm
    by_cases he : a = u
    · subst u
      exact ⟨[], [], by simp⟩
    · have hm' : a ∈ (g.get u).flatMap nodes := by
        simpa [hnodes u, he] using hm
      obtain ⟨c, hc, hac⟩ := List.mem_flatMap.mp hm'
      have hs := fields_child_shorter g nodes hnodes u c hc
      obtain ⟨p, q, hsub⟩ := ih c (by omega) hac
      obtain ⟨l, r, hkids⟩ := fields_flatMap_split (dfsTrace g nodes) (g.get u) c hc
      refine ⟨.enter u :: (l ++ p), q ++ r ++ [.exit u], ?_⟩
      simp [dfsTrace_unfold g nodes hnodes u, hkids, hsub, List.append_assoc]

end TraceFacts

/-- With exact ordered buckets, the entry cell is the zero-based preorder
position, and the exclusive exit cell is that position plus the subtree length. -/
theorem layout_bucket_correct (g : ChildLists N) (root : Fin N)
    (parent : Fin N → Fin N) (depth : Fin N → Nat)
    (hTree : ValidDepthTree root parent depth)
    (hBuckets : ∀ v, g.get v = bucketChildren root parent v) :
    let s := layout g root (2 * N)
    commandLog g (2 * N) (initial root) =
      dfsTrace g (dfsSubtree root parent depth) root ∧
    s.stack = [] ∧
    ∀ a : Fin N,
      s.entries[a.val]'(by rw [s.entries_size]; exact a.isLt) =
        entry root parent depth a ∧
      s.ends[a.val]'(by rw [s.ends_size]; exact a.isLt) =
        entry root parent depth a + (dfsSubtree root parent depth a).length := by
  intro s
  let nodes := dfsSubtree root parent depth
  let tr := dfsTrace g nodes
  have hn : ∀ v, nodes v = v :: (g.get v).flatMap nodes := by
    intro v
    change dfsSubtree root parent depth v =
      v :: (g.get v).flatMap (dfsSubtree root parent depth)
    rw [hBuckets v, dfsSubtree_unfold hTree v]
    apply congrArg (List.cons v)
    generalize bucketChildren root parent v = kids
    induction kids with
    | nil => rfl
    | cons c cs ih =>
      exact congrArg (fun xs => dfsSubtree root parent depth c ++ xs) ih
  have htr : ∀ v, tr v = .enter v :: ((g.get v).flatMap tr ++ [.exit v]) :=
    dfsTrace_unfold g nodes hn
  have hinit : stackEvents tr (initial root).stack = tr root := by
    change tr root ++ [] = tr root
    exact List.append_nil _
  have hlen : (nodes root).length = N := length_dfsPreorder hTree
  have htraceLen : (tr root).length = 2 * (nodes root).length :=
    (fields_trace_facts g nodes hn (.enter root) root).2.1
  have hcount : (stackEvents tr (initial root).stack).length = 2 * N := by
    rw [hinit, htraceLen, hlen]
  have hfuel : (stackEvents tr (initial root).stack).length ≤ 2 * N := by
    simp only [hcount, Nat.le_refl]
  have hrun := run_event_trace g tr htr (2 * N) (initial root) hfuel
  rw [hinit] at hrun
  obtain ⟨hlog, hempty, _, hread⟩ := hrun
  refine ⟨hlog, hempty, ?_⟩
  have hunique : (nodes root).Pairwise (· ≠ ·) := nodup_dfsSubtree hTree root
  have hrootHits (key : Command N) : fields_hits key (tr root) ≤ 1 := by
    have hh : fields_hits key (tr root) =
        fields_hits (fields_vertex key) (nodes root) :=
      (fields_trace_facts g nodes hn key root).2.2
    rw [hh]
    exact fields_hits_le_one _ _ hunique
  intro a
  have ha : a ∈ nodes root := mem_dfsPreorder hTree a
  obtain ⟨p, q, hs⟩ := fields_trace_split g nodes hn a root ha
  change tr root = p ++ tr a ++ q at hs
  let body := (g.get a).flatMap tr
  have ht : tr a = .enter a :: (body ++ [.exit a]) := htr a
  have henter : tr root = p ++ (.enter a :: ((body ++ [.exit a]) ++ q)) := by
    simpa only [ht, List.append_assoc, List.cons_append] using hs
  have hexit : tr root = (p ++ (.enter a :: body)) ++ (.exit a :: q) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using henter
  have hav : eventVertices (tr a) = nodes a :=
    (fields_trace_facts g nodes hn (.enter a) a).1
  have hbody : eventVertices (.enter a :: body) = nodes a := by
    simpa only [ht, eventVertices, eventVertices_append, List.append_nil] using hav
  have hsplit : dfsPreorder root parent depth =
      eventVertices p ++ dfsSubtree root parent depth a ++ eventVertices q := by
    calc
      dfsPreorder root parent depth = eventVertices (tr root) :=
        (fields_trace_facts g nodes hn (.enter a) root).1.symm
      _ = eventVertices p ++ nodes a ++ eventVertices q := by
        simpa only [eventVertices_append, hav] using congrArg eventVertices hs
  have hentry : entry root parent depth a = (eventVertices p).length :=
    entry_eq_length_of_dfsPreorder_split hTree hsplit
  have hmissEnter : Command.enter a ∉ (body ++ [.exit a]) ++ q := by
    apply fields_no_later_hit (Command.enter a) p
    rw [← henter]
    exact hrootHits (.enter a)
  have hmissExit : Command.exit a ∉ q := by
    apply fields_no_later_hit (Command.exit a) (p ++ (.enter a :: body))
    rw [← hexit]
    exact hrootHits (.exit a)
  have hi : a.val < s.entries.size := by
    rw [s.entries_size]
    exact a.isLt
  have hj : a.val < s.ends.size := by
    rw [s.ends_size]
    exact a.isLt
  have hin := hread (.enter a)
  change (s.entries[a.val]?).getD 0 = eventStamp (.enter a) (tr root) 0 _ at hin
  rw [henter, eventStamp_last _ _ _ _ _ hmissEnter, Nat.zero_add] at hin
  have hout := hread (.exit a)
  change (s.ends[a.val]?).getD 0 = eventStamp (.exit a) (tr root) 0 _ at hout
  rw [hexit, eventStamp_last _ _ _ _ _ hmissExit, Nat.zero_add] at hout
  constructor
  · calc
      s.entries[a.val]'hi = (eventVertices p).length := by
        simpa [getElem?_pos, hi] using hin
      _ = entry root parent depth a := hentry.symm
  · calc
      s.ends[a.val]'hj = (eventVertices (p ++ (.enter a :: body))).length := by
        simpa [getElem?_pos, hj] using hout
      _ = entry root parent depth a + (nodes a).length := by
        rw [eventVertices_append, List.length_append, hbody, hentry]

end PaperB.ForestLayout
