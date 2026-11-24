module

public import PaperB.ArcBuckets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace FreshHeadIndex

universe u
variable {E : Type u} {B : Nat}

/-- For `Log H`, pass `Event.head`, `Event.fresh`, and the executable nonroot test. -/
def build (head : E → Fin B) (fresh nonroot : E → Bool)
    (log : List E) : EX51.Rows B E :=
  (EX51.groupMap (fun e => head e) id
    (log.filter (fun e => fresh e && nonroot e))).1

def lookup (rows : EX51.Rows B E) (j : Fin B) : Option E :=
  (rows.row j).head?

private theorem eq_of_mem_of_head_eq (head : E → Fin B) (xs : List E)
    (hn : (xs.map head).Nodup) {a b : E} (hab : head a = head b) :
    a ∈ xs → b ∈ xs → a = b := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    intro ha hb
    have hc : head c ∉ xs.map head ∧ (xs.map head).Nodup :=
      List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with h | ha
    · subst a
      rcases List.mem_cons.mp hb with h | hb
      · subst b
        rfl
      · exact (hc.1 (List.mem_map.mpr ⟨b, hb, hab.symm⟩)).elim
    · rcases List.mem_cons.mp hb with h | hb
      · subst b
        exact (hc.1 (List.mem_map.mpr ⟨a, ha, hab⟩)).elim
      · exact ih hc.2 ha hb

private theorem head_hit_iff_mem (xs : List E) (e : E)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, a = b) :
    xs.head? = some e ↔ e ∈ xs := by
  cases xs with
  | nil => simp
  | cons a tl =>
    constructor
    · intro hit
      have h : a = e := Option.some.inj hit
      subst e
      simp
    · intro he
      exact congrArg some (unique a (by simp) e he)

theorem lookup_eq_some_iff (head : E → Fin B) (fresh nonroot : E → Bool)
    (log : List E) (hn : (log.map head).Nodup) (j : Fin B) (e : E) :
    lookup (build head fresh nonroot log) j = some e ↔
      e ∈ log ∧ fresh e = true ∧ nonroot e = true ∧ head e = j := by
  simp only [lookup, build, EX51.groupMap_row, List.map_id]
  let bucket := (log.filter (fun x => fresh x && nonroot x)).filter
    (fun x => decide (head x = j))
  change bucket.head? = some e ↔ _
  have mem_bucket (x : E) : x ∈ bucket ↔
      x ∈ log ∧ fresh x = true ∧ nonroot x = true ∧ head x = j := by
    simp [bucket, List.mem_filter, Bool.and_eq_true] <;> grind
  rw [← mem_bucket e]
  apply head_hit_iff_mem
  intro a ha b hb
  have ha' := (mem_bucket a).mp ha
  have hb' := (mem_bucket b).mp hb
  exact eq_of_mem_of_head_eq head log hn
    (ha'.2.2.2.trans hb'.2.2.2.symm) ha'.1 hb'.1

end FreshHeadIndex
