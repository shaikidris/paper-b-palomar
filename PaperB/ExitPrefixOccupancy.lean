module

public import PaperB.ExitInterleavedPacked

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42.ArraySweep.Packed.PrefixOcc

variable {n m l : Nat} {P : Plan n m}
variable (S : Schedule P) (addr : Fin m → Nat) (probe : Nat → Prop)

def Creates (a : Fin n) (x : Nat) : Prop :=
  ∃ i, S.mapSlot.read (S.vertex a) = some i ∧ x = addr i

/-- `probe` describes only initial seeds; dynamic occupancy uses schedule writes. -/
def occ (k x : Nat) : Prop :=
  probe x ∨ ∃ a : Fin n, a.val < k ∧ Creates S addr a x

@[simp] theorem zero (x : Nat) : occ S addr probe 0 x ↔ probe x := by
  simp [occ]

theorem step (a : Fin n) (x : Nat) :
    occ S addr probe (a.val + 1) x ↔
      occ S addr probe a.val x ∨ Creates S addr a x := by
  unfold occ
  constructor
  · rintro (hs | ⟨b, hb, hc⟩)
    · exact Or.inl (Or.inl hs)
    · by_cases h : b.val < a.val
      · exact Or.inl (Or.inr ⟨b, h, hc⟩)
      · have e : b = a := Fin.ext (by omega)
        subst b
        exact Or.inr hc
  · rintro ((hs | ⟨b, hb, hc⟩) | hc)
    · exact Or.inl hs
    · exact Or.inr ⟨b, by omega, hc⟩
    · exact Or.inr ⟨a, Nat.lt_succ_self _, hc⟩

theorem slot_once {a b : Fin n} {i : Fin m}
    (ha : S.mapSlot.read (S.vertex a) = some i)
    (hb : S.mapSlot.read (S.vertex b) = some i) : a = b := by
  have fa := (S.slot_exact _ _).1 ha
  have fb := (S.slot_exact _ _).1 hb
  have hab : ¬ a.val < b.val := fun h =>
    fb.2 ⟨S.vertex a, S.increasing a b h, fa.1⟩
  have hba : ¬ b.val < a.val := fun h =>
    fa.2 ⟨S.vertex b, S.increasing b a h, fb.1⟩
  exact Fin.ext (by omega)

theorem keep {a : Fin n} (h : S.mapSlot.read (S.vertex a) = none) :
    occ S addr probe (a.val + 1) = occ S addr probe a.val := by
  funext x
  apply propext
  rw [step]
  simp [Creates, h]

theorem put {a : Fin n} {i : Fin m}
    (h : S.mapSlot.read (S.vertex a) = some i)
    (inj : ∀ {i j}, addr i = addr j → i = j) (seed : ¬ probe (addr i)) :
    ¬ occ S addr probe a.val (addr i) ∧
      occ S addr probe (a.val + 1) = (fun x => x = addr i ∨ occ S addr probe a.val x) := by
  constructor
  · unfold occ Creates
    rintro (hs | ⟨b, hb, j, hj, e⟩)
    · exact seed hs
    · have e' := inj e
      subst j
      have e'' := slot_once S hj h
      subst b
      exact Nat.lt_irrefl _ hb
  · funext x
    apply propext
    rw [step]
    constructor
    · rintro (ho | ⟨j, hj, e⟩)
      · exact Or.inr ho
      · exact Or.inl (e.trans (congrArg addr (Option.some.inj (hj.symm.trans h))))
    · rintro (e | ho)
      · exact Or.inr ⟨i, h, e⟩
      · exact Or.inl ho

private theorem before_first (Q : Plan n l) (r : Nat) (q : Fin l) :
    Q.mapBefore r q ↔ ∃ y, Q.rank y < r ∧ Q.firstAt y q := by
  constructor
  · induction r with
    | zero => rintro ⟨y, hy, _⟩; omega
    | succ r ih =>
      intro h
      by_cases hb : Q.mapBefore r q
      · obtain ⟨y, hy, hf⟩ := ih hb
        exact ⟨y, by omega, hf⟩
      · obtain ⟨y, hy, ho⟩ := h
        have hn : ¬ Q.rank y < r := fun hr => hb ⟨y, hr, ho⟩
        have e : Q.rank y = r := by omega
        exact ⟨y, hy, ho, by simpa only [e] using hb⟩
  · rintro ⟨y, hy, hf⟩
    exact ⟨y, hy, hf.1⟩

theorem exactPrefix {Q : Plan n l} {q : Fin l} {x k r : Nat}
    (seed : ¬ probe x)
    (first : ∀ b, Creates S addr b x ↔ Q.firstAt (S.vertex b) q)
    (cut : ∀ b, Q.rank (S.vertex b) < r ↔ b.val < k) :
    occ S addr probe k x ↔ Q.mapBefore r q := by
  rw [before_first Q r q]
  unfold occ
  constructor
  · rintro (hs | ⟨b, hb, hc⟩)
    · exact (seed hs).elim
    · exact ⟨S.vertex b, (cut b).2 hb, (first b).1 hc⟩
  · rintro ⟨y, hy, hf⟩
    obtain ⟨b, hb⟩ := S.covers y
    subst y
    exact Or.inr ⟨b, (cut b).1 hy, (first b).2 hf⟩

theorem bridges {Q : Plan n l} {q : Fin l} {x : Nat} (a : Fin n)
    (seed : ¬ probe x) (rank_eq : ∀ y, Q.rank y = P.rank y)
    (first : ∀ b, Creates S addr b x ↔ Q.firstAt (S.vertex b) q) :
    (occ S addr probe a.val x ↔ Q.mapBefore (Q.rank (S.vertex a)) q) ∧
    (occ S addr probe (a.val + 1) x ↔
      Q.mapBefore (Q.rank (S.vertex a)) q ∨ Q.observe (S.vertex a) q = true) := by
  constructor
  · apply exactPrefix S addr probe seed first
    intro b
    simpa only [rank_eq] using S.rank_lt_rank_iff b a
  · rw [← Q.before_succ (S.vertex a) q]
    apply exactPrefix S addr probe seed first
    intro b
    rw [rank_eq (S.vertex b), rank_eq (S.vertex a), S.after_cut a (S.vertex b)]
    exact S.lt_cut_iff _ (Nat.succ_le_of_lt a.isLt) b

theorem same_first (inj : ∀ {i j}, addr i = addr j → i = j)
    (a : Fin n) (i : Fin m) : Creates S addr a (addr i) ↔ P.firstAt (S.vertex a) i := by
  constructor
  · rintro ⟨j, hj, he⟩
    have e := inj he
    subst j
    exact (S.slot_exact _ _).1 hj
  · intro h
    exact ⟨i, (S.slot_exact _ _).2 h, rfl⟩

end EX42.ArraySweep.Packed.PrefixOcc
