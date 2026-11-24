module

public import PaperB.ExitConcreteDepthContract
public import PaperB.ExitRawIncoming
public import PaperB.GenericRawExitModel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.BuiltExit.PackedRuntime.DirectIntegration

open PaperB.LabelledQuotient PaperB.ExitSummary PaperB.ExitMap

variable {H : LabelledQuotient} {N m bits : Nat}

private theorem foldl_map_eq_on
    {A : Type _} {O : Type _} {C : Type _}
    (xs : List A) (occ : A → O)
    (step : C → A → C) (step' : C → O → C)
    (same : ∀ a ∈ xs, ∀ acc, step acc a = step' acc (occ a))
    (acc : C) :
    xs.foldl step acc = (xs.map occ).foldl step' acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [same a (List.mem_cons.mpr (Or.inl rfl)) acc]
      exact ih
        (fun b hb => same b (List.mem_cons.mpr (Or.inr hb))) _

private theorem rawArc_eq_on_source
    {A : Type _} {O : Type _} {V : Type _} {T : Type _} [DecidableEq V]
    {endpoint : Fin 2 → V} {rank rank' : T → Nat}
    {fields : A → V × T} {fields' : O → V × T}
    {loss : V → Bool} {read read' : V → Values}
    {a : A} {o : O}
    (fieldOK : fields a = fields' o)
    (rankOK : rank (fields a).2 = rank' (fields a).2)
    (readOK :
      (fields a).1 ≠ endpoint 0 →
      (fields a).1 ≠ endpoint 1 →
      loss (fields a).1 = true →
      read (fields a).1 = read' (fields a).1) :
    RawIncoming.arcValue endpoint rank fields loss read a =
      RawIncoming.arcValue endpoint rank' fields' loss read' o := by
  by_cases h₀ : (fields a).1 = endpoint 0
  · simp [RawIncoming.arcValue, ← fieldOK, rankOK, h₀]
  by_cases h₁ : (fields a).1 = endpoint 1
  · simp [RawIncoming.arcValue, ← fieldOK, rankOK, h₀, h₁]
  cases hl : loss (fields a).1 with
  | false =>
      simp [RawIncoming.arcValue, ← fieldOK, h₀, h₁, hl]
  | true =>
      simp [RawIncoming.arcValue, ← fieldOK, h₀, h₁, hl,
        readOK h₀ h₁ hl]

theorem incomingLaw_of_occurrence
    {r : Input H N bits} {W : Model.{0} H m}
    {cut : Fin N} {B : CutPair H} {y : Fin H.vertexCount}
    {R : Fin H.vertexCount → Prop} {S : Fin m → Prop}
    (I : Site W B y R S)
    (occ : _ → W.Occ)
    (rowOK :
      (ForestIncomingRaw.row H r.rows y).map occ = W.incoming y)
    (fieldOK : ∀ a ∈ ForestIncomingRaw.row H r.rows y,
      r.arcFields a = (W.source (occ a), W.physicalTail (occ a)))
    (rankOK : ∀ a ∈ ForestIncomingRaw.row H r.rows y,
      r.entryRank.read (r.arcFields a).2 = W.rank (r.arcFields a).2)
    (lossOK : ∀ z, ¬ B.Mem z →
      (r.knownLoss cut z = true ↔ H.ProperLoss B z))
    (hy : H.ProperLoss B y)
    (rb : BaseReader R) (rm : MapReader S)
    (hb : ∀ v hv, rb v hv = some (W.wantBase v))
    (hm : ∀ i hi, rm i hi = some (W.wantMap i))
    (queryOK : ∀ z, H.ProperLoss B z →
      ∀ q : Query W R S B z, W.ref B z = q.run rb rm) :
    IncomingLaw r W cut B y := by
  intro read hread
  let row := ForestIncomingRaw.row H r.rows y
  let fields : W.Occ → Fin H.vertexCount × Fin H.origVertexCount :=
    fun a => (W.source a, W.physicalTail a)
  have hrun :
      RawIncoming.run (W.endpoint B) r.entryRank.read r.arcFields
        (r.knownLoss cut) read row =
      RawIncoming.run (W.endpoint B) (fun t => W.rank t) fields
        (r.knownLoss cut) (W.ref B) (row.map occ) := by
    unfold RawIncoming.run
    refine foldl_map_eq_on row occ _ _ ?_ _
    intro a ha acc
    apply congrArg (fun v => vjoin acc v)
    have hf : r.arcFields a = fields (occ a) := fieldOK a ha
    refine rawArc_eq_on_source hf (rankOK a ha) ?_
    intro h₀ h₁ hl
    exact hread (r.arcFields a).1 ⟨⟨a, ha, rfl⟩, h₀, h₁, hl⟩
  have hstored : I.items.map Item.arc = row.map occ :=
    I.keep.trans rowOK.symm
  exact hrun.trans <|
    (RawIncoming.run_eq_site I rb rm (row.map occ) hstored fields
      (r.knownLoss cut) (W.ref B) (fun _ => rfl) lossOK queryOK).trans
      (I.run_exact hy rb rm hb hm)

end PaperB.BuiltExit.PackedRuntime.DirectIntegration
