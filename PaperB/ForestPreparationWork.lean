module

public import PaperB.ForestInputPrepStorage

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Append at file scope after the preparation declarations.
namespace PaperB.PreparationWorkChecks

set_option maxHeartbeats 100000

private theorem supplied_length (H : LabelledQuotient) :
    (ForestIncomingRaw.supplied H).length = H.arcCount := by
  rw [ForestIncomingRaw.length_supplied,
    ForestPreparedBuild.arcTotal_eq_arcCount]

private theorem emitted_length (H : LabelledQuotient) :
    ForestIncomingPrep.mapCalls H (ForestIncomingRaw.prepare H) =
      H.arcCount := by
  rw [ForestIncomingPrep.mapCalls_prepare, supplied_length]

private theorem prepare_work (H : LabelledQuotient) :
    (ForestIncomingRaw.prepare H).2 =
      ⟨H.vertexCount, H.arcCount, H.arcCount, H.arcCount, H.vertexCount⟩ := by
  unfold ForestIncomingRaw.prepare
  rw [EX51.groupMap_work, supplied_length]

private theorem epoch_visits (H : LabelledQuotient)
    (cover : ForestIncomingPrep.Cover H) :
    (ForestIncomingPrep.build H cover).visits = H.arcCount := by
  rw [ForestIncomingPrep.visits_supplied, supplied_length]

-- One unit per requested fill slot, enumerated head, fold step,
-- row read and row write. The generated list map also reverses its
-- accumulator, so each mapped entry pays for both visits.
private def sourceCharge (H : LabelledQuotient)
    (p : ForestIncomingRaw.Prepared H) : Nat :=
  let heads := (List.finRange H.vertexCount).length
  H.vertexCount + heads + heads + heads + heads +
    2 * ForestIncomingPrep.mapCalls H p

private theorem source_charge_prepare (H : LabelledQuotient) :
    sourceCharge H (ForestIncomingRaw.prepare H) =
      5 * H.vertexCount + 2 * H.arcCount := by
  simp only [sourceCharge, List.length_finRange, emitted_length] <;> omega

private def groupCharge : EX51.Work → Nat
  | ⟨init, scatterRead, scatterWrite, reverse, finish⟩ =>
    init + scatterRead + scatterWrite + reverse + 2 * finish

/-- Charge zero fills, head enumeration, the outer dedup loop, and the
two row accesses per head. On every stamp visit, reserve a stamp read,
the visit itself, a stamp write, and an emitted list cell. The last two
charges cover the fresh branch and may be unused on a repeated stamp. -/
private def epochCharge (H : LabelledQuotient) (visits : Nat) : Nat :=
  6 * H.vertexCount + 4 * visits

/-- The exact sum of the preparation charges, including padded site
allowances. The counters are from the actual preparation, which never
computes an adjacency length or measures the projected rows at runtime. -/
def preparationSites (H : LabelledQuotient) (cover : ForestIncomingPrep.Cover H) : Nat :=
  let heads := (List.finRange H.vertexCount).length
  heads + heads + ForestIncomingRaw.arcTotal H +
    groupCharge (ForestIncomingRaw.prepare H).2 +
    sourceCharge H (ForestIncomingRaw.prepare H) +
    epochCharge H (ForestIncomingPrep.build H cover).visits

theorem preparation_sites_exact (H : LabelledQuotient)
    (cover : ForestIncomingPrep.Cover H) :
    preparationSites H cover = 16 * H.vertexCount + 10 * H.arcCount := by
  unfold preparationSites
  dsimp only
  rw [ForestPreparedBuild.arcTotal_eq_arcCount, prepare_work,
    source_charge_prepare, epoch_visits]
  simp only [List.length_finRange, groupCharge, epochCharge] <;> omega

theorem preparation_charge_bound (H : LabelledQuotient)
    (cover : ForestIncomingPrep.Cover H) :
    preparationSites H cover ≤ 16 * (H.vertexCount + H.arcCount) := by
  rw [preparation_sites_exact]
  omega

end PaperB.PreparationWorkChecks
