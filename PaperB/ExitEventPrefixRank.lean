module

public import PaperB.ExitActualLog

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

namespace PaperB.OrderedFreshHeads

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
  {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
  {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount} [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)
  (full : FullRows p rank (orderedRows p data size_data))

include full

theorem logRankPairwise :
    r.log.Pairwise (fun a b => rank a.head < rank b.head) := by
  have h : (r.log.map Event.head).Pairwise (fun a b => rank a < rank b) := by
    rw [r.logHeads]
    simpa only [List.pairwise_map] using full.ordered
  simpa only [List.pairwise_map] using h

theorem rank_lt_of_mem_log_prefix {pre post : List (Event H)} {driver row : Event H}
    (hsplit : r.log = pre ++ row :: post) (hdriver : driver ∈ pre) :
    rank driver.head < rank row.head := by
  have h := logRankPairwise r full
  rw [hsplit, List.pairwise_append] at h
  exact h.2.2 driver hdriver row (by simp)

theorem logHeadCovers (y : Vertex H) : ∃ e ∈ r.log, e.head = y := by
  obtain ⟨src, hsrc, hy⟩ := full.covers y
  have hm : y ∈ r.log.map Event.head := by
    rw [r.logHeads]
    exact List.mem_map.mpr ⟨src, hsrc, hy⟩
  exact List.mem_map.mp hm

theorem mem_log_prefix_of_rank_lt {pre post : List (Event H)} {source row : Event H}
    (hsplit : r.log = pre ++ row :: post) (hsource : source ∈ r.log)
    (hlt : rank source.head < rank row.head) : source ∈ pre := by
  have h := logRankPairwise r full
  rw [hsplit, List.pairwise_append] at h
  rw [hsplit] at hsource
  rcases List.mem_append.mp hsource with hpre | htail
  · exact hpre
  · rcases List.mem_cons.mp htail with rfl | hpost
    · exact (Nat.lt_irrefl _ hlt).elim
    · have hrow := (List.pairwise_cons.mp h.2.1).1 source hpost
      exact (Nat.lt_irrefl _ (Nat.lt_trans hlt hrow)).elim

end PaperB.OrderedFreshHeads
