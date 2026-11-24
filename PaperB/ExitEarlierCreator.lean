module

public import PaperB.ExitParentEarlier

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep.ChronologicalIndex

open PaperB PaperB.LabelledQuotient EX24.PreStep

theorem SlotRun.creator_mem_prefix {H : LabelledQuotient}
    {t out : Tables H} {pre rest : Log H} {source creator : Event H}
    (h : SlotRun t (pre ++ rest) out)
    (hs : source ∈ pre) (hc : creator ∈ pre ++ rest)
    (hf : creator.fresh = true) (hle : creator.node ≤ source.node) :
    creator ∈ pre := by
  obtain ⟨mid, front, back⟩ := SlotRun.splitAtPrefix h
  rcases List.mem_append.mp hc with hpre | hrest
  · exact hpre
  · have hlt := front.node_lt source hs
    have hge := back.fresh_ge creator hrest hf
    omega

end EX24.PreparedSweep.ChronologicalIndex
