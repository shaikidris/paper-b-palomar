module

public import PaperB.ForestRetainedWords
public import PaperB.ForestKnownProbe
public import PaperB.OraclePackedWidth

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex
open _root_.EX24.PreparedSweep

/-- Read the original word, with the same zero default used in the packed
membership test. Each call reads one cell. -/
private def probeWord {bits : Nat} (bank : Array (Fin (2 ^ bits))) (i : Nat) : Nat × Nat :=
  CountedProbe.mapC (fun x => (x.map Fin.val).getD 0) (CountedProbe.read bank i)

def WordColumns.knownProbed {bits : Nat} (w : WordColumns bits) (a v : Nat) :
    Bool × Nat :=
  CountedProbe.bindC (probeWord w.labels v) fun label =>
    CountedProbe.bindC (probeWord w.entry label) fun entry =>
      CountedProbe.bindC (probeWord w.entry a) fun lo =>
        CountedProbe.mapC (fun hi => decide (lo ≤ entry) && decide (entry < hi))
          (probeWord w.stop a)

theorem WordColumns.knownProbed_exact {bits : Nat} (w : WordColumns bits) (a v : Nat) :
    w.knownProbed a v = (w.known a v, 4) :=
  rfl

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

theorem packWordColumns_knownProbed {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (a v : Nat) :
    (packWordColumns r cap).knownProbed a v = ((ofOrderedReader r).known a v, 4) := by
  rw [WordColumns.knownProbed_exact, packWordColumns_known]

theorem packWordColumns_dictionary_represents {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) :
    FlatPairDictionary.Represents (packWordColumns r cap).dictionary (ofOrderedReader r) :=
  FlatPairDictionary.serialize_represents _ _

/-- A fixed five-bit slack suffices for this local quotient image. -/
theorem local_word_columns_fit (N : Nat) : 1 + 18 * N < 2 ^ OracleContract.wordBits 5 N 0 :=
  OracleContract.linear_payload_fits 5 N 0 18 (1 + 18 * N) (by decide) (by
    simp only [Nat.add_zero, Nat.mul_add, Nat.mul_one]
    omega)

end PaperB.RetainedProperLoss
