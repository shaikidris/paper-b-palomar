module

public import PaperB.RamExitFamilyAdvance
public import PaperB.RamExitFamilyEmitStage
public import PaperB.RamExitFamilyForestStage
public import PaperB.RamExitFamilyKernels
public import PaperB.RamExitFamilyCopies
public import PaperB.RamExitFamilyRegisters
public import PaperB.RamExitFamilyProgram
public import PaperB.RamExitFamilyLoop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
set_option maxErrors 160

/-!
EX5.1 Exit-Summary Family Loop Program and End-to-End Proof (`PaperB.RamExitFamilyLoop`):
Sections 3–5 constructing `exitFamilyLoopProgram` and proving `run_exit_family_loop`,
chaining from `prefixAndForestLoopProgram` into `sealedPackAndShiftProgram`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter prefixTreeBase)
open PaperB.ForestHead (Vertex)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex rawInputCap)
open PaperB.ForestSlimIndex
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamStaticReaderBridge (denseRank)
open PaperB.RamFamilyForestLoop
open PaperB.RamQuotientEmitter
open PaperB.RamDataSliceAdapter
open PaperB.RetainedProperLoss
open PaperB.ExitActualContract
open PaperB.RamSealedPacker
open PaperB.RamProgram.ExitSummaryBuild
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open PaperB.RamForestProgram.Finish (packedPayload)
open PaperB.ExitMap.Retention (TagsFit)
open PaperB.OracleContract (L)


/-! ### 5. Loop Invariant, Sub-Program Chaining, and `run_exit_family_loop` -/

section LoopInductionAndMain

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

private theorem wordCols_sizes {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {pH : PaperB.ForestDictionary.Rows H} {dataH : Array (Vertex H)}
    {sizeH : dataH.size = H.vertexCount} {rankH : Vertex H → Nat}
    {hlarge : 3 ≤ H.vertexCount}
    (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits) :
    let w := packWordColumns ordResH hWidth
    let D := ((w.dictionary[0]?).map Fin.val).getD 0
    w.dictionary.size = 1 + 3 * D ∧
    w.back.tagAndFirst.size = H.vertexCount + 1 ∧
    w.back.second.size = H.vertexCount + 1 ∧
    w.labels.size = H.vertexCount ∧
    w.entry.size = ordResH.out.tables.next ∧
    w.stop.size = ordResH.out.tables.next ∧
    ordResH.out.tables.next ≤ H.vertexCount + 1 := by
  let w := packWordColumns ordResH hWidth
  let D := ((w.dictionary[0]?).map Fin.val).getD 0
  let s := ofOrderedReader ordResH
  have fitS : H.vertexCount < 2 ^ bits := by omega
  obtain ⟨_, _, G, _, _⟩ := ordResH.index.ok.2.2
  have hRowCnt : FlatPairDictionary.rowCount w.dictionary = s.dict.size :=
    FlatPairDictionary.rowCount_serialize s (dictionary_fits ordResH hWidth)
  have hDEq : D = s.dict.size := hRowCnt
  have hRet : w.dictionary.size = 1 + s.dict.size + s.dict.size + s.slots.size :=
    FlatPairDictionary.retained_words s (dictionary_fits ordResH hWidth)
  have hSlotSz : s.slots.size = s.dict.size := G.slot_size
  have hDictSz : w.dictionary.size = 1 + 3 * D := by omega
  have hBackSz := packBackWords_size s fitS
  have hSBackSz : s.back.size = H.vertexCount + 1 := G.back_size
  have hLabSz : w.labels.size = H.vertexCount := by
    dsimp only [w, packWordColumns]; rw [BoundedScalarArray.size_pack]; exact ordResH.index.ok.1
  have hNodeEq : nodeCount (orderedConfig pH hlarge) ordResH.out = ordResH.out.tables.next :=
    nodeCount_eq_next ordResH.index.ok
  have hEntSz : w.entry.size = ordResH.out.tables.next := by
    dsimp only [w, packWordColumns]; rw [BoundedScalarArray.size_pack, ← hNodeEq]
    exact ordResH.index.reader.layout.endpoints.entry.len
  have hStpSz : w.stop.size = ordResH.out.tables.next := by
    dsimp only [w, packWordColumns]; rw [BoundedScalarArray.size_pack, ← hNodeEq]
    exact ordResH.index.reader.layout.endpoints.stop.len
  have hNextLe : ordResH.out.tables.next ≤ H.vertexCount + 1 := by
    rw [← hNodeEq]; exact nodeCount_le ordResH.index.ok
  exact ⟨hDictSz, hBackSz.1.trans hSBackSz, hBackSz.2.trans hSBackSz, hLabSz, hEntSz, hStpSz, hNextLe⟩

private theorem payload_field_slices (w : WordColumns bits)
    {data : Array (Word bits)} {fp0 : Nat}
    (hFit : fp0 + w.wordCount ≤ data.size)
    (hPay : ∀ k < w.wordCount, data[fp0 + k]? = (RamForestProgram.Finish.packedPayload w)[k]?) :
    let fp1 := fp0 + w.dictionary.size
    let fp2 := fp1 + w.back.tagAndFirst.size
    let fp3 := fp2 + w.back.second.size
    let fp4 := fp3 + w.labels.size
    let fp5 := fp4 + w.entry.size
    (∀ j < w.back.tagAndFirst.size, data[fp1 + j]? = w.back.tagAndFirst[j]?) ∧
    (∀ j < w.back.second.size, data[fp2 + j]? = w.back.second[j]?) ∧
    (∀ j < w.labels.size, data[fp3 + j]? = w.labels[j]?) ∧
    (∀ j < w.entry.size, data[fp4 + j]? = w.entry[j]?) ∧
    (∀ j < w.stop.size, data[fp5 + j]? = w.stop[j]?) := by
  intro fp1 fp2 fp3 fp4 fp5
  have hPsz : (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++
      w.stop).size = w.wordCount := by
    simp only [Array.size_append, WordColumns.wordCount]
  have hPay' : ∀ k < (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++
      w.stop).size, data[fp0 + k]? = (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++
        w.labels ++ w.entry ++ w.stop)[k]? :=
    fun k hk => hPay k (by rw [← hPsz]; exact hk)
  have hAt : ∀ (off : Nat) (xs : Array (Word bits)),
      (∀ j < xs.size,
        (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
          off + j]? = xs[j]?) →
      off + xs.size ≤ w.wordCount →
      ∀ j < xs.size, data[(fp0 + off) + j]? = xs[j]? := by
    intro off xs hSub hOff j hj
    rw [show (fp0 + off) + j = fp0 + (off + j) by omega, hPay' (off + j) (by rw [hPsz]; omega)]
    exact hSub j hj
  have hSubBF : ∀ j < w.back.tagAndFirst.size,
      (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
        w.dictionary.size + j]? = w.back.tagAndFirst[j]? := by
    intro j hj
    rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have hSubBS : ∀ j < w.back.second.size,
      (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
        (w.dictionary.size + w.back.tagAndFirst.size) + j]? = w.back.second[j]? := by
    intro j hj
    rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_right (by simp only [Array.size_append]; omega),
      Array.size_append, show w.dictionary.size + w.back.tagAndFirst.size + j -
        (w.dictionary.size + w.back.tagAndFirst.size) = j by omega]
  have hSubLab : ∀ j < w.labels.size,
      (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
        (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size) + j]? = w.labels[j]? := by
    intro j hj
    rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_right (by simp only [Array.size_append]; omega),
      Array.size_append, Array.size_append,
      show w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + j -
        (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size) = j by omega]
  have hSubEnt : ∀ j < w.entry.size,
      (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
        (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size) + j]? =
        w.entry[j]? := by
    intro j hj
    rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
      Array.getElem?_append_right (by simp only [Array.size_append]; omega),
      Array.size_append, Array.size_append, Array.size_append,
      show w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size + j -
        (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size) = j by omega]
  have hSubStp : ∀ j < w.stop.size,
      (w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels ++ w.entry ++ w.stop)[
        (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size + w.entry.size) + j]? =
        w.stop[j]? := by
    intro j hj
    rw [Array.getElem?_append_right (by simp only [Array.size_append]; omega),
      Array.size_append, Array.size_append, Array.size_append, Array.size_append,
      show w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size +
        w.entry.size + j - (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size +
        w.labels.size + w.entry.size) = j by omega]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hAt _ w.back.tagAndFirst hSubBF (by unfold WordColumns.wordCount; omega)
  · intro j hj
    have h := hAt (w.dictionary.size + w.back.tagAndFirst.size) w.back.second hSubBS
      (by unfold WordColumns.wordCount; omega) j hj
    simpa only [fp1, fp2, fp3, fp4, fp5, Nat.add_assoc] using h
  · intro j hj
    have h := hAt (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size) w.labels hSubLab
      (by unfold WordColumns.wordCount; omega) j hj
    simpa only [fp1, fp2, fp3, fp4, fp5, Nat.add_assoc] using h
  · intro j hj
    have h := hAt (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size)
      w.entry hSubEnt (by unfold WordColumns.wordCount; omega) j hj
    simpa only [fp1, fp2, fp3, fp4, fp5, Nat.add_assoc] using h
  · intro j hj
    have h := hAt (w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size + w.labels.size +
      w.entry.size) w.stop hSubStp (by unfold WordColumns.wordCount; omega) j hj
    simpa only [fp1, fp2, fp3, fp4, fp5, Nat.add_assoc] using h

theorem exitLarge_stage_steps
    (h100 : 100 ≤ 2 ^ bits) (input : Input L16)
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ j : Fin dense.length, (S.ramQuotient j).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (origData[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (j : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs j).length),
      let ea := (countingSortedArcs (1 + (S.childSlice j).length) (S.emittedArcs j))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds j hx).2.1)).symm)
      (origData[emitBaseOf workCap + 3 * n + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (origData[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.headLocal ∧
      (origData[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ j : Fin dense.length,
      OwnerForestPackedRecordAt S j (loopBaseOf workCap) n m forestUsed origData)
    {d : Fin dense.length} {exitUsed : Nat} {s₀ : State L16}
    (hInv : ExitLoopInv S n m Q forestUsed d.val exitUsed s₀)
    (hPC : s₀.pc = offLargeA)
    (hr11 : (reg s₀ r11).val = 1 + (S.childSlice d).length)
    (hLarge : 3 ≤ 1 + (S.childSlice d).length) :
    ∃ (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
      (dataH : Array (Vertex (S.ramQuotient d)))
      (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
      (rankH : Vertex (S.ramQuotient d) → Nat)
      (hlarge : 3 ≤ (S.ramQuotient d).vertexCount)
      (incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
        rankH (orderedVertexAt dataH sizeH i) < rankH (orderedVertexAt dataH sizeH j))
      (covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
        orderedVertexAt dataH sizeH i = v)
      (rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v →
        rankH u < rankH v)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
      (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits)
      (ptrBase : Nat),
      let w := packWordColumns ordResH hWidth
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      let n_d := (S.ramQuotient d).vertexCount
      let N_d := ordResH.out.tables.next
      let loopBase := loopBaseOf workCap
      let stBase := exitSubStateBase loopBase n m
      let inBase := exitSubInBase loopBase n m
      let dataBase := exitSubWorkBase loopBase n m workCap
      let subL := RamForestProgram.layout bits (exitFamilySubInCap workCap) (exitFamilySubWorkCap workCap)
        (by unfold exitFamilySubInCap; omega) (by unfold exitFamilySubWorkCap; omega)
      ∃ (beforeSave staged : State L16) (subIn : Input subL),
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ j < w.wordCount, s₀.data[ptrBase + j]? = (packedPayload w)[j]?) ∧
      N_d ≤ n_d + 1 ∧
      Steps (exitFamilyLoopProgram hi hw h100) input
        (19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) +
          3 * (6 * (S.emittedArcs d).length + 16) + 23) s₀ staged ∧
      staged.pc = offSub ∧
      ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap) loopBase d.val exitUsed beforeSave ∧
      (∀ k : Fin 11, staged.data[stBase + k.val]? = some (reg beforeSave ⟨k.val, Nat.lt_trans k.isLt (by decide : 11 < 16)⟩)) ∧
      (∀ addr < stBase, staged.data[addr]? = s₀.data[addr]?) ∧
      (∀ j, 11 ≤ j → j < 15 → staged.data[stBase + j]? = s₀.data[stBase + j]?) ∧
      (staged.data[inBase]?).map Fin.val = some n_d ∧
      (staged.data[inBase + 2]?).map Fin.val = some N_d ∧
      (∀ j < exitFamilySubInCap workCap, staged.data[inBase + j]? = subIn.words[j]?) ∧
      ExitBuildInput subIn (S.ramQuotient d) ordResH (denseRank S) g.vertexCount := by
  let subCode := exitSubProgram hw h100
  let code := exitFamilyLoopProgram hi hw h100
  have hCodeSize : code.size = 397 + 4 * subCode.size :=
    exitFamilyLoopCodeOf_size (hi := hi) (hw := hw) subCode h100
  let treeBase := prefixTreeBase workCap
  let emitBase := emitBaseOf workCap
  let loopBase := loopBaseOf workCap
  let fpPtrBase := ownerForestPtrsBase loopBase n m + 6 * d.val
  let ep0 := exitArenaBase loopBase n m + exitUsed
  let stBase := exitSubStateBase loopBase n m
  let inBase := exitSubInBase loopBase n m
  let dataBase := exitSubWorkBase loopBase n m workCap
  let n_d := 1 + (S.childSlice d).length
  let m_d := (S.emittedArcs d).length
  have hnPos : 1 ≤ n := by rw [hn]; exact Fin.pos r
  have hQn : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have h4 : 4 * prefixQuarter workCap ≤ workCap := Nat.mul_div_le workCap 4
  have h64 : 64 * (workCap / 64) ≤ workCap := Nat.mul_div_le workCap 64
  have h16 : 16 * (workCap / 16) ≤ workCap := Nat.mul_div_le workCap 16
  have hWorkEnd : exitSubWorkBase loopBase n m workCap + workCap / 16 ≤ workCap :=
    exitSubWorkEnd_le_workCap hCap
  have hTreeFit : treeBase + staticTreeWords Q ≤ workCap := by
    first | (simp only [treeBase, prefixTreeBase, staticTreeWords]; omega) | omega
  have hEmitFit : emitBase + emitterWorkWords n m ≤ workCap := by
    first | (simp only [emitBase, emitBaseOf, emitterWorkWords]; omega) | omega
  have hDisjEmit : emitBase + emitterWorkWords n m ≤ loopBase := by
    first | (simp only [emitBase, emitBaseOf, loopBase, loopBaseOf, emitterWorkWords, prefixQuarter]; omega) | omega
  have hdQ : d.val < Q := by rw [hQ]; exact d.isLt
  have hInData : dataBase = inBase + workCap / 64 := rfl
  have hDataEnd : dataBase + workCap / 16 ≤ workCap := hWorkEnd
  have hWork64 : 12 ≤ workCap / 64 := by omega
  have hWork16 : 2 ≤ workCap / 16 := by omega
  have hDataGt : inBase + 4 ≤ dataBase := by omega
  have hPtrIn : exitPtrsBase loopBase n m < inBase := by
    simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]
    omega
  have hFAEnd : forestArenaBase loopBase n m + forestUsed ≤ exitPtrsBase loopBase n m := by
    have h := forestArenaEnd_eq loopBase n m
    unfold exitPtrsBase
    omega
  have hDisjEmitIn : emitBase + emitterWorkWords n m ≤ inBase := by
    have : loopBase ≤ exitPtrsBase loopBase n m := by first | (simp only [exitPtrsBase]; omega) | omega
    first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega
  have hDisjFP : ownerForestPtrsBase loopBase n m + 6 * Q ≤ exitArenaBase loopBase n m := by
    have := ownerForestPtrsBase_add_44n loopBase n m
    first | (simp only [exitArenaBase]; omega) | omega
  have hEndEP : exitPtrsBase loopBase n m + 3 * Q ≤ exitArenaBase loopBase n m := by
    first | (simp only [exitArenaBase]; omega) | omega
  have hEnter : stBase + 16 = inBase := rfl
  have hArenaIn : exitArenaBase loopBase n m ≤ inBase := by
    simp only [inBase, exitSubInBase, stBase, exitSubStateBase]
    omega
  have hArena48 : exitArenaBase loopBase n m + 48 * n ≤ stBase := by
    first | (simp only [stBase, exitSubStateBase]; omega) | omega
  have hNdLe : n_d ≤ n := by rw [hn]; exact ramQuotient_vertexCount_le S d
  have hmEq : (S.ramQuotient d).arcCount = m_d := ramQuotient_arcCount_eq S d
  have hmLe : m_d ≤ m := by rw [hm, ← hmEq]; exact ramQuotient_arcCount_le S d
  -- Unpack `OwnerForestPackedRecordAt` at `d`
  have hRecD := hRecs d
  dsimp only [OwnerForestPackedRecordAt] at hRecD
  rw [ite_eq_right (by omega : ¬ n_d < 3)] at hRecD
  obtain ⟨pH, dataH, sizeH, rankH, hlargeH, incH, covH, rArcH, ordResH, hWidth, ptrBase,
    hIdx, hwCnt, hfaLo, hfaHi, hfp0, hfp1, hfp2, hfp3, hfp4, hfp5, hPay⟩ := hRecD
  let wCols := packWordColumns ordResH hWidth
  let N_d := ordResH.out.tables.next
  obtain ⟨hwDictSz, hwBFSz, hwBSSz, hwLabSz, hwEntSz, hwStpSz, hNextLe⟩ :=
    wordCols_sizes ordResH hWidth
  have hwNextPos : 1 ≤ N_d := (B_next_pos (hFlat d) incH covH rArcH ordResH).1
  change wCols.wordCount ≤ 19 * n_d at hwCnt
  change ptrBase + wCols.wordCount ≤ forestArenaBase loopBase n m + forestUsed at hfaHi
  change wCols.dictionary.size = 1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0) at hwDictSz
  change wCols.back.tagAndFirst.size = n_d + 1 at hwBFSz
  change wCols.back.second.size = n_d + 1 at hwBSSz
  change wCols.labels.size = n_d at hwLabSz
  change wCols.entry.size = N_d at hwEntSz
  change wCols.stop.size = N_d at hwStpSz
  change N_d ≤ n_d + 1 at hNextLe
  have hSlices := payload_field_slices wCols (data := s₀.data) (fp0 := ptrBase) (by
    rw [hInv.szEq]
    omega) (fun k hk => by
      rw [hInv.outerFrame (ptrBase + k) (by first | (simp only [forestArenaBase, ownerForestPtrsBase, loopBase, loopBaseOf, prefixQuarter] at hfaLo ⊢; omega) | omega)
        (by have := forestArenaEnd_eq loopBase n m; first | (simp only [exitPtrsBase]; omega) | omega)]
      exact hPay k hk)
  -- `origData` matches for `fp0..fp5`, `qStarts`, `arcs`
  have hOrigToS0 : ∀ addr, 3 ≤ addr → addr < exitPtrsBase loopBase n m →
      s₀.data[addr]? = origData[addr]? := hInv.outerFrame
  have hFPBounds : ∀ k < 6, 3 ≤ fpPtrBase + k ∧ fpPtrBase + k < exitPtrsBase loopBase n m := by
    intro k hk
    have h44 := ownerForestPtrsBase_add_44n loopBase n m
    have hLo : 3 ≤ ownerForestPtrsBase loopBase n m := by
      simp only [ownerForestPtrsBase, loopSortEntryBase, loopCursorBase, loopDegBase]
      omega
    dsimp only [fpPtrBase]
    omega
  have hfp4_s0 : (s₀.data[fpPtrBase + 4]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) +
        2 * (n_d + 1) + n_d) := by
    rw [hOrigToS0 _ (hFPBounds 4 (by decide)).1 (hFPBounds 4 (by decide)).2]; exact hfp4
  have hfp5_s0 : (s₀.data[fpPtrBase + 5]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) +
        2 * (n_d + 1) + n_d + wCols.entry.size) := by
    rw [hOrigToS0 _ (hFPBounds 5 (by decide)).1 (hFPBounds 5 (by decide)).2]; exact hfp5
  let fp4Val := ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + 2 * (n_d + 1) + n_d
  let fp5Val := fp4Val + N_d
  have hfp5Minus4 : fp5Val - fp4Val = N_d := by
    dsimp only [fp5Val]; omega
  -- 1. `exitLargeA`
  have hSubInFit : inBase + (workCap / 64) ≤ workCap := by
    try simp only [inBase]; have := hWorkEnd; unfold exitSubWorkBase at this; omega
  have hInCapFit : 4 + n_d + 4 * N_d + 3 * m_d ≤ workCap / 64 := by
    have := exitSubInCap_fits hCap hNdLe hmLe
    omega
  have hQS0 : (s₀.data[emitBase + 2 * n + d.val]?).map Fin.val = some (qStartFn S d.val) := by
    rw [hOrigToS0 _ (by first | (simp only [emitBase, emitBaseOf, prefixQuarter]; omega) | omega)
      (by have := d.isLt; first | (simp only [emitBase, emitBaseOf, loopBase, loopBaseOf, exitPtrsBase, loopWorkWords, prefixQuarter]; omega) | omega)]
    exact hQStarts d.val (by omega)
  have hQS1 : (s₀.data[emitBase + 2 * n + (d.val + 1)]?).map Fin.val = some (qStartFn S (d.val + 1)) := by
    rw [hOrigToS0 _ (by first | (simp only [emitBase, emitBaseOf, prefixQuarter]; omega) | omega)
      (by have := d.isLt; first | (simp only [emitBase, emitBaseOf, loopBase, loopBaseOf, exitPtrsBase, loopWorkWords, prefixQuarter]; omega) | omega)]
    exact hQStarts (d.val + 1) (by omega)
  obtain ⟨sA, hsA, pcA, szA, regsA, rA11, rA12, rA15, hIn0A, hIn1A, hW0A, hFrA⟩ :=
    exitLargeA_steps (code := code) (input := input) h100 (sp_largeA subCode h100)
      (by rw [hCodeSize]; first | (simp only [offLargeB]; omega) | omega)
      S hm hQ hQn d hPC hInv.szEq hInv.regs hr11
      hInv.statePtr hInv.st13 hInv.st14 hQS0 hQS1 hEmitFit hDisjEmit
      (show inBase + 2 ≤ dataBase from by omega)
      (show dataBase + 2 ≤ workCap from by omega) hBits
  change ∀ addr, addr ≠ inBase → addr ≠ inBase + 1 → addr ≠ dataBase →
    sA.data[addr]? = s₀.data[addr]? at hFrA
  have hMemEq_A : ∀ addr, addr < inBase → sA.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    exact hFrA addr (by omega) (by omega) (by omega)
  have hSt11A : (sA.data[stBase + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [hMemEq_A _ (by first | (simp only [stBase, inBase, exitSubInBase]; omega) | omega)]; exact hInv.st11
  have hfp4A : (sA.data[fpPtrBase + 4]?).map Fin.val = some fp4Val := by
    rw [hMemEq_A _ (by have := (hFPBounds 4 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]
    exact hfp4_s0
  have hfp5A : (sA.data[fpPtrBase + 5]?).map Fin.val = some fp5Val := by
    rw [hMemEq_A _ (by have := (hFPBounds 5 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]
    simpa only [fp4Val, fp5Val, N_d, ← hwEntSz] using hfp5_s0
  have hWcExact : fp5Val + N_d = ptrBase + wCols.wordCount := by
    unfold fp5Val fp4Val WordColumns.wordCount
    rw [hwDictSz, hwBFSz, hwBSSz, hwLabSz, hwEntSz, hwStpSz]
    omega
  have hfp5Lt : fp5Val < workCap := by omega
  -- 2. `exitLargeB`
  obtain ⟨sB, hsB, pcB, szB, regsB, rB15, hW1B, hIn2B, hIn3B, hFrB⟩ :=
    exitLargeB_steps (code := code) (input := input) h100 (sp_largeB subCode h100)
      (by rw [hCodeSize]; first | (simp only [offFp]; omega) | omega)
      pcA szA regsA rA11 rA12 rA15 hSt11A hfp4A hfp5A (by omega) hfp5Lt hdQ hQn
      (show inBase + 4 ≤ dataBase from hDataGt)
      (show dataBase + 2 ≤ workCap from by omega) hDisjFP
      (show exitArenaBase loopBase n m ≤ workCap from by omega) hBits
  change ∀ addr, addr ≠ dataBase + 1 → addr ≠ inBase + 2 → addr ≠ inBase + 3 →
    sB.data[addr]? = sA.data[addr]? at hFrB
  have hPreCopyLt : ∀ addr, addr < inBase + 4 → addr ≠ inBase → addr ≠ inBase + 1 →
      addr ≠ inBase + 2 → addr ≠ inBase + 3 → sB.data[addr]? = s₀.data[addr]? := by
    intro addr hlt h0 h1 h2 h3
    rw [hFrB addr (by omega) h2 h3,
      hFrA addr h0 h1 (by omega)]
  have hMem0B : (sB.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hPreCopyLt _ (by first | (simp only [inPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [inPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [inPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [inPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [inPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)]
    exact hInv.inPtr
  have hMem1B : (sB.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hPreCopyLt _ (by first | (simp only [dataPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [dataPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [dataPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [dataPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)
      (by first | (simp only [dataPtrAddr, inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords]; omega) | omega)]
    exact hInv.dataPtr
  have hIn0B : (sB.data[inBase]?).map Fin.val = some n_d := by
    rw [hFrB _ (by omega) (by omega) (by omega)]; exact hIn0A
  have hIn1B : (sB.data[inBase + 1]?).map Fin.val = some m_d := by
    rw [hFrB _ (by omega) (by omega) (by omega)]; exact hIn1A
  have hIn2B' : (sB.data[inBase + 2]?).map Fin.val = some N_d := by
    rwa [hfp5Minus4] at hIn2B
  have hW0B : (sB.data[dataBase]?).map Fin.val = some (qStartFn S d.val) := by
    rw [hFrB _ (by omega) (by omega) (by omega)]
    exact hW0A
  have hKeepPreB : ∀ addr, addr < inBase → sB.data[addr]? = s₀.data[addr]? :=
    fun addr ha => hPreCopyLt addr (by omega) (by omega) (by omega) (by omega) (by omega)
  change (reg sB r15).val = inBase + 4 at rB15
  have hIn03B : (sB.data[inBase]?).map Fin.val = some n_d ∧
      (sB.data[inBase + 1]?).map Fin.val = some m_d ∧
      (sB.data[inBase + 2]?).map Fin.val = some N_d ∧
      (sB.data[inBase + 3]?).map Fin.val = some n := ⟨hIn0B, hIn1B, hIn2B', hIn3B⟩
  -- Source bounds for `fp0..fp4`:
  have hfaEnd : forestArenaBase loopBase n m + forestUsed ≤ inBase := by
    have := forestArenaEnd_eq loopBase n m
    first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase]; omega) | omega
  have hfp1_s0 : (s₀.data[fpPtrBase + 1]?).map Fin.val = some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0))) := by
    rw [hOrigToS0 _ (hFPBounds 1 (by decide)).1 (hFPBounds 1 (by decide)).2]; exact hfp1
  have hfp2_s0 : (s₀.data[fpPtrBase + 2]?).map Fin.val = some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + (n_d + 1)) := by
    rw [hOrigToS0 _ (hFPBounds 2 (by decide)).1 (hFPBounds 2 (by decide)).2]; exact hfp2
  have hfp3_s0 : (s₀.data[fpPtrBase + 3]?).map Fin.val = some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + 2 * (n_d + 1)) := by
    rw [hOrigToS0 _ (hFPBounds 3 (by decide)).1 (hFPBounds 3 (by decide)).2]; exact hfp3
  let fp1Val := ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0))
  let fp2Val := fp1Val + (n_d + 1)
  let fp3Val := fp1Val + 2 * (n_d + 1)
  have hfp1B : (sB.data[fpPtrBase + 1]?).map Fin.val = some fp1Val := by
    rw [hKeepPreB _ (by have := (hFPBounds 1 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]; exact hfp1_s0
  have hfp2B : (sB.data[fpPtrBase + 2]?).map Fin.val = some fp2Val := by
    rw [hKeepPreB _ (by have := (hFPBounds 2 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]; exact hfp2_s0
  have hfp3B : (sB.data[fpPtrBase + 3]?).map Fin.val = some fp3Val := by
    rw [hKeepPreB _ (by have := (hFPBounds 3 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]; exact hfp3_s0
  have hfp4B : (sB.data[fpPtrBase + 4]?).map Fin.val = some fp4Val := by
    rw [hKeepPreB _ (by have := (hFPBounds 4 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]; exact hfp4_s0
  have hfp5B : (sB.data[fpPtrBase + 5]?).map Fin.val = some fp5Val := by
    rw [hKeepPreB _ (by have := (hFPBounds 5 (by decide)).2; first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega)]
    simpa only [fp4Val, fp5Val, N_d, ← hwEntSz] using hfp5_s0
  have hWcBnd : fp5Val + N_d ≤ inBase := by omega
  have hFp3End : fp3Val + n_d ≤ fp5Val + N_d := by
    dsimp only [fp3Val, fp2Val, fp1Val, fp5Val, fp4Val]
    omega
  have hFp1End : fp1Val + N_d ≤ fp5Val + N_d := by
    dsimp only [fp1Val, fp5Val, fp4Val]
    omega
  have hFp2End : fp2Val + N_d ≤ fp5Val + N_d := by
    dsimp only [fp2Val, fp1Val, fp5Val, fp4Val]
    omega
  have hFp4End : fp4Val + N_d ≤ fp5Val + N_d := by
    dsimp only [fp5Val]
    omega
  have hCopyEnd : inBase + 4 + n_d + 4 * N_d + 3 * m_d ≤ dataBase := by omega
  have hInGt : 2 < inBase := by simp only [inBase, exitSubInBase]; omega
  have hFpLast : fpPtrBase + 5 < inBase := by
    have h := (hFPBounds 5 (by decide)).2
    omega
  obtain ⟨sF4, hFpSteps, pcF4, szF4, regsF4, hR15F4, hCpF0, hCpF1, hCpF2, hCpF3, hCpF4,
      hKeepHeaderF4, hKeepWorkF4⟩ :=
    stageForestColumns_steps input h100 pcB szB regsB hMem0B hMem1B hW1B hIn0B hIn2B' rB15
      hFpLast hfp1B hfp2B hfp3B hfp4B hfp5B
      (show fp1Val + N_d ≤ inBase from by omega)
      (show fp2Val + N_d ≤ inBase from by omega)
      (show fp3Val + n_d ≤ inBase from by omega)
      (show fp4Val + N_d ≤ inBase from by omega)
      hWcBnd (show inBase + 4 + n_d + 4 * N_d ≤ dataBase from by omega)
      (show dataBase ≤ workCap from by omega) hBits
  have hKeepBeforeF4 (addr : Nat) (ha : addr < inBase) : sF4.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF4 addr (show addr < inBase + 4 from by omega)
  have hMem0F4 : (sF4.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeF4 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0B
  have hMem1F4 : (sF4.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeF4 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1B
  have hW0_F4 : (sF4.data[dataBase]?).map Fin.val = some (qStartFn S d.val) := by
    rw [hKeepWorkF4 dataBase (Nat.le_refl _)]
    exact hW0B
  have hIn1F4 : (sF4.data[inBase + 1]?).map Fin.val = some m_d := by
    rw [hKeepHeaderF4 (inBase + 1) (show inBase + 1 < inBase + 4 from by omega)]
    exact hIn1B
  have hmQStartBnd : qStartFn S d.val + m_d ≤ m := by
    rw [← qStartFn_succ S d.isLt, hm]; exact qStartFn_le_arcCount S (d.val + 1)
  -- Stage the three emitted arc columns after the forest columns.
  obtain ⟨sE2, hEmitSteps, pcE2, szE2, regsE2, hEmitPayload, hKeepBeforeEmit⟩ :=
    stageEmitColumns_steps input h100 (sF4 := sF4) (n_d := n_d) (N_d := N_d)
      (by rw [pcF4]; change offFp 4 + 19 = offEmit 0; rfl) szF4 regsF4
      hMem0F4 hMem1F4 hW0_F4 hIn1F4 hR15F4 hmQStartBnd hDisjEmitIn hCopyEnd
      (show dataBase ≤ workCap from by omega) hBits
  have hKeepHeaderE2 (addr : Nat) (ha : addr < inBase + 4) : sE2.data[addr]? = sB.data[addr]? :=
    (hKeepBeforeEmit addr (by change addr < inBase + 4 + n_d + 4 * N_d; omega)).trans
      (hKeepHeaderF4 addr ha)
  have hKeepPreS0_E2 (addr : Nat) (ha : addr < inBase) : sE2.data[addr]? = s₀.data[addr]? :=
    (hKeepHeaderE2 addr (by omega)).trans (hKeepPreB addr ha)
  have hStToIn : inBase = stBase + 16 := rfl
  have hInEnd : inBase + exitFamilySubInCap workCap ≤ workCap := by
    change inBase + workCap / 64 ≤ workCap
    omega
  -- 5. `exitSaveRegs`
  obtain ⟨sSaved, hsSave, pcSave, szSave, hSavedSlots, hFrSave⟩ :=
    exitSaveRegs_steps (code := code) (input := input) h100 (sp_saveRegs subCode h100)
      (by rw [hCodeSize]; first | (simp only [offSub]; omega) | omega)
      pcE2 szE2 regsE2
      (by rw [hKeepPreS0_E2 statePtrAddr (by simp only [statePtrAddr]; omega)]; exact hInv.statePtr)
      (show stBase + 11 ≤ workCap from by omega) hBits
  have hInEqSave : ∀ j < 4 + n_d + 4 * N_d + 3 * m_d,
      sSaved.data[inBase + j]? = sE2.data[inBase + j]? := by
    intro j hj
    exact hFrSave (inBase + j) (Or.inr (show stBase + 11 ≤ inBase + j from by omega))
  have hKeepLowSave : ∀ addr, addr < stBase → sSaved.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    rw [hFrSave addr (Or.inl ha)]
    exact hKeepPreS0_E2 addr (by omega)
  have hSt11Save : (sSaved.data[stBase + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [hFrSave (stBase + 11) (Or.inr (show stBase + 11 ≤ stBase + 11 from by omega)),
      hKeepPreS0_E2 (stBase + 11) (by omega)]; exact hInv.st11
  have hSt12Save : (sSaved.data[stBase + 12]?).map Fin.val = some (exitArenaBase loopBase n m) := by
    rw [hFrSave (stBase + 12) (Or.inr (show stBase + 11 ≤ stBase + 12 from by omega)),
      hKeepPreS0_E2 (stBase + 12) (by omega)]; exact hInv.st12
  have hSt13Save : (sSaved.data[stBase + 13]?).map Fin.val = some inBase := by
    rw [hFrSave (stBase + 13) (Or.inr (show stBase + 11 ≤ stBase + 13 from by omega)),
      hKeepPreS0_E2 (stBase + 13) (by omega)]; exact hInv.st13
  have hSt14Save : (sSaved.data[stBase + 14]?).map Fin.val = some dataBase := by
    rw [hFrSave (stBase + 14) (Or.inr (show stBase + 11 ≤ stBase + 14 from by omega)),
      hKeepPreS0_E2 (stBase + 14) (by omega)]; exact hInv.st14
  -- 6. Construct `subIn` and `subStart0`, prove `ExitBuildInput`, `run_exitSummaryBuild`, `liftProgram_relocated_steps`
  let subIn : Input (RamForestProgram.layout bits (exitFamilySubInCap workCap) (exitFamilySubWorkCap workCap)
      (by first | (simp only [exitFamilySubInCap]; omega) | omega) (by first | (simp only [exitFamilySubWorkCap]; omega) | omega)) :=
    ⟨Array.ofFn (fun i : Fin (exitFamilySubInCap workCap) => sSaved.data[inBase + i.val]?.getD 0),
      Array.size_ofFn⟩
  have hSubInWord : ∀ j (hj : j < exitFamilySubInCap workCap),
      subIn.words[j]'(by rw [subIn.size_eq]; exact hj) = (sSaved.data[inBase + j]?.getD 0) := by
    intro j hj; dsimp only [subIn]; rw [Array.getElem_ofFn]
  have hSubInSome : ∀ j (hj : j < exitFamilySubInCap workCap),
      (subIn.words[j]?).map Fin.val = (sSaved.data[inBase + j]?).map Fin.val := by
    intro j hj
    rw [getElem?_pos subIn.words j (by rw [subIn.size_eq]; exact hj), hSubInWord j hj]
    have hBnd : inBase + j < sSaved.data.size := by rw [szSave]; omega
    obtain ⟨w, hw⟩ : ∃ w, sSaved.data[inBase + j]? = some w :=
      ⟨sSaved.data[inBase + j]'hBnd, getElem?_pos sSaved.data (inBase + j) hBnd⟩
    simp only [hw, Option.getD_some, Option.map_some]
  have hWordFit (j : Nat) (hj : j < 4 + n_d + 4 * N_d + 3 * m_d) :
      j < exitFamilySubInCap workCap :=
    Nat.lt_of_lt_of_le hj hInCapFit
  have hHeaderRead (j : Nat) (hj : j < 4) :
      (subIn.words[j]?).map Fin.val = (sB.data[inBase + j]?).map Fin.val := by
    rw [hSubInSome j (hWordFit j (by omega)), hInEqSave j (by omega),
      hKeepHeaderE2 (inBase + j) (by omega)]
  have hIn0_B : (subIn.words[0]?).map Fin.val = some n_d := by
    simpa only [Nat.add_zero, hIn0B] using hHeaderRead 0 (by decide)
  have hIn1_B : (subIn.words[1]?).map Fin.val = some m_d :=
    (hHeaderRead 1 (by decide)).trans hIn1B
  have hIn2_B : (subIn.words[2]?).map Fin.val = some N_d :=
    (hHeaderRead 2 (by decide)).trans hIn2B'
  have hIn3_B : (subIn.words[3]?).map Fin.val = some n :=
    (hHeaderRead 3 (by decide)).trans hIn3B
  have hBeforeEmit (addr : Nat) (ha : addr < inBase + 4 + n_d + 4 * N_d) :
      sE2.data[addr]? = sF4.data[addr]? := hKeepBeforeEmit addr ha
  have hBuildIn : ExitBuildInput subIn (S.ramQuotient d) ordResH (denseRank S) g.vertexCount := by
    as_aux_lemma =>
      refine exitBuildInput_of_staged S d ordResH (hWidth := hWidth) subIn
        (by change 4 + n_d + 4 * N_d + 3 * (S.ramQuotient d).arcCount ≤ exitFamilySubInCap workCap
            rw [hmEq]; exact hInCapFit)
        (ramQuotient_vertexCount_le S d)
        hIn0_B (by change (subIn.words[1]?).map Fin.val = some (S.ramQuotient d).arcCount; rw [hmEq]; exact hIn1_B)
        hIn2_B (hn ▸ hIn3_B) ?_ ?_ ?_ ?_ ?_ ?_
      · intro y
        have hj : y.val < n_d := y.isLt
        let j := 4 + y.val
        have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
        have hSrcBefore : fp3Val + y.val < inBase := by
          have := hFp3End
          omega
        change (subIn.words[j]?).map Fin.val = _
        rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
          hBeforeEmit (inBase + j) (by dsimp only [j]; omega),
          show inBase + j = (inBase + 4) + y.val by dsimp only [j]; omega,
          hCpF0 y.val hj, hKeepPreB (fp3Val + y.val) hSrcBefore]
        have hSl := hSlices.2.2.1 y.val (by rw [hwLabSz]; exact hj)
        have hFpEq : fp3Val = ptrBase + wCols.dictionary.size + wCols.back.tagAndFirst.size + wCols.back.second.size := by
          simp only [hwDictSz, hwBFSz, hwBSSz, fp3Val, fp1Val, Nat.two_mul, Nat.add_assoc]
        rw [← hFpEq] at hSl
        exact congrArg (Option.map Fin.val) hSl
      · intro u
        have hj : u.val < N_d := u.isLt
        let j := 4 + n_d + u.val
        have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
        have hSrcBefore : fp1Val + u.val < inBase := by
          have := hFp1End
          omega
        change (subIn.words[j]?).map Fin.val = _
        rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
          hBeforeEmit (inBase + j) (by dsimp only [j]; omega),
          show inBase + j = (inBase + 4 + n_d) + u.val by dsimp only [j]; omega,
          hCpF1 u.val hj, hKeepPreB (fp1Val + u.val) hSrcBefore]
        have hSl := hSlices.1 u.val (by rw [hwBFSz]; exact Nat.lt_of_lt_of_le hj hNextLe)
        have hFpEq : fp1Val = ptrBase + wCols.dictionary.size := by
          dsimp only [fp1Val]
          rw [hwDictSz] <;> omega
        rw [← hFpEq] at hSl
        exact congrArg (Option.map Fin.val) hSl
      · intro u
        have hj : u.val < N_d := u.isLt
        let j := 4 + n_d + N_d + u.val
        have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
        have hSrcBefore : fp2Val + u.val < inBase := by
          have := hFp2End
          omega
        change (subIn.words[j]?).map Fin.val = _
        rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
          hBeforeEmit (inBase + j) (by dsimp only [j]; omega),
          show inBase + j = (inBase + 4 + n_d + N_d) + u.val by dsimp only [j]; omega,
          hCpF2 u.val hj, hKeepPreB (fp2Val + u.val) hSrcBefore]
        have hSl := hSlices.2.1 u.val (by rw [hwBSSz]; exact Nat.lt_of_lt_of_le hj hNextLe)
        have hFpEq : fp2Val = ptrBase + wCols.dictionary.size + wCols.back.tagAndFirst.size := by
          dsimp only [fp2Val, fp1Val]
          rw [hwDictSz, hwBFSz] <;> omega
        rw [← hFpEq] at hSl
        exact congrArg (Option.map Fin.val) hSl
      · intro u
        have hj : u.val < N_d := u.isLt
        let j := 4 + n_d + 2 * N_d + u.val
        have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
        have hSrcBefore : fp4Val + u.val < inBase := by
          have := hFp4End
          omega
        change (subIn.words[j]?).map Fin.val = _
        rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
          hBeforeEmit (inBase + j) (by dsimp only [j]; omega),
          show inBase + j = (inBase + 4 + n_d + 2 * N_d) + u.val by dsimp only [j]; omega,
          hCpF3 u.val hj, hKeepPreB (fp4Val + u.val) hSrcBefore]
        have hSl := hSlices.2.2.2.1 u.val (by rw [hwEntSz]; exact hj)
        have hFpEq : fp4Val = ptrBase + wCols.dictionary.size + wCols.back.tagAndFirst.size + wCols.back.second.size + wCols.labels.size := by
          simp only [hwDictSz, hwBFSz, hwBSSz, hwLabSz, fp4Val, Nat.two_mul, Nat.add_assoc]
        rw [← hFpEq] at hSl
        exact congrArg (Option.map Fin.val) hSl
      · intro u
        have hj : u.val < N_d := u.isLt
        let j := 4 + n_d + 3 * N_d + u.val
        have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
        have hSrcBefore : fp5Val + u.val < inBase := by
          omega
        change (subIn.words[j]?).map Fin.val = _
        rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
          hBeforeEmit (inBase + j) (by dsimp only [j]; omega),
          show inBase + j = (inBase + 4 + n_d + 3 * N_d) + u.val by dsimp only [j]; omega,
          hCpF4 u.val hj, hKeepPreB (fp5Val + u.val) hSrcBefore]
        have hSl := hSlices.2.2.2.2 u.val (by rw [hwStpSz]; exact hj)
        have hFpEq : fp5Val = ptrBase + wCols.dictionary.size + wCols.back.tagAndFirst.size + wCols.back.second.size + wCols.labels.size + wCols.entry.size := by
          simp only [hwDictSz, hwBFSz, hwBSSz, hwLabSz, hwEntSz, fp5Val, fp4Val, Nat.two_mul, Nat.add_assoc]
        rw [← hFpEq] at hSl
        exact congrArg (Option.map Fin.val) hSl
      · intro p hp
        have hp' : p < m_d := hp
        have hArcD := hArcs d p hp'
        have hEmitEnd : emitBase + emitterWorkWords n m ≤ inBase := hDisjEmitIn
        simp only [emitterWorkWords] at hEmitEnd
        have hEmitLoop : emitBase + (3 * n + 3 * m + 3) ≤ loopBase := hDisjEmit
        have hLoopPtr : loopBase ≤ exitPtrsBase loopBase n m := by simp only [exitPtrsBase]; omega
        have hEmitLo : 3 ≤ emitBase := by simp only [emitBase, emitBaseOf, prefixQuarter]; omega
        refine ⟨?_, ?_, ?_⟩
        · let j := 4 + n_d + 4 * N_d + p
          have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
          have hSrc : emitBase + 3 * n + 1 + qStartFn S d.val + p < inBase := by omega
          have hCopy := hEmitPayload ⟨0, by decide⟩ p hp'
          simp only [Fin.val_mk, Nat.zero_mul, Nat.add_zero] at hCopy
          change (subIn.words[j]?).map Fin.val = _
          rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
            show inBase + j = (inBase + 4 + n_d + 4 * N_d) + p by dsimp only [j]; omega,
            hCopy]
          change (sF4.data[emitBase + 3 * n + 1 + qStartFn S d.val + p]?).map Fin.val = _
          rw [hKeepBeforeF4 (emitBase + 3 * n + 1 + qStartFn S d.val + p) hSrc,
            hKeepPreB (emitBase + 3 * n + 1 + qStartFn S d.val + p) hSrc,
            hOrigToS0 (emitBase + 3 * n + 1 + qStartFn S d.val + p) (by omega) (by omega)]
          simpa only [Nat.zero_mul, Nat.add_zero, Nat.add_assoc] using hArcD.1
        · let j := 4 + n_d + 4 * N_d + m_d + p
          have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
          have hSrc : emitBase + 3 * n + 1 + m + qStartFn S d.val + p < inBase := by omega
          have hCopy := hEmitPayload ⟨1, by decide⟩ p hp'
          simp only [Fin.val_mk, Nat.one_mul] at hCopy
          change (subIn.words[j]?).map Fin.val = _
          rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
            show inBase + j = (inBase + 4 + n_d + 4 * N_d + m_d) + p by dsimp only [j]; omega,
            hCopy]
          change (sF4.data[emitBase + 3 * n + 1 + m + qStartFn S d.val + p]?).map Fin.val = _
          rw [hKeepBeforeF4 (emitBase + 3 * n + 1 + m + qStartFn S d.val + p) hSrc,
            hKeepPreB (emitBase + 3 * n + 1 + m + qStartFn S d.val + p) hSrc,
            hOrigToS0 (emitBase + 3 * n + 1 + m + qStartFn S d.val + p) (by omega) (by omega)]
          simpa only [Nat.one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hArcD.2.1
        · let j := 4 + n_d + 4 * N_d + 2 * m_d + p
          have hjFit : j < 4 + n_d + 4 * N_d + 3 * m_d := by dsimp only [j]; omega
          have hSrc : emitBase + 3 * n + 1 + 2 * m + qStartFn S d.val + p < inBase := by omega
          have hCopy := hEmitPayload ⟨2, by decide⟩ p hp'
          simp only [Fin.val_mk] at hCopy
          change (subIn.words[j]?).map Fin.val = _
          rw [hSubInSome j (hWordFit j hjFit), hInEqSave j hjFit,
            show inBase + j = (inBase + 4 + n_d + 4 * N_d + 2 * m_d) + p by dsimp only [j]; omega,
            hCopy]
          change (sF4.data[emitBase + 3 * n + 1 + 2 * m + qStartFn S d.val + p]?).map Fin.val = _
          rw [hKeepBeforeF4 (emitBase + 3 * n + 1 + 2 * m + qStartFn S d.val + p) hSrc,
            hKeepPreB (emitBase + 3 * n + 1 + 2 * m + qStartFn S d.val + p) hSrc,
            hOrigToS0 (emitBase + 3 * n + 1 + 2 * m + qStartFn S d.val + p) (by omega) (by omega)]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hArcD.2.2
  have hFrames (j : Nat) (hj1 : 11 ≤ j) (hj2 : j < 15) :
      sSaved.data[stBase + j]? = s₀.data[stBase + j]? := by
    rw [hFrSave (stBase + j) (Or.inr (show stBase + 11 ≤ stBase + j from by omega)),
      hKeepPreS0_E2 (stBase + j) (by omega)]
  have hEqInput (j : Nat) (hj : j < exitFamilySubInCap workCap) :
      sSaved.data[inBase + j]? = subIn.words[j]? := by
    have hjIn : j < subIn.words.size := by rw [subIn.size_eq]; exact hj
    have hjB : inBase + j < sSaved.data.size := by rw [szSave]; omega
    rw [getElem?_pos subIn.words j hjIn, hSubInWord j hj, getElem?_pos sSaved.data (inBase + j) hjB]
    rfl
  have hStaged0 : (sSaved.data[inBase]?).map Fin.val = some n_d := by
    have h := hHeaderRead 0 (by decide)
    rw [Nat.add_zero] at h
    have hW := hSubInSome 0 (hWordFit 0 (by omega))
    rw [Nat.add_zero] at hW
    exact hW.symm.trans hIn0_B
  have hStaged2 : (sSaved.data[inBase + 2]?).map Fin.val = some N_d :=
    (hSubInSome 2 (hWordFit 2 (by omega))).symm.trans hIn2_B
  have hStagedCost : Steps code input (19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) +
      3 * (6 * m_d + 16) + 23) s₀ sSaved := by
    simpa only [Nat.add_assoc] using
      hsA.append (hsB.append (hFpSteps.append (hEmitSteps.append hsSave)))
  have hfp0_s0 : (s₀.data[fpPtrBase]?).map Fin.val = some ptrBase := by
    have hb : 3 ≤ fpPtrBase ∧ fpPtrBase < exitPtrsBase loopBase n m := by
      simpa only [Nat.add_zero] using hFPBounds 0 (by decide)
    rw [hOrigToS0 fpPtrBase hb.1 hb.2]
    exact hfp0
  refine ⟨pH, dataH, sizeH, rankH, hlargeH, incH, covH, rArcH, ordResH, hWidth, ptrBase,
    sE2, sSaved, subIn, hfaLo, hfaHi, hfp0_s0,
    hfp1_s0, hfp2_s0, ?_, hfp4_s0, hfp5_s0, ?_, hNextLe, hStagedCost, pcSave,
    regsE2, hSavedSlots, hKeepLowSave, hFrames, hStaged0, hStaged2, hEqInput, hBuildIn⟩
  · change (s₀.data[fpPtrBase + 3]?).map Fin.val = some fp3Val
    exact hfp3_s0
  · intro k hk
    change k < wCols.wordCount at hk
    have hBefore : ptrBase + k < exitPtrsBase loopBase n m := by omega
    have hLo : 3 ≤ ptrBase + k := by
      change forestArenaBase loopBase n m ≤ ptrBase at hfaLo
      simp only [forestArenaBase, ownerForestPtrsBase, loopSortEntryBase, loopCursorBase,
        loopDegBase, loopSubStateBase, loopSubWorkBase, rawInputCap] at hfaLo
      omega
    rw [hOrigToS0 (ptrBase + k) hLo hBefore]
    exact hPay k hk

end LoopInductionAndMain
end PaperB.RamExitFamilyLoop
