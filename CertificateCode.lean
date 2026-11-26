module

public import HullQueryLanguage
public import WidthCode
public import ComplexityModel.PairCode

@[expose] public section

namespace CertificateCode

open ComplexityModel
open HullBatchMachine (ones forUnary forUnary_run stepWrite runTrue runFalse)
open WordCode (Preserves preserves_write setBit setBit_run putField)
open HullDecoder (word bits)
open HullRecovery (Bits lift)

abbrev Checker := Word → Word → Bool

def Implements (code : Code) (time : Poly) (checker : Checker) : Prop :=
  ∀ x w, ∃ out t, Run emptyLanguage code (State.input x w) out t 0 ∧
    t ≤ time.at (x.length + w.length) ∧ (out.output = [true] ↔ checker x w = true)

private def merge : Code := .branch (.head 32) .skip (setBit 33 false)

private theorem merge_run (s : State) (accept passed : Bool)
    (flag : s.reg 32 = [accept]) (acc : s.reg 33 = [passed]) :
    ∃ u t, Run emptyLanguage merge s u t 0 ∧ t ≤ 4 ∧
      u.reg 33 = [passed && accept] ∧ Preserves s u [33] := by
  cases accept
  · exact ⟨s.write 33 [false], 4, runFalse (by simp [Test.eval, flag]) (setBit_run ..),
      by decide, by simp, preserves_write ..⟩
  · exact ⟨s, 2, runTrue (by simp [Test.eval, flag]) .skip,
      by decide, by simpa using acc, ⟨rfl, fun _ _ => rfl⟩⟩

private def checkRow (c : Code) : Code :=
  .seq (FieldCode.takeField 1 22 25 26)
    (.seq (.write 21 (.copy 4))
      (.seq WidthCode.resizeCode
        (.seq (.write 27 (.copy 22))
          (.seq (putField 2 27 28 29 30)
            (.seq (PairCode.call 27 32 c)
              (.seq merge (.seq (.write 22 (.cons true 22)) (putField 22 40 28 29 30))))))))

private def rowRegs : List Nat := [1, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 40]

private theorem checkRow_pure {c : Code} (hc : c.pure) : (checkRow c).pure := by
  simp [checkRow, merge, setBit, Code.allowed, FieldCode.takeField_allowed, WidthCode.resize_allowed,
    WordCode.putField_allowed, PairCode.call_pure _ _ hc]

private theorem checkRow_run {c : Code} {time : Poly} {checker : Checker}
    (program : Implements c time checker) (s : State) (width : Nat) (acc : Bool)
    (hw : s.reg 4 = ones width) (ha : s.reg 33 = [acc]) :
    let fields := QueryEncoding.take (s.reg 1)
    let row := bits fields.1 width
    let answer := checker (s.reg 2) (word row)
    ∃ out t, Run emptyLanguage (checkRow c) s out t 0 ∧
      t ≤ (time.plus ⟨43, 1⟩).at ((s.reg 2).length + width) +
        14 * (s.reg 1).length + 14 * (s.reg 2).length + 27 * width + 130 ∧
      out.reg 1 = fields.2 ∧ out.reg 33 = [acc && answer] ∧
      out.reg 40 = QueryEncoding.put (word (lift row)) (s.reg 40) ∧ Preserves s out rowRegs := by
  dsimp only
  let fields := QueryEncoding.take (s.reg 1)
  let w := word (bits fields.1 width)
  let accepted := checker (s.reg 2) w
  obtain ⟨a, t₁, decode, time₁, rest, row, queue, frame⟩ :=
    FieldCode.takeField_run s (src := 1) (dst := 22) (scratch := 25) (flag := 26)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let b := a.write 21 (ones width)
  have count : Run emptyLanguage (.write 21 (.copy 4)) a b 1 0 := by
    simpa only [b, Expr.eval, frame 4 (by decide) (by decide) (by decide) (by decide), hw] using
      stepWrite a 21 (.copy 4)
  obtain ⟨d, t₂, resize, time₂, resized, keep⟩ :=
    WidthCode.resize_run b width (by simp [b])
  have value : d.reg 22 = w := by
    rw [resized]
    simpa [b, row, w, fields] using WidthCode.resize_eq_word width fields.1
  let e := d.write 27 w
  have save : Run emptyLanguage (.write 27 (.copy 22)) d e 1 0 := by
    simpa only [e, Expr.eval, value] using stepWrite d 27 (.copy 22)
  obtain ⟨f, pair, packet, framePair⟩ := WordCode.putField_run e
    (src := 2) (dst := 27) (tmp := 28) (rev := 29) (flag := 30)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have input : e.reg 2 = s.reg 2 := by
    simpa [e, b, frame 2 (by decide) (by decide) (by decide) (by decide)] using keep.2 2 (by decide)
  have pkt : f.reg 27 = QueryEncoding.put (s.reg 2) w := by
    rw [packet, input]
    simp [e]
  obtain ⟨t₃, called, time₃⟩ := PairCode.call_check program f (dst := 32) pkt
  let g := f.write 32 [accepted]
  have verify : Run emptyLanguage (PairCode.call 27 32 c) f g t₃ 0 := called
  have frameAll : Preserves s g rowRegs := by
    have frame₁ : Preserves s a rowRegs := ⟨queue, fun r hr => by
      simp [rowRegs] at hr
      exact frame r (by omega) (by omega) (by omega) (by omega)⟩
    have tail₂ : Preserves b d rowRegs := keep.mono (by intro r hr; simp [rowRegs] at hr ⊢; omega)
    have tail₃ : Preserves e f rowRegs := framePair.mono (by intro r hr; simp [rowRegs] at hr ⊢; omega)
    exact frame₁.trans (((preserves_write a 21 _).mono (by simp [rowRegs])).trans
      (tail₂.trans (((preserves_write d 27 _).mono (by simp [rowRegs])).trans
        (tail₃.trans ((preserves_write f 32 _).mono (by simp [rowRegs]))))))
  have old : g.reg 33 = [acc] := by
    simp [g, framePair.2 33 (by decide), e, keep.2 33 (by decide), b,
      frame 33 (by decide) (by decide) (by decide) (by decide), ha]
  obtain ⟨h, t₄, accumulate, time₄, agg, f₄⟩ := merge_run g accepted acc (by simp [g]) old
  have wr : h.reg 22 = w := by
    rw [f₄.2 22 (by decide)]
    simp [g, framePair.2 22 (by decide), e, value]
  let i := h.write 22 (true :: w)
  have lifted : Run emptyLanguage (.write 22 (.cons true 22)) h i 1 0 := by
    simpa only [i, Expr.eval, wr] using stepWrite h 22 (.cons true 22)
  obtain ⟨out, saveRow, encoded, frameRow⟩ := WordCode.putField_run i
    (src := 22) (dst := 40) (tmp := 28) (rev := 29) (flag := 30)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have cw := HullDecoder.word_length (bits fields.1 width)
  change w.length = width at cw
  have oldCert : g.reg 1 = fields.2 := by
    simp [g, framePair.2 1 (by decide), e, keep.2 1 (by decide), b, rest, fields]
  have oldRows : i.reg 40 = s.reg 40 := by
    simp [i, f₄.2 40 (by decide), g, framePair.2 40 (by decide), e,
      keep.2 40 (by decide), b, frame 40 (by decide) (by decide) (by decide) (by decide)]
  have iWord : i.reg 22 = true :: w := by simp [i]
  have run := Run.seq decode (Run.seq count (Run.seq resize (Run.seq save (Run.seq pair
    (Run.seq verify (Run.seq accumulate (Run.seq lifted saveRow)))))))
  refine ⟨out, _, run, ?_, ?_, ?_, ?_, ?_⟩
  · rw [input, iWord, List.length_cons, cw]
    rw [cw] at time₃
    omega
  · simp [frameRow.2 1 (by decide), i, f₄.2 1 (by decide), oldCert, fields]
  · simpa [frameRow.2 33 (by decide), i, accepted, w, fields] using agg
  · rw [encoded, iWord, oldRows, lift, HullDecoder.word_cons]
  · exact frameAll.trans ((f₄.mono (by simp [rowRegs])).trans
      (((preserves_write h 22 _).mono (by simp [rowRegs])).trans
        (frameRow.mono (by intro r hr; simp [rowRegs] at hr ⊢; omega))))

/-- Check every guessed point, restoring it before invoking the original
checker. Register 40 accumulates the lifted rows in reverse order. -/
def checkRows (c : Code) : Code :=
  .seq (.write 40 .empty)
    (.seq (setBit 33 true)
      (.seq (.write 34 (.copy 5)) (forUnary 34 (checkRow c))))

theorem checkRows_pure {c : Code} (hc : c.pure) : (checkRows c).pure := by
  simp [checkRows, setBit, forUnary, Code.allowed, checkRow_pure hc]

def rowBudget (time : Poly) (cert request width : Nat) : Nat :=
  (time.plus ⟨43, 1⟩).at (request + width) + 14 * cert + 14 * request + 27 * width + 130

theorem checkRows_run {c : Code} {time : Poly} {checker : Checker}
    (program : Implements c time checker) (s : State) (width rank : Nat)
    (hw : s.reg 4 = ones width) (hr : s.reg 5 = ones rank) :
    let rows := HullQueryLanguage.certificateRows width rank (s.reg 1)
    ∃ out t, Run emptyLanguage (checkRows c) s out t 0 ∧
      t ≤ (rowBudget time (s.reg 1).length (s.reg 2).length width + 3) * rank + 9 ∧
      out.reg 40 = QueryEncoding.pack (rows.reverse.map (word ∘ lift)) ∧
      out.reg 33 = [rows.all (fun v => checker (s.reg 2) (word v))] ∧
      Preserves s out (34 :: rowRegs) := by
  dsimp only
  let rows := HullQueryLanguage.certificateRows width rank (s.reg 1)
  let test (v : Bits width) := checker (s.reg 2) (word v)
  let budget := rowBudget time (s.reg 1).length (s.reg 2).length width
  let I (k : Nat) (u : State) :=
    Preserves s u (34 :: rowRegs) ∧ (u.reg 1).length ≤ (s.reg 1).length ∧
    ∃ seen : List (Bits width),
      seen.reverse ++ HullQueryLanguage.certificateRows width k (u.reg 1) = rows ∧
      u.reg 40 = QueryEncoding.pack (seen.map (word ∘ lift)) ∧ u.reg 33 = [seen.all test]
  let a := s.write 40 []
  let b := a.write 33 [true]
  let start := b.write 34 (ones rank)
  have clear : Run emptyLanguage (.write 40 .empty) s a 1 0 := .write
  have arm : Run emptyLanguage (setBit 33 true) a b 3 0 := setBit_run ..
  have count : Run emptyLanguage (.write 34 (.copy 5)) b start 1 0 := by
    simpa [start, a, b, Expr.eval, hr] using stepWrite b 34 (.copy 5)
  have init : I rank start := by
    refine ⟨?_, by simp [start, b, a], [], by simp [rows, start, b, a], by simp [start, b, a, QueryEncoding.pack],
      by simp [start, b, a]⟩
    exact ((preserves_write s 40 _).mono (by simp [rowRegs])).trans
      (((preserves_write a 33 _).mono (by simp [rowRegs])).trans
        ((preserves_write b 34 _).mono (by simp [rowRegs])))
  have step (k : Nat) (u : State) (clock : u.reg 34 = ones (k + 1)) (inv : I (k + 1) u) :
      ∃ v t, Run emptyLanguage (checkRow c) u v t 0 ∧ t ≤ budget ∧ v.reg 34 = ones (k + 1) ∧
        I k (v.write 34 (ones k)) := by
    obtain ⟨keep, short, seen, pending, packed, acc⟩ := inv
    have hWidth : u.reg 4 = ones width := (keep.2 4 (by decide)).trans hw
    obtain ⟨v, t, run, bound, remainder, checked, saved, frame⟩ :=
      checkRow_run program u width (seen.all test) hWidth acc
    have request : u.reg 2 = s.reg 2 := keep.2 2 (by decide)
    let row := bits (QueryEncoding.take (u.reg 1)).1 width
    let next := v.write 34 (ones k)
    have timeBound : t ≤ budget := by
      rw [request] at bound
      dsimp [budget, rowBudget]
      omega
    refine ⟨v, t, run, timeBound, (frame.2 34 (by decide)).trans clock, ?_, ?_, row :: seen, ?_, ?_, ?_⟩
    · exact keep.trans ((frame.mono (fun _ h => List.mem_cons_of_mem _ h)).trans
        ((preserves_write v 34 _).mono (by simp)))
    · have short' := QueryEncoding.take_lengths (u.reg 1)
      simp [next, remainder]
      omega
    · simpa [next, remainder, row, List.append_assoc, HullQueryLanguage.certificateRows] using pending
    · simpa [next, row, packed, QueryEncoding.pack] using saved
    · simpa [next, row, request, test, Bool.and_comm] using checked
  obtain ⟨u, t, loop, bound, _, frame, _short, seen, done, packed, accepted⟩ :=
    forUnary_run I step rank start (by simp [start]) init
  have done' : seen.reverse = rows := by simpa [HullQueryLanguage.certificateRows] using done
  have seenEq : seen = rows.reverse := by simpa using congrArg List.reverse done'
  have work : Run emptyLanguage (checkRows c) s u (t + 8) 0 := by
    have h := Run.seq clear (Run.seq arm (Run.seq count loop))
    have timeEq : 1 + (3 + (1 + t + 1) + 1) + 1 = t + 8 := by omega
    simpa only [checkRows, timeEq, Nat.add_zero] using h
  change t ≤ (rowBudget time (s.reg 1).length (s.reg 2).length width + 3) * rank + 1 at bound
  refine ⟨u, _, work, by omega, by simpa [seenEq] using packed, ?_, frame⟩
  simpa [seenEq, test, List.all_reverse] using accepted

end CertificateCode
