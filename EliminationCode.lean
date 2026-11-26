module

public import ComplexityModel.WordCode

/-! Register-machine Gaussian elimination over the two-element field.
Rows are length-delimited bit strings. The scan selects the first pivot
and prepends the resulting rows to its output register. This reverses the
order without changing their span. -/

@[expose] public section

namespace EliminationCode

open ComplexityModel HullRecovery HullDecoder
open WordCode (Preserves preserves_write)

local infixr:12 " ⨟ " => Code.seq

abbrev rowsReg := 40
abbrev vectorReg := 41
abbrev widthReg := 42
abbrev rankReg := 43
abbrev normalReg := 44

private theorem wr (s : State) (r : Nat) (e : Expr) :
    Run emptyLanguage (.write r e) s (s.write r (e.eval s)) 1 0 := .write

private theorem yes {s t : State} {test : Test} {a b : Code} {k : Nat}
    (h : test.eval s = true) (run : Run emptyLanguage a s t k 0) :
    Run emptyLanguage (.branch test a b) s t (k + 1) 0 := .branch h run

private theorem no {s t : State} {test : Test} {a b : Code} {k : Nat}
    (h : test.eval s = false) (run : Run emptyLanguage b s t k 0) :
    Run emptyLanguage (.branch test a b) s t (k + 1) 0 := .branch h run

private def xorHead : Code :=
  .branch (.head 50)
    (.branch (.head 51) (.write 53 (.cons false 53)) (.write 53 (.cons true 53)))
    (WordCode.prependHead 51 53)

private theorem xorHead_run (s : State) {a b : Bool} {w v : Word}
    (ha : s.reg 50 = a :: w) (hb : s.reg 51 = b :: v) :
    Run emptyLanguage xorHead s (s.write 53 ((a ^^ b) :: s.reg 53)) 3 0 := by
  cases a <;> cases b
  · exact no (by simp [Test.eval, ha])
      (by simpa [hb] using WordCode.prependHead_run emptyLanguage s 51 53)
  · exact no (by simp [Test.eval, ha])
      (by simpa [hb] using WordCode.prependHead_run emptyLanguage s 51 53)
  · exact yes (by simp [Test.eval, ha]) (no (by simp [Test.eval, hb]) .write)
  · exact yes (by simp [Test.eval, ha]) (yes (by simp [Test.eval, hb]) .write)

private def xorLoop : Code :=
  .loop (.head 54)
    (.branch (.empty 50) (.write 54 .empty)
      (xorHead ⨟ .write 50 (.tail 50) ⨟ .write 51 (.tail 51)))

private theorem xorLoop_run (s : State) (w v : Word)
    (hw : s.reg 50 = w) (hv : s.reg 51 = v) (hlen : w.length = v.length)
    (flag : s.reg 54 = [true]) :
    ∃ u, Run emptyLanguage xorLoop s u (9 * w.length + 4) 0 ∧
      u.reg 53 = (List.zipWith Bool.xor w v).reverse ++ s.reg 53 ∧ Preserves s u [50, 51, 53, 54] := by
  induction w generalizing s v with
  | nil =>
    let u := s.write 54 []
    have step : Run emptyLanguage
        (.branch (.empty 50) (.write 54 .empty)
          (xorHead ⨟ .write 50 (.tail 50) ⨟ .write 51 (.tail 51))) s u 2 0 :=
      yes (by simp [Test.eval, hw]) .write
    have stop : Run emptyLanguage xorLoop u u 1 0 := .loopFalse (by simp [u, Test.eval, State.write])
    refine ⟨u, .loopTrue (by simp [Test.eval, flag]) step stop, ?_, ?_⟩
    · simp [u, State.write]
    · exact (preserves_write ..).mono (by simp)
  | cons a as ih =>
    cases v with
    | nil => simp at hlen
    | cons b bs =>
      let bit := a ^^ b
      let u := s.write 53 (bit :: s.reg 53)
      let w' := u.write 50 as
      let v' := w'.write 51 bs
      have r₀ : Run emptyLanguage xorHead s u 3 0 := xorHead_run s hw hv
      have r₁ : Run emptyLanguage (.write 50 (.tail 50)) u w' 1 0 := by
        simpa [u, w', State.write, Expr.eval, hw] using wr u 50 (.tail 50)
      have r₂ : Run emptyLanguage (.write 51 (.tail 51)) w' v' 1 0 := by
        simpa [u, w', v', State.write, Expr.eval, hv] using wr w' 51 (.tail 51)
      have step : Run emptyLanguage
          (.branch (.empty 50) (.write 54 .empty)
            (xorHead ⨟ .write 50 (.tail 50) ⨟ .write 51 (.tail 51))) s v' 8 0 :=
        no (by simp [Test.eval, hw]) (.seq r₀ (.seq r₁ r₂))
      obtain ⟨out, later, val, frame⟩ := ih v' bs
        (by simp [v', w', State.write]) (by simp [v', State.write]) (by simpa using hlen)
        (by simp [u, w', v', State.write, flag])
      refine ⟨out, ?_, ?_, ?_⟩
      · have time : 9 * (a :: as).length + 4 = 8 + (9 * as.length + 4) + 1 := by
          simp [List.length_cons]; omega
        rw [time]
        exact .loopTrue (by simp [Test.eval, flag]) step later
      · simp [val, v', w', u, State.write, bit, List.append_assoc]
      · have initial : Preserves s v' [50, 51, 53, 54] := by
          refine ⟨rfl, fun j hj => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
          simp [v', w', u, State.write, hj.1, hj.2.1, hj.2.2.1]
        exact initial.trans frame

/-- Add the two input rows. Operands have equal length and are consumed.
The bitwise sum is stored in register 52. -/
def xorRows : Code :=
  .write 53 .empty ⨟ WordCode.setBit 54 true ⨟ xorLoop ⨟ FieldCode.reverse 53 52 54

theorem xorRows_pure : xorRows.pure := by
  simp [xorRows, WordCode.setBit, xorLoop, xorHead, WordCode.prependHead,
    FieldCode.reverse_allowed, Code.allowed]

theorem xorRows_run (s : State) {w v : Word} (hw : s.reg 50 = w)
    (hv : s.reg 51 = v) (h : w.length = v.length) :
    ∃ u, Run emptyLanguage xorRows s u (15 * w.length + 21) 0 ∧
      u.reg 52 = List.zipWith Bool.xor w v ∧ Preserves s u [50, 51, 52, 53, 54] := by
  let clear := s.write 53 []
  let input := clear.write 54 [true]
  have i₁ : Run emptyLanguage (.write 53 .empty) s clear 1 0 := .write
  have i₂ : Run emptyLanguage (WordCode.setBit 54 true) clear input 3 0 := WordCode.setBit_run ..
  obtain ⟨u, loop, data, frame⟩ := xorLoop_run input w v
    (by simp [input, clear, State.write, hw]) (by simp [input, clear, State.write, hv]) h
    (by simp [input, State.write])
  have hdata : u.reg 53 = (List.zipWith Bool.xor w v).reverse := by
    simpa [input, clear, State.write] using data
  obtain ⟨out, order, _, restored, queue, others⟩ := FieldCode.reverse_run u (src := 53)
    (dst := 52) (flag := 54) (by decide) (by decide) (by decide)
  have initial : Preserves s input [50, 51, 52, 53, 54] := by
    refine ⟨rfl, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [input, clear, State.write, hr.2.2.2.1, hr.2.2.2.2]
  have final : Preserves u out [50, 51, 52, 53, 54] := by
    refine ⟨queue, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact others r hr.2.2.2.1 hr.2.2.1 hr.2.2.2.2
  refine ⟨out, ?_, by simpa [hdata] using restored, initial.trans ((frame.mono (more := [50, 51, 52, 53, 54]) (by simp)).trans final)⟩
  have hlen : (u.reg 53).length = w.length := by simp [hdata, List.length_zipWith, h]
  have time : 1 + (3 + (9 * w.length + 4 + (6 * (u.reg 53).length + 10) + 1) + 1) + 1 =
      15 * w.length + 21 := by rw [hlen]; omega
  rw [← time]
  exact .seq i₁ (.seq i₂ (.seq loop order))


/-- Encode rows one after the other before an arbitrary suffix. -/
def packRowsInto : List (Bits n) → Word → Word
  | [], suffix => suffix
  | x :: xs, suffix => QueryEncoding.put (word x) (packRowsInto xs suffix)

abbrev packRows (xs : List (Bits n)) : Word := packRowsInto xs []

theorem packRows_eq (xs : List (Bits n)) : packRows xs = QueryEncoding.pack (xs.map word) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [packRowsInto, QueryEncoding.pack, ih]

private theorem packRowsInto_append (xs ys : List (Bits n)) (suffix : Word) :
    packRowsInto (xs ++ ys) suffix = packRowsInto xs (packRowsInto ys suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [packRowsInto, ih]

private theorem packRows_length (xs : List (Bits n)) :
    (packRows xs).length = (2 * n + 1) * xs.length := by
  induction xs with
  | nil => simp [packRowsInto]
  | cons x xs ih =>
    simp [packRowsInto, QueryEncoding.put_length, ih, Nat.mul_succ]
    omega

@[simp] private theorem word_tail (x : Bits (n + 1)) : (word x).tail = word (tail x) := by
  conv => lhs; rw [← cons_head_tail x, word_cons]
  rfl

@[simp] private theorem word_head (x : Bits (n + 1)) : (word x).headD false = head x := by
  conv => lhs; rw [← cons_head_tail x, word_cons]
  rfl

private def rowAction (pivot : Option (Bits (n + 1))) (x : Bits (n + 1)) :
    Option (Bits (n + 1)) × Option (Bits n) :=
  match pivot with
  | some p => (pivot, some (lower p x))
  | none => if head x then (some x, none) else (none, some (tail x))

private def sweep : List (Bits (n + 1)) → Option (Bits (n + 1)) →
    Option (Bits (n + 1)) × List (Bits n)
  | [], p => (p, [])
  | x :: xs, p =>
    let (next, row) := rowAction p x
    let (chosen, rows) := sweep xs next
    (chosen, row.toList ++ rows)

private theorem sweep_some (xs : List (Bits (n + 1))) (p : Bits (n + 1)) :
    sweep xs (some p) = (some p, xs.map (lower p)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sweep, rowAction, ih]

private theorem sweep_none (xs : List (Bits (n + 1))) :
    sweep xs none = ((splitPivot xs).map Prod.fst, subproblem xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : head x
    · cases e : splitPivot xs with
      | none => simp [sweep, rowAction, subproblem, splitPivot, h, e, ih]
      | some pair =>
        obtain ⟨p, rest⟩ := pair
        simp [sweep, rowAction, subproblem, splitPivot, lower, h, e, ih]
    · simp [sweep, rowAction, subproblem, splitPivot, h, sweep_some]

private def pivotFlag (p : Option (Bits (n + 1))) : Word := if p.isSome then [true] else []
private def pivotWord (p : Option (Bits (n + 1))) : Word := (p.map (word ∘ tail)).getD []
private def PivotIn (s : State) (p : Option (Bits (n + 1))) : Prop :=
  s.reg 45 = pivotFlag p ∧ s.reg 46 = pivotWord p

private def rowSlots : List Nat := [45, 46, 47, 48, 50, 51, 52, 53, 54, 56, 57, 58]

private def putTail : Code := .write 48 (.tail 48) ⨟ WordCode.putField 48 47 56 57 58

private theorem putTail_run (s : State) (x : Bits (n + 1)) (wordIn : s.reg 48 = word x) :
    ∃ u, Run emptyLanguage putTail s u (14 * n + 25) 0 ∧
      u.reg 47 = QueryEncoding.put (word (tail x)) (s.reg 47) ∧
      Preserves s u [47, 48, 56, 57, 58] := by
  let a := s.write 48 (word (tail x))
  have step : Run emptyLanguage (.write 48 (.tail 48)) s a 1 0 := by
    simpa only [a, Expr.eval, wordIn, word_tail] using wr s 48 (.tail 48)
  obtain ⟨out, put, val, frame⟩ := WordCode.putField_run a
    (src := 48) (dst := 47) (tmp := 56) (rev := 57) (flag := 58)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSource : a.reg 48 = word (tail x) := by simp [a, State.write]
  have bound : 1 + (14 * (a.reg 48).length + 23) + 1 = 14 * n + 25 := by
    simp [hSource]; omega
  refine ⟨out, ?_, by simpa [a, State.write] using val, ?_⟩
  · rw [← bound]
    exact .seq step put
  · exact ((preserves_write s 48 _).mono (by simp)).trans
      (frame.mono (by simp [List.cons_subset]))

private def savedPivot : Code := .write 46 (.tail 48) ⨟ WordCode.setBit 45 true

private theorem savedPivot_run (s : State) (x : Bits (n + 1)) (wordIn : s.reg 48 = word x) :
    ∃ u, Run emptyLanguage savedPivot s u 5 0 ∧ PivotIn u (some x) ∧ Preserves s u [45, 46] := by
  let a := s.write 46 (word (tail x))
  let b := a.write 45 [true]
  have saveWord : Run emptyLanguage (.write 46 (.tail 48)) s a 1 0 := by
    simpa only [a, Expr.eval, wordIn, word_tail] using wr s 46 (.tail 48)
  have saveFlag : Run emptyLanguage (WordCode.setBit 45 true) a b 3 0 := WordCode.setBit_run ..
  exact ⟨b, .seq saveWord saveFlag, by simp [PivotIn, pivotFlag, pivotWord, a, b, State.write],
    ((preserves_write s 46 _).mono (by simp)).trans ((preserves_write a 45 _).mono (by simp))⟩

private def putXor : Code :=
  .write 50 (.tail 48) ⨟ .write 51 (.copy 46) ⨟ xorRows ⨟ WordCode.putField 52 47 56 57 58

private theorem putXor_run (s : State) (x p : Bits (n + 1)) (wordIn : s.reg 48 = word x)
    (pword : s.reg 46 = word (tail p)) :
    ∃ out, Run emptyLanguage putXor s out (29 * n + 49) 0 ∧
      out.reg 47 = QueryEncoding.put (word (add (tail x) (tail p))) (s.reg 47) ∧
      Preserves s out [47, 50, 51, 52, 53, 54, 56, 57, 58] := by
  let a := s.write 50 (word (tail x))
  let b := a.write 51 (word (tail p))
  have u₁ : Run emptyLanguage (.write 50 (.tail 48)) s a 1 0 := by
    simpa only [a, Expr.eval, wordIn, word_tail] using wr s 50 (.tail 48)
  have u₂ : Run emptyLanguage (.write 51 (.copy 46)) a b 1 0 := by
    simpa [a, b, State.write, Expr.eval, pword] using wr a 51 (.copy 46)
  obtain ⟨c, xrun, xword, xframe⟩ := xorRows_run b
    (w := word (tail x)) (v := word (tail p))
    (by simp [a, b, State.write]) (by simp [b, State.write]) (by simp)
  obtain ⟨out, emit, val, frame⟩ := WordCode.putField_run c
    (src := 52) (dst := 47) (tmp := 56) (rev := 57) (flag := 58)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lowerWord : c.reg 52 = word (add (tail x) (tail p)) := by
    simpa [HullDecoder.word_add, AffineSearch.translate] using xword
  have slot : c.reg 47 = s.reg 47 := by
    rw [xframe.2 47 (by decide)]
    simp [a, b, State.write]
  have time : 1 + (1 + (15 * (word (tail x)).length + 21 +
      (14 * (c.reg 52).length + 23) + 1) + 1) + 1 = 29 * n + 49 := by
    simp [lowerWord]; omega
  refine ⟨out, ?_, by simpa [lowerWord, slot] using val, ?_⟩
  · rw [← time]
    exact .seq u₁ (.seq u₂ (.seq xrun emit))
  · have f₁ : Preserves s a [47, 50, 51, 52, 53, 54, 56, 57, 58] :=
      (preserves_write ..).mono (by simp)
    have f₂ : Preserves a b [47, 50, 51, 52, 53, 54, 56, 57, 58] :=
      (preserves_write ..).mono (by simp)
    have f₃ := xframe.mono (more := [47, 50, 51, 52, 53, 54, 56, 57, 58])
      (by simp [List.cons_subset])
    have f₄ := frame.mono (more := [47, 50, 51, 52, 53, 54, 56, 57, 58])
      (by simp [List.cons_subset])
    exact f₁.trans (f₂.trans (f₃.trans f₄))

private def rowStep : Code :=
  .branch (.head 48) (.branch (.head 45) putXor savedPivot) putTail

private theorem rowStep_run (s : State) (x : Bits (n + 1)) (pivot : Option (Bits (n + 1)))
    (wordIn : s.reg 48 = word x) (pivotIn : PivotIn s pivot) :
    let (p, y) := rowAction pivot x
    ∃ u time, Run emptyLanguage rowStep s u time 0 ∧ time ≤ 29 * n + 51 ∧
      PivotIn u p ∧ u.reg 47 = packRowsInto y.toList (s.reg 47) ∧ Preserves s u rowSlots := by
  cases hp : head x with
  | false =>
    obtain ⟨out, result, value, frame⟩ := putTail_run s x wordIn
    have preservedPivot : PivotIn out pivot := by
      constructor
      · rw [frame.2 45 (by decide)]; exact pivotIn.1
      · rw [frame.2 46 (by decide)]; exact pivotIn.2
    have run : Run emptyLanguage rowStep s out (14 * n + 25 + 1) 0 :=
      no (by simp only [Test.eval, wordIn, word_head, hp]) result
    have val : out.reg 47 = packRowsInto [tail x] (s.reg 47) := value
    have h : (rowAction pivot x) = (pivot, some (tail x)) := by
      cases pivot <;> simp [rowAction, lower, hp]
    simp only [h, Option.toList_some]
    exact ⟨out, _, run, by omega, preservedPivot, val, frame.mono (by simp [rowSlots, List.cons_subset])⟩
  | true =>
    have leading : (Test.head 48).eval s = true := by simp only [Test.eval, wordIn, word_head, hp]
    cases pivot with
    | none =>
      obtain ⟨out, result, newPivot, frame⟩ := savedPivot_run s x wordIn
      have noPivot : (Test.head 45).eval s = false := by simp [Test.eval, pivotIn.1, pivotFlag]
      have run : Run emptyLanguage rowStep s out 7 0 := yes leading (no noPivot result)
      have val : out.reg 47 = s.reg 47 := frame.2 47 (by decide)
      simp only [rowAction, hp, if_pos rfl, Option.toList_none, packRowsInto]
      exact ⟨out, 7, run, by omega, newPivot, val, frame.mono (by simp [rowSlots, List.cons_subset])⟩
    | some p =>
      have hasPivot : (Test.head 45).eval s = true := by simp [Test.eval, pivotIn.1, pivotFlag]
      have pw : s.reg 46 = word (tail p) := pivotIn.2
      obtain ⟨out, result, value, frame⟩ := putXor_run s x p wordIn pw
      have run : Run emptyLanguage rowStep s out (29 * n + 49 + 1 + 1) 0 :=
        yes leading (yes hasPivot result)
      have eq : lower p x = add (tail x) (tail p) := by simp [lower, hp]
      simp only [rowAction, Option.toList_some, packRowsInto, eq]
      exact ⟨out, _, run, by omega,
        ⟨(frame.2 45 (by decide)).trans pivotIn.1, (frame.2 46 (by decide)).trans pivotIn.2⟩,
        value, frame.mono (by simp [rowSlots, List.cons_subset])⟩


private def sweepSlots : List Nat :=
  [40, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

private def parseRow : Code := FieldCode.takeField 40 48 49 59

private def sweepLoop : Code :=
  .loop (.head 55) (.branch (.empty 40) (.write 55 .empty) (parseRow ⨟ rowStep))

private theorem sweepLoop_run (s : State) {budget : Nat} (xs : List (Bits (n + 1)))
    (p : Option (Bits (n + 1))) (packed : s.reg 40 = packRows xs)
    (size : (packRows xs).length ≤ budget) (pivotIn : PivotIn s p)
    (active : s.reg 55 = [true]) :
    ∃ out time, Run emptyLanguage sweepLoop s out time 0 ∧
      time ≤ (14 * budget + 29 * n + 71) * xs.length + 4 ∧
      out.reg 40 = [] ∧ PivotIn out (sweep xs p).1 ∧
      out.reg 47 = packRowsInto (sweep xs p).2.reverse (s.reg 47) ∧
      Preserves s out sweepSlots := by
  induction xs generalizing s p with
  | nil =>
    let out := s.write 55 []
    have step : Run emptyLanguage
        (.branch (.empty 40) (.write 55 .empty) (parseRow ⨟ rowStep)) s out 2 0 :=
      yes (by simp [Test.eval, packed, packRowsInto]) .write
    have stop : Run emptyLanguage sweepLoop out out 1 0 :=
      .loopFalse (by simp [out, Test.eval, State.write])
    refine ⟨out, 4, .loopTrue (by simp [Test.eval, active]) step stop,
      by simp, by simpa [out, State.write, packRowsInto] using packed, ?_, ?_, ?_⟩
    · exact ⟨by simpa [out, State.write, sweep] using pivotIn.1,
        by simpa [out, State.write, sweep] using pivotIn.2⟩
    · simp [sweep, packRowsInto, out, State.write]
    · exact (preserves_write ..).mono (by simp [sweepSlots])
  | cons x xs ih =>
    have input : s.reg 40 = QueryEncoding.put (word x) (packRows xs) := packed
    obtain ⟨parsed, t₁, parse, cost₁, rem, data, queue, registers⟩ := FieldCode.takeField_run s
      (src := 40) (dst := 48) (scratch := 49) (flag := 59)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [input, QueryEncoding.take_put] at rem data
    have pp : PivotIn parsed p := by
      constructor
      · rw [registers 45 (by decide) (by decide) (by decide) (by decide)]; exact pivotIn.1
      · rw [registers 46 (by decide) (by decide) (by decide) (by decide)]; exact pivotIn.2
    have hactive : parsed.reg 55 = [true] :=
      (registers 55 (by decide) (by decide) (by decide) (by decide)).trans active
    generalize e : rowAction p x = action
    obtain ⟨nextPivot, row⟩ := action
    have act := rowStep_run parsed x p data pp
    rw [e] at act
    dsimp only at act
    obtain ⟨next, t₂, process, cost₂, nextP, output, frame⟩ := act
    have nonempty : (Test.empty 40).eval s = false := by
      rw [Test.eval, input]
      cases word x <;> rfl
    have step : Run emptyLanguage
        (.branch (.empty 40) (.write 55 .empty) (parseRow ⨟ rowStep)) s next (t₁ + t₂ + 2) 0 := by
      simpa [parseRow, Nat.add_assoc] using no nonempty (Run.seq parse process)
    have nextSize : (packRows xs).length ≤ budget := by
      change (QueryEncoding.put (word x) (packRows xs)).length ≤ budget at size
      rw [QueryEncoding.put_length] at size
      omega
    obtain ⟨out, tr, loop, costR, empty, finished, acc, restFrame⟩ :=
      ih next nextPivot ((frame.2 40 (by decide)).trans rem) nextSize nextP
        ((frame.2 55 (by decide)).trans hactive)
    have hcost : t₁ ≤ 14 * budget + 17 := by
      rw [packed] at cost₁
      exact Nat.le_trans cost₁ (Nat.add_le_add_right (Nat.mul_le_mul_left _ size) _)
    refine ⟨out, _, .loopTrue (by simp [Test.eval, active]) step loop, ?_, empty, ?_, ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_succ]
      omega
    · simpa [sweep, e] using finished
    · have preserved : parsed.reg 47 = s.reg 47 :=
        registers 47 (by decide) (by decide) (by decide) (by decide)
      rw [output, preserved] at acc
      have reverseOpt : row.toList.reverse = row.toList := by cases row <;> rfl
      simpa [sweep, e, List.reverse_append, reverseOpt, packRowsInto_append] using acc
    · have parsedFrame : Preserves s parsed [40, 48, 49, 59] := by
        refine ⟨queue, fun j hj => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        exact registers j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
      exact (parsedFrame.mono (by simp [sweepSlots, List.cons_subset])).trans
        ((frame.mono (by simp [rowSlots, sweepSlots, List.cons_subset])).trans restFrame)

/-- Run one column of Gaussian elimination. Register 47 receives the
remaining rows in reverse order, register 45 the pivot flag, and
register 46 the pivot tail (or an empty word if there is no pivot). -/
def column : Code :=
  .write 45 .empty ⨟ .write 46 .empty ⨟ .write 47 .empty ⨟ WordCode.setBit 55 true ⨟ sweepLoop

theorem column_pure : column.pure := by
  simp [column, sweepLoop, parseRow, rowStep, savedPivot, putTail, putXor,
    FieldCode.takeField_pure, WordCode.putField_allowed, WordCode.setBit, Code.allowed, xorRows_pure]

theorem column_run (s : State) (xs : List (Bits (n + 1))) (packed : s.reg 40 = packRows xs) :
    let p := (splitPivot xs).map Prod.fst
    ∃ out time, Run emptyLanguage column s out time 0 ∧
      time ≤ (14 * (packRows xs).length + 29 * n + 71) * xs.length + 14 ∧
      out.reg 40 = [] ∧ PivotIn out p ∧ out.reg 47 = packRows (subproblem xs).reverse ∧
      Preserves s out sweepSlots := by
  let a := s.write 45 []
  let b := a.write 46 []
  let c := b.write 47 []
  let d := c.write 55 [true]
  have ard : Run emptyLanguage (WordCode.setBit 55 true) c d 3 0 := WordCode.setBit_run ..
  obtain ⟨out, t, h, bound, empty, pivots, reduced, frame⟩ :=
    sweepLoop_run d xs none (budget := (packRows xs).length)
      (by simp [d, c, b, a, State.write, packed]) (by omega)
      (by simp [PivotIn, pivotFlag, pivotWord, d, c, b, a, State.write])
      (by simp [d, State.write])
  rw [sweep_none] at pivots reduced
  refine ⟨out, 1 + (1 + (1 + (3 + t + 1) + 1) + 1) + 1, ?_, by omega, empty,
    pivots, by simpa [d, c, State.write] using reduced, ?_⟩
  · exact .seq (show Run emptyLanguage (.write 45 .empty) s a 1 0 from .write)
      (.seq (show Run emptyLanguage (.write 46 .empty) a b 1 0 from .write)
        (.seq (show Run emptyLanguage (.write 47 .empty) b c 1 0 from .write) (.seq ard h)))
  · have initial : Preserves s d sweepSlots := by
      refine ⟨rfl, fun j hj => ?_⟩
      have h₁ : j ≠ 45 := fun eq => hj (eq ▸ (by decide : 45 ∈ sweepSlots))
      have h₂ : j ≠ 46 := fun eq => hj (eq ▸ (by decide : 46 ∈ sweepSlots))
      have h₃ : j ≠ 47 := fun eq => hj (eq ▸ (by decide : 47 ∈ sweepSlots))
      have h₄ : j ≠ 55 := fun eq => hj (eq ▸ (by decide : 55 ∈ sweepSlots))
      simp [d, c, b, a, State.write, h₁, h₂, h₃, h₄]
    exact initial.trans frame


private def xorVector : Code :=
  .write 50 (.tail 41) ⨟ .write 51 (.copy 46) ⨟ xorRows ⨟ .write 41 (.copy 52)

private theorem xorVector_run (s : State) (x p : Bits (n + 1))
    (xIn : s.reg 41 = word x) (pIn : s.reg 46 = word (tail p)) :
    ∃ out, Run emptyLanguage xorVector s out (15 * n + 27) 0 ∧
      out.reg 41 = word (add (tail x) (tail p)) ∧ Preserves s out [41, 50, 51, 52, 53, 54] := by
  let a := s.write 50 (word (tail x))
  let b := a.write 51 (word (tail p))
  have u₁ : Run emptyLanguage (.write 50 (.tail 41)) s a 1 0 := by
    simpa only [a, Expr.eval, xIn, word_tail] using wr s 50 (.tail 41)
  have u₂ : Run emptyLanguage (.write 51 (.copy 46)) a b 1 0 := by
    simpa [a, b, State.write, Expr.eval, pIn] using wr a 51 (.copy 46)
  obtain ⟨c, xrun, xword, xframe⟩ := xorRows_run b (w := word (tail x)) (v := word (tail p))
    (by simp [a, b, State.write]) (by simp [b, State.write]) (by simp)
  have lowerWord : c.reg 52 = word (add (tail x) (tail p)) := by
    simpa [HullDecoder.word_add, AffineSearch.translate] using xword
  let out := c.write 41 (c.reg 52)
  have time : 1 + (1 + (15 * (word (tail x)).length + 21 + 1 + 1) + 1) + 1 = 15 * n + 27 := by
    simp; omega
  refine ⟨out, ?_, by simp [out, State.write, lowerWord], ?_⟩
  · rw [← time]
    exact .seq u₁ (.seq u₂ (.seq xrun (wr c 41 (.copy 52))))
  · have f₁ : Preserves s a [41, 50, 51, 52, 53, 54] := (preserves_write ..).mono (by simp)
    have f₂ : Preserves a b [41, 50, 51, 52, 53, 54] := (preserves_write ..).mono (by simp)
    have f₃ := xframe.mono (more := [41, 50, 51, 52, 53, 54]) (by simp [List.cons_subset])
    have f₄ : Preserves c out [41, 50, 51, 52, 53, 54] := (preserves_write ..).mono (by simp)
    exact f₁.trans (f₂.trans (f₃.trans f₄))

private def vSlots : List Nat := [41, 43, 44, 50, 51, 52, 53, 54]

private def reduceVector : Code := .branch (.head 41) xorVector (.write 41 (.tail 41))

private theorem reduceVector_run (s : State) (x p : Bits (n + 1))
    (xIn : s.reg 41 = word x) (pIn : s.reg 46 = word (tail p)) :
    ∃ out time, Run emptyLanguage reduceVector s out time 0 ∧ time ≤ 15 * n + 28 ∧
      out.reg 41 = word (lower p x) ∧ Preserves s out [41, 50, 51, 52, 53, 54] := by
  cases hx : head x
  · let out := s.write 41 (word (tail x))
    have drop : Run emptyLanguage (.write 41 (.tail 41)) s out 1 0 := by
      simpa only [out, Expr.eval, xIn, word_tail] using wr s 41 (.tail 41)
    exact ⟨out, 2, no (by simp only [Test.eval, xIn, word_head, hx]) drop, by omega,
      by simp [out, State.write, lower, hx], (preserves_write ..).mono (by simp)⟩
  · obtain ⟨out, run, value, frame⟩ := xorVector_run s x p xIn pIn
    exact ⟨out, _, yes (by simp only [Test.eval, xIn, word_head, hx]) run, by omega,
      by simpa [lower, hx] using value, frame⟩

private def vectorStep : Code :=
  .branch (.head 45)
    (.write 43 (.cons true 43) ⨟ .write 44 (.cons false 44) ⨟ reduceVector)
    (WordCode.prependHead 41 44 ⨟ .write 41 (.tail 41))

private def nextVector (p : Option (Bits (n + 1))) (x : Bits (n + 1)) : Bits n :=
  match p with
  | none => tail x
  | some r => lower r x

private def normalHead (p : Option (Bits (n + 1))) (x : Bits (n + 1)) : Bool :=
  if p.isSome then false else head x

private def rankDelta (p : Option (Bits (n + 1))) : Nat := if p.isSome then 1 else 0

private theorem vectorStep_run (s : State) (p : Option (Bits (n + 1))) (x : Bits (n + 1))
    (pin : PivotIn s p) (xin : s.reg 41 = word x) :
    ∃ out time, Run emptyLanguage vectorStep s out time 0 ∧ time ≤ 15 * n + 33 ∧
      out.reg 41 = word (nextVector p x) ∧
      out.reg 43 = List.replicate (rankDelta p) true ++ s.reg 43 ∧
      out.reg 44 = normalHead p x :: s.reg 44 ∧ Preserves s out vSlots := by
  cases p with
  | none =>
    let a := s.write 44 (head x :: s.reg 44)
    let b := a.write 41 (word (tail x))
    have ha : Run emptyLanguage (WordCode.prependHead 41 44) s a 2 0 := by
      simpa only [a, xin, word_head] using WordCode.prependHead_run emptyLanguage s 41 44
    have hb : Run emptyLanguage (.write 41 (.tail 41)) a b 1 0 := by
      have input : a.reg 41 = word x := by simp [a, State.write, xin]
      simpa only [b, Expr.eval, input, word_tail] using wr a 41 (.tail 41)
    refine ⟨b, 5, no (by simp [Test.eval, pin.1, pivotFlag]) (.seq ha hb), by omega,
      by simp [b, nextVector, State.write], by simp [b, a, rankDelta, State.write],
      by simp [b, a, normalHead, State.write], ?_⟩
    exact ((preserves_write s 44 _).mono (by simp [vSlots])).trans
      ((preserves_write a 41 _).mono (by simp [vSlots]))
  | some p =>
    let a := s.write 43 (true :: s.reg 43)
    let b := a.write 44 (false :: s.reg 44)
    have ha : Run emptyLanguage (.write 43 (.cons true 43)) s a 1 0 := .write
    have hb : Run emptyLanguage (.write 44 (.cons false 44)) a b 1 0 := by
      simpa [a, b, Expr.eval, State.write] using wr a 44 (.cons false 44)
    have pEq : s.reg 46 = word (tail p) := pin.2
    obtain ⟨out, tr, hr, bound, value, frame⟩ := reduceVector_run b x p
      (by simp [b, a, State.write, xin]) (by simp [b, a, State.write, pEq])
    refine ⟨out, _, yes (by simp [Test.eval, pin.1, pivotFlag]) (.seq ha (.seq hb hr)),
      by omega, value, ?_, ?_, ?_⟩
    · rw [frame.2 43 (by decide)]
      simp [b, a, State.write, rankDelta]
    · rw [frame.2 44 (by decide)]
      simp [b, normalHead, State.write]
    · have f₁ : Preserves s a vSlots := (preserves_write ..).mono (by simp [vSlots])
      have f₂ : Preserves a b vSlots := (preserves_write ..).mono (by simp [vSlots])
      exact f₁.trans (f₂.trans (frame.mono (by simp [vSlots, List.cons_subset])))

private theorem reverse_span (xs : List (Bits n)) : SameSpan xs.reverse xs := by
  intro x
  exact ⟨Span.mono (fun w h => Span.gen (by simpa using h)),
    Span.mono (fun w h => Span.gen (by simpa using h))⟩

private theorem rank_column (xs : List (Bits (n + 1))) :
    rank xs = rank (subproblem xs).reverse + rankDelta ((splitPivot xs).map Prod.fst) := by
  rw [rank_congr (reverse_span (subproblem xs)), rank_step]
  cases e : splitPivot xs <;> simp [rankDelta, pivotCount, e]

private theorem normal_column (xs : List (Bits (n + 1))) (x : Bits (n + 1)) :
    let p := (splitPivot xs).map Prod.fst
    normal xs x = cons (normalHead p x) (normal (subproblem xs).reverse (nextVector p x)) := by
  rw [normal_congr (reverse_span (subproblem xs))]
  cases e : splitPivot xs with
  | none => simpa [e, normalHead, subproblem, nextVector] using normal_none e x
  | some pair =>
    obtain ⟨p, rest⟩ := pair
    simpa [e, normalHead, subproblem, nextVector] using normal_some e x

private def iterationSlots : List Nat :=
  [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

private def iteration : Code := column ⨟ vectorStep ⨟ .write 40 (.copy 47) ⨟ .write 42 (.tail 42)

private theorem iteration_run (s : State) (xs : List (Bits (n + 1))) (x : Bits (n + 1))
    (rowsIn : s.reg 40 = packRows xs) (vectorIn : s.reg 41 = word x)
    (clock : s.reg 42 = List.replicate (n + 1) true) :
    let p := (splitPivot xs).map Prod.fst
    ∃ out time, Run emptyLanguage iteration s out time 0 ∧
      time ≤ (14 * (packRows xs).length + 29 * n + 71) * xs.length + 15 * n + 52 ∧
      out.reg 40 = packRows (subproblem xs).reverse ∧
      out.reg 41 = word (nextVector p x) ∧ out.reg 42 = List.replicate n true ∧
      out.reg 43 = List.replicate (rankDelta p) true ++ s.reg 43 ∧
      out.reg 44 = normalHead p x :: s.reg 44 ∧ Preserves s out iterationSlots := by
  obtain ⟨reduced, ct, sweepRun, bounded, _, pIn, reducedRows, fCol⟩ := column_run s xs rowsIn
  have xIn : reduced.reg 41 = word x := (fCol.2 41 (by decide)).trans vectorIn
  obtain ⟨normal, vt, vecRun, vBound, vectorOut, rankOut, bitOut, fVec⟩ :=
    vectorStep_run reduced _ x pIn xIn
  let copied := normal.write 40 (normal.reg 47)
  let out := copied.write 42 (List.replicate n true)
  have widthIn : copied.reg 42 = List.replicate (n + 1) true := by
    simp [copied, State.write, fVec.2 42 (by decide), fCol.2 42 (by decide), clock]
  have drop : Run emptyLanguage (.write 42 (.tail 42)) copied out 1 0 := by
    simpa [out, Expr.eval, widthIn, List.replicate_succ] using wr copied 42 (.tail 42)
  have copy : Run emptyLanguage (.write 40 (.copy 47)) normal copied 1 0 := .write
  refine ⟨out, _, .seq sweepRun (.seq vecRun (.seq copy drop)), by omega,
    ?_, ?_, by simp [out, State.write], ?_, ?_, ?_⟩
  · simp [out, copied, State.write, fVec.2 47 (by decide), reducedRows]
  · simp [out, copied, State.write, vectorOut]
  · simp [out, copied, State.write, rankOut, fCol.2 43 (by decide)]
  · simp [out, copied, State.write, bitOut, fCol.2 44 (by decide)]
  · have a := fCol.mono (more := iterationSlots) (by simp [sweepSlots, iterationSlots, List.cons_subset])
    have b := fVec.mono (more := iterationSlots) (by simp [vSlots, iterationSlots, List.cons_subset])
    have c : Preserves normal copied iterationSlots := (preserves_write ..).mono (by simp [iterationSlots])
    have d : Preserves copied out iterationSlots := (preserves_write ..).mono (by simp [iterationSlots])
    exact a.trans (b.trans (c.trans d))


/-- A shared polynomial bound for one column when the number of columns and
rows are at most the original matrix's dimensions. -/
def columnTime (columns rows : Nat) : Nat :=
  (14 * ((2 * columns + 1) * rows) + 29 * columns + 71) * rows + 15 * columns + 53

private def eliminateLoop : Code := .loop (.head 42) iteration

private theorem eliminateLoop_run (columns rows : Nat) (s : State) (xs : List (Bits n)) (x : Bits n)
    (colBound : n ≤ columns) (rowBound : xs.length ≤ rows)
    (hx : s.reg 40 = packRows xs) (hv : s.reg 41 = word x)
    (clock : s.reg 42 = List.replicate n true) :
    ∃ out time, Run emptyLanguage eliminateLoop s out time 0 ∧ time ≤ columnTime columns rows * n + 1 ∧
      out.reg 42 = [] ∧ out.reg 43 = List.replicate (rank xs) true ++ s.reg 43 ∧
      out.reg 44 = (word (normal xs x)).reverse ++ s.reg 44 ∧ Preserves s out iterationSlots := by
  induction n generalizing s with
  | zero =>
    have stop : Run emptyLanguage eliminateLoop s s 1 0 :=
      .loopFalse (by simp [Test.eval, clock])
    exact ⟨s, 1, stop, by simp, by simpa using clock, rfl, rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨next, one, run, bound, mx, v, k, rk, bit, frame⟩ := iteration_run s xs x hx hv clock
    let p := (splitPivot xs).map Prod.fst
    let rest := (subproblem xs).reverse
    have lowerN : n ≤ columns := Nat.le_trans (by omega) colBound
    have lowerRows : rest.length ≤ rows := by
      simpa [rest] using Nat.le_trans (subproblem_length_le xs) rowBound
    have kbound : (packRows xs).length ≤ (2 * columns + 1) * rows := by
      rw [packRows_length]
      exact Nat.mul_le_mul (by omega) rowBound
    have b : (14 * (packRows xs).length + 29 * n + 71) * xs.length ≤
        (14 * ((2 * columns + 1) * rows) + 29 * columns + 71) * rows := by
      exact Nat.mul_le_mul (by omega) rowBound
    have stride : one + 1 ≤ columnTime columns rows := by
      unfold columnTime
      omega
    obtain ⟨out, more, loop, remain, nil, rankOut, normOut, endFrame⟩ :=
      ih next rest (nextVector p x) lowerN lowerRows mx v k
    have h : (Test.head 42).eval s = true := by
      simp [Test.eval, clock, List.replicate_succ]
    refine ⟨out, one + more + 1, .loopTrue h run loop, ?_, nil, ?_, ?_, frame.trans endFrame⟩
    · rw [Nat.mul_succ]
      omega
    · rw [rankOut, rk, rank_column xs]
      simp only [rest, ← List.append_assoc, List.replicate_append_replicate]
    · rw [normOut, bit, normal_column xs x]
      simp only [word_cons, List.reverse_cons, List.append_assoc, List.singleton_append, rest, p]

/-- Gaussian elimination and evaluation of its normal form at a supplied
vector. The scratch registers and input registers are consumed. The rank
is unary in register 43 and the normal vector is in register 44. -/
def eliminate : Code :=
  .write 43 .empty ⨟ .write 44 .empty ⨟ eliminateLoop ⨟ FieldCode.reverse 44 60 61 ⨟ .write 44 (.copy 60)

theorem eliminate_pure : eliminate.pure := by
  simp [eliminate, eliminateLoop, iteration, vectorStep, reduceVector, xorVector, Code.allowed,
    column_pure, xorRows_pure, WordCode.prependHead, FieldCode.reverse_allowed]

def footprint : List Nat := iterationSlots ++ [60, 61]

/-- Kernel-checked run and polynomial register-step bound. For an oracle
rank query the input vector can be zero. For a projection entry query
use a coordinate vector and read the desired bit from the output. -/
theorem eliminate_run (s : State) (xs : List (Bits n)) (x : Bits n)
    (matrix : s.reg rowsReg = packRows xs) (vector : s.reg vectorReg = word x)
    (clock : s.reg widthReg = List.replicate n true) :
    ∃ out time, Run emptyLanguage eliminate s out time 0 ∧
      time ≤ columnTime n xs.length * n + 6 * n + 18 ∧
      out.reg rankReg = List.replicate (rank xs) true ∧
      out.reg normalReg = word (normal xs x) ∧ Preserves s out footprint := by
  let a := s.write 43 []
  let input := a.write 44 []
  obtain ⟨mid, runTime, run, time, _, unary, reversed, frame⟩ :=
    eliminateLoop_run n xs.length input xs x (by omega) (by omega)
      (by simpa [input, a, State.write, rowsReg] using matrix)
      (by simpa [input, a, State.write, vectorReg] using vector)
      (by simpa [input, a, State.write, widthReg] using clock)
  have rev : mid.reg 44 = (word (normal xs x)).reverse := by simpa [input, State.write] using reversed
  have size : (mid.reg 44).length = n := by simp [rev]
  have r : mid.reg 43 = List.replicate (rank xs) true := by
    simpa [input, a, State.write] using unary
  obtain ⟨ordered, order, _, ready, queue, others⟩ :=
    FieldCode.reverse_run mid (src := 44) (dst := 60) (flag := 61)
      (by decide) (by decide) (by decide)
  let out := ordered.write 44 (ordered.reg 60)
  have copy : Run emptyLanguage (.write 44 (.copy 60)) ordered out 1 0 := .write
  have i₁ : Run emptyLanguage (.write 43 .empty) s a 1 0 := .write
  have i₂ : Run emptyLanguage (.write 44 .empty) a input 1 0 := .write
  refine ⟨out, _, .seq i₁ (.seq i₂ (.seq run (.seq order copy))), by omega, ?_, ?_, ?_⟩
  · simp [out, State.write, rankReg, others 43 (by decide) (by decide) (by decide), r]
  · simp [out, State.write, normalReg, ready, rev]
  · have i₁f : Preserves s a footprint := (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have i₂f : Preserves a input footprint := (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have frame' := frame.mono (more := footprint) (fun _ h => List.mem_append_left _ h)
    have order' : Preserves mid ordered footprint := by
      refine ⟨queue, fun j left => ?_⟩
      apply others
      · intro e; apply left; rw [e]; decide
      · intro e; apply left; rw [e]; decide
      · intro e; apply left; rw [e]; decide
    have copy' : Preserves ordered out footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    exact i₁f.trans (i₂f.trans (frame'.trans (order'.trans copy')))

end EliminationCode
