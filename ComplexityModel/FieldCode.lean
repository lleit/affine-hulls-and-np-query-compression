module

public import ComplexityModel.Machine
public import QueryEncoding

@[expose] public section

namespace ComplexityModel.FieldCode

open QueryEncoding (take)

private def prependHead (src dst : Nat) : Code :=
  .branch (.head src) (.write dst (.cons true dst)) (.write dst (.cons false dst))

private theorem prependHead_run (A : Language) (s : State) {src dst : Nat} {b : Bool}
    {rest : Word} (h : s.reg src = b :: rest) :
    Run A (prependHead src dst) s (s.write dst (b :: s.reg dst)) 2 0 := by
  apply Run.branch (bit := b)
  · simp [Test.eval, h]
  · cases b <;> exact Run.write

private def escapedStep (src dst : Nat) : Code :=
  .seq (.write src (.tail src))
    (.branch (.empty src) .skip (.seq (prependHead src dst) (.write src (.tail src))))

private def takeReverseLoop (src dst : Nat) : Code := .loop (.head src) (escapedStep src dst)

private theorem takeReverseLoop_run (s : State) {src dst : Nat} (hd : dst ≠ src)
    (input : Word) (h : s.reg src = input) :
    ∃ u t, Run emptyLanguage (takeReverseLoop src dst) s u t 0 ∧ t ≤ 8 * input.length + 2 ∧
      (u.reg src).tail = (take input).2 ∧ u.reg dst = (take input).1.reverse ++ s.reg dst ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → u.reg r = s.reg r := by
  have nonemptyRun (u : State) (head : (Test.head src).eval u = true)
      {v out : State} {t₁ t₂ : Nat}
      (step : Run emptyLanguage (escapedStep src dst) u v t₁ 0)
      (loop : Run emptyLanguage (takeReverseLoop src dst) v out t₂ 0) :
      Run emptyLanguage (takeReverseLoop src dst) u out (t₁ + t₂ + 1) 0 :=
    .loopTrue head step loop
  match input with
  | [] =>
    exact ⟨s, 1, .loopFalse (by simp [Test.eval, h]), by decide,
      by simp [h, take], by simp [take], rfl, fun _ _ _ => rfl⟩
  | false :: rest =>
    exact ⟨s, 1, .loopFalse (by simp [Test.eval, h]), by simp [List.length_cons],
      by simp [h, take], by simp [take], rfl, fun _ _ _ => rfl⟩
  | [true] =>
    let u := s.write src []
    have dropTag : Run emptyLanguage (.write src (.tail src)) s u 1 0 := by
      simpa [u, Expr.eval, h] using
        (Run.write (A := emptyLanguage) (s := s) (d := src) (e := .tail src))
    have checkEmpty : Run emptyLanguage
        (.branch (.empty src) .skip (.seq (prependHead src dst) (.write src (.tail src))))
        u u 2 0 := .branch (bit := true) (by simp [u, Test.eval, State.write]) .skip
    have stop : Run emptyLanguage (takeReverseLoop src dst) u u 1 0 :=
      .loopFalse (by simp [u, Test.eval, State.write])
    have run : Run emptyLanguage (takeReverseLoop src dst) s u 6 0 :=
      nonemptyRun s (by simp [Test.eval, h]) (.seq dropTag checkEmpty) stop
    exact ⟨u, 6, run, by decide, by simp [u, State.write, take],
      by simp [u, State.write, hd, take], rfl, fun r hs _ => by simp [u, State.write, hs]⟩
  | true :: b :: rest =>
    let afterTag := s.write src (b :: rest)
    let afterData := afterTag.write dst (b :: s.reg dst)
    let next := afterData.write src rest
    have dropTag : Run emptyLanguage (.write src (.tail src)) s afterTag 1 0 := by
      simpa [afterTag, Expr.eval, h] using
        (Run.write (A := emptyLanguage) (s := s) (d := src) (e := .tail src))
    have push : Run emptyLanguage (prependHead src dst) afterTag afterData 2 0 := by
      simpa [afterData, afterTag, State.write, hd] using
        (prependHead_run emptyLanguage afterTag (src := src) (dst := dst)
          (b := b) (rest := rest) (by simp [afterTag, State.write]))
    have dropData : Run emptyLanguage (.write src (.tail src)) afterData next 1 0 := by
      simpa [next, afterData, afterTag, Expr.eval, State.write, Ne.symm hd] using
        (Run.write (A := emptyLanguage) (s := afterData) (d := src) (e := .tail src))
    have branch : Run emptyLanguage
        (.branch (.empty src) .skip (.seq (prependHead src dst) (.write src (.tail src))))
        afterTag next 5 0 :=
      .branch (bit := false) (by simp [Test.eval, afterTag, State.write]) (.seq push dropData)
    obtain ⟨u, time, loop, bound, rem, data, queue, unchanged⟩ :=
      takeReverseLoop_run next hd rest (by simp [next, State.write])
    refine ⟨u, 7 + time + 1, nonemptyRun s (by simp [Test.eval, h]) (.seq dropTag branch) loop,
      by simp only [List.length_cons]; omega, ?_, ?_, queue, ?_⟩
    · simpa [take] using rem
    · cases he : take rest with
      | mk word suffix =>
        rw [data]
        simp [take, he, next, afterData, State.write, hd, List.append_assoc]
    · intro r hs ht
      rw [unchanged r hs ht]
      simp [next, afterData, afterTag, State.write, hs, ht]

/-- Parse one escaped field, placing its reversal in the destination
register. The source register advances to the rest of the packed word. -/
def takeReverse (src dst : Nat) : Code :=
  .seq (.write dst .empty) (.seq (takeReverseLoop src dst) (.write src (.tail src)))

theorem takeReverse_allowed (src dst : Nat) (push direct queued : Bool) :
    (takeReverse src dst).allowed push direct queued := by
  simp [takeReverse, takeReverseLoop, escapedStep, prependHead, Code.allowed]

theorem takeReverse_pure (src dst : Nat) : (takeReverse src dst).pure := takeReverse_allowed ..

theorem takeReverse_run (s : State) {src dst : Nat} (hd : dst ≠ src) :
    ∃ u t, Run emptyLanguage (takeReverse src dst) s u t 0 ∧ t ≤ 8 * (s.reg src).length + 6 ∧
      u.reg src = (take (s.reg src)).2 ∧ u.reg dst = (take (s.reg src)).1.reverse ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → u.reg r = s.reg r := by
  let start := s.write dst []
  have hstart : start.reg src = s.reg src := by simp [start, State.write, Ne.symm hd]
  obtain ⟨u, t, loop, bound, rem, data, queue, others⟩ :=
    takeReverseLoop_run start hd (s.reg src) hstart
  let out := u.write src (u.reg src).tail
  have clear : Run emptyLanguage (.write dst .empty) s start 1 0 := .write
  have finish : Run emptyLanguage (.write src (.tail src)) u out 1 0 := .write
  refine ⟨out, 1 + (t + 1 + 1) + 1, .seq clear (.seq loop finish), by omega,
    by simpa [out, State.write] using rem, ?_, queue, ?_⟩
  · simpa [out, start, State.write, hd] using data
  · intro r hs ht
    simpa [out, start, State.write, hs, ht] using others r hs ht

private def reverseLoop (src dst flag : Nat) : Code :=
  .loop (.head flag)
    (.branch (.empty src) (.write flag .empty) (.seq (prependHead src dst) (.write src (.tail src))))

private theorem reverseLoop_run (s : State) {src dst flag : Nat}
    (hd : dst ≠ src) (hf : flag ≠ src) (hfd : flag ≠ dst) (input : Word)
    (h : s.reg src = input) (active : s.reg flag = [true]) :
    ∃ u, Run emptyLanguage (reverseLoop src dst flag) s u (6 * input.length + 4) 0 ∧
      u.reg src = [] ∧ u.reg dst = input.reverse ++ s.reg dst ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → r ≠ flag → u.reg r = s.reg r := by
  induction input generalizing s with
  | nil =>
    let out := s.write flag []
    have step : Run emptyLanguage
        (.branch (.empty src) (.write flag .empty) (.seq (prependHead src dst) (.write src (.tail src))))
        s out 2 0 := .branch (bit := true) (by simp [Test.eval, h]) .write
    have stop : Run emptyLanguage (reverseLoop src dst flag) out out 1 0 :=
      .loopFalse (by simp [out, Test.eval, State.write])
    exact ⟨out, .loopTrue (by simp [Test.eval, active]) step stop,
      by simp [out, State.write, Ne.symm hf, h], by simp [out, State.write, Ne.symm hfd],
      rfl, fun r _ _ hrf => by simp [out, State.write, hrf]⟩
  | cons b rest ih =>
    let pushed := s.write dst (b :: s.reg dst)
    let next := pushed.write src rest
    have drop : Run emptyLanguage (.write src (.tail src)) pushed next 1 0 := by
      simpa [next, pushed, Expr.eval, State.write, Ne.symm hd, h] using
        (Run.write (A := emptyLanguage) (s := pushed) (d := src) (e := .tail src))
    have step : Run emptyLanguage
        (.branch (.empty src) (.write flag .empty) (.seq (prependHead src dst) (.write src (.tail src))))
        s next 5 0 :=
      .branch (bit := false) (by simp [Test.eval, h]) (.seq (prependHead_run _ _ h) drop)
    obtain ⟨out, loop, empty, data, queue, others⟩ :=
      ih next (by simp [next, State.write]) (by simp [next, pushed, State.write, hf, hfd, active])
    refine ⟨out, ?_, empty, ?_, queue, ?_⟩
    · have total : 5 + (6 * rest.length + 4) + 1 = 6 * (b :: rest).length + 4 := by
        simp only [List.length_cons]
        omega
      rw [← total]
      exact .loopTrue (by simp [Test.eval, active]) step loop
    · simp [data, next, pushed, State.write, hd, List.append_assoc]
    · intro r hs ht hflag
      rw [others r hs ht hflag]
      simp [next, pushed, State.write, hs, ht]

/-- Reverse a scratch word onto an existing suffix. -/
def reverseAppend (src dst flag : Nat) : Code :=
  .seq (.write flag .empty) (.seq (.write flag (.cons true flag)) (reverseLoop src dst flag))

theorem reverseAppend_allowed (src dst flag : Nat) (push direct queued : Bool) :
    (reverseAppend src dst flag).allowed push direct queued := by
  simp [reverseAppend, reverseLoop, prependHead, Code.allowed]

theorem reverseAppend_run (s : State) {src dst flag : Nat}
    (hd : dst ≠ src) (hf : flag ≠ src) (hfd : flag ≠ dst) :
    ∃ u, Run emptyLanguage (reverseAppend src dst flag) s u (6 * (s.reg src).length + 8) 0 ∧
      u.reg src = [] ∧ u.reg dst = (s.reg src).reverse ++ s.reg dst ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → r ≠ flag → u.reg r = s.reg r := by
  let clear := s.write flag []
  let start := clear.write flag [true]
  have first : Run emptyLanguage (.write flag .empty) s clear 1 0 := .write
  have second : Run emptyLanguage (.write flag (.cons true flag)) clear start 1 0 := by
    simpa [start, clear, Expr.eval, State.write] using
      (Run.write (A := emptyLanguage) (s := clear) (d := flag) (e := .cons true flag))
  obtain ⟨u, loop, empty, data, queue, others⟩ := reverseLoop_run start hd hf hfd (s.reg src)
    (by simp [start, clear, State.write, Ne.symm hf]) (by simp [start, State.write])
  refine ⟨u, ?_, empty, ?_, queue, ?_⟩
  · have total : 1 + (1 + (6 * (s.reg src).length + 4) + 1) + 1 =
        6 * (s.reg src).length + 8 := by omega
    rw [← total]
    exact .seq first (.seq second loop)
  · simpa [start, clear, State.write, Ne.symm hfd] using data
  · intro r hs ht hflag
    simpa [start, clear, State.write, hflag] using others r hs ht hflag

def reverse (src dst flag : Nat) : Code :=
  .seq (.write dst .empty) (reverseAppend src dst flag)

theorem reverse_allowed (src dst flag : Nat) (push direct queued : Bool) :
    (reverse src dst flag).allowed push direct queued := by
  simp [reverse, reverseAppend_allowed, Code.allowed]

theorem reverse_run (s : State) {src dst flag : Nat}
    (hd : dst ≠ src) (hf : flag ≠ src) (hfd : flag ≠ dst) :
    ∃ u, Run emptyLanguage (reverse src dst flag) s u (6 * (s.reg src).length + 10) 0 ∧
      u.reg src = [] ∧ u.reg dst = (s.reg src).reverse ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → r ≠ flag → u.reg r = s.reg r := by
  let start := s.write dst []
  have clear : Run emptyLanguage (.write dst .empty) s start 1 0 := .write
  obtain ⟨u, reversed, emptied, data, queue, others⟩ := reverseAppend_run start hd hf hfd
  have srcValue : start.reg src = s.reg src := by simp [start, State.write, Ne.symm hd]
  rw [srcValue] at reversed
  refine ⟨u, ?_, emptied, ?_, queue, ?_⟩
  · have total : 1 + (6 * (s.reg src).length + 8) + 1 =
        6 * (s.reg src).length + 10 := by omega
    rw [← total]
    exact .seq clear reversed
  · simpa [srcValue, show start.reg dst = [] by simp [start, State.write]] using data
  · intro r hs ht hflag
    simpa [start, State.write, ht] using others r hs ht hflag

/-- Parse one field in a linear number of machine steps, producing the data
in its original order. Only the four supplied registers can be modified. -/
def takeField (src dst scratch flag : Nat) : Code :=
  .seq (takeReverse src scratch) (reverse scratch dst flag)

theorem takeField_allowed (src dst scratch flag : Nat) (push direct queued : Bool) :
    (takeField src dst scratch flag).allowed push direct queued := by
  simp [takeField, takeReverse_allowed, reverse_allowed, Code.allowed]

theorem takeField_pure (src dst scratch flag : Nat) : (takeField src dst scratch flag).pure :=
  takeField_allowed ..

theorem takeField_run (s : State) {src dst scratch flag : Nat}
    (hds : dst ≠ src) (hss : scratch ≠ src) (hsd : scratch ≠ dst)
    (hfs : flag ≠ src) (hfd : flag ≠ dst) (hft : flag ≠ scratch) :
    ∃ u t, Run emptyLanguage (takeField src dst scratch flag) s u t 0 ∧
      t ≤ 14 * (s.reg src).length + 17 ∧
      u.reg src = (take (s.reg src)).2 ∧ u.reg dst = (take (s.reg src)).1 ∧
      u.queries = s.queries ∧ ∀ r, r ≠ src → r ≠ dst → r ≠ scratch → r ≠ flag →
        u.reg r = s.reg r := by
  obtain ⟨mid, t, scan, bound, tail, data, queue, unchanged⟩ := takeReverse_run s hss
  obtain ⟨out, order, _, restored, queue', unchanged'⟩ :=
    reverse_run mid (Ne.symm hsd) hft hfd
  refine ⟨out, t + (6 * (mid.reg scratch).length + 10) + 1, .seq scan order, ?_, ?_, ?_,
    queue'.trans queue, ?_⟩
  · have width := QueryEncoding.take_data_le (s.reg src)
    simp only [data, List.length_reverse]
    omega
  · rw [unchanged' src (Ne.symm hss) (Ne.symm hds) (Ne.symm hfs), tail]
  · simpa [data] using restored
  · intro r hs hd ht hf
    rw [unchanged' r ht hd hf, unchanged r hs ht]

end ComplexityModel.FieldCode
