module

public import ComplexityModel.WordCode

@[expose] public section

namespace ComplexityModel.ParityCode

open WordCode (Preserves preserves_write setBit setBit_run)

private theorem ifYes {test : Test} {s u : State} {yes no : Code} {t : Nat}
    (hs : test.eval s = true) (h : Run emptyLanguage yes s u t 0) :
    Run emptyLanguage (.branch test yes no) s u (t + 1) 0 := .branch hs h

private theorem ifNo {test : Test} {s u : State} {yes no : Code} {t : Nat}
    (hs : test.eval s = false) (h : Run emptyLanguage no s u t 0) :
    Run emptyLanguage (.branch test yes no) s u (t + 1) 0 := .branch hs h

private def toggle (dst : Nat) : Code :=
  .branch (.head dst) (setBit dst false) (setBit dst true)

private theorem toggle_run (dst : Nat) (s : State) {b : Bool} (h : s.reg dst = [b]) :
    Run emptyLanguage (toggle dst) s (s.write dst [!b]) 4 0 := by
  cases b
  · exact ifNo (by simp [Test.eval, h]) (setBit_run ..)
  · exact ifYes (by simp [Test.eval, h]) (setBit_run ..)

private def accumulate (a b dst : Nat) : Code :=
  .branch (.head a) (.branch (.head b) (toggle dst) .skip) .skip

private theorem accumulate_run (s : State) {a b dst : Nat} {x y : Word} {u v parity : Bool}
    (left : s.reg a = u :: x) (right : s.reg b = v :: y) (acc : s.reg dst = [parity]) :
    let bit := (u && v) ^^ parity
    ∃ t, Run emptyLanguage (accumulate a b dst) s (s.write dst [bit]) t 0 ∧ t ≤ 6 := by
  have same : s.write dst [parity] = s := by
    refine State.ext ?_ rfl
    funext i
    by_cases hi : i = dst <;> simp [State.write, hi, acc]
  cases u with
  | false =>
    simp only [Bool.false_and, Bool.false_xor, same]
    exact ⟨2, ifNo (by simp [Test.eval, left]) .skip, by decide⟩
  | true =>
    have aTrue : (Test.head a).eval s = true := by simp [Test.eval, left]
    cases v with
    | false =>
      simp only [Bool.true_and, Bool.false_xor, same]
      exact ⟨3, ifYes aTrue (ifNo (by simp [Test.eval, right]) .skip), by decide⟩
    | true =>
      have bTrue : (Test.head b).eval s = true := by simp [Test.eval, right]
      simp only [Bool.true_and, Bool.true_xor]
      exact ⟨6, ifYes aTrue (ifYes bTrue (toggle_run dst s acc)), by decide⟩

private def dotStep (a b dst flag : Nat) : Code :=
  .branch (.empty a) (.write flag .empty)
    (.branch (.empty b) (.write flag .empty)
      (.seq (accumulate a b dst) (.seq (.write a (.tail a)) (.write b (.tail b)))))

private def dotLoop (a b dst flag : Nat) : Code := .loop (.head flag) (dotStep a b dst flag)

private theorem dotLoop_run (s : State) {a b dst flag : Nat}
    (hab : a ≠ b) (hda : dst ≠ a) (hdb : dst ≠ b)
    (hfa : flag ≠ a) (hfb : flag ≠ b) (hfd : flag ≠ dst) (x y : Word) (acc : Bool)
    (hx : s.reg a = x) (hy : s.reg b = y) (hd : s.reg dst = [acc]) (hf : s.reg flag = [true]) :
    ∃ out t, Run emptyLanguage (dotLoop a b dst flag) s out t 0 ∧ t ≤ 13 * x.length + 5 ∧
      out.reg dst = [AffineSearch.dot x y ^^ acc] ∧ Preserves s out [a, b, dst, flag] := by
  have ready : (Test.head flag).eval s = true := by simp [Test.eval, hf]
  have done (t : Nat) (step : Run emptyLanguage (dotStep a b dst flag) s (s.write flag []) t 0)
      (cost : t + 2 ≤ 13 * x.length + 5) (value : AffineSearch.dot x y = false) :
      ∃ out t, Run emptyLanguage (dotLoop a b dst flag) s out t 0 ∧ t ≤ 13 * x.length + 5 ∧
        out.reg dst = [AffineSearch.dot x y ^^ acc] ∧ Preserves s out [a, b, dst, flag] := by
    refine ⟨s.write flag [], t + 1 + 1, .loopTrue ready step (.loopFalse ?_), cost, ?_, ?_⟩
    · simp [Test.eval, State.write]
    · simp [State.write, Ne.symm hfd, hd, value]
    · exact (preserves_write ..).mono (by simp)
  match x with
  | [] =>
    exact done 2 (ifYes (by simp [Test.eval, hx]) .write) (by decide) rfl
  | u :: us =>
    cases y with
    | nil =>
      exact done 3 (ifNo (by simp [Test.eval, hx]) (ifYes (by simp [Test.eval, hy]) .write))
        (by simp [List.length_cons]) rfl
    | cons v vs =>
      let bit := (u && v) ^^ acc
      let added := s.write dst [bit]
      let dropped := added.write a us
      let next := dropped.write b vs
      obtain ⟨stepTime, update, stepBound⟩ := accumulate_run s hx hy hd
      have update' : Run emptyLanguage (accumulate a b dst) s added stepTime 0 := update
      have dropA : Run emptyLanguage (.write a (.tail a)) added dropped 1 0 := by
        simpa [dropped, added, Expr.eval, State.write, Ne.symm hda, hx] using
          (Run.write (A := emptyLanguage) (s := added) (d := a) (e := .tail a))
      have dropB : Run emptyLanguage (.write b (.tail b)) dropped next 1 0 := by
        simpa [next, dropped, added, Expr.eval, State.write, Ne.symm hab, Ne.symm hdb, hy] using
          (Run.write (A := emptyLanguage) (s := dropped) (d := b) (e := .tail b))
      have first : Run emptyLanguage (dotStep a b dst flag) s next (stepTime + (1 + 1 + 1) + 1 + 1 + 1) 0 :=
        ifNo (by simp [Test.eval, hx]) (ifNo (by simp [Test.eval, hy]) (.seq update' (.seq dropA dropB)))
      obtain ⟨out, t, loop, bound, eq, frame⟩ :=
        dotLoop_run next hab hda hdb hfa hfb hfd us vs bit
        (by simp [next, dropped, State.write, hab]) (by simp [next, State.write])
        (by simp [next, dropped, added, State.write, hda, hdb])
        (by simp [next, dropped, added, State.write, hfa, hfb, hfd, hf])
      refine ⟨out, _, .loopTrue ready first loop, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · rw [eq]
        simp [AffineSearch.dot, bit, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]
      · apply Preserves.trans (t := next) _ frame
        exact ((preserves_write s dst _).mono (by simp)).trans
          (((preserves_write added a _).mono (by simp)).trans ((preserves_write dropped b _).mono (by simp)))
termination_by x.length

/-- Dot product modulo two. The two input registers are scratch space and
the result is a singleton bit. -/
def dot (a b dst flag : Nat) : Code :=
  .seq (setBit dst false) (.seq (setBit flag true) (dotLoop a b dst flag))

theorem dot_allowed (a b dst flag : Nat) (push direct queued : Bool) :
    (dot a b dst flag).allowed push direct queued := by
  simp [dot, setBit, dotLoop, dotStep, accumulate, toggle, Code.allowed]

theorem dot_run (s : State) {a b dst flag : Nat}
    (hab : a ≠ b) (hda : dst ≠ a) (hdb : dst ≠ b)
    (hfa : flag ≠ a) (hfb : flag ≠ b) (hfd : flag ≠ dst) :
    ∃ out t, Run emptyLanguage (dot a b dst flag) s out t 0 ∧ t ≤ 13 * (s.reg a).length + 13 ∧
      out.reg dst = [AffineSearch.dot (s.reg a) (s.reg b)] ∧ Preserves s out [a, b, dst, flag] := by
  let first := s.write dst [false]
  let start := first.write flag [true]
  obtain ⟨out, t, run, cost, eq, frame⟩ := dotLoop_run start hab hda hdb hfa hfb hfd
    (s.reg a) (s.reg b) false
    (by simp [start, first, State.write, Ne.symm hfa, Ne.symm hda])
    (by simp [start, first, State.write, Ne.symm hfb, Ne.symm hdb])
    (by simp [start, first, State.write, Ne.symm hfd]) (by simp [start, State.write])
  have aRun : Run emptyLanguage (setBit dst false) s first 3 0 := setBit_run ..
  have bRun : Run emptyLanguage (setBit flag true) first start 3 0 := setBit_run ..
  exact ⟨out, _, .seq aRun (.seq bRun run), by omega, by simpa using eq,
    ((preserves_write s dst _).mono (by simp)).trans
      (((preserves_write first flag _).mono (by simp)).trans frame)⟩

end ComplexityModel.ParityCode
