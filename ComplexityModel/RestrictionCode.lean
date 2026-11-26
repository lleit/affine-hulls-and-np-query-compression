module

public import ComplexityModel.ParityCode

@[expose] public section

namespace ComplexityModel.RestrictionCode

open WordCode (Preserves preserves_write prependHead prependHead_run setBit setBit_run)

private theorem ifYes {test : Test} {s u : State} {yes no : Code} {t : Nat}
    (hs : test.eval s = true) (h : Run emptyLanguage yes s u t 0) :
    Run emptyLanguage (.branch test yes no) s u (t + 1) 0 := .branch hs h

private theorem ifNo {test : Test} {s u : State} {yes no : Code} {t : Nat}
    (hs : test.eval s = false) (h : Run emptyLanguage no s u t 0) :
    Run emptyLanguage (.branch test yes no) s u (t + 1) 0 := .branch hs h

private def scanStep : Code :=
  .branch (.empty 10) (.write 13 .empty)
    (.branch (.head 10) (.write 13 .empty)
      (.branch (.empty 11) (.write 13 .empty)
        (.seq (prependHead 11 12) (.seq (.write 10 (.tail 10)) (.write 11 (.tail 11))))))

private def scan : Code := .loop (.head 13) scanStep

private def stopped (s : State) : Prop :=
  s.reg 10 = [] ∨ (s.reg 10).headD false = true ∨ s.reg 11 = []

private def assembled (s : State) : Word :=
  (s.reg 12).reverse ++ AffineSearch.inflate (s.reg 10) (s.reg 11)

private theorem scan_run (s : State) (z x : Word) (hz : s.reg 10 = z) (hx : s.reg 11 = x)
    (active : s.reg 13 = [true]) :
    ∃ u t, Run emptyLanguage scan s u t 0 ∧ t ≤ 10 * z.length + 6 ∧
      stopped u ∧ assembled u = assembled s ∧
      (u.reg 10).length ≤ z.length ∧ (u.reg 12).length ≤ (s.reg 12).length + z.length ∧
      Preserves s u [10, 11, 12, 13] := by
  have live : (Test.head 13).eval s = true := by simp [Test.eval, active]
  have stop {t : Nat} (r : Run emptyLanguage scanStep s (s.write 13 []) t 0)
      (steps : t ≤ 4) (endState : stopped s) :
      ∃ u t, Run emptyLanguage scan s u t 0 ∧ t ≤ 10 * z.length + 6 ∧
        stopped u ∧ assembled u = assembled s ∧
        (u.reg 10).length ≤ z.length ∧ (u.reg 12).length ≤ (s.reg 12).length + z.length ∧
        Preserves s u [10, 11, 12, 13] := by
    refine ⟨s.write 13 [], _, .loopTrue live r (.loopFalse ?_), by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Test.eval, State.write]
    · simpa [stopped, State.write] using endState
    · simp [assembled, State.write]
    · simp [State.write, hz]
    · simp [State.write]
    · exact (preserves_write ..).mono (by simp)
  match z with
  | [] =>
    exact stop (ifYes (by simp [Test.eval, hz]) .write) (by decide) (Or.inl hz)
  | true :: tail =>
    exact stop (ifNo (by simp [Test.eval, hz]) (ifYes (by simp [Test.eval, hz]) .write))
      (by decide) (Or.inr (Or.inl (by simp [hz])))
  | false :: tail =>
    have notEmpty : (Test.empty 10).eval s = false := by simp [Test.eval, hz]
    have noPivot : (Test.head 10).eval s = false := by simp [Test.eval, hz]
    match x with
    | [] =>
      exact stop (ifNo notEmpty (ifNo noPivot (ifYes (by simp [Test.eval, hx]) .write)))
        (by decide) (Or.inr (Or.inr hx))
    | b :: bits =>
      let pushed := s.write 12 (b :: s.reg 12)
      let maskDropped := pushed.write 10 tail
      let next := maskDropped.write 11 bits
      have push : Run emptyLanguage (prependHead 11 12) s pushed 2 0 := by
        simpa [pushed, hx] using prependHead_run emptyLanguage s 11 12
      have dropZ : Run emptyLanguage (.write 10 (.tail 10)) pushed maskDropped 1 0 := by
        simpa [maskDropped, pushed, State.write, Expr.eval, hz] using
          (Run.write (A := emptyLanguage) (s := pushed) (d := 10) (e := .tail 10))
      have dropX : Run emptyLanguage (.write 11 (.tail 11)) maskDropped next 1 0 := by
        simpa [next, maskDropped, pushed, State.write, Expr.eval, hx] using
          (Run.write (A := emptyLanguage) (s := maskDropped) (d := 11) (e := .tail 11))
      have step : Run emptyLanguage scanStep s next 9 0 :=
        ifNo notEmpty (ifNo noPivot (ifNo (by simp [Test.eval, hx]) (.seq push (.seq dropZ dropX))))
      obtain ⟨u, t, loop, bound, halt, result, maskBound, prefBound, frame⟩ :=
        scan_run next tail bits (by simp [next, maskDropped, State.write])
          (by simp [next, State.write]) (by simp [next, maskDropped, pushed, State.write, active])
      refine ⟨u, _, .loopTrue live step loop, by simp only [List.length_cons]; omega,
        halt, ?_, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · rw [result]
        simp [assembled, next, maskDropped, pushed, State.write, hz, hx, AffineSearch.inflate, List.append_assoc]
      · simp [next, maskDropped, pushed, State.write] at prefBound
        simp only [List.length_cons]
        omega
      · exact ((preserves_write s 12 _).mono (by simp)).trans
          (((preserves_write pushed 10 _).mono (by simp)).trans
            (((preserves_write maskDropped 11 _).mono (by simp)).trans frame))
termination_by z.length

private def insertPivot : Code :=
  .seq (.write 10 (.tail 10))
    (.seq (.write 14 (.copy 11))
      (.seq (ParityCode.dot 10 14 15 16) (prependHead 15 11)))

private def insert : Code := .branch (.head 10) insertPivot .skip

private theorem insert_run (s : State) (done : stopped s) :
    ∃ u t, Run emptyLanguage insert s u t 0 ∧ t ≤ 13 * (s.reg 10).length + 21 ∧
      u.reg 11 = AffineSearch.inflate (s.reg 10) (s.reg 11) ∧
      Preserves s u [10, 11, 14, 15, 16] := by
  cases h : (Test.head 10).eval s with
  | false =>
    have out : AffineSearch.inflate (s.reg 10) (s.reg 11) = s.reg 11 := by
      rcases done with z | pivot | x
      · simp [z, AffineSearch.inflate]
      · change (s.reg 10).headD false = false at h
        rw [pivot] at h
        contradiction
      · cases z : s.reg 10 with
        | nil => simp [z, x, AffineSearch.inflate]
        | cons b tail =>
          cases b
          · simp [z, x, AffineSearch.inflate]
          · simp [Test.eval, z] at h
    exact ⟨s, 2, ifNo h .skip, by omega, out.symm, ⟨rfl, fun _ _ => rfl⟩⟩
  | true =>
    have top : ∃ tail, s.reg 10 = true :: tail := by
      cases z : s.reg 10 with
      | nil => simp [Test.eval, z] at h
      | cons bit tail =>
        cases bit
        · simp [Test.eval, z] at h
        · exact ⟨tail, rfl⟩
    obtain ⟨tail, hz⟩ := top
    let a := s.write 10 tail
    let b := a.write 14 (s.reg 11)
    have drop : Run emptyLanguage (.write 10 (.tail 10)) s a 1 0 := by
      simpa [a, Expr.eval, hz] using
        (Run.write (A := emptyLanguage) (s := s) (d := 10) (e := .tail 10))
    have copy : Run emptyLanguage (.write 14 (.copy 11)) a b 1 0 := by
      simpa [b, a, Expr.eval, State.write] using
        (Run.write (A := emptyLanguage) (s := a) (d := 14) (e := .copy 11))
    obtain ⟨mid, t, dot, time, value, frame⟩ := ParityCode.dot_run b
      (a := 10) (b := 14) (dst := 15) (flag := 16)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp [b, a, State.write] at value time
    have saved : mid.reg 11 = s.reg 11 := by
      simpa [b, a, State.write] using frame.2 11 (by decide)
    let out := mid.write 11 (AffineSearch.dot tail (s.reg 11) :: s.reg 11)
    have cons : Run emptyLanguage (prependHead 15 11) mid out 2 0 := by
      simpa [out, value, saved] using prependHead_run emptyLanguage mid 15 11
    refine ⟨out, _, ifYes h (.seq drop (.seq copy (.seq dot cons))), ?_,
      by simp [out, State.write, hz, AffineSearch.inflate], ?_⟩
    · simp only [hz, List.length_cons]
      omega
    · have widened : Preserves b mid [10, 11, 14, 15, 16] := by
        apply frame.mono
        intro r hr
        simp at hr ⊢
        omega
      exact ((preserves_write s 10 _).mono (by simp)).trans
        (((preserves_write a 14 _).mono (by simp)).trans
          (widened.trans ((preserves_write mid 11 _).mono (by simp))))

/-- Reconstruct the eliminated coordinate in register 11. Register 10
contains the restriction mask and registers 12 through 16 are scratch. -/
def inflate : Code :=
  .seq (.write 12 .empty)
    (.seq (setBit 13 true)
      (.seq scan (.seq insert (FieldCode.reverseAppend 12 11 13))))

theorem inflate_allowed (push direct queued : Bool) : inflate.allowed push direct queued := by
  simp [inflate, setBit, scan, scanStep, insert, insertPivot, prependHead,
    ParityCode.dot_allowed, FieldCode.reverseAppend_allowed, Code.allowed]

theorem inflate_run (s : State) :
    ∃ u t, Run emptyLanguage inflate s u t 0 ∧ t ≤ 29 * (s.reg 10).length + 43 ∧
      u.reg 11 = AffineSearch.inflate (s.reg 10) (s.reg 11) ∧
      Preserves s u [10, 11, 12, 13, 14, 15, 16] := by
  let a := s.write 12 []
  let start := a.write 13 [true]
  have clear : Run emptyLanguage (.write 12 .empty) s a 1 0 := .write
  have arm : Run emptyLanguage (setBit 13 true) a start 3 0 := setBit_run ..
  obtain ⟨mid, t, scanning, prefixCost, done, value, maskBound, prefBound, preserved⟩ :=
    scan_run start (s.reg 10) (s.reg 11)
      (by simp [start, a, State.write]) (by simp [start, a, State.write]) (by simp [start, State.write])
  obtain ⟨result, t', pivot, pivotCost, rebuilt, pivotFrame⟩ := insert_run mid done
  have saved : result.reg 12 = mid.reg 12 := pivotFrame.2 12 (by decide)
  obtain ⟨out, restore, _, restored, queue, restoreFrame⟩ :=
    FieldCode.reverseAppend_run result (src := 12) (dst := 11) (flag := 13)
      (by decide) (by decide) (by decide)
  refine ⟨out, _, .seq clear (.seq arm (.seq scanning (.seq pivot restore))), ?_, ?_, ?_⟩
  · simp [start, a, State.write] at prefBound
    rw [saved]
    omega
  · rw [restored, saved, rebuilt]
    change assembled mid = _
    rw [value]
    simp [assembled, start, a, State.write]
  · have scanFrame : Preserves start mid [10, 11, 12, 13, 14, 15, 16] := by
      apply preserved.mono
      intro r hr
      simp at hr ⊢
      omega
    have insertFrame : Preserves mid result [10, 11, 12, 13, 14, 15, 16] := by
      apply pivotFrame.mono
      intro r hr
      simp at hr ⊢
      omega
    have reverseFrame : Preserves result out [10, 11, 12, 13, 14, 15, 16] := by
      refine ⟨queue, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact restoreFrame r hr.2.2.1 hr.2.1 hr.2.2.2.1
    exact ((preserves_write s 12 _).mono (by simp)).trans
      (((preserves_write a 13 _).mono (by simp)).trans (scanFrame.trans (insertFrame.trans reverseFrame)))

end ComplexityModel.RestrictionCode
