module

public import ComplexityModel.FieldCode
public import ComplexityModelSimulation

@[expose] public section

namespace ComplexityModel.BatchCode

/-- The producer leaves a unary count alongside the queue. The consumer
uses it to distinguish a false answer from an empty queue. -/
def input (x : Word) (questions : List Word) : State :=
  { State.input x (List.replicate questions.length true) with queries := questions }

private def collectStep : Code :=
  .seq (.ask .queued 3)
    (.seq (.branch (.head 3) (.write 2 (.cons true 2)) (.write 2 (.cons false 2)))
      (.write 1 (.tail 1)))

private def collectLoop : Code := .loop (.head 1) collectStep

private theorem collectLoop_run (A : Language) (answer : Word → Bool) (s : State)
    (qs : List Word) (queue : s.queries = qs) (fuel : s.reg 1 = List.replicate qs.length true)
    (answers : ∀ q ∈ qs, answer q = true ↔ A q) :
    ∃ out, Run A collectLoop s out (7 * qs.length + 1) qs.length ∧
      out.queries = [] ∧ out.reg 1 = [] ∧
      out.reg 2 = (qs.map answer).reverse ++ s.reg 2 ∧
      ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → out.reg r = s.reg r := by
  induction qs generalizing s with
  | nil =>
    exact ⟨s, .loopFalse (by simp [Test.eval, fuel]), queue, by simpa using fuel,
      by simp, fun _ _ _ _ => rfl⟩
  | cons q tail ih =>
    let bit := answer q
    let asked := s.drop.write 3 [bit]
    let saved := asked.write 2 (bit :: s.reg 2)
    let next := saved.write 1 (List.replicate tail.length true)
    have ask : Run A (.ask .queued 3) s asked 1 1 :=
      .askSome (by simp [Source.read, queue]) (answers q List.mem_cons_self)
    have askResult : (Test.head 3).eval asked = bit := by
      simp [asked, Test.eval, State.write]
    have save : Run A (.branch (.head 3) (.write 2 (.cons true 2)) (.write 2 (.cons false 2)))
        asked saved 2 0 := by
      have writeBit (b : Bool) :
          Run A (.write 2 (.cons b 2)) asked (asked.write 2 (b :: s.reg 2)) 1 0 := by
        simpa [Expr.eval, asked, State.write, State.drop] using
          (Run.write (A := A) (s := asked) (d := 2) (e := .cons b 2))
      apply Run.branch askResult
      cases h : bit
      · simpa [h, saved] using writeBit false
      · simpa [h, saved] using writeBit true
    have pop : Run A (.write 1 (.tail 1)) saved next 1 0 := by
      simpa [next, saved, asked, Expr.eval, State.write, State.drop, fuel] using
        (Run.write (A := A) (s := saved) (d := 1) (e := .tail 1))
    have step : Run A collectStep s next 6 1 := .seq ask (.seq save pop)
    obtain ⟨out, loop, done, clock, values, rest⟩ := ih next
      (by simp [next, saved, asked, State.write, State.drop, queue])
      (by simp [next, State.write]) (fun w hw => answers w (List.mem_cons_of_mem _ hw))
    refine ⟨out, ?_, done, clock, ?_, ?_⟩
    · have t : 6 + (7 * tail.length + 1) + 1 = 7 * (q :: tail).length + 1 := by
        simp only [List.length_cons]
        omega
      rw [← t, List.length_cons, Nat.add_comm tail.length 1]
      exact .loopTrue (by simp [Test.eval, fuel, List.replicate_succ]) step loop
    · simp [values, next, saved, State.write, List.append_assoc, bit]
    · intro r h1 h2 h3
      rw [rest r h1 h2 h3]
      simp [next, saved, asked, State.write, State.drop, h1, h2, h3]

/-- Read exactly the queued questions and return their answers in the same
order in register one. Register zero still holds the original input. -/
def collect : Code :=
  .seq collectLoop (.seq (FieldCode.reverse 2 1 3) (.write 3 .empty))

theorem collect_consumer : collect.consumer := by
  simp [collect, collectLoop, collectStep, Code.allowed, FieldCode.reverse_allowed]

theorem collect_run (A : Language) (answer : Word → Bool) (x : Word) (qs : List Word)
    (answers : ∀ q ∈ qs, answer q = true ↔ A q) :
    Run A collect (input x qs) (State.input x (qs.map answer)) (13 * qs.length + 14) qs.length := by
  let s := input x qs
  obtain ⟨mid, loop, emptyQueue, _, data, unchanged⟩ :=
    collectLoop_run A answer s qs rfl (by simp [s, input, State.input]) answers
  have hdata : mid.reg 2 = (qs.map answer).reverse := by
    simpa [s, input, State.input] using data
  obtain ⟨ordered, reversing, emptyData, restored, stack, unchanged'⟩ :=
    FieldCode.reverse_run mid (src := 2) (dst := 1) (flag := 3) (by decide) (by decide) (by decide)
  have restore : ordered.reg 1 = qs.map answer := by simpa [hdata] using restored
  let out := ordered.write 3 []
  have clear : Run A (.write 3 .empty) ordered out 1 0 := .write
  have same : out = State.input x (qs.map answer) := by
    have eqState (a b : State) (regs : a.reg = b.reg) (queue : a.queries = b.queries) : a = b := by
      cases a
      cases b
      cases regs
      cases queue
      rfl
    apply eqState
    · funext r
      by_cases h1 : r = 1
      · subst r
        simpa [out, State.write, State.input] using restore
      by_cases h2 : r = 2
      · subst r
        simpa [out, State.write, State.input] using emptyData
      by_cases h3 : r = 3
      · subst r
        rfl
      simp [out, State.write, h3, unchanged' r h2 h1 h3, unchanged r h1 h2 h3, s, input, State.input, h1]
    · exact stack.trans emptyQueue
  have run := Run.seq loop (Run.seq (reversing.transfer rfl A) clear)
  rw [← same]
  have time : 7 * qs.length + 1 + (6 * (mid.reg 2).length + 10 + 1 + 1) + 1 =
      13 * qs.length + 14 := by
    simp only [hdata, List.length_reverse, List.length_map]
    omega
  simpa only [collect, s, time, Nat.add_zero] using run

end ComplexityModel.BatchCode
