module

public import AffineSearch
public import QueryEncoding
public import HullBatchMachine
public import ComplexityModelClasses

@[expose] public section

namespace SearchLoopCode

open ComplexityModel
open HullBatchMachine (ones stepWrite)

abbrev Decision := Word → Nat → List Word → Bool

/-- The input and remaining width, followed by the restrictions in reverse
chronological order. The fourth register indicates an active computation. -/
def Active (x : Word) (k : Nat) (history : List Word) (s : State) : Prop :=
  s.reg 0 = x ∧ s.reg 1 = ones k ∧ s.reg 2 = QueryEncoding.pack history ∧ s.reg 3 = [true] ∧
    s.queries = []

/-- A search round either decides the instance, or installs one nonzero
restriction and preserves the answer on the smaller instance. -/
def Round (decide : Decision) (initial : Word → Nat) (code : Code) (time : Poly) : Prop :=
  ∀ x k history s, AffineSearch.History (initial x) k history → Active x k history s →
    ∃ u t, Run emptyLanguage code s u t 0 ∧ t ≤ time.at x.length ∧
      ((u.reg 3 = [] ∧ u.reg 4 = [decide x k history]) ∨
        ∃ n z, k = n + 1 ∧ z.length = k ∧ true ∈ z ∧ Active x n (z :: history) u ∧
          decide x n (z :: history) = decide x k history)

private def loop (round : Code) : Code := .loop (.head 3) round

theorem loop_run {decide : Decision} {initial : Word → Nat} {round : Code} {time : Poly}
    (step : Round decide initial round time)
    (x : Word) {k : Nat} {history : List Word} {s : State}
    (hist : AffineSearch.History (initial x) k history) (active : Active x k history s) :
    ∃ u t, Run emptyLanguage (loop round) s u t 0 ∧
      t ≤ (time.at x.length + 1) * (k+1) + 1 ∧ u.reg 4 = [decide x k history] := by
  induction k generalizing history s with
  | zero =>
    obtain ⟨u, t, run, timeBound, status⟩ := step x 0 history s hist active
    have running : (Test.head 3).eval s = true := by simp [Test.eval, active.2.2.2.1]
    rcases status with ⟨off, answer⟩ | ⟨m, z, equal, _⟩
    · refine ⟨u, t + 1 + 1, .loopTrue running run (.loopFalse ?_), ?_, answer⟩
      · simp [Test.eval, off]
      · simp; omega
    · omega
  | succ k ih =>
    obtain ⟨u, t, run, timeBound, status⟩ := step x (k+1) history s hist active
    have running : (Test.head 3).eval s = true := by simp [Test.eval, active.2.2.2.1]
    rcases status with ⟨off, answer⟩ | ⟨m, z, equal, len, nonzero, state, same⟩
    · refine ⟨u, t + 1 + 1, .loopTrue running run (.loopFalse ?_), ?_, answer⟩
      · simp [Test.eval, off]
      · rw [Nat.mul_succ]
        omega
    · have he : m = k := by omega
      subst m
      obtain ⟨v, t', later, bound, result⟩ := ih (.cut hist len nonzero) state
      refine ⟨v, t + t' + 1, .loopTrue running run later, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [result, same]

def runSearch (round : Code) : Code := .seq (loop round) (.write 0 (.copy 4))

theorem runSearch_pure {c : Code} (hc : c.pure) : (runSearch c).pure := ⟨hc, trivial⟩

theorem runSearch_run {decide : Decision} {initial : Word → Nat} {round : Code} {time : Poly}
    (step : Round decide initial round time) (x : Word) {k : Nat}
    {history : List Word} {s : State}
    (hist : AffineSearch.History (initial x) k history) (active : Active x k history s) :
    ∃ u t, Run emptyLanguage (runSearch round) s u t 0 ∧
      t ≤ (time.at x.length + 1) * (k + 1) + 3 ∧ u.output = [decide x k history] := by
  obtain ⟨u, t, run, bound, result⟩ := loop_run step x hist active
  let out := u.write 0 (u.reg 4)
  have copy : Run emptyLanguage (.write 0 (.copy 4)) u out 1 0 := stepWrite u 0 (.copy 4)
  exact ⟨out, _, .seq run copy, by omega, by simp [out, State.output, State.write, result]⟩

/-- Prepare the initial search state with an empty restriction history. -/
def Initializes (initial : Word → Nat) (code : Code) (time : Poly) : Prop :=
  ∀ x, ∃ u t, Run emptyLanguage code (State.input x) u t 0 ∧ t ≤ time.at x.length ∧
    Active x (initial x) [] u

/-- Assemble a uniform polynomial-time decider from a checked initialization
and a checked round. This counts the complete sequence of restrictions. -/
theorem fp_of_round {decide : Decision} {initial : Word → Nat} {setup round : Code}
    {setupTime stepTime width : Poly}
    (pureSetup : setup.pure) (pureRound : round.pure)
    (startRun : Initializes initial setup setupTime)
    (step : Round decide initial round stepTime) (widthBound : ∀ x, initial x + 1 ≤ width.at x.length) :
    FP (fun x => [decide x (initial x) []]) := by
  let visit := stepTime.plus ⟨1, 0⟩
  let loopBound := visit.times width
  refine ⟨.seq setup (runSearch round), (setupTime.plus loopBound).plus ⟨4, 0⟩,
    ⟨pureSetup, runSearch_pure pureRound⟩, fun x => ?_⟩
  obtain ⟨initialState, t, init, initTime, active⟩ := startRun x
  obtain ⟨out, u, run, runTime, answer⟩ := runSearch_run step x (.start (initial x)) active
  let n := x.length
  have row : stepTime.at n + 1 ≤ visit.at n := by
    have bound := Poly.plus_bound stepTime ⟨1, 0⟩ n
    simpa only [show (Poly.mk 1 0).at n = 1 by simp [Poly.at]] using bound
  have total := Nat.mul_le_mul row (widthBound x)
  have mul : loopBound.at n = visit.at n * width.at n := Poly.times_at visit width n
  rw [← mul] at total
  have cost := Poly.plus_bound setupTime loopBound n
  have extra := Poly.plus_bound (setupTime.plus loopBound) ⟨4, 0⟩ n
  rw [show (Poly.mk 4 0).at n = 4 by simp [Poly.at]] at extra
  refine ⟨out, _, .seq init run, ?_, answer⟩
  change t + u + 1 ≤ ((setupTime.plus loopBound).plus ⟨4, 0⟩).at n
  change u ≤ (stepTime.at n + 1) * (initial x + 1) + 3 at runTime
  change t ≤ setupTime.at n at initTime
  omega

end SearchLoopCode
