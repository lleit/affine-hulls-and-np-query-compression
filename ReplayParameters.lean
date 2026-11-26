module

public import ReplayListCode
public import UnaryPolynomialCode

@[expose] public section

namespace ReplayParameters

open ComplexityModel
open HullBatchMachine (ones forUnary forUnary_run stepWrite runFalse runTrue normalize normalize_run)
open WordCode (setBit setBit_run)

private def halfStep : Code :=
  .branch (.head 23) (.seq (.write 22 (.cons true 22)) (setBit 23 false)) (setBit 23 true)

private def halve : Code :=
  .seq (.write 22 .empty) (.seq (setBit 23 false) (forUnary 21 halfStep))

private theorem halve_run (s : State) (n : Nat) (size : s.reg 21 = ones n) :
    ∃ u t, Run emptyLanguage halve s u t 0 ∧ t ≤ 9*n+7 ∧
      u.reg 22 = ones (n/2) ∧ WordCode.Preserves s u [21, 22, 23] := by
  let a := s.write 22 []
  let start := a.write 23 [false]
  let I (k : Nat) (st : State) :=
    k ≤ n ∧ st.reg 22 = ones ((n-k)/2) ∧ st.reg 23 = [decide ((n-k)%2 = 1)] ∧
      WordCode.Preserves s st [21, 22, 23]
  have reset : Run emptyLanguage (.write 22 .empty) s a 1 0 := .write
  have mode : Run emptyLanguage (setBit 23 false) a start 3 0 := setBit_run ..
  have init : I n start := by
    refine ⟨Nat.le_refl n, by simp [a,start], by simp [start], ?_⟩
    exact ((WordCode.preserves_write s 22 _).mono (by simp)).trans
      ((WordCode.preserves_write a 23 _).mono (by simp))
  have step (k : Nat) (v : State) (kc : v.reg 21 = ones (k+1)) (inv : I (k+1) v) :
      ∃ u t, Run emptyLanguage halfStep v u t 0 ∧ t ≤ 6 ∧ u.reg 21 = ones (k+1) ∧
        I k (u.write 21 (ones k)) := by
    obtain ⟨kl, count, flag, frame⟩ := inv
    let done := n-(k+1)
    have calcDone : n-k = done+1 := by dsimp [done]; omega
    by_cases odd : done%2 = 1
    · let b := v.write 22 (true :: v.reg 22)
      let u := b.write 23 [false]
      have plus : Run emptyLanguage (.write 22 (.cons true 22)) v b 1 0 := .write
      have run : Run emptyLanguage halfStep v u 6 0 :=
        runTrue (by simp [Test.eval, flag, done, odd]) (.seq plus (setBit_run ..))
      have value : (n-k)/2 = done/2+1 := by omega
      have rem : (n-k)%2 ≠ 1 := by omega
      refine ⟨u, 6, run, by decide, by simp [u,b,kc], by omega, ?_, ?_, ?_⟩
      · simp [u,b,count,value,done]
      · simp [u,b,rem]
      · exact frame.trans (((WordCode.preserves_write v 22 _).mono (by simp)).trans
          (((WordCode.preserves_write b 23 _).mono (by simp)).trans
            ((WordCode.preserves_write u 21 _).mono (by simp))))
    · let u := v.write 23 [true]
      have run : Run emptyLanguage halfStep v u 4 0 :=
        runFalse (by simp [Test.eval, flag, done, odd]) (setBit_run ..)
      have value : (n-k)/2 = done/2 := by omega
      have rem : (n-k)%2 = 1 := by omega
      refine ⟨u, 4, run, by decide, by simp [u,kc], by omega, ?_, ?_, ?_⟩
      · simp [u,count,value,done]
      · simp [u,rem]
      · exact frame.trans (((WordCode.preserves_write v 23 _).mono (by simp)).trans
          ((WordCode.preserves_write u 21 _).mono (by simp)))
  obtain ⟨u, t, loop, bound, _, _, result, _, frame⟩ :=
    forUnary_run I step n start (by simp [a,start,size]) init
  exact ⟨u, _, .seq reset (.seq mode loop), by omega, by simpa using result, frame⟩

private def logarithmStep (a : Nat) : Code :=
  .branch (.empty 21) (.write 24 .empty)
    (.seq (.write 25 (.tail 21))
      (.branch (.empty 25) (.write 24 .empty)
        (.seq halve (.seq (.write 21 (.copy 22)) (UnaryPolynomialCode.addConstant a)))))

private def logarithmLoop (a : Nat) : Code := .loop (.head 24) (logarithmStep a)

private theorem logarithmLoop_run (a cap n : Nat) (s : State) (bound : n ≤ cap)
    (ticks : s.reg 21 = ones n) (active : s.reg 24 = [true]) :
    ∃ u t, Run emptyLanguage (logarithmLoop a) s u t 0 ∧
      t ≤ (35+2*a)*(cap+1)*n+7 ∧ u.reg 1 = ones (a*n.log2) ++ s.reg 1 ∧
      WordCode.Preserves s u [1,21,22,23,24,25] := by
  have live : (Test.head 24).eval s = true := by simp [Test.eval, active]
  have stop {u : State} {t : Nat} (once : Run emptyLanguage (logarithmStep a) s u t 0)
      (short : t ≤ 5) (stopped : u.reg 24 = []) (small : n < 2)
      (same : u.reg 1 = s.reg 1) (kept : WordCode.Preserves s u [1,21,22,23,24,25]) :
      ∃ u t, Run emptyLanguage (logarithmLoop a) s u t 0 ∧
        t ≤ (35+2*a)*(cap+1)*n+7 ∧ u.reg 1 = ones (a*n.log2) ++ s.reg 1 ∧
        WordCode.Preserves s u [1,21,22,23,24,25] := by
    have z : n.log2 = 0 := by rw [Nat.log2_def n, ite_eq_right (by omega)]
    exact ⟨u, t+2, .loopTrue live once (.loopFalse (by simp [Test.eval, stopped])),
      by omega, by simpa [z] using same, kept⟩
  by_cases zero : n = 0
  · let out := s.write 24 []
    have once : Run emptyLanguage (logarithmStep a) s out 2 0 :=
      runTrue (by simp [Test.eval, ticks, zero]) .write
    exact stop once (by decide) (by simp [out]) (by omega) (by simp [out])
      ((WordCode.preserves_write ..).mono (by simp))
  · let b := s.write 25 (ones (n-1))
    have tail : Run emptyLanguage (.write 25 (.tail 21)) s b 1 0 := by
      cases n with
      | zero => contradiction
      | succ n => simpa [b, Expr.eval, ticks] using stepWrite s 25 (.tail 21)
    have nz : (Test.empty 21).eval s = false := by
      cases n with
      | zero => contradiction
      | succ n => simp [Test.eval, ticks]
    by_cases one : n = 1
    · let out := b.write 24 []
      have yes : (Test.empty 25).eval b = true := by simp [b, Test.eval,one]
      have once : Run emptyLanguage (logarithmStep a) s out 5 0 :=
        runFalse nz (.seq tail (runTrue yes .write))
      exact stop once (by decide) (by simp [out]) (by omega) (by simp [out,b])
        (((WordCode.preserves_write s 25 _).mono (by simp)).trans
          ((WordCode.preserves_write b 24 _).mono (by simp)))
    · have big : 2 ≤ n := by omega
      have positive : 1 ≤ n-1 := by omega
      have no : (Test.empty 25).eval b = false := by
        have : n-1 = (n-2)+1 := by omega
        simp [b, Test.eval, this]
      obtain ⟨c,t₁,half,halfTime,result,frame⟩ := halve_run b n (by simp [b,ticks])
      let d := c.write 21 (ones (n/2))
      have copy : Run emptyLanguage (.write 21 (.copy 22)) c d 1 0 := by
        simpa [d, Expr.eval, result] using stepWrite c 21 (.copy 22)
      obtain ⟨next, add, sums, q, other⟩ := UnaryPolynomialCode.addConstant_run a d
      have step : Run emptyLanguage (logarithmStep a) s next
          (t₁ + 2*a + 8) 0 := by
        have r := runFalse (a := .write 24 .empty) nz (.seq tail
          (runFalse (a := .write 24 .empty) no (.seq half (.seq copy add))))
        have steps : 1 + (t₁ + (1 + (2*a+1) + 1) + 1 + 1) + 1 + 1 =
            t₁ + 2*a + 8 := by omega
        simpa only [logarithmStep, steps, Nat.add_zero] using r
      have lt : n/2 < n := Nat.log2_terminates n big
      have nextWidth : next.reg 21 = ones (n/2) := by simp [other 21 (by decide),d]
      have on : next.reg 24 = [true] := by
        simp [other 24 (by decide), d, frame.2 24 (by decide), b, active]
      obtain ⟨u, t, loop, time, count, rest⟩ :=
        logarithmLoop_run a cap (n/2) next (by omega) nextWidth on
      refine ⟨u, _, .loopTrue live step loop, ?_, ?_, ?_⟩
      · let budget := (35+2*a)*(cap+1)
        have single : t₁ + 2*a + 8 + 1 ≤ budget := by
          have le := Nat.mul_le_mul_left (35+2*a) (show n+1 ≤ cap+1 by omega)
          change (35+2*a)*(n+1) ≤ budget at le
          rw [Nat.mul_succ, Nat.add_mul] at le
          omega
        have add := Nat.mul_le_mul_left budget (show n/2+1 ≤ n by omega)
        rw [Nat.mul_succ] at add
        change t ≤ budget*(n/2)+7 at time
        change t₁+2*a+8+t+1 ≤ budget*n+7
        omega
      · have log : n.log2 = (n/2).log2 + 1 := by rw [Nat.log2_def n, ite_eq_left big]
        rw [count, sums, log, Nat.mul_succ, ← List.append_assoc]
        simp [ones, d, frame.2 1 (by decide), b]
      · have cut : WordCode.Preserves b c [1,21,22,23,24,25] := frame.mono (by
          intro r hr; simp at hr ⊢; omega)
        have final : WordCode.Preserves d next [1,21,22,23,24,25] := ⟨q, fun r hr =>
          other r (by simp at hr; omega)⟩
        exact ((WordCode.preserves_write s 25 _).mono (by simp)).trans
          (cut.trans (((WordCode.preserves_write c 21 _).mono (by simp)).trans (final.trans rest)))
termination_by n

/-- Add `a * log2 n` to the unary count in register one. Register 21
contains `n` in unary and registers 22 through 25 are scratch. -/
def logCap (a : Nat) : Code := .seq (setBit 24 true) (logarithmLoop a)

theorem logCap_pure (a : Nat) : (logCap a).pure := by
  simp [logCap, logarithmLoop, logarithmStep, halve, halfStep, forUnary, setBit, Code.allowed,
    UnaryPolynomialCode.addConstant_pure]

theorem logCap_run (a n : Nat) (s : State) (source : s.reg 21 = ones n) :
    ∃ u t, Run emptyLanguage (logCap a) s u t 0 ∧ t ≤ (35+2*a)*(n+1)*n+11 ∧
      u.reg 1 = ones (a*n.log2) ++ s.reg 1 ∧ WordCode.Preserves s u [1,21,22,23,24,25] := by
  let start := s.write 24 [true]
  obtain ⟨u,t,run,cost,value,frame⟩ := logarithmLoop_run a n n start (Nat.le_refl n)
    (by simp [start,source]) (by simp [start])
  have arm : Run emptyLanguage (setBit 24 true) s start 3 0 := setBit_run ..
  exact ⟨u, _, .seq arm run, by omega, by simpa [start] using value,
    ((WordCode.preserves_write s 24 _).mono (by simp)).trans frame⟩


open MachineEnumeration (frameWidth loweringCost)

private def firstCoeff (c : Code) (p : Poly) := (2*frameWidth c+20)*p.coefficient
private def secondCoeff (p : Poly) := 4*p.coefficient*p.coefficient

private theorem clock_formula (c : Code) (p : Poly) (n : Nat) :
    loweringCost (frameWidth c) (p.at n) * p.at n =
      firstCoeff c p * (n+1)^p.degree +
        secondCoeff p * (n+1)^(p.degree+p.degree) := by
  unfold loweringCost firstCoeff secondCoeff Poly.at
  rw [Nat.add_mul, Nat.pow_add]
  congr 1 <;> ac_rfl

private def seed (c : Code) (p : Poly) (factor extra dst : Nat) : Code :=
  .seq (.write 1 .empty)
    (.seq (UnaryPolynomialCode.addConstant extra)
      (.seq (UnaryPolynomialCode.addMonomial (factor*firstCoeff c p) 64 p.degree)
        (.seq (UnaryPolynomialCode.addMonomial (factor*secondCoeff p) 64 (p.degree+p.degree))
          (.write dst (.copy 1)))))

private theorem seed_pure (c : Code) (p : Poly) (factor extra dst : Nat) :
    (seed c p factor extra dst).pure := by
  simp [seed, Code.allowed, UnaryPolynomialCode.addConstant_pure, UnaryPolynomialCode.addMonomial_pure]

private def seedTime (c : Code) (p : Poly) (factor extra n : Nat) : Nat :=
  (2*(factor*firstCoeff c p)+7)*(n+2)^p.degree +
  (2*(factor*secondCoeff p)+7)*(n+2)^(p.degree+p.degree) + 2*extra + 10

private theorem seed_run (c : Code) (p : Poly) (factor extra dst n : Nat) (s : State)
    (base : s.reg 5 = ones (n+1)) :
    ∃ u t, Run emptyLanguage (seed c p factor extra dst) s u t 0 ∧
      t ≤ seedTime c p factor extra n ∧
      u.reg dst = ones (factor*(loweringCost (frameWidth c) (p.at n)*p.at n)+extra) ∧
      u.queries = s.queries ∧
      ∀ r, r ≠ 1 → r ≠ dst → (r < 64 ∨ 64 + (p.degree+p.degree) ≤ r) → u.reg r = s.reg r := by
  let start := s.write 1 []
  have reset : Run emptyLanguage (.write 1 .empty) s start 1 0 := .write
  obtain ⟨a, extraRun, initial, qa, fa⟩ := UnaryPolynomialCode.addConstant_run extra start
  have ba : a.reg 5 = ones (n+1) := by simp [fa 5 (by decide),start,base]
  obtain ⟨b,t₁,first,time₁,firstData,fb⟩ :=
    UnaryPolynomialCode.addMonomial_run (factor*firstCoeff c p) 64 p.degree (by decide) a (n+1) ba
  have bb : b.reg 5 = ones (n+1) := (fb.2 5 (by decide) (Or.inl (by decide))).trans ba
  obtain ⟨d,t₂,second,time₂,secondData,fd⟩ :=
    UnaryPolynomialCode.addMonomial_run (factor*secondCoeff p) 64 (p.degree+p.degree) (by decide) b (n+1) bb
  let out := d.write dst (d.reg 1)
  have output : Run emptyLanguage (.write dst (.copy 1)) d out 1 0 := .write
  refine ⟨out,_, .seq reset (.seq extraRun (.seq first (.seq second output))), ?_, ?_,
    fd.1.trans (fb.1.trans qa), ?_⟩
  · change t₁ + 3 ≤ (2*(factor*firstCoeff c p)+7)*(n+2)^p.degree at time₁
    change t₂ + 3 ≤ (2*(factor*secondCoeff p)+7)*(n+2)^(p.degree+p.degree) at time₂
    unfold seedTime
    omega
  · simp only [out,HullBatchMachine.write_same, secondData, firstData, initial, start,
      HullBatchMachine.write_same, List.append_nil, ones, ← List.append_assoc, List.replicate_append_replicate,
      clock_formula, Nat.mul_add]
    congr 1
    rw [Nat.mul_assoc factor, Nat.mul_assoc factor]
    ac_rfl
  · intro r h₁ h₂ high
    have weak : r < 64 ∨ 64+p.degree ≤ r := by omega
    rw [HullBatchMachine.write_ne _ _ h₂, fd.2 r h₁ high, fb.2 r h₁ weak, fa r h₁]
    simp [start,h₁]


open ReplayFrameCode (clearRange clearRange_run clearRange_allowed HighClear frameSize)

private def requestLength : Code :=
  .seq (.write 2 (.copy 0)) (.seq (setBit 5 true) (normalize 2 5 6))

private theorem requestLength_run (x : Word) :
    ∃ u t, Run emptyLanguage requestLength (State.input x) u t 0 ∧ t ≤ 5*x.length+14 ∧
      u.reg 5 = ones (x.length+1) ∧ u.reg 0 = x ∧ u.queries = [] ∧ ∀ r, 16 ≤ r → u.reg r = [] := by
  let s := State.input x
  let a := s.write 2 x
  let b := a.write 5 [true]
  have copy : Run emptyLanguage (.write 2 (.copy 0)) s a 1 0 := .write
  have start : Run emptyLanguage (setBit 5 true) a b 3 0 := setBit_run ..
  obtain ⟨u,t,run,cost,count,queue,frame⟩ :=
    normalize_run (src:=2) (dst:=5) (flag:=6) (by decide) (by decide) (by decide) b
  have input : b.reg 2 = x := by simp [b,a]
  rw [input] at cost count
  refine ⟨u,_, .seq copy (.seq start run), by omega, ?_, ?_, queue, ?_⟩
  · simpa [b, ones, List.replicate_succ'] using count
  · simpa [b,a,s,State.input] using frame 0 (by decide) (by decide) (by decide)
  · intro r hr
    rw [frame r (by omega) (by omega) (by omega)]
    simp [b,a,s,State.input, show r ≠ 0 by omega, show r ≠ 1 by omega,
      show r ≠ 2 by omega, show r ≠ 5 by omega]

private def capSetup (a b : Nat) : Code :=
  .seq (.write 1 .empty)
    (.seq (UnaryPolynomialCode.addConstant b) (.seq (.write 21 (.cons true 5)) (logCap a)))

private theorem capSetup_run (a b n : Nat) (s : State) (size : s.reg 5 = ones (n+1)) :
    ∃ u t, Run emptyLanguage (capSetup a b) s u t 0 ∧
      t ≤ (35+2*a)*(n+3)*(n+2)+2*b+17 ∧
      u.reg 1 = ones ((n+2).log2*a+b) ∧ WordCode.Preserves s u [1,21,22,23,24,25] := by
  let cleared := s.write 1 []
  have clear : Run emptyLanguage (.write 1 .empty) s cleared 1 0 := .write
  obtain ⟨bState, set, value, queue, frame⟩ := UnaryPolynomialCode.addConstant_run b cleared
  let start := bState.write 21 (ones (n+2))
  have length : bState.reg 5 = ones (n+1) := by simp [frame 5 (by decide),cleared,size]
  have copy : Run emptyLanguage (.write 21 (.cons true 5)) bState start 1 0 := by
    simpa [start,Expr.eval,length,HullBatchMachine.ones_succ] using
      stepWrite bState 21 (.cons true 5)
  obtain ⟨u,t,log,cost,result,kept⟩ := logCap_run a (n+2) start (by simp [start])
  refine ⟨u,_, .seq clear (.seq set (.seq copy log)), ?_, ?_, ?_⟩
  · have bound : t ≤ (35+2*a)*(n+3)*(n+2)+11 := cost
    omega
  · simpa [start,value,cleared,ones,Nat.mul_comm] using result
  · have p : WordCode.Preserves cleared bState [1,21,22,23,24,25] :=
      ⟨queue,fun r hr => frame r (by simp at hr; omega)⟩
    exact ((WordCode.preserves_write s 1 _).mono (by simp)).trans
      (p.trans (((WordCode.preserves_write bState 21 _).mono (by simp)).trans kept))

/-- Calculate the replay parameters from the original word. No certificate
or other auxiliary input is required. -/
def prepare (c : Code) (p : Poly) (a b : Nat) : Code :=
  .seq requestLength
    (.seq (seed c p 1 0 7)
      (.seq (seed c p 24 36 11)
        (.seq (capSetup a b) (.seq (clearRange 21 5) (clearRange 64 (p.degree+p.degree))))))

theorem prepare_pure (c : Code) (p : Poly) (a b : Nat) : (prepare c p a b).pure := by
  simp [prepare, requestLength, capSetup, normalize, HullBatchMachine.set, HullBatchMachine.scanCore,
    seed_pure, logCap_pure, clearRange_allowed, setBit, UnaryPolynomialCode.addConstant_pure, Code.allowed]

def prepareBound (c : Code) (p : Poly) (a b n : Nat) : Nat :=
  seedTime c p 1 0 n + seedTime c p 24 36 n +
  (35+2*a)*(n+3)*(n+2) + 5*n + 2*b + 2*(p.degree+p.degree) + 60


theorem prepare_run (c : Code) (p : Poly) (a b : Nat) (x : Word) :
    let budget := p.at x.length
    let clock := loweringCost (frameWidth c) budget * budget
    let cap := (x.length+2).log2*a+b
    ∃ u t, Run emptyLanguage (prepare c p a b) (State.input x) u t 0 ∧
      t ≤ prepareBound c p a b x.length ∧
      u.reg 0 = x ∧ u.reg 1 = ones cap ∧ u.reg 7 = ones clock ∧
      u.reg 11 = ones (24*clock+36) ∧ u.queries = [] ∧ HighClear c u := by
  dsimp only
  let n := x.length
  obtain ⟨s, t₀, length, lenTime, size, input, q₀, noHigh⟩ := requestLength_run x
  obtain ⟨v,t₁,clocks,clockTime,clock,q₁,p₁⟩ := seed_run c p 1 0 7 n s size
  have size' : v.reg 5 = ones (n+1) :=
    (p₁ 5 (by decide) (by decide) (Or.inl (by decide))).trans size
  obtain ⟨w,t₂,queues,queueTime,queue,q₂,p₂⟩ := seed_run c p 24 36 11 n v size'
  have size'' : w.reg 5 = ones (n+1) :=
    (p₂ 5 (by decide) (by decide) (Or.inl (by decide))).trans size'
  obtain ⟨bState,t₃,log,logTime,cap,capFrame⟩ := capSetup_run a b n w size''
  obtain ⟨d,clear₁,q₄,after₁⟩ := clearRange_run 21 5 bState
  obtain ⟨u,clear₂,q₅,after₂⟩ := clearRange_run 64 (p.degree+p.degree) d
  have low (r : Nat) (h : r < 16) : u.reg r = bState.reg r := by
    rw [after₂, if_neg (by omega), after₁, if_neg (by omega)]
  refine ⟨u,_, .seq length (.seq clocks (.seq queues (.seq log (.seq clear₁ clear₂)))),
      ?_, ?_, (low 1 (by decide)).trans cap, ?_, ?_, q₅.trans (q₄.trans
        (capFrame.1.trans (q₂.trans (q₁.trans q₀)))), ?_⟩
  · change _ ≤ prepareBound c p a b n
    change t₀ ≤ 5*n+14 at lenTime
    unfold prepareBound
    omega
  · rw [low 0 (by decide),capFrame.2 0 (by decide),
      p₂ 0 (by decide) (by decide) (Or.inl (by decide)),
      p₁ 0 (by decide) (by decide) (Or.inl (by decide)),input]
  · rw [low 7 (by decide),capFrame.2 7 (by decide),p₂ 7 (by decide) (by decide) (Or.inl (by decide))]
    simpa only [Nat.one_mul,Nat.add_zero] using clock
  · rw [low 11 (by decide),capFrame.2 11 (by decide)]
    exact queue
  · intro r high
    rw [after₂,after₁]
    split
    · rfl
    · rename_i notScratch
      split
      · rfl
      · rename_i notLog
        rw [capFrame.2 r (by simp; omega),
          p₂ r (by omega) (by omega) (by omega), p₁ r (by omega) (by omega) (by omega),
          noHigh r (by omega)]


/-- A fixed monomial dominates parameter construction at every input size. -/
theorem prepareBound_poly (c : Code) (p : Poly) (a b : Nat) :
    ∃ time : Poly, ∀ n, prepareBound c p a b n ≤ time.at n := by
  let d := p.degree+p.degree
  let degree := d+2
  let u := 2*(1*firstCoeff c p)+7
  let v := 2*(1*secondCoeff p)+7
  let w := 2*(24*firstCoeff c p)+7
  let z := 2*(24*secondCoeff p)+7
  let coef := u+v+w+z
  let linear := 35+2*a
  let constant := 5+2*b+2*d+160
  refine ⟨⟨coef*2^degree + linear*6 + constant,degree⟩, fun n => ?_⟩
  let q := (n+1)^degree
  have pow (k : Nat) (bound : k ≤ degree) : (n+2)^k ≤ 2^degree*q := by
    have upper := Nat.le_trans (Nat.pow_le_pow_left (show n+2 ≤ 2*(n+1) by omega) k)
      (Nat.pow_le_pow_right (show 1 ≤ 2*(n+1) by omega) bound)
    simpa [q,Nat.mul_pow] using upper
  have h₁ := Nat.mul_le_mul_left u (pow p.degree (by dsimp [degree,d]; omega))
  have h₂ := Nat.mul_le_mul_left v (pow d (by dsimp [degree]; omega))
  have h₃ := Nat.mul_le_mul_left w (pow p.degree (by dsimp [degree,d]; omega))
  have h₄ := Nat.mul_le_mul_left z (pow d (by dsimp [degree]; omega))
  have clockCost : u*(n+2)^p.degree+v*(n+2)^d+w*(n+2)^p.degree+z*(n+2)^d ≤ coef*(2^degree*q) := by
    dsimp only [coef]
    simp only [Nat.add_mul]
    omega
  have quad : (n+1)^2 ≤ q :=
    Nat.pow_le_pow_right (show 1 ≤ n+1 by omega) (by dsimp [degree]; omega)
  have log : (n+3)*(n+2) ≤ 6*q := by
    have times := Nat.mul_le_mul (show n+3 ≤ 3*(n+1) by omega) (show n+2 ≤ 2*(n+1) by omega)
    have regroup : 3*(n+1)*(2*(n+1)) = 6*(n+1)^2 := by
      rw [Nat.pow_two]
      calc
        _ = (3*2)*((n+1)*(n+1)) := by ac_rfl
        _ = _ := rfl
    rw [regroup] at times
    exact Nat.le_trans times (Nat.mul_le_mul_left _ quad)
  have logCost := Nat.mul_le_mul_left linear log
  have qPos : 0 < q := Nat.pow_pos (Nat.succ_pos _)
  have nq : n ≤ q := by
    apply Nat.le_trans (Nat.le_succ _)
    simpa only [Nat.pow_one] using (Nat.pow_le_pow_right
      (show 1 ≤ n+1 by omega) (show 1 ≤ degree by dsimp [degree]; omega))
  have fixed : 5*n+2*b+2*d+152 ≤ constant*q := by
    have one := Nat.le_mul_of_pos_right (2*b+2*d+160) qPos
    have two := Nat.mul_le_mul_left 5 nq
    have split : constant = 5+(2*b+2*d+160) := by dsimp [constant]; omega
    rw [split,Nat.add_mul]
    omega
  change prepareBound c p a b n ≤ (coef*2^degree+linear*6+constant)*q
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  change u*(n+2)^p.degree + v*(n+2)^d + 2*0 + 10 +
      (w*(n+2)^p.degree + z*(n+2)^d + 2*36 + 10) +
      linear*(n+3)*(n+2) + 5*n + 2*b + 2*d + 60 ≤ _
  rw [Nat.mul_assoc linear]
  omega

/-- The candidate list has a verified polynomial-time implementation with
an ordinary word input. The output is framed, and its membership agrees with
the simulated mathematical candidate list. -/
theorem candidates_fp (c : Code) (p : Poly) (a b : Nat) :
    ∃ f : WordFunction, FP f ∧ ∀ x,
      let cap := (x.length+2).log2*a+b
      ∃ candidates : List Word, f x = QueryEncoding.pack candidates ∧
        candidates.length ≤ 2^cap ∧ ∀ w, w ∈ candidates ↔
          w ∈ MachineEnumeration.compiledCandidates c x (p.at x.length) cap := by
  classical
  obtain ⟨setupTime, prepBound⟩ := prepareBound_poly c p a b
  obtain ⟨runTime, execBound⟩ := ReplayListCode.collectionBound_poly c p a b
  let code : Code := .seq (prepare c p a b)
    (.seq (ReplayListCode.collectCandidates c) (.write 0 (.copy 14)))
  let time := (setupTime.plus runTime).plus ⟨3,0⟩
  have pure : code.pure := ⟨prepare_pure .., ReplayListCode.collectCandidates_pure c, trivial⟩
  have runs (x : Word) :
      ∃ out t candidates, Run emptyLanguage code (State.input x) out t 0 ∧
        t ≤ time.at x.length ∧ out.output = QueryEncoding.pack candidates ∧
        candidates.length ≤ 2^((x.length+2).log2*a+b) ∧ ∀ w, w ∈ candidates ↔
          w ∈ MachineEnumeration.compiledCandidates c x (p.at x.length) ((x.length+2).log2*a+b) := by
    obtain ⟨s,t,prep,prepCost,input,cap,clock,queueBound,empty,high⟩ := prepare_run c p a b x
    obtain ⟨u,t',candidates,collect,collectCost,result,_,_,size,member⟩ :=
      ReplayListCode.collectCandidates_run c s (p.at x.length) ((x.length+2).log2*a+b)
        clock queueBound cap empty high
    rw [input] at collectCost member
    let out := u.write 0 (u.reg 14)
    have finish : Run emptyLanguage (.write 0 (.copy 14)) u out 1 0 := .write
    refine ⟨out,_,candidates, .seq prep (.seq collect finish), ?_,
      by simp [out, State.output, State.write,result], size, member⟩
    have p₁ := Nat.le_trans prepCost (prepBound x.length)
    have p₂ := Nat.le_trans collectCost (execBound x)
    have p₃ := Poly.plus_bound setupTime runTime x.length
    have p₄ := Poly.plus_bound (setupTime.plus runTime) ⟨3,0⟩ x.length
    rw [show (Poly.mk 3 0).at x.length = 3 by simp [Poly.at]] at p₄
    change _ ≤ ((setupTime.plus runTime).plus ⟨3,0⟩).at x.length
    omega
  let output (x : Word) : State := Classical.choose (runs x)
  let f (x : Word) := (output x).output
  refine ⟨f, ⟨code,time,pure, fun x => ?_⟩, fun x => ?_⟩
  · obtain ⟨t,_,run,cost,_⟩ := Classical.choose_spec (runs x)
    exact ⟨output x,t,run,cost,rfl⟩
  · obtain ⟨_,xs,_,_,eq,count,member⟩ := Classical.choose_spec (runs x)
    exact ⟨xs,eq,count,member⟩

/-- Any logarithmic-query function has a polynomial-time list algorithm
that outputs a list containing its value, without calling the oracle. -/
theorem list_of_log {f : WordFunction} (h : FPLogNP f) :
    ∃ g : WordFunction, FP g ∧ ∃ size : Poly, ∀ x,
      ∃ words : List Word, g x = QueryEncoding.pack words ∧
        words.length ≤ size.at x.length ∧ f x ∈ words := by
  obtain ⟨c, p, a, b, genuine⟩ := FPLogNP.compiled_candidate_bound h
  obtain ⟨g, poly, produced⟩ := candidates_fp c p a b
  refine ⟨g, poly, ⟨2^a * 2^b, a⟩, fun x => ?_⟩
  obtain ⟨words, packed, small, member⟩ := produced x
  refine ⟨words, packed, ?_, (member (f x)).mpr (genuine x).1⟩
  apply Nat.le_trans small
  apply Nat.le_trans (pow_log_cap x.length a b)
  have upper := Nat.mul_le_mul_right (2^b)
    (Nat.pow_le_pow_left (show x.length+2 ≤ 2*(x.length+1) by omega) a)
  simpa only [Poly.at, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using upper

end ReplayParameters
