module

public import SearchLoopCode
public import UnaryPolynomialCode
public import FixedVerifier

@[expose] public section

namespace SearchInitCode

open ComplexityModel
open HullBatchMachine (ones normalize normalize_run stepWrite)
open WordCode (setBit setBit_run)

def setup (p : Poly) : Code :=
  .seq (.write 2 (.copy 0))
    (.seq (setBit 5 true)
      (.seq (normalize 2 5 6)
        (.seq (setBit 1 true)
          (.seq (UnaryPolynomialCode.addMonomial (2*p.coefficient) 64 p.degree)
            (.seq (.write 2 .empty) (setBit 3 true))))))

theorem setup_pure (p : Poly) : (setup p).pure := by
  have count : (normalize 2 5 6).pure := by
    simp [normalize, HullBatchMachine.set, HullBatchMachine.scanCore, Code.allowed]
  simp [setup, setBit, Code.allowed, count, UnaryPolynomialCode.addMonomial_pure]

def setupTime (p : Poly) : Poly :=
  (Poly.mk ((4*p.coefficient+7)*2^p.degree) p.degree).plus ⟨40, 1⟩

theorem setup_run (p : Poly) :
    SearchLoopCode.Initializes (FixedVerifier.width p) (setup p) (setupTime p) := by
  intro x
  let s := State.input x
  let a := s.write 2 x
  have copy : Run emptyLanguage (.write 2 (.copy 0)) s a 1 0 := .write
  let b := a.write 5 [true]
  have base : Run emptyLanguage (setBit 5 true) a b 3 0 := setBit_run ..
  obtain ⟨c, t₁, norm, lengthTime, counter, queue, keep⟩ :=
    normalize_run (src := 2) (dst := 5) (flag := 6) (by decide) (by decide) (by decide) b
  have len : c.reg 5 = ones (x.length+1) := by
    simpa [b, a, ones, List.replicate_succ'] using counter
  let d := c.write 1 [true]
  have initial : Run emptyLanguage (setBit 1 true) c d 3 0 := setBit_run ..
  obtain ⟨e, t₂, monomial, monoTime, width, frame⟩ :=
    UnaryPolynomialCode.addMonomial_run (2*p.coefficient) 64 p.degree (by decide) d
      (x.length+1) (by simpa [d] using len)
  let f := e.write 2 []
  let out := f.write 3 [true]
  have nilHistory : Run emptyLanguage (.write 2 .empty) e f 1 0 := .write
  have enabled : Run emptyLanguage (setBit 3 true) f out 3 0 := setBit_run ..
  refine ⟨out, _, .seq copy (.seq base (.seq norm (.seq initial (.seq monomial (.seq nilHistory enabled))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have inputLen : b.reg 2 = x := by simp [a,b]
    rw [inputLen] at lengthTime
    have power := Nat.pow_le_pow_left (show x.length+1+1 ≤ 2*(x.length+1) by omega) p.degree
    rw [Nat.mul_pow] at power
    have poly := Nat.mul_le_mul_left (4*p.coefficient+7) power
    rw [← Nat.mul_assoc] at poly
    have eq : 2*(2*p.coefficient)+7 = 4*p.coefficient+7 := by omega
    rw [eq] at monoTime
    have total := Poly.plus_bound (Poly.mk ((4*p.coefficient+7)*2^p.degree) p.degree) ⟨40,1⟩ x.length
    change (4*p.coefficient+7)*2^p.degree*(x.length+1)^p.degree +
      40*(x.length+1)^1 ≤ (setupTime p).at x.length at total
    rw [Nat.pow_one] at total
    omega
  · simp [out, f, frame.2 0 (by decide) (Or.inl (by decide)), d,
      keep 0 (by decide) (by decide) (by decide), b, a, s, State.input]
  · simp [out, f, width, d, FixedVerifier.width, Poly.at, Nat.mul_assoc, ones, List.replicate_succ']
  · simp [out, f, QueryEncoding.pack]
  · simp [out]
  · exact frame.1.trans queue

def widthBound (p : Poly) : Poly := ⟨2*p.coefficient+2, p.degree⟩

theorem width_bound (p : Poly) (x : Word) : FixedVerifier.width p x + 1 ≤ (widthBound p).at x.length := by
  change 2*(p.coefficient*(x.length+1)^p.degree)+1+1 ≤
    (2*p.coefficient+2)*(x.length+1)^p.degree
  rw [Nat.add_mul, Nat.mul_assoc]
  have pos : 0 < (x.length+1)^p.degree := Nat.pow_pos (Nat.succ_pos _)
  have two := Nat.le_mul_of_pos_right 2 pos
  omega

end SearchInitCode
