module

public import HullBatchMachine
public import ComplexityModel.WordCode

@[expose] public section

namespace UnaryPolynomialCode

open ComplexityModel
open HullBatchMachine (ones forUnary forUnary_run stepWrite normalize normalize_run)
open WordCode (setBit setBit_run)

def addConstant : Nat → Code
  | 0 => .skip
  | c + 1 => .seq (.write 1 (.cons true 1)) (addConstant c)

theorem addConstant_pure (c : Nat) : (addConstant c).pure := by
  induction c <;> simp_all [addConstant, Code.allowed]

theorem addConstant_run (c : Nat) (s : State) :
    ∃ u, Run emptyLanguage (addConstant c) s u (2*c+1) 0 ∧
      u.reg 1 = ones c ++ s.reg 1 ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 1 → u.reg r = s.reg r := by
  induction c generalizing s with
  | zero => exact ⟨s, .skip, rfl, rfl, fun _ _ => rfl⟩
  | succ c ih =>
    let a := s.write 1 (true :: s.reg 1)
    have push : Run emptyLanguage (.write 1 (.cons true 1)) s a 1 0 := .write
    obtain ⟨u, run, result, q, rest⟩ := ih a
    have time : 2*(c+1)+1 = 1+(2*c+1)+1 := by omega
    refine ⟨u, by rw [time]; exact .seq push run, ?_, q, ?_⟩
    · simp [result, a, ones, List.replicate_succ', List.append_assoc]
    · intro r hr
      simp [rest r hr, a, hr]

/-- Add a unary monomial to register 1. The base of the power stays in
register 5, and each nesting level uses a fresh loop counter. -/
def addMonomial (coefficient base : Nat) : Nat → Code
  | 0 => addConstant coefficient
  | k+1 => .seq (.write (base+k) (.copy 5)) (forUnary (base+k) (addMonomial coefficient base k))

theorem addMonomial_pure (c base degree : Nat) : (addMonomial c base degree).pure := by
  induction degree <;> simp_all [addMonomial, forUnary, Code.allowed, addConstant_pure]

private def Frame (base degree : Nat) (s u : State) : Prop :=
  u.queries = s.queries ∧
    ∀ r, r ≠ 1 → (r < base ∨ base + degree ≤ r) → u.reg r = s.reg r

theorem addMonomial_run (c base degree : Nat) (high : 5 < base) (s : State) (n : Nat)
    (source : s.reg 5 = ones n) :
    ∃ u t, Run emptyLanguage (addMonomial c base degree) s u t 0 ∧
      t + 3 ≤ (2*c+7)*(n+1)^degree ∧ u.reg 1 = ones (c*n^degree) ++ s.reg 1 ∧
      Frame base degree s u := by
  induction degree generalizing s with
  | zero =>
    obtain ⟨u, run, res, q, keep⟩ := addConstant_run c s
    refine ⟨u, _, run, ?_, by simpa using res, q, fun r hr _ => keep r hr⟩
    simp
  | succ k ih =>
    let counter := base+k
    let start := s.write counter (ones n)
    let unit := c*n^k
    let budget := (2*c+7)*(n+1)^k
    have minimum : 7 ≤ budget := by
      dsimp [budget]
      have pos : 0 < (n+1)^k := Nat.pow_pos (by omega)
      exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ pos)
    let I (remaining : Nat) (u : State) :=
      remaining ≤ n ∧ u.reg 5 = ones n ∧
      u.reg 1 = ones (unit*(n-remaining)) ++ s.reg 1 ∧ Frame base (k+1) s u
    have copy : Run emptyLanguage (.write counter (.copy 5)) s start 1 0 := by
      simpa only [start, Expr.eval, source] using stepWrite s counter (.copy 5)
    have initial : I n start := by
      refine ⟨Nat.le_refl n, ?_, ?_, rfl, ?_⟩
      · simp [start, counter, show 5 ≠ base+k by omega, source]
      · simp [start, counter, show 1 ≠ base+k by omega]
      · intro r _ outside
        have ne : r ≠ counter := by dsimp [counter]; omega
        simp [start, ne]
    have step (m : Nat) (u : State) (clock : u.reg counter = ones (m+1)) (inv : I (m+1) u) :
        ∃ v t, Run emptyLanguage (addMonomial c base k) u v t 0 ∧ t ≤ budget - 3 ∧
          v.reg counter = ones (m+1) ∧ I m (v.write counter (ones m)) := by
      obtain ⟨remaining, src, soFar, inFrame⟩ := inv
      obtain ⟨v, t, work, time, result, frame⟩ := ih u src
      have count : v.reg counter = ones (m+1) :=
        (frame.2 counter (by dsimp [counter]; omega) (Or.inr (Nat.le_refl _))).trans clock
      refine ⟨v, t, work, by dsimp [budget]; omega, count, by omega, ?_, ?_, ?_⟩
      · simp [counter, show 5 ≠ base+k by omega, frame.2 5 (by decide) (Or.inl high), src]
      · have diff : n-m = 1+(n-(m+1)) := by omega
        simp only [counter, HullBatchMachine.write_ne _ _ (show 1 ≠ base+k by omega), result,
          soFar, diff, Nat.mul_add, Nat.mul_one, List.append_assoc]
        simp [ones, unit, ← List.append_assoc]
      · refine ⟨frame.1.trans inFrame.1, fun r different outside => ?_⟩
        have ne : r ≠ counter := by dsimp [counter]; omega
        have left : r < base ∨ base+k ≤ r := by omega
        simp [ne, frame.2 r different left, inFrame.2 r different outside]
    obtain ⟨out, t, loop, time, _, _remain, _src, result, keep⟩ :=
      forUnary_run I step n start (by simp [start]) initial
    refine ⟨out, _, .seq copy loop, ?_, ?_, keep⟩
    · rw [Nat.sub_add_cancel (show 3 ≤ budget by omega)] at time
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      rw [show (2*c+7)*(n+1)^k = budget from rfl, Nat.mul_succ]
      omega
    · simpa only [Nat.sub_zero, Nat.pow_succ, Nat.mul_assoc, unit] using result

end UnaryPolynomialCode
