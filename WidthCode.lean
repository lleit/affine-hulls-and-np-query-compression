module

public import ComplexityModel.WordCode
public import HullBatchMachine

@[expose] public section

namespace WidthCode

open ComplexityModel
open HullBatchMachine (ones forUnary forUnary_run stepWrite)
open WordCode (Preserves prependHead prependHead_run preserves_write)

def resize : Nat → Word → Word
  | 0, _ => []
  | n + 1, w => w.headD false :: resize n w.tail

theorem resize_length (n : Nat) (w : Word) : (resize n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [resize, ih]

theorem resize_eq_word (n : Nat) (w : Word) : resize n w = HullDecoder.word (HullDecoder.bits w n) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [resize, ih]
    change _ = List.ofFn (HullDecoder.bits w (n+1))
    rw [List.ofFn_succ]
    cases w <;> simp [HullDecoder.word, HullDecoder.bits, Fin.succ] <;> rfl

private def collect : Code :=
  .seq (prependHead 22 23) (.write 22 (.tail 22))

/-- Resize the raw row in register 22 to the unary width in register 21.
Registers 23 and 24 are scratch and the width is consumed. -/
def resizeCode : Code :=
  .seq (.write 23 .empty)
    (.seq (forUnary 21 collect) (FieldCode.reverse 23 22 24))

theorem resize_allowed (p d q : Bool) : resizeCode.allowed p d q := by
  simp [resizeCode, collect, forUnary, prependHead, FieldCode.reverse_allowed, Code.allowed]

theorem resize_run (s : State) (n : Nat) (clock : s.reg 21 = ones n) :
    ∃ u t, Run emptyLanguage resizeCode s u t 0 ∧ t ≤ 13 * n + 14 ∧
      u.reg 22 = resize n (s.reg 22) ∧ Preserves s u [21, 22, 23, 24] := by
  let start := s.write 23 []
  let I (k : Nat) (st : State) : Prop :=
    (st.reg 23).reverse ++ resize k (st.reg 22) = resize n (s.reg 22) ∧
      Preserves s st [21, 22, 23, 24]
  have clear : Run emptyLanguage (.write 23 .empty) s start 1 0 := .write
  have step (k : Nat) (u : State) (kc : u.reg 21 = ones (k+1)) (ih : I (k+1) u) :
      ∃ v t, Run emptyLanguage collect u v t 0 ∧ t ≤ 4 ∧ v.reg 21 = ones (k+1) ∧
        I k (v.write 21 (ones k)) := by
    let a := u.write 23 ((u.reg 22).headD false :: u.reg 23)
    let b := a.write 22 (u.reg 22).tail
    have moved : Run emptyLanguage (prependHead 22 23) u a 2 0 :=
      prependHead_run emptyLanguage u 22 23
    have pop : Run emptyLanguage (.write 22 (.tail 22)) a b 1 0 := by
      simpa [a, b, Expr.eval] using stepWrite a 22 (.tail 22)
    refine ⟨b, 4, .seq moved pop, by decide, by simp [a, b, kc], ?_, ?_⟩
    · simpa [a, b, resize, List.append_assoc] using ih.1
    · exact ih.2.trans (((preserves_write u 23 _).mono (by simp)).trans
        (((preserves_write a 22 _).mono (by simp)).trans ((preserves_write b 21 _).mono (by simp))))
  have initial : I n start :=
    ⟨by simp [start], (preserves_write ..).mono (by simp)⟩
  obtain ⟨mid, t, run, time, _, inv⟩ := forUnary_run I step n start (by simpa [start] using clock) initial
  have output : (mid.reg 23).reverse = resize n (s.reg 22) := by
    simpa [resize, I] using inv.1
  have len : (mid.reg 23).length = n := by
    simpa [resize_length] using congrArg List.length output
  obtain ⟨out, reverse, _, value, queue, preserved⟩ :=
    FieldCode.reverse_run mid (src := 23) (dst := 22) (flag := 24) (by decide) (by decide) (by decide)
  rw [len] at reverse
  refine ⟨out, _, .seq clear (.seq run reverse), by omega, value.trans output, ?_⟩
  apply inv.2.trans
  refine ⟨queue, fun r hr => ?_⟩
  simp at hr
  exact preserved r (by omega) (by omega) (by omega)

end WidthCode
