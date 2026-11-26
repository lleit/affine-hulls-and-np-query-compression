module

public import ComplexityModel.WordCode
public import ComplexityModelClasses

@[expose] public section

namespace ComplexityModel.PairCode

/-- The scoped call reads an escaped first input followed by the raw second
input. Restore the two-input initial state, including the scratch registers. -/
def unpack : Code :=
  .seq (FieldCode.takeField 0 2 3 4)
    (.seq (.write 1 (.copy 0))
      (.seq (.write 0 (.copy 2))
        (.seq (.write 2 .empty)
          (.seq (.write 3 .empty) (.write 4 .empty)))))

theorem unpack_pure : unpack.pure := by
  simp [unpack, Code.allowed, FieldCode.takeField_pure]

theorem unpack_run (input : Word) :
    ∃ t, Run emptyLanguage unpack (State.input input)
      (State.input (QueryEncoding.take input).1 (QueryEncoding.take input).2) t 0 ∧
      t ≤ 14 * input.length + 27 := by
  let s := State.input input
  let x := (QueryEncoding.take input).1
  let w := (QueryEncoding.take input).2
  obtain ⟨parsed, time, scan, readTime, tail, data, queue, frame⟩ :=
    FieldCode.takeField_run s (src := 0) (dst := 2) (scratch := 3) (flag := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change parsed.reg 0 = w at tail
  change parsed.reg 2 = x at data
  change time ≤ 14 * input.length + 17 at readTime
  let a := parsed.write 1 w
  let b := a.write 0 x
  let c := b.write 2 []
  let d := c.write 3 []
  let e := d.write 4 []
  have copyWitness : Run emptyLanguage (.write 1 (.copy 0)) parsed a 1 0 := by
    simpa only [a, Expr.eval, tail] using (Run.write (A := emptyLanguage) (s := parsed)
      (d := 1) (e := .copy 0))
  have copyInput : Run emptyLanguage (.write 0 (.copy 2)) a b 1 0 := by
    have hx : a.reg 2 = x := by simp [a, State.write, data]
    simpa only [b, Expr.eval, hx] using (Run.write (A := emptyLanguage) (s := a)
      (d := 0) (e := .copy 2))
  have clear₂ : Run emptyLanguage (.write 2 .empty) b c 1 0 := .write
  have clear₃ : Run emptyLanguage (.write 3 .empty) c d 1 0 := .write
  have clear₄ : Run emptyLanguage (.write 4 .empty) d e 1 0 := .write
  have asInput : e = State.input x w := by
    refine State.ext ?_ queue
    funext r
    by_cases h0 : r = 0
    · subst r
      rfl
    by_cases h1 : r = 1
    · subst r
      rfl
    by_cases h2 : r = 2
    · subst r
      rfl
    by_cases h3 : r = 3
    · subst r
      rfl
    by_cases h4 : r = 4
    · subst r
      rfl
    simp [e, d, c, b, a, State.write, h0, h1, h2, h3, h4, frame r h0 h2 h3 h4, s, State.input]
  rw [← asInput]
  exact ⟨_, .seq scan (.seq copyWitness (.seq copyInput (.seq clear₂ (.seq clear₃ clear₄)))),
    by omega⟩

/-- Call an arbitrary deterministic two-input subprogram inside an empty
register file and query stack. Only the result register is modified. -/
def call (src dst : Nat) (body : Code) : Code := .callBit (.reg src) dst (.seq unpack body)

theorem call_pure (src dst : Nat) {c : Code} (h : c.pure) : (call src dst c).pure :=
  ⟨unpack_pure, h⟩

theorem call_run {c : Code} {x w : Word} {out : State} {t : Nat}
    (verify : Run emptyLanguage c (State.input x w) out t 0) (s : State) {src dst : Nat}
    (input : s.reg src = QueryEncoding.put x w) :
    ∃ elapsed,
      Run emptyLanguage (call src dst c) s (s.write dst [decide (out.output = [true])]) elapsed 0 ∧
      elapsed ≤ t + 28 * x.length + 14 * w.length + 43 := by
  obtain ⟨readTime, read, cost⟩ := unpack_run (s.reg src)
  have decoded : QueryEncoding.take (s.reg src) = (x, w) := by
    rw [input, QueryEncoding.take_put]
  rw [decoded] at read
  refine ⟨readTime + t + 2, ?_, ?_⟩
  · have action : Run emptyLanguage (.seq unpack c) (State.input (s.reg src)) out
        (readTime + t + 1) 0 := .seq read verify
    exact .callSome rfl action
  · rw [input, QueryEncoding.put_length] at cost
    omega

/-- Uniform polynomial bound when the two-input subprogram is polynomial. -/
theorem call_check {check : Word → Word → Bool} {c : Code} {time : Poly}
    (code : ∀ x w, ∃ out t, Run emptyLanguage c (State.input x w) out t 0 ∧
      t ≤ time.at (x.length + w.length) ∧ (out.output = [true] ↔ check x w = true))
    (s : State) {src dst : Nat} {x w : Word} (input : s.reg src = QueryEncoding.put x w) :
    ∃ t, Run emptyLanguage (call src dst c) s (s.write dst [check x w]) t 0 ∧
      t ≤ (time.plus ⟨43, 1⟩).at (x.length + w.length) := by
  obtain ⟨out, t, run, timeBound, spec⟩ := code x w
  obtain ⟨elapsed, exec, cost⟩ := call_run run s (dst := dst) input
  have same : decide (out.output = [true]) = check x w := by
    cases h : check x w <;> simp_all
  refine ⟨elapsed, by simpa only [same] using exec, ?_⟩
  have majorant := Poly.plus_bound time ⟨43, 1⟩ (x.length + w.length)
  have linear : (Poly.mk 43 1).at (x.length + w.length) = 43 * (x.length + w.length + 1) := by
    simp [Poly.at]
  rw [linear] at majorant
  omega

end ComplexityModel.PairCode
