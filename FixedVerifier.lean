module

public import MachineEnumeration
public import ComplexityModel.FieldCode
public import ComplexityModelClasses

@[expose] public section

namespace FixedVerifier

open ComplexityModel

def HaltsWithin (c : Code) (p : Poly) : Prop :=
  ∀ x w, ∃ s time, Run emptyLanguage c (State.input x w) s time 0 ∧
    time ≤ p.at (x.length + w.length)

def accepts (c : Code) (p : Poly) (x w : Word) : Bool :=
  match MachineEnumeration.replayCode c (State.input x w) (2 * p.at (x.length + w.length)) [] with
  | none => false
  | some (s, _, _) => s.output == [true]

theorem accepts_correct {c : Code} {p : Poly} (halts : HaltsWithin c p) (x w : Word) :
    accepts c p x w = true ↔
      ∃ u t, Run emptyLanguage c (State.input x w) u t 0 ∧ u.output = [true] := by
  obtain ⟨s, time, run, bound⟩ := halts x w
  obtain ⟨left, replay⟩ := MachineEnumeration.replayCode_of_run run (Nat.mul_le_mul_left 2 bound)
  unfold accepts
  rw [replay]
  simp only [beq_iff_eq]
  constructor
  · intro output
    exact ⟨s, time, run, output⟩
  · rintro ⟨u, _, other, output⟩
    rw [(run.deterministic other).1, output]

/-- Escape and terminate a variable-length witness, then fill the remaining
positions with zeroes to give the affine search a fixed width. -/
def width (p : Poly) (x : Word) : Nat := 2 * p.at x.length + 1

def pad (k : Nat) (w : Word) : Word := QueryEncoding.put w (List.replicate (2 * (k - w.length)) false)

@[simp] theorem unpad (k : Nat) (w : Word) : (QueryEncoding.take (pad k w)).1 = w := by
  simp [pad]

theorem pad_length (k : Nat) (w : Word) (h : w.length ≤ k) : (pad k w).length = 2 * k + 1 := by
  simp only [pad, QueryEncoding.put_length, List.length_replicate]
  omega

def check (c : Code) (timeBound : Poly) (x w : Word) : Bool :=
  accepts c timeBound x (QueryEncoding.take w).1

/-- Decode the padded input in register one before running the original
verifier. Reset all scratch registers so the verifier sees its usual input. -/
def compile (c : Code) : Code :=
  .seq (FieldCode.takeField 1 2 3 4)
    (.seq (.write 1 (.copy 2))
      (.seq (.write 2 .empty)
        (.seq (.write 3 .empty) (.seq (.write 4 .empty) c))))

theorem compile_pure (c : Code) (hc : c.pure) : (compile c).pure := by
  simpa [compile, Code.allowed, FieldCode.takeField_pure]

theorem compile_correct {c : Code} {p : Poly} (halts : HaltsWithin c p) (x w : Word) :
    ∃ out steps, Run emptyLanguage (compile c) (State.input x w) out steps 0 ∧
      steps ≤ (p.plus ⟨40, 1⟩).at (x.length + w.length) ∧
      (out.output = [true] ↔ check c p x w = true) := by
  let raw := (QueryEncoding.take w).1
  let input := State.input x w
  obtain ⟨parsed, t, scan, cost, _, data, queues, unchanged⟩ :=
    FieldCode.takeField_run input (src := 1) (dst := 2) (scratch := 3) (flag := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change parsed.reg 2 = raw at data
  let a := parsed.write 1 raw
  let b := a.write 2 []
  let d := b.write 3 []
  let e := d.write 4 []
  have load : Run emptyLanguage (.write 1 (.copy 2)) parsed a 1 0 := by
    simpa only [a, Expr.eval, data] using
      (Run.write (A := emptyLanguage) (s := parsed) (d := 1) (e := .copy 2))
  have clear₂ : Run emptyLanguage (.write 2 .empty) a b 1 0 := .write
  have clear₃ : Run emptyLanguage (.write 3 .empty) b d 1 0 := .write
  have clear₄ : Run emptyLanguage (.write 4 .empty) d e 1 0 := .write
  have asInput : e = State.input x raw := by
    have eqState (s u : State) (regs : s.reg = u.reg) (queue : s.queries = u.queries) : s = u := by
      cases s
      cases u
      cases regs
      cases queue
      rfl
    apply eqState
    · funext r
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
      simp [e, d, b, a, State.write, h1, h2, h3, h4, unchanged r h1 h2 h3 h4, input, State.input]
    · exact queues
  obtain ⟨out, elapsed, verify, time⟩ := halts x raw
  rw [← asInput] at verify
  have run := Run.seq scan (Run.seq load (Run.seq clear₂ (Run.seq clear₃ (Run.seq clear₄ verify))))
  refine ⟨out, _, run, ?_, ?_⟩
  · have len := QueryEncoding.take_data_le w
    have verifyTime := Nat.le_trans time (p.mono (Nat.add_le_add_left len x.length))
    have combined := Poly.plus_bound p ⟨40, 1⟩ (x.length + w.length)
    simp only [input, State.input, if_neg (show 1 ≠ 0 by decide), ↓reduceIte] at cost
    have linear : (Poly.mk 40 1).at (x.length + w.length) =
        40 * (x.length + w.length + 1) := by simp [Poly.at]
    rw [linear] at combined
    omega
  · change out.output = [true] ↔ accepts c p x raw = true
    rw [accepts_correct halts]
    constructor
    · intro accepts
      exact ⟨out, elapsed, asInput ▸ verify, accepts⟩
    · rintro ⟨s, _, other, accepts⟩
      exact (verify.deterministic (asInput.symm ▸ other)).1.symm ▸ accepts

theorem represents {A : Language} (h : NP A) :
    ∃ c : Code, ∃ witnessBound timeBound : Poly, c.pure ∧ HaltsWithin c timeBound ∧
      ∀ x, A x ↔ ∃ w, w.length = width witnessBound x ∧ check c timeBound x w = true := by
  obtain ⟨c, p, q, pure, halts, certifies⟩ := h
  refine ⟨c, p, q, pure, halts, fun x => ?_⟩
  rw [certifies]
  constructor
  · rintro ⟨w, bound, run⟩
    refine ⟨pad (p.at x.length) w, pad_length _ _ bound, ?_⟩
    simp [check, (accepts_correct halts x w).mpr run]
  · rintro ⟨w, size, acceptsPadded⟩
    have depth := QueryEncoding.take_lengths w
    change w.length = 2 * p.at x.length + 1 at size
    exact ⟨_, by omega, (accepts_correct halts x _).mp acceptsPadded⟩

end FixedVerifier
