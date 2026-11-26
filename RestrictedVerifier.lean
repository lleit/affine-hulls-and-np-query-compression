module

public import ComplexityModel.HistoryCode
public import ComplexityModel.PairCode

@[expose] public section

namespace RestrictedVerifier

open ComplexityModel
open QueryEncoding (take readRequest)
open WordCode (putField)

abbrev Checker := Word → Word → Bool

/-- The original checker on the witness reconstructed from the request.
The request's width is used by the caller when choosing the input length. -/
def check (checker : Checker) (s w : Word) : Bool :=
  let r := readRequest s
  checker r.input (AffineSearch.decode r.history w)

private theorem inflate_length_le (mask w : Word) :
    (AffineSearch.inflate mask w).length ≤ w.length + 1 := by
  induction mask generalizing w with
  | nil => simp [AffineSearch.inflate]
  | cons bit bits ih =>
    cases bit
    · cases w with
      | nil => simp [AffineSearch.inflate]
      | cons b w =>
        have bound := ih w
        simp only [AffineSearch.inflate, List.length_cons]
        omega
    · simp [AffineSearch.inflate]

private theorem decode_length_le (history : List Word) (w : Word) :
    (AffineSearch.decode history w).length ≤ w.length + history.length := by
  induction history generalizing w with
  | nil => simp [AffineSearch.decode]
  | cons mask history ih =>
    have restored := inflate_length_le mask w
    have bound := ih (AffineSearch.inflate mask w)
    rw [AffineSearch.decode_cons]
    simp only [List.length_cons]
    omega

private theorem unpack_length_le (fuel : Nat) (s : Word) :
    (QueryEncoding.unpack fuel s).length ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [QueryEncoding.unpack]
  | succ fuel ih =>
    unfold QueryEncoding.unpack
    split
    · simp
    · cases h : take s with
      | mk field suffix =>
        simpa only [List.length_cons, Nat.add_le_add_iff_right] using ih suffix

private def prepare : Code :=
  .seq (.write 11 (.copy 1))
    (.seq (FieldCode.takeField 0 2 7 8)
      (.seq (FieldCode.takeField 0 4 7 8) (.write 17 (.copy 0))))

private theorem prepare_run (s w : Word) :
    ∃ u t, Run emptyLanguage prepare (State.input s w) u t 0 ∧ t ≤ 28 * s.length + 40 ∧
      u.reg 2 = (take s).1 ∧ u.reg 11 = w ∧ u.reg 17 = (take (take s).2).2 := by
  let start := State.input s w
  let a := start.write 11 w
  have save : Run emptyLanguage (.write 11 (.copy 1)) start a 1 0 := by
    simpa [a, start, Expr.eval, State.input] using
      (Run.write (A := emptyLanguage) (s := start) (d := 11) (e := .copy 1))
  obtain ⟨first, t, parse, cost, tail, data, _, others⟩ :=
    FieldCode.takeField_run a (src := 0) (dst := 2) (scratch := 7) (flag := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have startValue : a.reg 0 = s := by rfl
  rw [startValue] at tail data cost
  obtain ⟨second, t', skipWidth, cost', history, _, _, others'⟩ :=
    FieldCode.takeField_run first (src := 0) (dst := 4) (scratch := 7) (flag := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [tail] at cost' history
  let u := second.write 17 (second.reg 0)
  have copy : Run emptyLanguage (.write 17 (.copy 0)) second u 1 0 := .write
  refine ⟨u, _, .seq save (.seq parse (.seq skipWidth copy)), ?_, ?_, ?_, ?_⟩
  · have bound := QueryEncoding.take_lengths s
    omega
  · have keep := others' 2 (by decide) (by decide) (by decide) (by decide)
    simpa [u, State.write, data] using keep
  · have keep := others' 11 (by decide) (by decide) (by decide) (by decide)
    rw [others 11 (by decide) (by decide) (by decide) (by decide)] at keep
    simpa [u, a, State.write] using keep
  · simpa [u, State.write] using history

/-- Restore a restricted witness before running the original verifier.
The original verifier executes in a fresh state. -/
def compile (c : Code) : Code :=
  .seq prepare
    (.seq HistoryCode.decode
      (.seq (.write 9 (.copy 11))
        (.seq (putField 2 9 5 6 7) (PairCode.call 9 0 c))))

theorem compile_pure {c : Code} (pure : c.pure) : (compile c).pure := by
  simp [compile, prepare, Code.allowed, FieldCode.takeField_pure, HistoryCode.decode_allowed,
    WordCode.putField_allowed, PairCode.call_pure _ _ pure]

/-- The checked compiler handles every request word and every proposed
witness, including malformed requests. -/
theorem compile_run {c : Code} {time : Poly} {checker : Checker}
    (code : ∀ x w, ∃ out t, Run emptyLanguage c (State.input x w) out t 0 ∧
      t ≤ time.at (x.length + w.length) ∧ (out.output = [true] ↔ checker x w = true))
    (s w : Word) :
    ∃ out t, Run emptyLanguage (compile c) (State.input s w) out t 0 ∧
      t ≤ ((time.plus ⟨43, 1⟩).plus ⟨300, 2⟩).at (s.length + w.length) ∧
      out.output = [check checker s w] := by
  let x := (take s).1
  let history := (take (take s).2).2
  let witness := AffineSearch.decode (QueryEncoding.unpack history.length history) w
  have checkEq : check checker s w = checker x witness := by
    rfl
  obtain ⟨prepared, t₁, setup, time₁, hx, hw, hh⟩ := prepare_run s w
  change prepared.reg 2 = x at hx
  change prepared.reg 17 = history at hh
  obtain ⟨restored, t₂, restore, time₂, value, frame⟩ := HistoryCode.decode_run prepared
  rw [hh, hw] at value
  rw [hh] at time₂
  have xSaved : restored.reg 2 = x := (frame.2 2 (by decide)).trans hx
  let staged := restored.write 9 witness
  have reserve : Run emptyLanguage (.write 9 (.copy 11)) restored staged 1 0 := by
    simpa only [staged, Expr.eval, value] using
      (Run.write (A := emptyLanguage) (s := restored) (d := 9) (e := .copy 11))
  obtain ⟨packet, packed, packetWord, _⟩ := WordCode.putField_run staged
    (src := 2) (dst := 9) (tmp := 5) (rev := 6) (flag := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sx : staged.reg 2 = x := by simp [staged, State.write, xSaved]
  have pkt : packet.reg 9 = QueryEncoding.put x witness := by
    rw [packetWord, sx]
    simp [staged, State.write]
  obtain ⟨t₃, invoked, time₃⟩ := PairCode.call_check code packet (dst := 0) pkt
  have all := Run.seq setup (Run.seq restore (Run.seq reserve (Run.seq packed invoked)))
  refine ⟨_, _, all, ?_, by simp [State.output, State.write, checkEq]⟩
  let n := s.length + w.length
  have fields := QueryEncoding.take_lengths s
  have suffix := QueryEncoding.take_lengths (take s).2
  have fit : x.length + history.length ≤ s.length := by
    dsimp [x, history]
    omega
  have shorter : witness.length ≤ w.length + history.length :=
    Nat.le_trans (decode_length_le _ _) (Nat.add_le_add_left (unpack_length_le ..) _)
  have callSize : x.length + witness.length ≤ n := by dsimp [n]; omega
  have callBound := Nat.le_trans time₃ ((time.plus ⟨43, 1⟩).mono callSize)
  have histBound : history.length ≤ n := by dsimp [n]; omega
  have decodeBound : 120 * (history.length + 1) * history.length ≤ 120 * (n+1)^2 := by
    rw [Nat.pow_two, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have linearBound : n + 1 ≤ (n+1)^2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have sum := Poly.plus_bound (time.plus ⟨43, 1⟩) ⟨300, 2⟩ n
  have big : (Poly.mk 300 2).at n = 300 * (n + 1) ^ 2 := rfl
  rw [big] at sum
  rw [sx]
  change _ ≤ ((time.plus ⟨43, 1⟩).plus ⟨300, 2⟩).at n
  have ns : s.length ≤ n := by dsimp [n]; omega
  omega

end RestrictedVerifier
