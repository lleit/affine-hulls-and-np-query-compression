module

public import MachineEnumeration
public import ComplexityModel.WordCode
public import ComplexityModel.ReplayFrameCode
public import ComplexityModelClasses

/-! Enumerate answer tapes with a little-endian binary counter. The cost
bound charges every visit and every counter transition in the actual machine.
Registers 3 through 6 belong to the iterator. -/

@[expose] public section

namespace ComplexityModel.ReplayListCode

open WordCode (Preserves preserves_write setBit setBit_run)

local infixr:60 " ▷ " => Code.seq

private theorem branchTrue {s u : State} {test : Test} {a b : Code} {t : Nat}
    (h : test.eval s = true) (run : Run emptyLanguage a s u t 0) :
    Run emptyLanguage (.branch test a b) s u (t + 1) 0 := .branch h run

private theorem branchFalse {s u : State} {test : Test} {a b : Code} {t : Nat}
    (h : test.eval s = false) (run : Run emptyLanguage b s u t 0) :
    Run emptyLanguage (.branch test a b) s u (t + 1) 0 := .branch h run

/-- Numerical order of tapes with the least significant bit first. -/
def value : Word → Nat
  | [] => 0
  | b :: tape => 2 * value tape + (if b then 1 else 0)

def next : Word → Option Word
  | [] => none
  | false :: tape => some (true :: tape)
  | true :: tape => (next tape).map (false :: ·)

theorem value_lt (tape : Word) : value tape < 2 ^ tape.length := by
  induction tape with
  | nil => decide
  | cons b tape ih =>
    cases b <;> simp only [List.length_cons, Nat.pow_succ, value, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero] <;> omega

theorem value_injective {v w : Word} (len : v.length = w.length) (val : value v = value w) :
    v = w := by
  induction v generalizing w with
  | nil => simpa using len.symm
  | cons b v ih =>
    cases w with
    | nil => simp at len
    | cons c w =>
      have hlen : v.length = w.length := by simpa using len
      have same : b = c ∧ value v = value w := by
        cases b <;> cases c <;> simp [value] at val ⊢ <;> omega
      simp [same.1, ih hlen same.2]

theorem next_spec (tape : Word) :
    match next tape with
    | none => value tape + 1 = 2 ^ tape.length
    | some afterwards => afterwards.length = tape.length ∧ value afterwards = value tape + 1 := by
  induction tape with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false =>
      simp [next, value]
    | true =>
      cases h : next rest with
      | none =>
        have eq : value rest + 1 = 2 ^ rest.length := by simpa only [h] using ih
        simp only [next, h, Option.map_none]
        change 2 * value rest + 1 + 1 = 2 ^ (rest.length + 1)
        rw [Nat.pow_succ]
        omega
      | some w =>
        have eq : w.length = rest.length ∧ value w = value rest + 1 := by simpa only [h] using ih
        simp only [next, h, Option.map_some]
        change w.length + 1 = rest.length + 1 ∧ 2 * value w + 0 = 2 * value rest + 1 + 1
        exact ⟨by omega, by omega⟩

private def ones (n : Nat) : Word := List.replicate n true

@[simp] private theorem ones_succ (n : Nat) : ones (n + 1) = true :: ones n :=
  List.replicate_succ

/-- Return the suffix after the initial ones and the number stripped. -/
private def strip : Word → Word × Nat
  | true :: rest => let result := strip rest; (result.1, result.2 + 1)
  | tape => (tape, 0)

private theorem strip_decomp (tape : Word) : tape = ones (strip tape).2 ++ (strip tape).1 := by
  match tape with
  | [] => rfl
  | false :: rest => rfl
  | true :: rest =>
    rw [strip, ones_succ, List.cons_append]
    exact congrArg (true :: ·) (strip_decomp rest)

private theorem strip_first (tape : Word) : (strip tape).1.headD false = false := by
  match tape with
  | [] => rfl
  | false :: rest => rfl
  | true :: rest => exact strip_first rest

private theorem strip_count (tape : Word) : (strip tape).2 ≤ tape.length := by
  have h := congrArg List.length (strip_decomp tape)
  simp [ones] at h
  omega

private theorem next_ones (n : Nat) (suffix : Word) :
    next (ones n ++ suffix) = (next suffix).map (List.replicate n false ++ ·) := by
  induction n with
  | zero => cases h : next suffix <;> simp [h, ones]
  | succ n ih =>
    simp only [ones_succ, List.cons_append, next, ih, List.replicate_succ]
    cases next suffix <;> rfl

private theorem next_strip (tape : Word) :
    next tape =
      match (strip tape).1 with
      | [] => none
      | _ :: rest => some (List.replicate (strip tape).2 false ++ true :: rest) := by
  have decomp := congrArg next (strip_decomp tape)
  rw [next_ones] at decomp
  rw [decomp]
  have hd := strip_first tape
  cases h : (strip tape).1 with
  | nil => rfl
  | cons b rest =>
    simp only [h, List.headD_cons] at hd
    subst b
    rfl

private def peel : Code :=
  .loop (.head 4) (.write 4 (.tail 4) ▷ .write 5 (.cons true 5))

private theorem peel_run (s : State) (n : Nat) (tape : Word)
    (work : s.reg 4 = tape) (counter : s.reg 5 = ones n) :
    ∃ u, Run emptyLanguage peel s u (4 * (strip tape).2 + 1) 0 ∧
      u.reg 4 = (strip tape).1 ∧ u.reg 5 = ones ((strip tape).2 + n) ∧
      Preserves s u [4, 5] := by
  match tape with
  | [] => exact ⟨s, .loopFalse (by simp [Test.eval, work]), work, by simpa [strip] using counter,
      rfl, fun _ _ => rfl⟩
  | false :: rest => exact ⟨s, .loopFalse (by simp [Test.eval, work]), work, by simpa [strip] using counter,
      rfl, fun _ _ => rfl⟩
  | true :: rest =>
    let u := s.write 4 rest
    let v := u.write 5 (ones (n + 1))
    have drop : Run emptyLanguage (.write 4 (.tail 4)) s u 1 0 := by
      simpa [u, Expr.eval, work] using (Run.write (A := emptyLanguage) (s := s)
        (d := 4) (e := .tail 4))
    have push : Run emptyLanguage (.write 5 (.cons true 5)) u v 1 0 := by
      simpa [u, v, Expr.eval, State.write, counter] using
        (Run.write (A := emptyLanguage) (s := u) (d := 5) (e := .cons true 5))
    obtain ⟨out, tailRun, data, count, frame⟩ :=
      peel_run v (n + 1) rest (by simp [v, u, State.write]) (by simp [v, State.write])
    refine ⟨out, ?_, data, ?_, ?_⟩
    · have time : 4 * (strip (true :: rest)).2 + 1 = 3 + (4 * (strip rest).2 + 1) + 1 := by
        simp only [strip]
        omega
      rw [time]
      exact .loopTrue (by simp [Test.eval, work]) (.seq drop push) tailRun
    · simpa only [strip, show (strip rest).2 + 1 + n = (strip rest).2 + (n + 1) by omega]
        using count
    · have uFrame : Preserves s u [4, 5] := (preserves_write ..).mono (by simp)
      have vFrame : Preserves u v [4, 5] := (preserves_write ..).mono (by simp)
      exact uFrame.trans (vFrame.trans frame)

private def prependCopies (bit : Bool) (counter dst : Nat) : Code :=
  .loop (.head counter) (.write counter (.tail counter) ▷ .write dst (.cons bit dst))

private theorem extendCopies (bit : Bool) (n : Nat) : List.replicate n bit ++ [bit] =
    List.replicate (n + 1) bit := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem prependCopies_run (bit : Bool) (s : State) {counter dst : Nat} (hd : dst ≠ counter) (n : Nat)
    (fuel : s.reg counter = ones n) :
    ∃ u, Run emptyLanguage (prependCopies bit counter dst) s u (4 * n + 1) 0 ∧
      u.reg dst = List.replicate n bit ++ s.reg dst ∧
      Preserves s u [counter, dst] := by
  induction n generalizing s with
  | zero =>
    exact ⟨s, .loopFalse (by simp [Test.eval, fuel, ones]), rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let u := s.write counter (ones n)
    let v := u.write dst (bit :: s.reg dst)
    have drop : Run emptyLanguage (.write counter (.tail counter)) s u 1 0 := by
      simpa [u, Expr.eval, fuel] using (Run.write (A := emptyLanguage) (s := s)
        (d := counter) (e := .tail counter))
    have push : Run emptyLanguage (.write dst (.cons bit dst)) u v 1 0 := by
      simpa [v, u, Expr.eval, State.write, hd] using (Run.write (A := emptyLanguage) (s := u)
        (d := dst) (e := .cons bit dst))
    obtain ⟨out, tailRun, data, frame⟩ :=
      ih v (by simp [v, u, State.write, Ne.symm hd])
    refine ⟨out, ?_, ?_, ?_⟩
    · have time : 4 * (n + 1) + 1 = 3 + (4 * n + 1) + 1 := by omega
      rw [time]
      exact .loopTrue (by simp [Test.eval, fuel]) (.seq drop push) tailRun
    · rw [data]
      simp only [v, State.write, if_pos rfl]
      change List.replicate n bit ++ ([bit] ++ s.reg dst) =
        List.replicate (n + 1) bit ++ s.reg dst
      rw [← List.append_assoc, extendCopies]
    · have uFrame : Preserves s u [counter, dst] := (preserves_write ..).mono (by simp)
      have vFrame : Preserves u v [counter, dst] := (preserves_write ..).mono (by simp)
      exact uFrame.trans (vFrame.trans frame)

private def finish : Code :=
  .branch (.empty 4) (.write 6 .empty)
    (.write 3 (.tail 4) ▷ .write 3 (.cons true 3) ▷ prependCopies false 5 3 ▷ setBit 6 true)

/-- The current tape is in register 3. Register 6 signals whether increment
produced another tape. The two other registers are scratch space. -/
def advance : Code :=
  .write 4 (.copy 3) ▷ .write 5 .empty ▷ peel ▷ finish

theorem advance_allowed (push direct queued : Bool) : advance.allowed push direct queued := by
  simp [advance, peel, finish, prependCopies, setBit, Code.allowed]

theorem advance_run (s : State) :
    ∃ u t, Run emptyLanguage advance s u t 0 ∧ t ≤ 8 * (s.reg 3).length + 30 ∧
      Preserves s u [3, 4, 5, 6] ∧
      match next (s.reg 3) with
      | none => u.reg 6 = []
      | some w => u.reg 3 = w ∧ u.reg 6 = [true] := by
  let tape := s.reg 3
  let a := s.write 4 tape
  let b := a.write 5 []
  have copy : Run emptyLanguage (.write 4 (.copy 3)) s a 1 0 := .write
  have clear : Run emptyLanguage (.write 5 .empty) a b 1 0 := .write
  obtain ⟨mid, scan, suffix, count, pres⟩ := peel_run b 0 tape
    (by simp [a, b, State.write]) (by simp [b, State.write, ones])
  have prefixFrame : Preserves s mid [3, 4, 5, 6] := by
    have h₁ : Preserves s a [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
    have h₂ : Preserves a b [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
    have sub : ∀ i ∈ ([4, 5] : List Nat), i ∈ [3, 4, 5, 6] := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e <;> simp [e]
    exact h₁.trans (h₂.trans (pres.mono sub))
  have bound := strip_count tape
  change (strip tape).2 ≤ (s.reg 3).length at bound
  change ∃ u t, Run emptyLanguage advance s u t 0 ∧ t ≤ 8 * (s.reg 3).length + 30 ∧
    Preserves s u [3, 4, 5, 6] ∧ _ at ⊢
  rw [show next (s.reg 3) = next tape from rfl, next_strip]
  cases h : (strip tape).1 with
  | nil =>
    let out := mid.write 6 []
    have last : Run emptyLanguage finish mid out 2 0 :=
      branchTrue (by simp [Test.eval, suffix, h]) .write
    have frame : Preserves mid out [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
    exact ⟨out, _, .seq copy (.seq clear (.seq scan last)), by omega,
      prefixFrame.trans frame, by simp [out, State.write]⟩
  | cons first rest =>
    let q := mid.write 3 rest
    let r := q.write 3 (true :: rest)
    have init : Run emptyLanguage (.write 3 (.tail 4)) mid q 1 0 := by
      simpa [q, Expr.eval, suffix, h] using
        (Run.write (A := emptyLanguage) (s := mid) (d := 3) (e := .tail 4))
    have set : Run emptyLanguage (.write 3 (.cons true 3)) q r 1 0 := by
      simpa [q, r, Expr.eval, State.write] using
        (Run.write (A := emptyLanguage) (s := q) (d := 3) (e := .cons true 3))
    obtain ⟨u, zero, zeroResult, zeroFrame⟩ :=
      prependCopies_run false r (counter := 5) (dst := 3) (by decide) (strip tape).2
        (by simp [q, r, State.write, count])
    let out := u.write 6 [true]
    have mark : Run emptyLanguage (setBit 6 true) u out 3 0 := setBit_run ..
    have last : Run emptyLanguage finish mid out _ 0 :=
      branchFalse (by simp [Test.eval, suffix, h]) (.seq init (.seq set (.seq zero mark)))
    refine ⟨out, _, .seq copy (.seq clear (.seq scan last)), by omega, ?_, ?_, ?_⟩
    · have pq : Preserves mid q [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
      have qr : Preserves q r [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
      have ru : Preserves r u [3, 4, 5, 6] := zeroFrame.mono (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with e | e <;> simp [e])
      have uout : Preserves u out [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
      exact prefixFrame.trans (pq.trans (qr.trans (ru.trans uout)))
    · simpa [out, q, r, State.write] using zeroResult
    · simp [out, State.write]

/-- Process the current tape before incrementing it. The action is executed
even when the tape width is zero. -/
def visitLoop (body : Code) : Code := .loop (.head 6) (body ▷ advance)

theorem visitLoop_pure {body : Code} (pure : body.pure) : (visitLoop body).pure :=
  ⟨pure, advance_allowed ..⟩

/-- Loop invariants may use registers outside the iterator's frame. The
callback receives register 3 and preserves it until the counter advances. -/
structure VisitInvariant (body : Code) (cap cost : Nat) (Valid : List Word → State → Prop) : Prop where
  step : ∀ seen tape s, tape.length = cap → s.reg 3 = tape → Valid seen s →
    ∃ u t, Run emptyLanguage body s u t 0 ∧ t ≤ cost ∧
      u.reg 3 = tape ∧ Valid (tape :: seen) u
  frame : ∀ seen s u, Valid seen s → Preserves s u [3, 4, 5, 6] → Valid seen u

theorem visitLoop_run {body : Code} {cap cost : Nat} {Valid : List Word → State → Prop}
    (inv : VisitInvariant body cap cost Valid) (seen : List Word) (tape : Word) (s : State)
    (width : tape.length = cap) (entry : s.reg 3 = tape) (ready : s.reg 6 = [true])
    (ok : Valid seen s) :
    ∃ out t done, Run emptyLanguage (visitLoop body) s out t 0 ∧
      t ≤ (cost + 8 * cap + 33) * (2 ^ cap - value tape) + 1 ∧
      Valid done out ∧ done.length = seen.length + (2 ^ cap - value tape) ∧
      ∀ w, w ∈ done ↔ w ∈ seen ∨ (w.length = cap ∧ value tape ≤ value w) := by
  have live : (Test.head 6).eval s = true := by simp [Test.eval, ready]
  obtain ⟨mid, firstCost, firstRun, firstBound, tapeStill, validMid⟩ := inv.step seen tape s width entry ok
  obtain ⟨after, secondCost, secondRun, secondBound, frame, result⟩ := advance_run mid
  rw [tapeStill, width] at secondBound
  rw [tapeStill] at result
  have validAfter := inv.frame _ _ _ validMid frame
  let C := cost + 8 * cap + 33
  have combined : firstCost + secondCost + 2 ≤ C := by omega
  have tapeBound : value tape < 2 ^ cap := by simpa only [width] using value_lt tape
  have spec := next_spec tape
  cases h : next tape with
  | none =>
    simp only [h] at result spec
    have halt : Run emptyLanguage (visitLoop body) after after 1 0 :=
      .loopFalse (by simp [Test.eval, result])
    refine ⟨after, _, tape :: seen, .loopTrue live (.seq firstRun secondRun) halt, ?_, validAfter, ?_, ?_⟩
    · have last : value tape + 1 = 2 ^ cap := by simpa only [width] using spec
      have one : 2 ^ cap - value tape = 1 := by omega
      change firstCost + secondCost + 1 + 1 + 1 ≤ C * _ + 1
      rw [one, Nat.mul_one]
      omega
    · have last : value tape + 1 = 2 ^ cap := by simpa only [width] using spec
      simp only [List.length_cons]
      omega
    · intro w
      rw [List.mem_cons]
      constructor
      · rintro (rfl | prior)
        · exact Or.inr ⟨width, Nat.le_refl _⟩
        · exact Or.inl prior
      · rintro (prior | ⟨wWidth, ge⟩)
        · exact Or.inr prior
        · have lt : value w < 2 ^ cap := by simpa only [wWidth] using value_lt w
          have last : value tape + 1 = 2 ^ cap := by simpa only [width] using spec
          exact Or.inl (value_injective (wWidth.trans width.symm) (by omega))
  | some nextTape =>
    simp only [h] at result spec
    have nextWidth := spec.1.trans width
    have smaller : 2 ^ cap - value nextTape < 2 ^ cap - value tape := by
      have bounded : value nextTape < 2 ^ cap := by simpa only [nextWidth] using value_lt nextTape
      omega
    obtain ⟨out, restCost, done, restRun, restBound, valid, length, members⟩ :=
      visitLoop_run inv (tape :: seen) nextTape after nextWidth result.1 result.2 validAfter
    refine ⟨out, _, done, .loopTrue live (.seq firstRun secondRun) restRun, ?_, valid, ?_, ?_⟩
    · have budget : (2 ^ cap - value nextTape) + 1 = 2 ^ cap - value tape := by omega
      change restCost ≤ C * (2 ^ cap - value nextTape) + 1 at restBound
      change firstCost + secondCost + 1 + restCost + 1 ≤ C * (2 ^ cap - value tape) + 1
      rw [← budget, Nat.mul_succ]
      omega
    · rw [List.length_cons] at length
      omega
    · intro w
      rw [members, List.mem_cons]
      constructor
      · rintro ((rfl | prior) | ⟨wWidth, ge⟩)
        · exact Or.inr ⟨width, Nat.le_refl _⟩
        · exact Or.inl prior
        · exact Or.inr ⟨wWidth, by omega⟩
      · rintro (prior | ⟨wWidth, ge⟩)
        · exact Or.inl (Or.inr prior)
        · by_cases eq : value w = value tape
          · exact Or.inl (Or.inl (value_injective (wWidth.trans width.symm) eq))
          · exact Or.inr ⟨wWidth, by omega⟩
termination_by 2 ^ cap - value tape

private theorem value_zeros (cap : Nat) : value (List.replicate cap false) = 0 := by
  induction cap with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

/-- Visit every tape at the unary width in register 1. -/
def enumerate (body : Code) : Code :=
  .write 3 .empty ▷ .write 4 (.copy 1) ▷ prependCopies false 4 3 ▷ setBit 6 true ▷ visitLoop body

theorem enumerate_pure {body : Code} (pure : body.pure) : (enumerate body).pure := by
  simp [enumerate, prependCopies, setBit, Code.allowed, visitLoop_pure pure]

theorem enumerate_run {body : Code} {cap cost : Nat} {Valid : List Word → State → Prop}
    (inv : VisitInvariant body cap cost Valid) (s : State)
    (width : s.reg 1 = List.replicate cap true) (ok : Valid [] s) :
    ∃ out t done, Run emptyLanguage (enumerate body) s out t 0 ∧
      t ≤ (cost + 8 * cap + 33) * 2 ^ cap + 4 * cap + 13 ∧
      Valid done out ∧ done.length = 2 ^ cap ∧ ∀ w, w ∈ done ↔ w ∈ MachineEnumeration.tapes cap := by
  let a := s.write 3 []
  let b := a.write 4 (ones cap)
  have clear : Run emptyLanguage (.write 3 .empty) s a 1 0 := .write
  have copy : Run emptyLanguage (.write 4 (.copy 1)) a b 1 0 := by
    simpa [b, a, State.write, Expr.eval, width, ones] using
      (Run.write (A := emptyLanguage) (s := a) (d := 4) (e := .copy 1))
  obtain ⟨zero, init, zeroData, zeroFrame⟩ := prependCopies_run false b (counter := 4) (dst := 3) (by decide) cap
    (by simp [b, State.write])
  let start := zero.write 6 [true]
  have on : Run emptyLanguage (setBit 6 true) zero start 3 0 := setBit_run ..
  have tapeEq : start.reg 3 = List.replicate cap false := by
    simpa [start, State.write, b, a] using zeroData
  have first : Preserves s a [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
  have second : Preserves a b [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
  have third : Preserves b zero [3, 4, 5, 6] := zeroFrame.mono (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with e | e <;> simp [e])
  have fourth : Preserves zero start [3, 4, 5, 6] := (preserves_write ..).mono (by simp)
  have valid := inv.frame _ _ _ ok (first.trans (second.trans (third.trans fourth)))
  obtain ⟨out, t, done, loop, costBound, doneOk, count, members⟩ := visitLoop_run inv []
    (List.replicate cap false) start (by simp) tapeEq (by simp [start, State.write]) valid
  refine ⟨out, _, done, .seq clear (.seq copy (.seq init (.seq on loop))), ?_, doneOk, ?_, ?_⟩
  · simp only [value_zeros, Nat.sub_zero] at costBound
    omega
  · simpa [value_zeros] using count
  · intro w
    rw [members, MachineEnumeration.mem_tapes]
    simp [value_zeros]

/-- Materialize the tape list as consecutive escaped fields in register zero.
The other register contains the unary tape width. -/
def packTapes : Code :=
  .write 0 .empty ▷ enumerate (WordCode.putField 3 0 7 8 9)

theorem packTapes_pure : packTapes.pure := by
  exact ⟨trivial, enumerate_pure (WordCode.putField_allowed ..)⟩

theorem packTapes_run (s : State) (cap : Nat) (width : s.reg 1 = List.replicate cap true) :
    ∃ out t tapes, Run emptyLanguage packTapes s out t 0 ∧
      t ≤ (22 * cap + 56) * 2 ^ cap + 4 * cap + 15 ∧
      out.reg 0 = QueryEncoding.pack tapes ∧ out.queries = s.queries ∧ tapes.length = 2 ^ cap ∧
      ∀ word, word ∈ tapes ↔ word.length = cap := by
  let next := s.write 0 []
  let Valid (history : List Word) (u : State) :=
    u.reg 0 = QueryEncoding.pack history ∧ u.queries = s.queries
  have inv : VisitInvariant (WordCode.putField 3 0 7 8 9) cap (14 * cap + 23) Valid := by
    constructor
    · intro seen tape mid hlen tapeReady ok
      obtain ⟨out, run, a, b⟩ := WordCode.putField_run mid (src := 3) (dst := 0)
        (tmp := 7) (rev := 8) (flag := 9)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [tapeReady, hlen] at run
      exact ⟨out, 14 * cap + 23, run, Nat.le_refl _, (b.2 3 (by simp)).trans tapeReady,
        by simp [Valid, a, tapeReady, ok.1, QueryEncoding.pack, b.1, ok.2]⟩
    · intro seen mid out ok frame
      exact ⟨(frame.2 0 (by simp)).trans ok.1, frame.1.trans ok.2⟩
  obtain ⟨out, time, tapes, run, cost, data, count, members⟩ :=
    enumerate_run inv next (by simpa [next, State.write] using width)
      (by simp [Valid, next, State.write, QueryEncoding.pack])
  have start : Run emptyLanguage (.write 0 .empty) s next 1 0 := .write
  refine ⟨out, _, tapes, .seq start run, ?_, data.1, data.2, count, ?_⟩
  · rw [show 14 * cap + 23 + 8 * cap + 33 = 22 * cap + 56 by omega] at cost
    omega
  · intro w
    rw [members, MachineEnumeration.mem_tapes]

open MachineEnumeration
open ReplayFrameCode (HighClear frameSize)

private def withClock : Code :=
  .write 2 (.copy 3) ▷ .write 2 (.cons false 2) ▷ .write 8 (.copy 7) ▷
    prependCopies true 8 2

private theorem withClock_run (s : State) {clock : Nat} (fuel : s.reg 7 = List.replicate clock true) :
    ∃ out, Run emptyLanguage withClock s out (4 * clock + 7) 0 ∧
      out.reg 2 = clockWord clock ++ s.reg 3 ∧ Preserves s out [2, 8] := by
  let a := s.write 2 (s.reg 3)
  let b := a.write 2 (false :: s.reg 3)
  let c := b.write 8 (List.replicate clock true)
  have tape : Run emptyLanguage (.write 2 (.copy 3)) s a 1 0 := .write
  have mark : Run emptyLanguage (.write 2 (.cons false 2)) a b 1 0 := by
    have cur : a.reg 2 = s.reg 3 := by simp [a, State.write]
    simpa only [b, Expr.eval, cur] using (Run.write (A := emptyLanguage) (s := a)
      (d := 2) (e := .cons false 2))
  have count : Run emptyLanguage (.write 8 (.copy 7)) b c 1 0 := by
    have cur : b.reg 7 = List.replicate clock true := by simp [b, a, State.write, fuel]
    simpa only [c, Expr.eval, cur] using (Run.write (A := emptyLanguage) (s := b)
      (d := 8) (e := .copy 7))
  obtain ⟨out, time, data, frame⟩ :=
    prependCopies_run true c (dst := 2) (counter := 8) (by decide) clock (by simp [c, State.write, ones])
  refine ⟨out, ?_, ?_, ?_⟩
  · rw [show 4 * clock + 7 = 1 + (1 + (1 + (4 * clock + 1) + 1) + 1) + 1 by omega]
    exact .seq tape (.seq mark (.seq count time))
  · simpa [c, b, State.write, clockWord, List.append_assoc] using data
  · have sa : Preserves s a [2, 8] := (preserves_write ..).mono (by simp)
    have ab : Preserves a b [2, 8] := (preserves_write ..).mono (by simp)
    have bc : Preserves b c [2, 8] := (preserves_write ..).mono (by simp)
    have cd : Preserves c out [2, 8] := frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with e | e <;> simp [e])
    exact sa.trans (ab.trans (bc.trans cd))

private def collect : Code :=
  .branch (.empty 10) .skip (.write 10 (.tail 10) ▷ WordCode.putField 10 14 8 9 15)

private theorem collect_run (s : State) (result : Option Word)
    (data : s.reg 10 = (result.map (true :: ·)).getD []) :
    ∃ out t, Run emptyLanguage collect s out t 0 ∧ t ≤ 14 * (s.reg 10).length + 26 ∧
      out.reg 14 = ((result.map (fun w => QueryEncoding.put w (s.reg 14))).getD (s.reg 14)) ∧
      Preserves s out [8, 9, 10, 14, 15] := by
  cases result with
  | none =>
    refine ⟨s, 2, branchTrue (by simp [Test.eval, data]) .skip, by omega, rfl, ?_⟩
    exact ⟨rfl, fun _ _ => rfl⟩
  | some word =>
    let a := s.write 10 word
    have take : Run emptyLanguage (.write 10 (.tail 10)) s a 1 0 := by
      simpa [a, Expr.eval, data] using (Run.write (A := emptyLanguage) (s := s)
        (d := 10) (e := .tail 10))
    obtain ⟨out, run, output, frame⟩ := WordCode.putField_run a (src := 10) (dst := 14)
      (tmp := 8) (rev := 9) (flag := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨out, _, branchFalse (by simp [Test.eval, data]) (.seq take run), ?_, ?_, ?_⟩
    · simp [a, State.write, data]
      omega
    · simpa [a, State.write] using output
    · have sa : Preserves s a [8, 9, 10, 14, 15] := (preserves_write ..).mono (by simp)
      have ao : Preserves a out [8, 9, 10, 14, 15] := frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with e | e | e | e <;> simp [e])
      exact sa.trans ao

private def replayAndCollect (c : Code) : Code :=
  withClock ▷ ReplayFrameCode.replay c ▷ collect

private theorem replayAndCollect_pure (c : Code) : (replayAndCollect c).pure := by
  simp [replayAndCollect, withClock, prependCopies, collect, WordCode.putField_allowed,
    Code.allowed, ReplayFrameCode.replay_pure]

def oneReplayBound (c : Code) (x : Word) (budget cap : Nat) : Nat :=
  let clock := loweringCost (frameWidth c) budget * budget
  let gas := 24 * clock + 36
  4 * clock + 2 * frameSize c + 5 * gas + 14 * (x.length + (clock + 1 + cap) + gas) + 50

private def ListsReplays (c : Code) (x : Word) (budget : Nat)
    (seen : List Word) (s : State) : Prop :=
  let clock := loweringCost (frameWidth c) budget * budget
  s.reg 0 = x ∧ s.reg 7 = List.replicate clock true ∧
    s.reg 11 = List.replicate (24 * clock + 36) true ∧
    s.reg 14 = QueryEncoding.pack (seen.filterMap (fun tape => compiledTapeOutput c x tape budget)) ∧
    s.queries = [] ∧ HighClear c s

private theorem replayInvariant (c : Code) (x : Word) (budget cap : Nat) :
    VisitInvariant (replayAndCollect c) cap (oneReplayBound c x budget cap) (ListsReplays c x budget) := by
  dsimp only [oneReplayBound]
  let clock := loweringCost (frameWidth c) budget * budget
  let fuel := 24 * clock + 36
  constructor
  · intro seen tape s width source valid
    obtain ⟨sx, sc, sg, aggregate, empty, high⟩ := valid
    obtain ⟨packed, loading, input, loadFrame⟩ := withClock_run s sc
    have clockTape : packed.reg 2 = clockWord clock ++ tape := input.trans (congrArg _ source)
    have queued : packed.queries = [] := loadFrame.1.trans empty
    have px : packed.reg 0 = x := (loadFrame.2 0 (by simp)).trans sx
    have pclock : packed.reg 7 = List.replicate clock true := (loadFrame.2 7 (by simp)).trans sc
    have pgas : packed.reg 11 = List.replicate fuel true := (loadFrame.2 11 (by simp)).trans sg
    have paggregate : packed.reg 14 = _ := (loadFrame.2 14 (by simp)).trans aggregate
    have ptape : packed.reg 3 = tape := (loadFrame.2 3 (by simp)).trans source
    have phigh : HighClear c packed := by
      intro r hr
      exact (loadFrame.2 r (by simp; omega)).trans (high r hr)
    obtain ⟨result, t, execution, time, output, size, clean, resultHigh, low⟩ :=
      ReplayFrameCode.replay_run c packed tape budget phigh queued clockTape pgas
    rw [px] at output size
    have ra : result.reg 14 = _ := (low 14 (by decide) (by decide) (by decide) (by decide)).trans paggregate
    obtain ⟨out, t', store, cost, stored, storeFrame⟩ :=
      collect_run result (compiledTapeOutput c x tape budget) output
    have saved (r : Nat) (rlo : r < 16) (h10 : r ≠ 10) (h12 : r ≠ 12) (h13 : r ≠ 13)
        (unchanged : r ∉ [8, 9, 10, 14, 15]) : out.reg r = packed.reg r :=
      (storeFrame.2 r unchanged).trans (low r rlo h10 h12 h13)
    refine ⟨out, _, .seq loading (.seq execution store), ?_,
      (saved 3 (by decide) (by decide) (by decide) (by decide) (by simp)).trans ptape, ?_⟩
    · have tapeSize : (packed.reg 2).length = clock + 1 + cap := by
        rw [clockTape]
        simp [clockWord, width, Nat.add_assoc, Nat.add_comm]
      rw [tapeSize] at size
      change t ≤ 2 * frameSize c + 5 * fuel + 15 at time
      change 4 * clock + 7 + (t + t' + 1) + 1 ≤
        4 * clock + 2 * frameSize c + 5 * fuel + 14 * (x.length + (clock + 1 + cap) + fuel) + 50
      omega
    · refine ⟨(saved 0 (by decide) (by decide) (by decide) (by decide) (by simp)).trans px,
        (saved 7 (by decide) (by decide) (by decide) (by decide) (by simp)).trans pclock,
        (saved 11 (by decide) (by decide) (by decide) (by decide) (by simp)).trans pgas,
        ?_, storeFrame.1.trans clean, ?_⟩
      · rw [stored, ra]
        cases ht : compiledTapeOutput c x tape budget <;> simp [ht, List.filterMap, QueryEncoding.pack]
      · intro r hr
        exact (storeFrame.2 r (by simp; omega)).trans (resultHigh r hr)
  · intro seen s u valid frame
    obtain ⟨a, b, c', data, queue, high⟩ := valid
    refine ⟨(frame.2 0 (by simp)).trans a, (frame.2 7 (by simp)).trans b,
      (frame.2 11 (by simp)).trans c', (frame.2 14 (by simp)).trans data, frame.1.trans queue, ?_⟩
    intro r hr
    exact (frame.2 r (by simp; omega)).trans (high r hr)

def collectionBound (c : Code) (x : Word) (budget cap : Nat) : Nat :=
  (oneReplayBound c x budget cap + 8 * cap + 33) * 2 ^ cap + 4 * cap + 15

/-- Replay every tape from an initial state carrying unary width in register
1, replay clock in register 7 and the queue bound in register 11. Successful
outputs are returned in register 14 as consecutive escaped fields. -/
def collectCandidates (c : Code) : Code :=
  .write 14 .empty ▷ enumerate (replayAndCollect c)

theorem collectCandidates_pure (c : Code) : (collectCandidates c).pure :=
  ⟨trivial, enumerate_pure (replayAndCollect_pure c)⟩

theorem collectCandidates_run (c : Code) (s : State) (budget cap : Nat)
    (clock : s.reg 7 = List.replicate (loweringCost (frameWidth c) budget * budget) true)
    (queueBound : s.reg 11 = List.replicate (24 * (loweringCost (frameWidth c) budget * budget) + 36) true)
    (width : s.reg 1 = List.replicate cap true)
    (empty : s.queries = []) (high : HighClear c s) :
    ∃ out t candidates, Run emptyLanguage (collectCandidates c) s out t 0 ∧
      t ≤ collectionBound c (s.reg 0) budget cap ∧
      out.reg 14 = QueryEncoding.pack candidates ∧ out.queries = [] ∧ out.reg 0 = s.reg 0 ∧ candidates.length ≤ 2 ^ cap ∧
      ∀ w, w ∈ candidates ↔ w ∈ compiledCandidates c (s.reg 0) budget cap := by
  let start := s.write 14 []
  have initialized : Run emptyLanguage (.write 14 .empty) s start 1 0 := .write
  have valid : ListsReplays c (s.reg 0) budget [] start := by
    refine ⟨by simp [start, State.write], by simpa [start, State.write] using clock,
      by simpa [start, State.write] using queueBound, rfl, empty, ?_⟩
    intro r hr
    simpa [start, State.write, show r ≠ 14 by omega] using high r hr
  have ready : start.reg 1 = List.replicate cap true := by simpa [start, State.write] using width
  obtain ⟨out, t, tapes, work, cost, correct, len, coverage⟩ :=
    enumerate_run (replayInvariant c (s.reg 0) budget cap) start ready valid
  obtain ⟨input, _, _, output, clean, _⟩ := correct
  refine ⟨out, _, tapes.filterMap (fun tape => compiledTapeOutput c (s.reg 0) tape budget),
    .seq initialized work, ?_, output, clean, input, ?_, ?_⟩
  · unfold collectionBound
    omega
  · exact Nat.le_trans (List.length_filterMap_le ..) (Nat.le_of_eq len)
  · intro w
    simp only [compiledCandidates, List.mem_filterMap, coverage]

private def scale (a : Nat) (p : Poly) : Poly := ⟨a * p.coefficient, p.degree⟩

@[simp] private theorem scale_at (a : Nat) (p : Poly) (n : Nat) :
    (scale a p).at n = a * p.at n := by simp [scale, Poly.at, Nat.mul_assoc]

/-- A polynomial majorizes the single concrete collection program when
started with the logarithmic query cap and the advertised replay budget. -/
theorem collectionBound_poly (c : Code) (budget : Poly) (a b : Nat) :
    ∃ p : Poly, ∀ x : Word,
      collectionBound c x (budget.at x.length) ((x.length + 2).log2 * a + b) ≤ p.at x.length := by
  let costFactor := 2 * frameWidth c + 20
  let clockPoly := (scale costFactor budget).plus (scale 4 (budget.times budget))
  let capPoly : Poly := ⟨2 * a + b, 1⟩
  let inputPoly : Poly := ⟨14, 1⟩
  let fixedPoly : Poly := ⟨2 * frameSize c + 796, 0⟩
  let visitPoly := ((scale 474 clockPoly).plus inputPoly).plus ((scale 26 capPoly).plus fixedPoly)
  let countPoly : Poly := ⟨2 ^ a * 2 ^ b, a⟩
  refine ⟨visitPoly.times countPoly, fun x => ?_⟩
  let n := x.length
  let cap := (n + 2).log2 * a + b
  let atBudget := budget.at n
  let clock := loweringCost (frameWidth c) atBudget * atBudget
  have clockBound : clock ≤ clockPoly.at n := by
    have bounds := Poly.plus_bound (scale costFactor budget) (scale 4 (budget.times budget)) n
    simp only [scale_at, Poly.times_at] at bounds
    change costFactor * atBudget + 4 * (atBudget * atBudget) ≤ clockPoly.at n at bounds
    have eq : clock = costFactor * atBudget + 4 * (atBudget * atBudget) := by
      change (costFactor + 4 * atBudget) * atBudget = _
      rw [Nat.add_mul, Nat.mul_assoc]
    exact eq ▸ bounds
  have capBound : cap ≤ capPoly.at n := by
    have first : (n + 2).log2 * a ≤ (2 * (n + 1)) * a :=
      Nat.mul_le_mul_right _ (Nat.le_trans (Nat.log2_le_self _) (by omega))
    have second := Nat.le_mul_of_pos_right b (show 0 < n + 1 by omega)
    have expanded : (2 * a + b) * (n + 1) = (2 * (n + 1)) * a + b * (n + 1) := by
      rw [Nat.add_mul]
      ac_rfl
    simpa [cap, capPoly, Poly.at, expanded] using Nat.add_le_add first second
  have numTapes : 2 ^ cap ≤ countPoly.at n := by
    apply Nat.le_trans (pow_log_cap n a b)
    have bounded := Nat.mul_le_mul_right (2 ^ b)
      (Nat.pow_le_pow_left (show n + 2 ≤ 2 * (n + 1) by omega) a)
    simpa [countPoly, Poly.at, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using bounded
  have visits : 474 * clock + 14 * n + 26 * cap + (2 * frameSize c + 796) ≤ visitPoly.at n := by
    have first := Nat.mul_le_mul_left 474 clockBound
    have fCap := Nat.mul_le_mul_left 26 capBound
    have second := Poly.plus_bound (scale 474 clockPoly) inputPoly n
    have third := Poly.plus_bound (scale 26 capPoly) fixedPoly n
    have all := Poly.plus_bound ((scale 474 clockPoly).plus inputPoly)
      ((scale 26 capPoly).plus fixedPoly) n
    simp only [scale_at] at second third
    change 474 * clockPoly.at n + 14 * ((n + 1) ^ 1) ≤
      ((scale 474 clockPoly).plus inputPoly).at n at second
    change 26 * capPoly.at n + (2 * frameSize c + 796) * ((n + 1) ^ 0) ≤
      ((scale 26 capPoly).plus fixedPoly).at n at third
    simp only [Nat.pow_one] at second
    simp only [Nat.pow_zero, Nat.mul_one] at third
    change _ ≤ visitPoly.at n at all
    set_option maxRecDepth 4096 in omega
  change collectionBound c x atBudget cap ≤ (visitPoly.times countPoly).at n
  rw [Poly.times_at]
  refine Nat.le_trans ?_ (Nat.mul_le_mul visits numTapes)
  have remainder : 4 * cap + 15 ≤ (4 * cap + 15) * 2^cap :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))
  have inside : oneReplayBound c x atBudget cap + 8 * cap + 33 + (4 * cap + 15) =
      474 * clock + 14 * n + 26 * cap + (2 * frameSize c + 796) := by
    change 4 * clock + 2 * frameSize c + 5 * (24 * clock + 36) +
      14 * (n + (clock + 1 + cap) + (24 * clock + 36)) + 50 + 8 * cap + 33 + (4 * cap + 15) = _
    omega
  rw [← inside, Nat.add_mul, collectionBound]
  exact Nat.add_le_add_left remainder _

end ComplexityModel.ReplayListCode
