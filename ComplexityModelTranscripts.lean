module

public import ComplexityModel.Machine

@[expose] public section

namespace ComplexityModel

inductive Frame
  | next (code : Code)
  | callResult (caller : State) (dest : Nat)

inductive Config
  | exec (code : Code) (state : State) (frames : List Frame)
  | resume (state : State) (frames : List Frame)

inductive Event
  | halt (out : State)
  | next (config : Config)
  | question (word : Word) (no yes : Config)

/-- A single machine transition. On a query, both successor configurations
are computed from the machine instruction before any answer is selected. -/
def Config.step : Config → Event
  | .exec .skip s frames => .next (.resume s frames)
  | .exec (.write d e) s frames => .next (.resume (s.write d (e.eval s)) frames)
  | .exec (.push r) s frames => .next (.resume (s.push r) frames)
  | .exec (.pop d) s frames => .next (.resume (s.drop.write d (s.queries.headD [])) frames)
  | .exec (.seq a b) s frames => .next (.exec a s (.next b :: frames))
  | .exec (.branch test yes no) s frames =>
    .next (.exec (if test.eval s then yes else no) s frames)
  | .exec (.loop test body) s frames =>
    if test.eval s then .next (.exec body s (.next (.loop test body) :: frames))
    else .next (.resume s frames)
  | .exec (.ask src d) s frames =>
    let answer b := Config.resume ((src.advance s).write d [b]) frames
    match src.read s with
    | none => .next (answer false)
    | some w => .question w (answer false) (answer true)
  | .exec (.callBit src d body) s frames =>
    match src.read s with
    | none => .next (.resume ((src.advance s).write d [false]) frames)
    | some w => .next (.exec body (State.input w) (.callResult (src.advance s) d :: frames))
  | .resume s [] => .halt s
  | .resume s (.next c :: frames) => .next (.exec c s frames)
  | .resume s (.callResult caller d :: frames) =>
    .next (.resume (caller.write d [decide (s.output = [true])]) frames)

inductive Path (A : Language) : Config → Config → Nat → Nat → Prop
  | refl : Path A c c 0 0
  | next : c.step = .next d → Path A d e t q → Path A c e (t + 1) q
  | ask : c.step = .question w no yes → (bit = true ↔ A w) →
      Path A (if bit then yes else no) e t q → Path A c e (t + 1) (q + 1)

theorem Path.append (h₁ : Path A a b t q) (h₂ : Path A b c t' q') :
    Path A a c (t + t') (q + q') := by
  induction h₁ with
  | refl => simpa using h₂
  | next step _ ih =>
    simpa only [Nat.succ_add] using Path.next step (ih h₂)
  | ask step answer _ ih =>
    simpa only [Nat.succ_add] using Path.ask step answer (ih h₂)

/-- At most one continuation transition is added per executed instruction. -/
theorem Run.toPath (h : Run A c s u t q) (frames : List Frame) :
    ∃ steps ≤ 2 * t, Path A (.exec c s frames) (.resume u frames) steps q := by
  induction h generalizing frames with
  | skip | write | push | pop =>
    exact ⟨1, by decide, .next rfl .refl⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨k₁, h₁, p₁⟩ := ih₁ (.next _ :: frames)
    obtain ⟨k₂, h₂, p₂⟩ := ih₂ frames
    exact ⟨_, by show k₁ + (k₂ + 1) + 1 ≤ _; omega,
      .next rfl (p₁.append (.next rfl p₂))⟩
  | branch he _ ih =>
    obtain ⟨k, hk, path⟩ := ih frames
    exact ⟨k + 1, by omega, .next (by simp only [Config.step, he]) path⟩
  | loopFalse he =>
    exact ⟨1, by decide, .next (by simp [Config.step, he]) .refl⟩
  | loopTrue he _ _ ih₁ ih₂ =>
    obtain ⟨k₁, h₁, p₁⟩ := ih₁ (.next _ :: frames)
    obtain ⟨k₂, h₂, p₂⟩ := ih₂ frames
    exact ⟨_, by show k₁ + (k₂ + 1) + 1 ≤ _; omega,
      .next (by simp [Config.step, he]) (p₁.append (.next rfl p₂))⟩
  | askEmpty he =>
    exact ⟨1, by decide, .next (by simp [Config.step, he]) .refl⟩
  | @askSome w bit src d s he hb =>
    refine ⟨1, by decide, Path.ask
      (no := .resume ((src.advance s).write d [false]) frames)
      (yes := .resume ((src.advance s).write d [true]) frames)
      (by simp [Config.step, he]) hb ?_⟩
    cases bit <;> exact .refl
  | callEmpty he =>
    exact ⟨1, by decide, .next (by simp [Config.step, he]) .refl⟩
  | @callSome w body u t q src d s he _ ih =>
    obtain ⟨k, hk, path⟩ := ih (.callResult (src.advance s) d :: frames)
    have finish : Path A (.resume u (.callResult (src.advance s) d :: frames))
        (.resume ((src.advance s).write d [decide (u.output = [true])]) frames) 1 0 :=
      .next rfl .refl
    have tail := path.append finish
    refine ⟨k + 1 + 1, by omega, .next (d := .exec body (State.input w)
      (.callResult (src.advance s) d :: frames)) (by simp [Config.step, he]) ?_⟩
    simpa only [Nat.add_zero] using tail

/-- Run every hypothetical answer branch with separate step and query
budgets. A branch that exhausts either budget before halting is dropped. -/
def Config.candidates (t q : Nat) (c : Config) : List Word :=
  match c.step with
  | .halt s => [s.output]
  | .next d =>
    match t with
    | 0 => []
    | k + 1 => d.candidates k q
  | .question _ no yes =>
    match t, q with
    | k + 1, l + 1 => no.candidates k l ++ yes.candidates k l
    | _, _ => []
termination_by t

theorem Path.output_mem (h : Path A c d t q) (halted : d.step = .halt s)
    (ht : t ≤ clock) (hq : q ≤ cap) : s.output ∈ c.candidates clock cap := by
  induction h generalizing clock cap with
  | refl =>
    rw [Config.candidates, halted]
    exact List.mem_singleton_self _
  | next step _ ih =>
    cases clock with
    | zero => omega
    | succ k =>
      rw [Config.candidates, step]
      exact ih (clock := k) (cap := cap) halted (by omega) hq
  | @ask bit w yes no d t q c step _ _ ih =>
    cases clock with
    | zero => omega
    | succ k =>
      cases cap with
      | zero => omega
      | succ l =>
        rw [Config.candidates, step]
        have member := ih (clock := k) (cap := l) halted (by omega) (by omega)
        cases bit
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ member

theorem Run.output_mem_candidates (h : Run A c s u t q) (ht : 2 * t ≤ clock)
    (hq : q ≤ cap) : u.output ∈ (Config.exec c s []).candidates clock cap := by
  obtain ⟨steps, bound, p⟩ := h.toPath []
  exact p.output_mem rfl (Nat.le_trans bound ht) hq

theorem Config.candidates_length_le (t q : Nat) (c : Config) :
    (c.candidates t q).length ≤ 2 ^ q := by
  induction t generalizing q c with
  | zero =>
    rw [Config.candidates]
    cases c.step <;> simp
    exact Nat.two_pow_pos _
  | succ k ih =>
    rw [Config.candidates]
    cases c.step with
    | halt => exact Nat.two_pow_pos _
    | next d => exact ih q d
    | question _ no yes =>
      cases q with
      | zero => simp
      | succ l =>
        simp only [List.length_append, Nat.pow_succ]
        have h₁ := ih l no
        have h₂ := ih l yes
        omega

/-- Number of inspected machine configurations, including the root and any
leaves stopped by one of the budgets. -/
def Config.inspections (t q : Nat) (c : Config) : Nat :=
  match c.step with
  | .halt _ => 1
  | .next d =>
    match t with
    | 0 => 1
    | k + 1 => 1 + d.inspections k q
  | .question _ no yes =>
    match t, q with
    | k + 1, l + 1 => 1 + no.inspections k l + yes.inspections k l
    | _, _ => 1
termination_by t

theorem Config.inspections_le (t q : Nat) (c : Config) :
    c.inspections t q ≤ (t + 1) * 2 ^ q := by
  have positive (v : Nat) : 1 ≤ 2 ^ v := Nat.two_pow_pos _
  induction t generalizing q c with
  | zero =>
    rw [Config.inspections]
    cases c.step <;> simpa using positive q
  | succ k ih =>
    have lower : 1 ≤ (k + 1 + 1) * 2 ^ q :=
      Nat.le_trans (positive q) (by
        simpa using Nat.mul_le_mul_right (2 ^ q) (show 1 ≤ k + 1 + 1 by omega))
    rw [Config.inspections]
    cases c.step with
    | halt => exact lower
    | next d =>
      have calls := ih q d
      change 1 + d.inspections k q ≤ (k + 1 + 1) * 2 ^ q
      rw [Nat.add_mul, Nat.one_mul]
      have := positive q
      omega
    | question _ no yes =>
      cases q with
      | zero => simp
      | succ l =>
        have rec₁ := ih l no
        have rec₂ := ih l yes
        have expand : (k + 1 + 1) * 2 ^ (l + 1) =
            (k + 1) * 2 ^ l + (k + 1) * 2 ^ l + 2 ^ l + 2 ^ l := by
          rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two, Nat.add_mul, Nat.one_mul]
          omega
        change 1 + no.inspections k l + yes.inspections k l ≤ _
        rw [expand]
        have := positive l
        omega

theorem pow_log_cap (n k b : Nat) :
    2 ^ ((n + 2).log2 * k + b) ≤ (n + 2)^k * 2^b := by
  rw [Nat.pow_add, Nat.pow_mul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.log2_self_le (by omega)) _)

/-- Explicit candidate enumeration for a logarithmic-query machine. The
machine's actual output is in the list, and even branches with incorrect or
inconsistent hypothetical answers are subject to both clocks. -/
theorem FPLogNP.candidate_bound {f : WordFunction} (hf : FPLogNP f) :
    ∃ c : Code, ∃ p : Poly, ∃ k b : Nat, ∀ x,
      let config := Config.exec c (State.input x) []
      let clock := 2 * p.at x.length
      let cap := (x.length + 2).log2 * k + b
      f x ∈ config.candidates clock cap ∧
      (config.candidates clock cap).length ≤ (x.length + 2)^k * 2^b ∧
      config.inspections clock cap ≤ (clock + 1) * ((x.length + 2)^k * 2^b) := by
  obtain ⟨_, _, c, p, k, b, run⟩ := hf
  refine ⟨c, p, k, b, ?_⟩
  intro x
  dsimp only
  obtain ⟨s, t, q, hs, ht, hq, he⟩ := run x
  refine ⟨he ▸ hs.output_mem_candidates (Nat.mul_le_mul_left _ ht) hq, ?_, ?_⟩
  · exact Nat.le_trans (Config.candidates_length_le ..) (pow_log_cap ..)
  · exact Nat.le_trans (Config.inspections_le ..) (Nat.mul_le_mul_left _ (pow_log_cap ..))

end ComplexityModel
