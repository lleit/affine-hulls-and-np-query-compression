module

public import Std

/-! Transcript enumeration for a deterministic computation with binary oracle
answers. A transition runs from one query boundary to the next, or returns a
final output. Its internal machine-time cost is outside this module. -/

@[expose] public section

namespace OracleTranscripts

variable {State Query Output : Type}
abbrev Step (State Query Output : Type) :=
  State → Sum Output (Query × (Bool → State))

def run (step : Step State Query Output) (oracle : Query → Bool) :
    Nat → State → Option Output
  | fuel, s => match step s with
    | .inl value => some value
    | .inr (q, next) => match fuel with
      | 0 => none
      | k + 1 => run step oracle k (next (oracle q))

/-- Explore hypothetical answers. A branch still asking a question at the
query cap has no output. No oracle is an argument to this function. -/
def outputs (step : Step State Query Output) : Nat → State → List Output
  | fuel, s => match step s with
    | .inl value => [value]
    | .inr (_, next) => match fuel with
      | 0 => []
      | k + 1 => outputs step k (next false) ++ outputs step k (next true)

theorem genuine_mem (step : Step State Query Output) (oracle : Query → Bool)
    (fuel : Nat) (s : State) (v : Output) (h : run step oracle fuel s = some v) :
    v ∈ outputs step fuel s := by
  induction fuel generalizing s with
  | zero => cases e : step s with
    | inl a => simpa [run, outputs, e] using h.symm
    | inr p => cases p; simp [run, e] at h
  | succ k ih => cases e : step s with
    | inl a => simpa [run, outputs, e] using h.symm
    | inr p =>
      obtain ⟨q, next⟩ := p
      rw [run, e] at h
      rw [outputs, e]
      cases b : oracle q
      · exact List.mem_append_left _ (ih (next false) (by simpa only [b] using h))
      · exact List.mem_append_right _ (ih (next true) (by simpa only [b] using h))

theorem output_bound (step : Step State Query Output) (fuel : Nat) (s : State) :
    (outputs step fuel s).length ≤ 2^fuel := by
  induction fuel generalizing s with
  | zero =>
    cases e : step s with
    | inl a => simp [outputs, e]
    | inr p => cases p; simp [outputs, e]
  | succ k ih =>
    cases e : step s with
    | inl a => simp [outputs, e]; exact Nat.two_pow_pos _
    | inr p =>
      obtain ⟨_, next⟩ := p
      rw [outputs, e]
      simp only [List.length_append, Nat.pow_succ]
      have h0 := ih (next false)
      have h1 := ih (next true)
      omega

/-- Number of calls to the transition function in the enumeration tree. -/
def visits (step : Step State Query Output) : Nat → State → Nat
  | fuel, s => match step s with
    | .inl _ => 1
    | .inr (_, next) => match fuel with
      | 0 => 1
      | k + 1 => 1 + visits step k (next false) + visits step k (next true)

theorem visit_bound (step : Step State Query Output) (fuel : Nat) (s : State) :
    visits step fuel s + 1 ≤ 2^(fuel + 1) := by
  induction fuel generalizing s with
  | zero =>
    cases e : step s with
    | inl a => simp [visits, e]
    | inr p => cases p; simp [visits, e]
  | succ k ih =>
    cases e : step s with
    | inl a =>
      rw [visits, e, Nat.pow_succ]
      dsimp only
      have := Nat.two_pow_pos (k+1)
      omega
    | inr p =>
      obtain ⟨_, next⟩ := p
      rw [visits, e, Nat.pow_succ]
      dsimp only
      have h0 := ih (next false)
      have h1 := ih (next true)
      omega

/-- Explicit polynomial list bound for q ≤ c log₂(n+2) + b (integer log). -/
theorem log_query_bound (step : Step State Query Output) (s : State)
    (n c b q : Nat) (cap : q ≤ (n + 2).log2 * c + b) :
    (outputs step q s).length ≤ (n + 2)^c * 2^b := by
  calc
    _ ≤ 2^q := output_bound step q s
    _ ≤ 2^((n + 2).log2 * c + b) := Nat.pow_le_pow_right (by decide) cap
    _ = (2^(n + 2).log2)^c * 2^b := by rw [Nat.pow_add, Nat.pow_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.log2_self_le (by omega)) c)

end OracleTranscripts
