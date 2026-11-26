module

public import ComplexityModelSimulation

@[expose] public section

namespace ComplexityModel

def Poly.plus (p q : Poly) : Poly :=
  ⟨p.coefficient + q.coefficient, max p.degree q.degree⟩

def Poly.times (p q : Poly) : Poly :=
  ⟨p.coefficient * q.coefficient, p.degree + q.degree⟩

def Poly.comp (p q : Poly) : Poly :=
  ⟨p.coefficient * (q.coefficient + 1) ^ p.degree, q.degree * p.degree⟩

theorem Poly.plus_bound (p q : Poly) (n : Nat) : p.at n + q.at n ≤ (p.plus q).at n := by
  simp only [Poly.at, Poly.plus, Nat.add_mul]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))

theorem Poly.times_at (p q : Poly) (n : Nat) : (p.times q).at n = p.at n * q.at n := by
  simp [Poly.times, Poly.at, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem Poly.comp_bound (p q : Poly) (n : Nat) : p.at (q.at n) ≤ (p.comp q).at n := by
  have h : q.at n + 1 ≤ (q.coefficient + 1) * (n + 1) ^ q.degree := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.pow_pos (by omega)) _
  calc
    p.at (q.at n) ≤ p.coefficient * ((q.coefficient + 1) * (n + 1) ^ q.degree) ^ p.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = (p.comp q).at n := by simp [Poly.comp, Poly.at, Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

theorem Poly.add_const_bound (p : Poly) (k n : Nat) :
    p.at n + k ≤ (p.plus ⟨k, 0⟩).at n := by
  simpa [Poly.at] using p.plus_bound ⟨k, 0⟩ n

theorem State.input_clear_witness (x w : Word) :
    (State.input x w).write 1 [] = State.input x := by
  unfold State.input State.write
  congr
  funext i
  by_cases hi : i = 1
  · simp [hi]
  · simp [hi]

theorem p_subset_np {A : Language} (h : P A) : NP A := by
  obtain ⟨f, ⟨c, p, hp, hc⟩, hA⟩ := h
  refine ⟨.seq (.write 1 .empty) c, ⟨0, 0⟩, p.plus ⟨2, 0⟩, ⟨trivial, hp⟩, ?_, ?_⟩
  · intro x w
    obtain ⟨s, t, hr, ht, _⟩ := hc x
    have clear : Run emptyLanguage (.write 1 .empty) (State.input x w) (State.input x) 1 0 := by
      rw [← State.input_clear_witness x w]
      exact .write
    refine ⟨s, 1 + t + 1, .seq clear hr, ?_⟩
    have bound := p.add_const_bound 2 (x.length + w.length)
    have mono := p.mono (show x.length ≤ x.length + w.length by omega)
    omega
  · intro x
    obtain ⟨s, t, hr, _, hf⟩ := hc x
    have clear : Run emptyLanguage (.write 1 .empty) (State.input x) (State.input x) 1 0 := by
      have h : Run emptyLanguage (.write 1 .empty) (State.input x) ((State.input x).write 1 []) 1 0 := .write
      rwa [State.input_clear_witness] at h
    have verifier := Run.seq clear hr
    constructor
    · intro hx
      exact ⟨[], by simp [Poly.at], s, _, verifier, hf.trans ((hA x).mpr hx)⟩
    · rintro ⟨w, hw, u, r, hu, htrue⟩
      have empty : w = [] := by simpa [Poly.at] using hw
      subst w
      have e := (verifier.deterministic hu).1
      exact (hA x).mp (hf.symm.trans (e ▸ htrue))

theorem emptyLanguage_np : NP emptyLanguage := by
  apply p_subset_np
  refine ⟨fun _ => [], ⟨.write 0 .empty, ⟨1, 0⟩, trivial, ?_⟩, ?_⟩
  · intro x
    exact ⟨_, 1, .write, by simp [Poly.at], by simp [State.output, State.write, Expr.eval]⟩
  · simp [emptyLanguage]

theorem FP.toParallelNP {f : WordFunction} (h : FP f) : FPParallelNP f := by
  obtain ⟨c, p, hp, hr⟩ := h
  refine ⟨emptyLanguage, emptyLanguage_np, c, .skip, p.plus ⟨1, 0⟩, hp, trivial, ?_⟩
  intro x
  obtain ⟨s, t, he, ht, hf⟩ := hr x
  exact ⟨s, s, t, 1, 0, he, .skip, Nat.le_trans (Nat.add_le_add_right ht _) (p.add_const_bound _ _), hf⟩

theorem FP.toLogNP {f : WordFunction} (h : FP f) : FPLogNP f := by
  obtain ⟨c, p, _, hr⟩ := h
  refine ⟨emptyLanguage, emptyLanguage_np, c, p, 0, 0, ?_⟩
  intro x
  obtain ⟨s, t, he, ht, hf⟩ := hr x
  exact ⟨s, t, 0, he, ht, Nat.zero_le _, hf⟩

/-- A polynomial-time P oracle provides no additional power even when the
machine may ask polynomially many adaptive queries. -/
theorem fp_of_p_oracle {f : WordFunction} {A : Language}
    (hA : P A) (c : Code) (p : Poly)
    (hr : ∀ x, ∃ s t q, Run A c (State.input x) s t q ∧
      t ≤ p.at x.length ∧ s.output = f x) : FP f := by
  obtain ⟨g, ⟨decider, d, hp, hd⟩, gCorrect⟩ := hA
  let inputBound : Poly := (⟨1, 1⟩ : Poly).plus p
  let clock : Poly := p.plus (p.times (d.comp inputBound))
  refine ⟨c.replaceOracle decider, clock, Code.replaceOracle_pure decider hp c, ?_⟩
  intro x
  obtain ⟨s, t, q, he, ht, hf⟩ := hr x
  have inputBounded : x.length + t ≤ inputBound.at x.length := by
    have hb := (⟨1, 1⟩ : Poly).plus_bound p x.length
    simp only [Poly.at, Nat.pow_one, Nat.one_mul] at hb
    change x.length + t ≤ ((⟨1, 1⟩ : Poly).plus p).at x.length
    simp only [Poly.at] at ht ⊢
    omega
  have init : (State.input x).Fits x.length := State.input_fits (Nat.le_refl _) (Nat.zero_le _)
  obtain ⟨r, compiled, hr'⟩ :=
    he.replaceOracle init decider ((d.comp inputBound).at x.length) (by
      intro w hw
      obtain ⟨u, t', hu, htime, hvalue⟩ := hd w
      refine ⟨u, t', hu, ?_, hvalue ▸ gCorrect w⟩
      exact Nat.le_trans htime (Nat.le_trans (d.mono (Nat.le_trans hw inputBounded))
        (d.comp_bound inputBound x.length)))
  refine ⟨s, r, compiled, ?_, hf⟩
  apply Nat.le_trans hr'
  have hb := p.plus_bound (p.times (d.comp inputBound)) x.length
  rw [Poly.times_at] at hb
  exact Nat.le_trans
    (Nat.add_le_add ht (Nat.mul_le_mul_right _ (Nat.le_trans he.queries_le_time ht))) hb

theorem FPParallelNP.toFP {f : WordFunction} (collapse : PEqualsNP)
    (h : FPParallelNP f) : FP f := by
  obtain ⟨A, hA, producer, consumer, p, _, _, hr⟩ := h
  apply fp_of_p_oracle ((collapse A).mpr hA) (.seq producer consumer) (p.plus ⟨1, 0⟩)
  intro x
  obtain ⟨mid, out, t₁, t₂, q, h₁, h₂, ht, hf⟩ := hr x
  exact ⟨out, t₁ + t₂ + 1, q, (by simpa only [Nat.zero_add] using Run.seq (h₁.transfer rfl A) h₂),
    Nat.le_trans (Nat.add_le_add_right ht _) (p.add_const_bound _ _), hf⟩

theorem FPLogNP.toFP {f : WordFunction} (collapse : PEqualsNP)
    (h : FPLogNP f) : FP f := by
  obtain ⟨A, hA, c, p, _, _, hr⟩ := h
  apply fp_of_p_oracle ((collapse A).mpr hA) c p
  intro x
  obtain ⟨s, t, q, hs, ht, _, hf⟩ := hr x
  exact ⟨s, t, q, hs, ht, hf⟩

theorem classEquality_of_pEqualsNP (collapse : PEqualsNP) : ClassEquality :=
  fun _ => ⟨fun h => (h.toFP collapse).toLogNP, fun h => (h.toFP collapse).toParallelNP⟩

end ComplexityModel
