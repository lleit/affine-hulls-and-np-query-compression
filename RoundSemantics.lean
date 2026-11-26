module

public import SearchSplitter

@[expose] public section

namespace RoundSemantics

open AffineSearch hiding mask

def Sat (check : Word → Bool) (k : Nat) (hs : List Word) : Prop :=
  ∃ w, Models check k hs w

/-- The Boolean specification for the decision returned by a round. -/
noncomputable def answer (check : Word → Bool) (k : Nat) (hs : List Word) : Bool :=
  @decide (Sat check k hs) (Classical.propDecidable _)

@[simp] theorem answer_eq_true {check : Word → Bool} {k : Nat} {hs : List Word} :
    answer check k hs = true ↔ Sat check k hs := by
  classical
  exact decide_eq_true_iff

@[simp] theorem answer_eq_false {check : Word → Bool} {k : Nat} {hs : List Word} :
    answer check k hs = false ↔ ¬ Sat check k hs := by
  classical
  exact decide_eq_false_iff_not

theorem answer_congr {check : Word → Bool} {k₁ k₂ : Nat} {hs₁ hs₂ : List Word}
    (same : Sat check k₁ hs₁ ↔ Sat check k₂ hs₂) : answer check k₁ hs₁ = answer check k₂ hs₂ :=
  Bool.eq_iff_iff.mpr (answer_eq_true.trans (same.trans answer_eq_true.symm))

def found (check : Word → Bool) (hs : List Word) (K : Nat) (cs : List Candidate) : Bool :=
  (cs.filter (small K)).any (fun a => a.points.any (fun w => check (decode hs w)))

/-- The machine prepends large candidates to the splitter's input. -/
def large (K : Nat) (cs : List Candidate) : List Candidate :=
  (cs.filter (fun a => !small K a)).reverse

def mask (k K : Nat) (cs : List Candidate) : Word := AffineSearch.mask k (large K cs)

theorem zero_iff (check : Word → Bool) (hs : List Word) :
    Sat check 0 hs ↔ check (decode hs []) = true := by
  simp only [Sat, Models, valid, Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff]
  constructor
  · rintro ⟨_, rfl, accept⟩
    exact accept
  · exact fun accept => ⟨[], rfl, accept⟩

theorem answer_zero (check : Word → Bool) (hs : List Word) :
    answer check 0 hs = check (decode hs []) :=
  Bool.eq_iff_iff.mpr (answer_eq_true.trans (zero_iff check hs))

theorem initial_iff (check : Word → Bool) (k : Nat) :
    Sat check k [] ↔ ∃ w, w.length = k ∧ check w = true := by
  simp [Sat, Models, valid, decode]

theorem found_sound {check : Word → Bool} {k K : Nat} {hs : List Word} {cs : List Candidate}
    (formed : ∀ a ∈ cs, Shaped k a.pivots ∧ a.base.length = k)
    (accept : found check hs K cs = true) : Sat check k hs := by
  obtain ⟨a, amem, probe⟩ := List.any_eq_true.mp accept
  obtain ⟨row, member, pass⟩ := List.any_eq_true.mp probe
  obtain ⟨shape, base⟩ := formed a (List.mem_filter.mp amem).1
  obtain ⟨linear, inHull, rfl⟩ := List.mem_map.mp member
  have len := shape.points_width inHull
  have width : (translate a.base linear).length = k := by simp [translate, base, len]
  exact ⟨translate a.base linear, by simp [Models, valid, width, pass]⟩

theorem mask_spec {k K : Nat} {cs : List Candidate}
    (formed : ∀ a ∈ cs, Shaped k a.pivots ∧ a.base.length = k)
    (count : cs.length ≤ K) :
    (mask k K cs).length = k ∧ ∀ a ∈ large K cs, Splits (mask k K cs) a := by
  have bound : (large K cs).length ≤ K := by
    simpa only [large, List.length_reverse] using
      Nat.le_trans (List.length_filter_le (fun a => !small K a) cs) count
  refine AffineSearch.mask_spec (fun a mem => formed a ?_) (fun a mem => ?_)
  · exact (List.mem_filter.mp (List.mem_reverse.mp mem)).1
  · have rank : K < 2 ^ a.basis.length := by
      simpa [small] using (List.mem_filter.mp (List.mem_reverse.mp mem)).2
    exact Nat.lt_of_le_of_lt bound rank

theorem sat_before_cut {check : Word → Bool} {k : Nat} {hs : List Word} {z : Word}
    (len : z.length = k + 1) (nonzero : true ∈ z) :
    Sat check k (z :: hs) → Sat check (k + 1) hs := by
  rintro ⟨w, hw⟩
  have iw : w.length = k ∧ check (decode hs (inflate z w)) = true := by
    simpa [Models, valid] using hw
  have width := (inflate_spec z w nonzero (by rw [iw.1, len])).1
  exact ⟨inflate z w, by simp [Models, valid, width, len, iw.2]⟩

private theorem sat_after_cut_of_zero {check : Word → Bool} {k : Nat} {hs : List Word} {z w : Word}
    (len : z.length = k + 1) (nonzero : true ∈ z) (model : Models check (k + 1) hs w)
    (zero : dot z w = false) : Sat check k (z :: hs) := by
  have hw : w.length = k + 1 ∧ check (decode hs w) = true := by simpa [Models, valid] using model
  have ws := hw.1.trans len.symm
  have shorter := drop_length z w nonzero ws
  refine ⟨dropPivot z w, ?_⟩
  simp [Models, valid, show (dropPivot z w).length = k by omega, inflate_drop z w ws zero, hw.2]

/-- If the small candidates contained no model, the genuine hull occurs
among the candidates split by the greedy mask. Either parity then has a model. -/
theorem cut_of_sat {check : Word → Bool} {k K : Nat} {hs : List Word} {cs : List Candidate}
    (formed : ∀ a ∈ cs, Shaped (k + 1) a.pivots ∧ a.base.length = k + 1)
    (count : cs.length ≤ K)
    (contains : Sat check (k + 1) hs → ∃ a ∈ cs, Genuine (Models check (k + 1) hs) a)
    (rejected : found check hs K cs = false) (sat : Sat check (k + 1) hs) :
    true ∈ mask (k + 1) K cs ∧ Sat check k (mask (k + 1) K cs :: hs) := by
  obtain ⟨a, inList, cover, hull⟩ := contains sat
  obtain ⟨w, model⟩ := sat
  have test : check (decode hs w) = true := by
    have fields : w.length = k + 1 ∧ check (decode hs w) = true := by
      simpa [Models, valid] using model
    exact fields.2
  have isLarge : (!small K a) = true := by
    cases hs' : small K a
    · rfl
    · have hc : found check hs K cs = true := List.any_eq_true.mpr
        ⟨a, List.mem_filter.mpr ⟨inList, hs'⟩, List.any_eq_true.mpr ⟨w, cover _ model, test⟩⟩
      simp [rejected] at hc
  have mem : a ∈ large K cs := List.mem_reverse.mpr (List.mem_filter.mpr ⟨inList, isLarge⟩)
  obtain ⟨width, splits⟩ := mask_spec formed count
  obtain ⟨p, hp, parityOne⟩ := splits a mem true
  let z := mask (k + 1) K cs
  have nonzero : true ∈ z := by
    apply Classical.byContradiction
    intro h
    change dot z p = true at parityOne
    simp [dot_zero_left z p h] at parityOne
  obtain ⟨q, hq, parityZero⟩ := splits a mem false
  obtain ⟨target, isModel, zero⟩ := AffinePruning.attained_on_witness dot (hull q hq) parityZero
  exact ⟨nonzero, sat_after_cut_of_zero width nonzero isModel zero⟩

/-- A nonzero mask installs an equivalent smaller instance. In the absence
of a tested model, the zero mask certifies that no model exists. -/
theorem round_spec {check : Word → Bool} {k K : Nat} {hs : List Word} {cs : List Candidate}
    (formed : ∀ a ∈ cs, Shaped (k + 1) a.pivots ∧ a.base.length = k + 1)
    (count : cs.length ≤ K)
    (contains : Sat check (k + 1) hs → ∃ a ∈ cs, Genuine (Models check (k + 1) hs) a)
    (rejected : found check hs K cs = false) :
    let z := mask (k + 1) K cs
    z.length = k + 1 ∧ (true ∈ z → (Sat check k (z :: hs) ↔ Sat check (k + 1) hs)) ∧
      (true ∉ z → ¬ Sat check (k + 1) hs) := by
  have width := (mask_spec formed count).1
  exact ⟨width, fun nz => ⟨sat_before_cut width nz, fun sat =>
    (cut_of_sat formed count contains rejected sat).2⟩,
    fun zero sat => zero (cut_of_sat formed count contains rejected sat).1⟩

end RoundSemantics
