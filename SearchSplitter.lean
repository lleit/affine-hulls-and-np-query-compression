module

public import AffineBasis
public import Splitter

@[expose] public section

namespace AffineSearch

theorem directions_length (ps : Splitter.Schedule) :
    (directions ps).length = Splitter.rank ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [directions, ih]

theorem dot_swap_model (a b : Word) : Splitter.dot a b = dot b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs => simp [Splitter.dot, dot, ih, Bool.and_comm]

theorem satisfies_of_zero {ps : Splitter.Schedule} {z : Word}
    (width : ps.length = z.length)
    (allZero : ∀ r ∈ directions ps, dot z r = false) :
    Splitter.satisfies ps z := by
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
    cases z with
    | nil => simp at width
    | cons b z =>
      have tails : ps.length = z.length := by simpa using width
      cases p with
      | none =>
        refine ⟨trivial, ih tails ?_⟩
        intro r hr
        simpa [dot] using allZero (false :: r) (List.mem_map_of_mem hr)
      | some row =>
        refine ⟨?_, ih tails ?_⟩
        · have zero := allZero (true :: row) List.mem_cons_self
          change b = Splitter.dot row z
          rw [dot_swap_model]
          simp only [dot, Bool.and_true] at zero
          cases b <;> cases h : dot z row <;> simp_all
        · intro r hr
          simpa [dot] using allZero (false :: r)
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))

def pack (A : Candidate) : Splitter.Candidate := ⟨A.pivots.reverse, 1⟩
def mask (n : Nat) (L : List Candidate) : Word := (Splitter.search n [] (L.map pack)).1

theorem pack_score (L : List Candidate) : Splitter.score (L.map pack) = L.length := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    change 1 + Splitter.score (l.map pack) = l.length + 1
    omega

theorem mask_spec {n : Nat} {L : List Candidate}
    (formed : ∀ A ∈ L, Shaped n A.pivots ∧ A.base.length = n)
    (large : ∀ A ∈ L, L.length < 2^A.basis.length) :
    (mask n L).length = n ∧ ∀ A ∈ L, Splits (mask n L) A := by
  have hw : ∀ c ∈ L.map pack, c.steps.length = n := by
    intro c hc
    obtain ⟨A, ha, rfl⟩ := List.mem_map.mp hc
    simpa [pack] using (formed A ha).1.length
  obtain ⟨⟨pre, hpre, hp⟩, hs, hh⟩ := Splitter.search_spec n [] (L.map pack) hw
  have hlen : (mask n L).length = n := by simpa [mask, hp] using hpre
  refine ⟨hlen, ?_⟩
  intro A ha
  obtain ⟨shape, base⟩ := formed A ha
  have ex : ∃ r ∈ A.basis, dot (mask n L) r = true := by
    apply Classical.byContradiction
    intro hn
    have hz (r) (hr : r ∈ A.basis) : dot (mask n L) r = false := by
      cases he : dot (mask n L) r with
      | false => rfl
      | true => exact False.elim (hn ⟨r, hr, he⟩)
    have sat := satisfies_of_zero (shape.length.trans hlen.symm) hz
    have hsched : Splitter.satisfies (pack A).steps.reverse (mask n L) := by
      simpa [pack] using sat
    have bound := hh (pack A) (List.mem_map_of_mem ha) hsched
    have contra := Nat.le_trans bound hs
    rw [pack_score] at contra
    simp only [pack, Splitter.rank_reverse, Nat.one_mul] at contra
    have tooLarge := large A ha
    rw [Candidate.basis, directions_length] at tooLarge
    omega
  obtain ⟨r, hr, he⟩ := ex
  exact candidate_splits shape base hr he

/-- Deterministic search is now conditional only on the input list of hulls.
Its splitter, low-dimensional scan, and variable-eliminating cuts are concrete. -/
theorem solve_iff (check : Word → Bool) (n : Nat) (listHulls : Lister)
    (formed : ∀ k hs, History n k hs → ∀ A ∈ listHulls k hs,
      Shaped k A.pivots ∧ A.base.length = k)
    (lists : ∀ k hs, History n k hs → (∃ w, Models check k hs w) →
      ∃ A ∈ listHulls k hs, Genuine (Models check k hs) A) :
    (∃ x, search check listHulls mask n [] = some x) ↔
      ∃ x, x.length = n ∧ check x = true := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,search_sound _ _ _ (.start n) hx⟩
  · rintro ⟨x, hw, hx⟩
    refine search_complete check listHulls mask lists ?_ (.start n) ?_
    · intro k hs hist
      let L := listHulls k hs
      let big := L.filter (fun a => !small L.length a)
      have hf : ∀ A ∈ big, Shaped k A.pivots ∧ A.base.length = k :=
        fun a ha => formed k hs hist a (List.mem_filter.mp ha).1
      have hb : ∀ A ∈ big, big.length < 2^A.basis.length := by
        intro a ha
        have h := (List.mem_filter.mp ha).2
        have hl : L.length < 2^a.basis.length := by simpa [small] using h
        exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) hl
      obtain ⟨len, spl⟩ := mask_spec hf hb
      exact fun a ha => ⟨len, spl a ha⟩
    · exact ⟨x, by simp [Models, valid, hw, hx, decode]⟩

end AffineSearch
