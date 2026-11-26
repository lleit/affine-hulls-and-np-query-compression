module

public import HullRecovery
public import AffineBasis

@[expose] public section

namespace HullDecoder
open HullRecovery
open AffineSearch

abbrev word {n : Nat} (x : Bits n) : Word := List.ofFn x
@[simp] theorem word_length (x : Bits n) : (word x).length = n := List.length_ofFn
@[simp] theorem word_cons (b : Bool) (x : Bits n) :
    word (cons b x) = b :: word x := by
  rw [word, List.ofFn_succ]
  simp [cons, word]

theorem word_add (x y : Bits n) : word (add x y) = translate (word x) (word y) := by
  induction n with
  | zero => simp [word, translate]
  | succ n ih =>
    rw [← cons_head_tail x, ← cons_head_tail y]
    rw [← cons_head_tail (add _ _)]
    simp only [head_add, tail_add, head_cons, tail_cons, word_cons, ih]
    rfl

def bits (w : Word) (n : Nat) : Bits n := fun i => w[i.val]?.getD false

theorem word_bits {n : Nat} {w : Word} (hw : w.length = n) : word (bits w n) = w := by
  apply List.ext_getElem
  · simpa using hw.symm
  · intro i hi hj
    simp [word, bits, List.getElem?_eq_getElem hj]

theorem bits_word (x : Bits n) : bits (word x) n = x := by
  funext i
  simp [bits, word, i.isLt]

theorem word_inj {x y : Bits n} (h : word x = word y) : x = y := by
  simpa [bits_word] using congrArg (fun w => bits w n) h

/-- Gaussian elimination into triangular generators. Each pivot row
retains only its suffix in the stored code. -/
def triangular : (n : Nat) → List (Bits n) → List (Option Word)
  | 0, _ => []
  | n+1, xs =>
    (splitPivot xs).map (fun t => word (tail t.1)) :: triangular n (subproblem xs)

theorem triangular_shape (xs : List (Bits n)) : Shaped n (triangular n xs) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [triangular]
    cases h : splitPivot xs with
    | none => exact .free (ih _)
    | some a => exact .pivot (word_length _) (ih _)

private theorem mem_map_translate {ps : List (Option Word)} (shape : Shaped n ps)
    (v x : Bits n) :
    word x ∈ (linearPoints ps).map (translate (word v)) ↔
      word (add v x) ∈ linearPoints ps := by
  rw [word_add]
  constructor
  · intro hm
    obtain ⟨y, hy, eq⟩ := List.mem_map.mp hm
    rw [← eq, translate_self_left (by rw [word_length, shape.points_width hy])]
    exact hy
  · intro hm
    exact List.mem_map.mpr ⟨_, hm, translate_self_left (by simp)⟩

theorem triangular_spec (xs : List (Bits n)) (x : Bits n) :
    word x ∈ linearPoints (triangular n xs) ↔ ListSpan xs x := by
  induction n with
  | zero =>
    have ex : x = zero 0 := funext (fun i => Fin.elim0 i)
    subst x
    exact ⟨fun _ => .zero, fun _ => by simp [word, triangular, linearPoints]⟩
  | succ n ih =>
    let rest := subproblem xs
    let ps := triangular n rest
    have low (y : Bits n) : word y ∈ linearPoints ps ↔ ListSpan xs (cons false y) :=
      (ih rest y).trans (subproblem_span xs y)
    have reconstruct : word x = head x :: word (tail x) := by
      conv => lhs; rw [← cons_head_tail x, word_cons]
    rw [triangular, reconstruct]
    cases he : splitPivot xs with
    | none =>
      dsimp only [Option.map, linearPoints]
      cases hx : head x with
      | false =>
        have eqx : cons false (tail x) = x := by rw [← hx, cons_head_tail]
        simpa [List.mem_map, eqx] using low (tail x)
      | true =>
        simp only [List.mem_map, List.cons.injEq, Bool.false_eq_true,
          false_and, and_false, exists_const, false_iff]
        intro h
        have hh := span_head_false (splitPivot_none he) h
        simp [hh] at hx
    | some pr =>
      obtain ⟨p, rs⟩ := pr
      obtain ⟨hp, perm⟩ := splitPivot_some he
      have pmem : ListSpan xs p := .gen (perm.mem_iff.mp List.mem_cons_self)
      have red := span_without_head (x := x) pmem hp
      dsimp only [Option.map, linearPoints]
      simp only [List.mem_append, List.mem_map,
        List.cons.injEq]
      cases hx : head x with
      | false =>
        simp only [Bool.false_eq_true, Bool.true_eq_false, and_true, true_and,
          false_and, and_false, exists_const, or_false, exists_prop, exists_eq_right]
        change word (tail x) ∈ linearPoints ps ↔ _
        exact (low _).trans (by simpa [lower, hx] using red.symm)
      | true =>
        simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
          and_false, exists_const, false_or]
        have mapEquiv := mem_map_translate (triangular_shape rest) (tail p) (tail x)
        rw [List.mem_map] at mapEquiv
        apply mapEquiv.trans
        rw [add_comm]
        exact (low _).trans (by simpa [lower, hx] using red.symm)

theorem normal_idempotent (xs : List (Bits n)) (x : Bits n) :
    normal xs (normal xs x) = normal xs x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases he : splitPivot xs with
    | none => simp [normal_none he, ih]
    | some pr =>
      obtain ⟨p, rs⟩ := pr
      rw [normal_some he x, normal_some he]
      simp [lower, ih]

/-- Reconstruct generators from normal-form matrix columns. Column i of
I+N is the component of unit i that belongs to the required space. -/
def columns (M : Matrix n) : List (Bits n) := List.ofFn fun i => add (unit i) (M i)

theorem applyColumns_in_span {S : Bits m → Prop} (cols : Fin n → Bits m) (x : Bits n)
    (contained : ∀ i, Span S (cols i)) : Span S (applyColumns n cols x) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    rw [applyColumns]
    apply Span.add _ (ih _ _ (fun i => contained i.succ))
    split
    · exact contained _
    · exact .zero

theorem projected_sameSpan (xs : List (Bits n)) : SameSpan (columns (encode xs)) xs := by
  let f := fun x => add x (normal xs x)
  have hcols : columns (encode xs) = List.ofFn (fun i => f (unit i)) := rfl
  have hf (x y : Bits n) : f (add x y) = add (f x) (f y) := by
    funext i
    simp only [f, normal_add, add]
    cases x i <;> cases y i <;> cases normal xs x i <;> cases normal xs y i <;> rfl
  intro x
  constructor
  · apply Span.mono
    intro y hy
    rw [hcols] at hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    apply (normal_eq_zero_iff _ _).mp
    simp [f, normal_add, normal_idempotent]
  · intro mem
    have hxx : f x = x := by simp [f, (normal_eq_zero_iff xs x).mpr mem]
    have colsMem (i : Fin n) : ListSpan (columns (encode xs)) (f (unit i)) :=
      .gen (by rw [hcols]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)
    have proof := applyColumns_in_span (fun i => f (unit i)) x colsMem
    rw [applyColumns_linear f (by simp [f, normal_zero]) hf, hxx] at proof
    exact proof

/-- Decode even spurious matrix outputs. Every returned space has width n.
The slice can be empty if no generator meets the homogenizing coordinate. -/
def candidate (M : Matrix (n+1)) : Option Candidate :=
  let xs := columns M
  (splitPivot xs).map (fun pair =>
    ⟨word (tail pair.1), triangular n (subproblem xs)⟩)

theorem candidate_shape {M : Matrix (n+1)} {A : Candidate}
    (ok : candidate M = some A) : Shaped n A.pivots ∧ A.base.length = n := by
  unfold candidate at ok
  cases h : splitPivot (columns M) with
  | none => simp [h] at ok
  | some p =>
    simp [h] at ok
    subst A
    exact ⟨triangular_shape _, word_length _⟩

theorem candidate_mem (M : Matrix (n+1)) (x : Bits n) :
    (∃ A, candidate M = some A ∧ word x ∈ A.points) ↔
      ListSpan (columns M) (lift x) := by
  rw [← triangular_spec, triangular, lift, word_cons]
  cases e : splitPivot (columns M) with
  | none => simp [candidate, e, linearPoints, List.mem_map]
  | some pr => cases pr; simp [candidate, e, linearPoints, Candidate.points, List.mem_map]

theorem points_width {M : Matrix (n+1)} {A : Candidate} (ok : candidate M = some A)
    {w : Word} (hm : w ∈ A.points) : w.length = n := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨shape, hbase⟩ := candidate_shape ok
  simp [shape.points_width hp, hbase]

theorem parity_add (z : Word) (x y : Bits n) :
    dot z (word (add x y)) = (dot z (word x) ^^ dot z (word y)) := by
  rw [word_add, dot_translate _ _ _ (by simp)]

theorem parity_hull {S : Word → Prop} {x : Bits n}
    (hx : AffineHull (fun v : Bits n => S (word v)) x) :
    AffinePruning.hull dot S (word x) := by
  intro z b eqn
  apply affineHull_minimal (T := fun v => dot z (word v) = b) (fun v hv => eqn _ hv) _ hx
  intro v w u hv hw hu
  change dot z (word (add (add v w) u)) = b
  rw [parity_add, parity_add, hv, hw, hu]
  cases b <;> rfl

theorem true_candidate {S : Word → Prop} (width : ∀ w, S w → w.length = n)
    (sat : ∃ w, S w) (xs : List (Bits (n+1)))
    (rep : ∀ v, ListSpan xs v ↔ Span (Lifted (fun v : Bits n => S (word v))) v) :
    ∃ A, candidate (encode xs) = some A ∧ Genuine S A := by
  let M := encode xs
  have holds (x : Bits n) :
      (∃ A, candidate M = some A ∧ word x ∈ A.points) ↔
        AffineHull (fun v : Bits n => S (word v)) x :=
    (candidate_mem M x).trans (((projected_sameSpan xs _).trans (rep _)).trans
      (affineHull_iff_lifted_span _ _).symm)
  have incl (w : Word) (hw : S w) : ∃ A, candidate M = some A ∧ w ∈ A.points := by
    have back := word_bits (width w hw)
    have tmp := (holds (bits w n)).mpr (affineHull_gen (by simpa only [back] using hw))
    simpa only [back] using tmp
  obtain ⟨w, hw⟩ := sat
  obtain ⟨A, ha, _⟩ := incl w hw
  refine ⟨A, ha, ?_, ?_⟩
  · intro v hv
    obtain ⟨B, hb, hmem⟩ := incl v hv
    rw [ha] at hb
    cases hb
    exact hmem
  · intro v hmem
    have back := word_bits (points_width ha hmem)
    have aff := (holds (bits v n)).mp ⟨A, ha, by simpa only [back] using hmem⟩
    simpa only [back] using parity_hull aff

end HullDecoder
