module

public import Std

/-! Binary affine-hull recovery using one batch of existential queries.
The homogenizing coordinate is first. Gaussian elimination computes a canonical
linear normal form whose kernel is the row span. Its values on the coordinate
vectors encode the span by a square binary matrix. The nonzero equations are
independent, and the remaining equations supply the zero padding.

At width d = m + 1, the batch has (d + 1)(1 + d²) queries, including rank zero.
A rank-r certificate holds r points of m bits each. The executable verifier
tests membership in the supplied predicate at most r times and runs one
elimination. A bit query additionally applies the normal form to one coordinate
vector. The bounds below count certificates, queries, and elimination row bits. -/

@[expose] public section

namespace HullRecovery

abbrev Bits (n : Nat) := Fin n → Bool

def zero (n : Nat) : Bits n := fun _ => false
def add {n : Nat} (x y : Bits n) : Bits n := fun i => xor (x i) (y i)
def cons {n : Nat} (b : Bool) (x : Bits n) : Bits (n + 1) := Fin.cases b x
def head {n : Nat} (x : Bits (n + 1)) : Bool := x 0
def tail {n : Nat} (x : Bits (n + 1)) : Bits n := fun i => x i.succ

@[simp] theorem head_cons (b : Bool) (x : Bits n) : head (cons b x) = b := rfl
@[simp] theorem tail_cons (b : Bool) (x : Bits n) : tail (cons b x) = x := by
  funext i
  simp [tail, cons]
@[simp] theorem cons_head_tail (x : Bits (n + 1)) : cons (head x) (tail x) = x := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.cases_succ i

theorem eq_of_head_tail {x y : Bits (n + 1)} (h : head x = head y)
    (t : tail x = tail y) : x = y := by
  rw [← cons_head_tail x, ← cons_head_tail y, h, t]

@[simp] theorem head_zero : head (zero (n + 1)) = false := rfl
@[simp] theorem tail_zero : tail (zero (n + 1)) = zero n := rfl
@[simp] theorem head_add (x y : Bits (n + 1)) :
    head (add x y) = xor (head x) (head y) := rfl
@[simp] theorem tail_add (x y : Bits (n + 1)) :
    tail (add x y) = add (tail x) (tail y) := rfl

@[simp] theorem zero_add (x : Bits n) : add (zero n) x = x := by
  funext i
  simp [add, zero]
@[simp] theorem add_zero (x : Bits n) : add x (zero n) = x := by
  funext i
  simp [add, zero]
@[simp] theorem add_self (x : Bits n) : add x x = zero n := by
  funext i
  simp [add, zero]
theorem add_comm (x y : Bits n) : add x y = add y x := by
  funext i
  exact Bool.xor_comm _ _
theorem add_assoc (x y z : Bits n) : add (add x y) z = add x (add y z) := by
  funext i
  exact Bool.xor_assoc _ _ _
@[simp] theorem add_cancel_right (x y : Bits n) : add (add x y) y = x := by
  rw [add_assoc, add_self, add_zero]
theorem add_eq_zero_iff (x y : Bits n) : add x y = zero n ↔ x = y := by
  constructor
  · intro h
    rw [← add_cancel_right x y, h, zero_add]
  · rintro rfl
    exact add_self x

/-- The ordinary binary linear span, formed by finite additions of generators. -/
inductive Span {n : Nat} (S : Bits n → Prop) : Bits n → Prop
  | zero : Span S (zero n)
  | gen {x} : S x → Span S x
  | add {x y} : Span S x → Span S y → Span S (add x y)

abbrev ListSpan (xs : List (Bits n)) := Span (· ∈ xs)

theorem Span.map {S : Bits n → Prop} {T : Bits m → Prop}
    (f : Bits n → Bits m) (hz : f (HullRecovery.zero n) = HullRecovery.zero m)
    (ha : ∀ x y, f (HullRecovery.add x y) = HullRecovery.add (f x) (f y))
    (hg : ∀ x, S x → Span T (f x)) {x} (hx : Span S x) : Span T (f x) := by
  induction hx with
  | zero => rw [hz]; exact Span.zero
  | gen h => exact hg _ h
  | add _ _ h₁ h₂ => rw [ha]; exact Span.add h₁ h₂

theorem Span.mono {S T : Bits n → Prop} (h : ∀ x, S x → Span T x)
    {x} (hx : Span S x) : Span T x :=
  Span.map id rfl (fun _ _ => rfl) h hx

/-- The first row with a one in the leading coordinate, and the other rows
in their original order. -/
def splitPivot : List (Bits (n + 1)) → Option (Bits (n + 1) × List (Bits (n + 1)))
  | [] => none
  | x :: xs =>
    if head x then some (x, xs)
    else (splitPivot xs).map fun (p, rest) => (p, x :: rest)

theorem splitPivot_none {xs : List (Bits (n + 1))} (h : splitPivot xs = none) :
    ∀ x ∈ xs, head x = false := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [splitPivot] at h
    split at h
    · contradiction
    · rename_i hy
      cases e : splitPivot ys with
      | none =>
        simp only [List.mem_cons]
        rintro x (rfl | hx)
        · simpa using hy
        · exact ih e x hx
      | some a => simp [e] at h

theorem splitPivot_some {xs : List (Bits (n + 1))} {p rest}
    (h : splitPivot xs = some (p, rest)) : head p = true ∧ (p :: rest).Perm xs := by
  induction xs generalizing rest with
  | nil => simp [splitPivot] at h
  | cons y ys ih =>
    rw [splitPivot] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨‹head y = true›, List.Perm.refl _⟩
    · cases e : splitPivot ys with
      | none => simp [e] at h
      | some pair =>
        obtain ⟨q, rs⟩ := pair
        simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hq, hperm⟩ := ih e
        exact ⟨hq, (List.Perm.swap y q rs).trans (hperm.cons y)⟩

def lower {n : Nat} (p x : Bits (n + 1)) : Bits n :=
  if head x then tail (add x p) else tail x

@[simp] theorem lower_zero (p : Bits (n + 1)) : lower p (zero (n + 1)) = zero n := by
  simp [lower]

@[simp] theorem lower_self (p : Bits (n + 1)) (hp : head p = true) :
    lower p p = zero n := by simp [lower, hp]

theorem lower_add (p x y : Bits (n + 1)) :
    lower p (add x y) = add (lower p x) (lower p y) := by
  cases hx : head x <;> cases hy : head y <;>
    simp [lower, hx, hy, add_assoc]
  · rw [add_comm (tail y) (tail p)]
  · rw [← add_assoc (tail p), add_comm (tail p) (tail y), add_assoc,
      add_self, add_zero]

theorem cons_false_zero : cons false (zero n) = zero (n + 1) :=
  eq_of_head_tail (by simp) (by simp)

theorem cons_false_add (x y : Bits n) :
    cons false (add x y) = add (cons false x) (cons false y) :=
  eq_of_head_tail (by simp) (by simp)

theorem span_head_false {xs : List (Bits (n + 1))}
    (h : ∀ x ∈ xs, head x = false) {x} (hx : ListSpan xs x) : head x = false := by
  induction hx with
  | zero => rfl
  | gen hx => exact h _ hx
  | add _ _ hi hj => simp [hi, hj]

theorem span_without_head {S : Bits (n + 1) → Prop} {p x : Bits (n + 1)}
    (hp : Span S p) (hp₀ : head p = true) :
    Span S x ↔ Span S (cons false (lower p x)) := by
  cases hx : head x
  · have e : cons false (lower p x) = x :=
      eq_of_head_tail (by simp [hx]) (by simp [lower, hx])
    rw [e]
  · have e : cons false (lower p x) = add x p :=
      eq_of_head_tail (by simp [hx, hp₀]) (by simp [lower, hx])
    rw [e]
    exact ⟨fun h => Span.add h hp, fun h => by
      simpa only [add_cancel_right] using Span.add h hp⟩

def subproblem (xs : List (Bits (n + 1))) : List (Bits n) :=
  match splitPivot xs with
  | none => xs.map tail
  | some (p, rest) => rest.map (lower p)

def pivotCount (xs : List (Bits (n + 1))) : Nat :=
  if (splitPivot xs).isSome then 1 else 0

theorem subproblem_span (xs : List (Bits (n + 1))) (y : Bits n) :
    ListSpan (subproblem xs) y ↔ ListSpan xs (cons false y) := by
  cases e : splitPivot xs with
  | none =>
    rw [subproblem, e]
    constructor
    · apply Span.map (cons false) cons_false_zero cons_false_add
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      have h := splitPivot_none e x hx
      have ex : cons false (tail x) = x := by rw [← h, cons_head_tail]
      rw [ex]
      exact Span.gen hx
    · intro h
      have h' := Span.map tail tail_zero tail_add
        (fun x (hx : x ∈ xs) => Span.gen (List.mem_map_of_mem hx)) h
      simpa only [tail_cons] using h'
  | some pair =>
    obtain ⟨p, rest⟩ := pair
    obtain ⟨hp₀, perm⟩ := splitPivot_some e
    have hp : ListSpan xs p := Span.gen (perm.mem_iff.mp (by simp))
    rw [subproblem, e]
    constructor
    · apply Span.map (cons false) cons_false_zero cons_false_add
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact (span_without_head hp hp₀).mp (Span.gen (perm.mem_iff.mp (by simp [hx])))
    · intro h
      have hg (x : Bits (n + 1)) (hx : x ∈ xs) :
          ListSpan (rest.map (lower p)) (lower p x) := by
        rcases List.mem_cons.mp (perm.mem_iff.mpr hx) with rfl | hm
        · rw [lower_self _ hp₀]
          exact Span.zero
        · exact Span.gen (List.mem_map_of_mem hm)
      have h' := Span.map (lower p) (lower_zero p) (lower_add p) hg h
      have eq : lower p (cons false y) = y := by simp [lower]
      rwa [eq] at h'

/-- Store a row eagerly, so repeated reads do not re-evaluate row operations. -/
@[noinline] def materialize (x : Bits n) : Bits n :=
  let row := Vector.ofFn x
  fun i => row.get i

@[simp] theorem materialize_eq (x : Bits n) : materialize x = x := by
  funext i
  exact Vector.getElem_ofFn i.isLt

/-- Simultaneous elimination computes the rank and returns a linear map that
removes the pivot coordinates. The recursive result is shared. -/
structure Elimination (n : Nat) where
  rank : Nat
  normal : Bits n → Bits n
  free : Bits n

def eliminate : (n : Nat) → List (Bits n) → Elimination n
  | 0, _ => ⟨0, id, zero 0⟩
  | n + 1, xs =>
    match splitPivot xs with
    | none =>
      let e := eliminate n (xs.map (fun x => materialize (tail x)))
      ⟨e.rank, (fun x => cons (head x) (e.normal (materialize (tail x)))), cons true e.free⟩
    | some (p, rest) =>
      let e := eliminate n (rest.map (fun x => materialize (lower p x)))
      ⟨e.rank + 1, (fun x => cons false (e.normal (materialize (lower p x)))), cons false e.free⟩

def rank (xs : List (Bits n)) := (eliminate n xs).rank
def normal (xs : List (Bits n)) := (eliminate n xs).normal

theorem rank_step (xs : List (Bits (n + 1))) :
    rank xs = rank (subproblem xs) + pivotCount xs := by
  cases h : splitPivot xs with
  | none => simp [rank, eliminate, subproblem, pivotCount, h]
  | some p => cases p; simp [rank, eliminate, subproblem, pivotCount, h]

theorem rank_bounds (xs : List (Bits n)) : rank xs ≤ n ∧ rank xs ≤ xs.length := by
  induction n with
  | zero => simp [rank, eliminate]
  | succ n ih =>
    rw [rank_step]
    obtain ⟨hn, hl⟩ := ih (subproblem xs)
    cases h : splitPivot xs with
    | none =>
      simp only [subproblem, pivotCount, h, Option.isSome_none, Bool.false_eq_true,
        if_false, Nat.add_zero, List.length_map] at *
      omega
    | some p =>
      obtain ⟨p, rest⟩ := p
      have len := (splitPivot_some h).2.length_eq
      simp only [List.length_cons] at len
      simp only [subproblem, pivotCount, h, Option.isSome_some, if_true, List.length_map] at *
      omega


theorem subproblem_length_le (xs : List (Bits (n + 1))) :
    (subproblem xs).length ≤ xs.length := by
  cases h : splitPivot xs with
  | none => simp [subproblem, h]
  | some pair =>
    obtain ⟨p, rest⟩ := pair
    have len := (splitPivot_some h).2.length_eq
    simp only [List.length_cons] at len
    simp [subproblem, h, ← len]

/-- The number of Boolean cells materialized in the elimination's recursive
row lists. Pivot scans and applications of the normal form are separate work. -/
def eliminationRowBits : (n : Nat) → List (Bits n) → Nat
  | 0, _ => 0
  | n + 1, xs =>
    let ys := subproblem xs
    ys.length * n + eliminationRowBits n ys

theorem eliminationRowBits_bound (xs : List (Bits n)) :
    eliminationRowBits n xs ≤ xs.length * n * n := by
  induction n with
  | zero => simp [eliminationRowBits]
  | succ n ih =>
    let ys := subproblem xs
    have h : ys.length * n ≤ xs.length * n := Nat.mul_le_mul_right _ (subproblem_length_le xs)
    change ys.length * n + eliminationRowBits n ys ≤ xs.length * (n + 1) * (n + 1)
    calc
      _ ≤ xs.length * n + xs.length * n * n :=
        Nat.add_le_add h (Nat.le_trans (ih ys) (Nat.mul_le_mul_right _ h))
      _ = (xs.length * n) * (n + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))

theorem normal_none {xs : List (Bits (n + 1))} (e : splitPivot xs = none)
    (x : Bits (n + 1)) :
    normal xs x = cons (head x) (normal (xs.map tail) (tail x)) := by
  simp [normal, eliminate, e]

theorem normal_some {xs : List (Bits (n + 1))} {p rest}
    (e : splitPivot xs = some (p, rest)) (x : Bits (n + 1)) :
    normal xs x = cons false (normal (rest.map (lower p)) (lower p x)) := by
  simp [normal, eliminate, e]

theorem normal_add (xs : List (Bits n)) (x y : Bits n) :
    normal xs (add x y) = add (normal xs x) (normal xs y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases e : splitPivot xs with
    | none =>
      simp only [normal_none e]
      exact eq_of_head_tail (by simp) (by simp [ih])
    | some pair =>
      obtain ⟨p, rest⟩ := pair
      simp only [normal_some e, lower_add, ih, cons_false_add]

theorem normal_zero (xs : List (Bits n)) : normal xs (zero n) = zero n := by
  simpa using normal_add xs (zero n) (zero n)

theorem normal_eq_zero_iff (xs : List (Bits n)) (x : Bits n) :
    normal xs x = zero n ↔ ListSpan xs x := by
  induction n with
  | zero =>
    have e : x = zero 0 := funext (fun i => Fin.elim0 i)
    rw [e]
    exact ⟨fun _ => Span.zero, fun _ => normal_zero xs⟩
  | succ n ih =>
    cases e : splitPivot xs with
    | none =>
      rw [normal_none e]
      have hk (u : Bits n) := subproblem_span xs u
      rw [subproblem, e] at hk
      constructor
      · intro h
        have hh := congrArg head h
        have ht := congrArg tail h
        simp only [head_cons, head_zero] at hh
        simp only [tail_cons, tail_zero] at ht
        have hs := (hk (tail x)).mp ((ih _ _).mp ht)
        rwa [← hh, cons_head_tail] at hs
      · intro h
        have hh := span_head_false (splitPivot_none e) h
        have hs : ListSpan xs (cons false (tail x)) := by
          rwa [← hh, cons_head_tail]
        rw [hh, (ih _ _).mpr ((hk _).mpr hs), cons_false_zero]
    | some pair =>
      obtain ⟨p, rest⟩ := pair
      obtain ⟨hp₀, perm⟩ := splitPivot_some e
      have hp : ListSpan xs p := Span.gen (perm.mem_iff.mp (by simp))
      have hk := subproblem_span xs (lower p x)
      rw [subproblem, e] at hk
      rw [normal_some e, ← cons_false_zero (n := n)]
      exact ⟨fun h => (span_without_head hp hp₀).mpr
          (hk.mp ((ih _ _).mp (by simpa only [tail_cons] using congrArg tail h))),
        fun h => congrArg (cons false)
          ((ih _ _).mpr (hk.mpr ((span_without_head hp hp₀).mp h)))⟩

theorem normal_eq_iff (xs : List (Bits n)) (x y : Bits n) :
    normal xs x = normal xs y ↔ ListSpan xs (add x y) := by
  rw [← normal_eq_zero_iff, normal_add, add_eq_zero_iff]

abbrev SameSpan (xs ys : List (Bits n)) : Prop :=
  ∀ x, ListSpan xs x ↔ ListSpan ys x

theorem subproblem_le {xs ys : List (Bits (n + 1))}
    (h : ∀ x, ListSpan xs x → ListSpan ys x) :
    ∀ x, ListSpan (subproblem xs) x → ListSpan (subproblem ys) x :=
  fun x hx => (subproblem_span ys x).mpr (h _ ((subproblem_span xs x).mp hx))

theorem pivotCount_eq_one_iff (xs : List (Bits (n + 1))) :
    pivotCount xs = 1 ↔ ∃ x, ListSpan xs x ∧ head x = true := by
  cases e : splitPivot xs with
  | none =>
    simp only [pivotCount, e, Option.isSome_none, Bool.false_eq_true, if_false,
      Nat.zero_ne_one, false_iff]
    rintro ⟨x, hx, h⟩
    rw [span_head_false (splitPivot_none e) hx] at h
    contradiction
  | some pair =>
    obtain ⟨p, rest⟩ := pair
    obtain ⟨hp, perm⟩ := splitPivot_some e
    simp only [pivotCount, e, Option.isSome_some, if_true, true_iff]
    exact ⟨p, Span.gen (perm.mem_iff.mp (by simp)), hp⟩

theorem pivotCount_le {xs ys : List (Bits (n + 1))}
    (h : ∀ x, ListSpan xs x → ListSpan ys x) : pivotCount xs ≤ pivotCount ys := by
  unfold pivotCount
  split
  · rename_i hx
    have hx' : pivotCount xs = 1 := by simp [pivotCount, hx]
    obtain ⟨x, hx, hb⟩ := (pivotCount_eq_one_iff xs).mp hx'
    have hy := (pivotCount_eq_one_iff ys).mpr ⟨x, h x hx, hb⟩
    exact Nat.le_of_eq hy.symm
  · exact Nat.zero_le _

/-- Inclusion is rank-monotone, and inclusion at equal rank is equality. -/
theorem rank_mono_complete {xs ys : List (Bits n)}
    (h : ∀ x, ListSpan xs x → ListSpan ys x) :
    rank xs ≤ rank ys ∧ (rank xs = rank ys → ∀ x, ListSpan ys x → ListSpan xs x) := by
  induction n with
  | zero =>
    refine ⟨Nat.le_refl _, fun _ x _ => ?_⟩
    rw [show x = zero 0 from funext (fun i => Fin.elim0 i)]
    exact Span.zero
  | succ n ih =>
    obtain ⟨hk, hk'⟩ := ih (subproblem_le h)
    have hp := pivotCount_le h
    rw [rank_step, rank_step]
    refine ⟨by omega, fun heq x hx => ?_⟩
    have eRank : rank (subproblem xs) = rank (subproblem ys) := by omega
    have ePivot : pivotCount xs = pivotCount ys := by omega
    have back (u : Bits n) (hu : ListSpan ys (cons false u)) : ListSpan xs (cons false u) :=
      (subproblem_span xs u).mp (hk' eRank u ((subproblem_span ys u).mpr hu))
    cases e : splitPivot xs with
    | none =>
      have ey : splitPivot ys = none := by
        cases ey : splitPivot ys with
        | none => rfl
        | some pair => simp [pivotCount, e, ey] at ePivot
      have b := span_head_false (splitPivot_none ey) hx
      have hc : cons false (tail x) = x := by rw [← b, cons_head_tail]
      rw [← hc] at hx ⊢
      exact back _ hx
    | some pair =>
      obtain ⟨p, rest⟩ := pair
      obtain ⟨hp₀, perm⟩ := splitPivot_some e
      have hp : ListSpan xs p := Span.gen (perm.mem_iff.mp (by simp))
      exact (span_without_head hp hp₀).mpr
        (back _ ((span_without_head (h _ hp) hp₀).mp hx))

theorem rank_congr {xs ys : List (Bits n)} (h : SameSpan xs ys) : rank xs = rank ys :=
  Nat.le_antisymm (rank_mono_complete (fun x => (h x).mp)).1
    (rank_mono_complete (fun x => (h x).mpr)).1

/-- The normal form is invariant under a change of spanning list. -/
theorem normal_congr {xs ys : List (Bits n)} (h : SameSpan xs ys) :
    normal xs = normal ys := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hk : SameSpan (subproblem xs) (subproblem ys) :=
      fun x => ⟨subproblem_le (fun u => (h u).mp) x, subproblem_le (fun u => (h u).mpr) x⟩
    have hn := ih hk
    have hp : pivotCount xs = pivotCount ys :=
      Nat.le_antisymm (pivotCount_le (fun x => (h x).mp)) (pivotCount_le (fun x => (h x).mpr))
    funext x
    cases e : splitPivot xs <;> cases f : splitPivot ys
    · rw [subproblem, e, subproblem, f] at hn
      rw [normal_none e, normal_none f, hn]
    · simp [pivotCount, e, f] at hp
    · simp [pivotCount, e, f] at hp
    · rename_i a b
      obtain ⟨p, ps⟩ := a
      obtain ⟨q, qs⟩ := b
      obtain ⟨p₀, pp⟩ := splitPivot_some e
      obtain ⟨q₀, qp⟩ := splitPivot_some f
      rw [subproblem, e, subproblem, f] at hn
      rw [normal_some e, normal_some f, hn]
      apply congrArg (cons false)
      cases hx : head x
      · simp [lower, hx]
      · apply (normal_eq_iff _ _ _).mpr
        have pin : ListSpan ys p := (h p).mp (Span.gen (pp.mem_iff.mp (by simp)))
        have qin : ListSpan ys q := Span.gen (qp.mem_iff.mp (by simp))
        have both : ListSpan ys (add p q) := Span.add pin qin
        have k : ListSpan (subproblem ys) (tail (add p q)) := by
          apply (subproblem_span _ _).mpr
          have he : cons false (tail (add p q)) = add p q :=
            eq_of_head_tail (by simp [p₀, q₀]) (by simp)
          rwa [he]
        rw [subproblem, f] at k
        have he : add (lower p x) (lower q x) = tail (add p q) := by
          simp [lower, hx, add_assoc, add_comm (tail p) (add (tail x) (tail q)),
            ← add_assoc (tail x) (tail x), add_self]
          exact add_comm _ _
        rwa [he]

theorem span_cons_mono {x : Bits n} {xs ys : List (Bits n)}
    (h : ∀ y, ListSpan xs y → ListSpan ys y) :
    ∀ y, ListSpan (x :: xs) y → ListSpan (x :: ys) y := by
  intro y hy
  apply Span.mono _ hy
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hm
  · exact Span.gen (by simp)
  · exact Span.mono (fun _ hw => Span.gen (List.mem_cons_of_mem _ hw)) (h z (Span.gen hm))

theorem span_cons_of_mem {x : Bits n} {xs : List (Bits n)} (hx : ListSpan xs x) :
    SameSpan (x :: xs) xs := by
  intro y
  constructor
  · apply Span.mono
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hm
    · exact hx
    · exact Span.gen hm
  · exact Span.mono (fun _ hm => Span.gen (List.mem_cons_of_mem _ hm))

theorem rank_strict_of_outside {x : Bits n} {xs : List (Bits n)} (hx : ¬ ListSpan xs x) :
    rank xs < rank (x :: xs) := by
  obtain ⟨hle, he⟩ := rank_mono_complete (xs := xs) (ys := x :: xs)
    (fun _ => Span.mono (fun _ h => Span.gen (List.mem_cons_of_mem _ h)))
  exact Nat.lt_of_le_of_ne hle (fun eq => hx (he eq x (Span.gen (by simp))))

/-- An independent list has every row outside the span of the subsequent
rows. Over GF(2), this excludes exactly the nontrivial zero relations. -/
def Independent {n : Nat} : List (Bits n) → Prop
  | [] => True
  | x :: xs => ¬ ListSpan xs x ∧ Independent xs

theorem independent_rank {xs : List (Bits n)} (h : Independent xs) :
    rank xs = xs.length := by
  induction xs with
  | nil => have := (rank_bounds (n := n) []).2; simp_all
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := h
    have := rank_strict_of_outside hx
    have := (rank_bounds (x :: xs)).2
    simp only [List.length_cons] at *
    have := ih ht
    omega

theorem shorter_of_dependent {xs : List (Bits n)} (h : ¬ Independent xs) :
    ∃ ys, ys.length < xs.length ∧ SameSpan xs ys := by
  classical
  induction xs with
  | nil => exact False.elim (h trivial)
  | cons x xs ih =>
    by_cases hx : ListSpan xs x
    · exact ⟨xs, by simp, span_cons_of_mem hx⟩
    · have ht : ¬ Independent xs := fun ht => h ⟨hx, ht⟩
      obtain ⟨ys, hl, hs⟩ := ih ht
      exact ⟨x :: ys, by simpa, fun y =>
        ⟨span_cons_mono (fun z => (hs z).mp) y, span_cons_mono (fun z => (hs z).mpr) y⟩⟩

theorem rank_eq_length_iff_independent (xs : List (Bits n)) :
    rank xs = xs.length ↔ Independent xs := by
  refine ⟨fun h => Classical.byContradiction (fun hd => ?_), independent_rank⟩
  obtain ⟨ys, hl, hs⟩ := shorter_of_dependent hd
  have hb := (rank_bounds ys).2
  rw [← rank_congr hs, h] at hb
  omega

theorem independent_basis (xs : List (Bits n)) :
    ∃ ys, Independent ys ∧ SameSpan ys xs := by
  classical
  induction xs with
  | nil => exact ⟨[], trivial, fun _ => Iff.rfl⟩
  | cons x xs ih =>
    obtain ⟨ys, hi, hs⟩ := ih
    have hc : SameSpan (x :: ys) (x :: xs) := fun y =>
      ⟨span_cons_mono (fun z => (hs z).mp) y, span_cons_mono (fun z => (hs z).mpr) y⟩
    by_cases hx : ListSpan ys x
    · exact ⟨ys, hi, fun y => (span_cons_of_mem hx y).symm.trans (hc y)⟩
    · exact ⟨x :: ys, ⟨hx, hi⟩, hc⟩

/-- The counted pivots equal the size of an independent spanning list. -/
theorem rank_is_basis_size (xs : List (Bits n)) :
    ∃ ys, Independent ys ∧ SameSpan ys xs ∧ ys.length = rank xs := by
  obtain ⟨ys, hi, hs⟩ := independent_basis xs
  exact ⟨ys, hi, hs, (independent_rank hi).symm.trans (rank_congr hs)⟩

def sum {n : Nat} : List (Bits n) → Bits n
  | [] => zero n
  | x :: xs => add x (sum xs)

theorem sum_append (xs ys : List (Bits n)) :
    sum (xs ++ ys) = add (sum xs) (sum ys) := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih => simp [sum, ih, add_assoc]

def lift (x : Bits m) : Bits (m + 1) := cons true x

/-- Odd finite binary sums of points of S, i.e. affine combinations over
GF(2). Repetitions are allowed and cancel in pairs. -/
def AffineHull (S : Bits m → Prop) (x : Bits m) : Prop :=
  ∃ pts, (∀ y ∈ pts, S y) ∧ pts.length % 2 = 1 ∧ sum pts = x

def Lifted (S : Bits m → Prop) (v : Bits (m + 1)) : Prop :=
  ∃ x, S x ∧ lift x = v

theorem lifted_span_iff_sum (S : Bits m → Prop) (v : Bits (m + 1)) :
    Span (Lifted S) v ↔ ∃ pts : List (Bits m), (∀ y ∈ pts, S y) ∧ sum (pts.map lift) = v := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨[], by simp, rfl⟩
    | gen h =>
      obtain ⟨x, hx, rfl⟩ := h
      exact ⟨[x], by simpa, by simp [sum]⟩
    | add _ _ ih₁ ih₂ =>
      obtain ⟨xs, hxs, rfl⟩ := ih₁
      obtain ⟨ys, hys, rfl⟩ := ih₂
      exact ⟨xs ++ ys, fun x h => (List.mem_append.mp h).elim (hxs x) (hys x),
        by rw [List.map_append, sum_append]⟩
  · rintro ⟨pts, hs, rfl⟩
    induction pts with
    | nil => exact Span.zero
    | cons x xs ih =>
      exact Span.add (Span.gen ⟨x, hs x (by simp), rfl⟩)
        (ih (fun y h => hs y (List.mem_cons_of_mem _ h)))

theorem sum_lifts (xs : List (Bits m)) :
    sum (xs.map lift) = cons (decide (xs.length % 2 = 1)) (sum xs) := by
  induction xs with
  | nil => exact cons_false_zero.symm
  | cons x xs ih =>
    simp only [List.map_cons, sum, ih]
    apply eq_of_head_tail
    · simp only [head_add, lift, head_cons, List.length_cons, Bool.true_xor]
      by_cases h : xs.length % 2 = 1
      · have h' : (xs.length + 1) % 2 ≠ 1 := by omega
        simp [h, h']
      · have h' : (xs.length + 1) % 2 = 1 := by omega
        simp [h, h']
    · simp [lift]

theorem affineHull_iff_lifted_span (S : Bits m → Prop) (x : Bits m) :
    AffineHull S x ↔ Span (Lifted S) (lift x) := by
  rw [lifted_span_iff_sum]
  constructor
  · rintro ⟨pts, hs, odd, rfl⟩
    exact ⟨pts, hs, by simp [sum_lifts, lift, odd]⟩
  · rintro ⟨pts, hs, eq⟩
    rw [sum_lifts] at eq
    exact ⟨pts, hs, by simpa [lift] using congrArg head eq,
      by simpa [lift] using congrArg tail eq⟩

/-- Any ternary-xor-closed set that contains S contains its affine hull.
This definition of closure also accommodates the empty set. -/
theorem affineHull_minimal {S T : Bits m → Prop}
    (hST : ∀ x, S x → T x)
    (closed : ∀ x y z, T x → T y → T z → T (add (add x y) z))
    {x} (hx : AffineHull S x) : T x := by
  obtain ⟨pts, hs, hodd, rfl⟩ := hx
  let rec go (pts : List (Bits m)) (hs : ∀ y ∈ pts, S y)
      (odd : pts.length % 2 = 1) : T (sum pts) := by
    match pts with
    | [] => simp at odd
    | [x] => simpa [sum] using hST x (hs x (by simp))
    | x :: y :: xs =>
      have ht : T (sum xs) := go xs (fun z hz => hs z (by simp [hz])) (by
        simp only [List.length_cons] at odd
        omega)
      simpa only [sum, add_assoc] using
        closed x y (sum xs) (hST x (hs x (by simp))) (hST y (hs y (by simp))) ht
  exact go pts hs hodd

theorem affineHull_gen {S : Bits m → Prop} {x} (h : S x) : AffineHull S x :=
  ⟨[x], by simpa, by simp, by simp [sum]⟩

theorem affineHull_closed {S : Bits m → Prop} {x y z : Bits m}
    (hx : AffineHull S x) (hy : AffineHull S y) (hz : AffineHull S z) :
    AffineHull S (add (add x y) z) := by
  obtain ⟨xs, hx, ox, rfl⟩ := hx
  obtain ⟨ys, hy, oy, rfl⟩ := hy
  obtain ⟨zs, hz, oz, rfl⟩ := hz
  refine ⟨(xs ++ ys) ++ zs, ?_, ?_, by simp only [sum_append]⟩
  · intro u hu
    simp only [List.mem_append] at hu
    exact hu.elim (fun h => h.elim (hx u) (hy u)) (hz u)
  · simp only [List.length_append]
    omega

def unit (i : Fin n) : Bits n := fun j => decide (j = i)

theorem unit_zero : unit (0 : Fin (n + 1)) = cons true (zero n) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [unit, cons]
  | succ j => simp [unit, cons, zero, Fin.succ_ne_zero]

theorem unit_succ (i : Fin n) : unit i.succ = cons false (unit i) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [unit, cons, (Fin.succ_ne_zero i).symm]
  | succ j => simp [unit, cons]

abbrev Matrix (n : Nat) := Fin n → Bits n

/-- Column i is the normal form of coordinate vector i. -/
def encode (xs : List (Bits n)) : Matrix n :=
  let e := eliminate n xs
  fun i => e.normal (unit i)

theorem encode_congr {xs ys : List (Bits n)} (h : SameSpan xs ys) :
    encode xs = encode ys := by
  have he := normal_congr h
  exact congrArg (fun (f : Bits n → Bits n) i => f (unit i)) he

/-- Multiply an explicit binary matrix (specified by its columns)
by an input vector. -/
def applyColumns {m : Nat} : (n : Nat) → (Fin n → Bits m) → Bits n → Bits m
  | 0, _, _ => zero m
  | n + 1, cols, x =>
    add (if head x then cols 0 else zero m)
      (applyColumns n (fun i => cols i.succ) (tail x))

theorem applyColumns_linear {m : Nat} (f : Bits n → Bits m)
    (h0 : f (zero n) = zero m) (ha : ∀ x y, f (add x y) = add (f x) (f y))
    (x : Bits n) : applyColumns n (fun i => f (unit i)) x = f x := by
  induction n with
  | zero =>
    have e : x = zero 0 := funext (fun i => Fin.elim0 i)
    simpa [applyColumns, e] using h0.symm
  | succ n ih =>
    simp only [applyColumns, unit_succ]
    rw [ih (fun v => f (cons false v)) (by simp [cons_false_zero, h0])
      (fun u v => by rw [cons_false_add, ha])]
    let v : Bits (n + 1) := if head x then unit 0 else zero (n + 1)
    have hv : (if head x then f (unit 0) else zero m) = f v := by
      cases hh : head x <;> simp [v, hh, h0]
    rw [hv, ← ha]
    apply congrArg f
    apply eq_of_head_tail
    · cases hh : head x <;> simp [v, hh, unit_zero]
    · cases hh : head x <;> simp [v, hh, unit_zero]

def free (xs : List (Bits n)) : Bits n := (eliminate n xs).free

theorem free_none {xs : List (Bits (n + 1))} (e : splitPivot xs = none) :
    free xs = cons true (free (xs.map tail)) := by
  simp [free, eliminate, e]

theorem free_some {xs : List (Bits (n + 1))} {p rest}
    (e : splitPivot xs = some (p, rest)) :
    free xs = cons false (free (rest.map (lower p))) := by
  simp [free, eliminate, e]

theorem normal_zero_at_pivot (xs : List (Bits n)) (x : Bits n) (i : Fin n)
    (hi : free xs i = false) : normal xs x i = false := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases e : splitPivot xs with
    | none =>
      rw [normal_none e, free_none e] at *
      cases i using Fin.cases with
      | zero => simp [cons] at hi
      | succ i => simpa [cons] using ih _ _ i (by simpa [cons] using hi)
    | some pair =>
      obtain ⟨p, rest⟩ := pair
      rw [normal_some e, free_some e] at *
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simpa [cons] using ih _ _ i (by simpa [cons] using hi)

theorem normal_free_unit (xs : List (Bits n)) (i : Fin n) (hi : free xs i = true) :
    normal xs (unit i) = unit i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases e : splitPivot xs with
    | none =>
      rw [normal_none e, free_none e] at *
      cases i using Fin.cases with
      | zero => simp [unit_zero, normal_zero]
      | succ i =>
        rw [unit_succ, head_cons, tail_cons, ih _ i (by simpa [cons] using hi)]
    | some pair =>
      obtain ⟨p, rest⟩ := pair
      rw [normal_some e, free_some e] at *
      cases i using Fin.cases with
      | zero => simp [cons] at hi
      | succ i =>
        rw [unit_succ]
        have he : lower p (cons false (unit i)) = unit i := by simp [lower]
        rw [he, ih _ i (by simpa [cons] using hi)]

def equation (xs : List (Bits n)) (i : Fin n) : Bits n := fun j => encode xs j i

theorem equation_zero_iff (xs : List (Bits n)) (i : Fin n) :
    equation xs i = zero n ↔ free xs i = false := by
  constructor
  · intro h
    cases hi : free xs i
    · rfl
    · have he := congrFun h i
      change normal xs (unit i) i = false at he
      simp [normal_free_unit xs i hi, unit] at he
  · intro h
    funext j
    exact normal_zero_at_pivot xs (unit j) i h

/-- The nonzero equations are linearly independent. The coordinate vector
at a free coordinate evaluates to one on its equation and zero on all the
other equations. -/
theorem equations_independent (xs : List (Bits n)) (i : Fin n) (hi : free xs i = true) :
    ¬ Span (fun row => ∃ j, free xs j = true ∧ j ≠ i ∧ equation xs j = row)
      (equation xs i) := by
  have eval (j : Fin n) : equation xs j i = decide (j = i) := by
    change normal xs (unit i) j = _
    rw [normal_free_unit xs i hi]
    rfl
  have vanishes (row : Bits n)
      (h : Span (fun row => ∃ j, free xs j = true ∧ j ≠ i ∧ equation xs j = row) row) :
      row i = false := by
    induction h with
    | zero => rfl
    | gen h =>
      obtain ⟨j, _, hj, rfl⟩ := h
      simp [eval, hj]
    | add _ _ hu hv =>
      simp [add, hu, hv]
  intro h
  simpa [eval] using vanishes _ h

theorem decode_span (xs : List (Bits n)) (x : Bits n) :
    applyColumns n (encode xs) x = zero n ↔ ListSpan xs x := by
  have he := applyColumns_linear (normal xs) (normal_zero xs) (normal_add xs) x
  change applyColumns n (encode xs) x = normal xs x at he
  rw [he, normal_eq_zero_iff]

theorem encode_eq_iff (xs ys : List (Bits n)) : encode xs = encode ys ↔ SameSpan xs ys := by
  constructor
  · intro h x
    rw [← decode_span xs x, ← decode_span ys x, h]
  · exact encode_congr

/-- The leading coordinate is fixed to one when interpreting the matrix. -/
def Decode (matrix : Matrix (m + 1)) (x : Bits m) : Prop :=
  applyColumns (m + 1) matrix (lift x) = zero (m + 1)

inductive Query (d : Nat) where
  | rank (r : Fin (d + 1))
  | bit (r : Fin (d + 1)) (col row : Fin d)
  deriving DecidableEq

def Query.level : Query d → Fin (d + 1)
  | .rank r => r
  | .bit r _ _ => r

abbrev Witness (m r : Nat) := { pts : List (Bits m) // pts.length = r }

def Valid (S : Bits m → Prop) {r : Nat} (w : Witness m r) : Prop :=
  (∀ x ∈ w.val, S x) ∧ rank (w.val.map lift) = r

def requestedBit (q : Query (m + 1)) (pts : List (Bits m)) : Bool :=
  match q with
  | .rank _ => true
  | .bit _ i j => encode (pts.map lift) i j

/-- Every query has a single existentially quantified, length-indexed witness. -/
def Yes (S : Bits m → Prop) (q : Query (m + 1)) : Prop :=
  ∃ w : Witness m q.level.val, Valid S w ∧ requestedBit q w.val = true

def verify (S : Bits m → Prop) [DecidablePred S] (q : Query (m + 1))
    (w : Witness m q.level.val) : Bool :=
  w.val.all (fun x => decide (S x)) &&
    let e := eliminate (m + 1) (w.val.map lift)
    (e.rank == q.level.val) &&
      match q with
      | .rank _ => true
      | .bit _ i j => e.normal (unit i) j

theorem verify_correct (S : Bits m → Prop) [DecidablePred S] (q : Query (m + 1))
    (w : Witness m q.level.val) :
    verify S q w = true ↔ Valid S w ∧ requestedBit q w.val = true := by
  cases q <;> simp [verify, Valid, rank, requestedBit, encode, List.all_eq_true, and_assoc]

/-- A witness can be supplied as fixed-length arrays of explicit bits. -/
abbrev PackedWitness (m r : Nat) := Vector (Vector Bool m) r

def pack (w : Witness m r) : PackedWitness m r :=
  Vector.ofFn fun i => Vector.ofFn (w.val.get (i.cast w.property.symm))

def unpack (w : PackedWitness m r) : Witness m r :=
  ⟨List.ofFn (fun i j => (w.get i).get j), List.length_ofFn⟩

theorem unpack_pack (w : Witness m r) : unpack (pack w) = w := by
  apply Subtype.ext
  apply List.ext_getElem (by simp [unpack, w.property])
  intro i hi₁ hi₂
  funext j
  change (List.ofFn (fun i j => ((pack w).get i).get j))[i] j = w.val[i] j
  rw [List.getElem_ofFn hi₁]
  have get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (k : Fin n) :
      (Vector.ofFn f).get k = f k := Vector.getElem_ofFn k.isLt
  simp only [pack, get_ofFn]
  all_goals rfl

def verifyPacked (S : Bits m → Prop) [DecidablePred S] (q : Query (m + 1))
    (w : PackedWitness m q.level.val) : Bool :=
  verify S q (unpack w)

theorem yes_iff_verifyPacked (S : Bits m → Prop) [DecidablePred S] (q : Query (m + 1)) :
    Yes S q ↔ ∃ w, verifyPacked S q w = true := by
  constructor
  · rintro ⟨w, h⟩
    exact ⟨pack w, by simpa [verifyPacked, unpack_pack] using (verify_correct S q w).mpr h⟩
  · rintro ⟨w, h⟩
    exact ⟨unpack w, (verify_correct S q _).mp h⟩

/-- Each rank block asks for feasibility and then each entry in column order. -/
def block (d : Nat) (r : Fin (d + 1)) : List (Query d) :=
  .rank r :: ((List.finRange d).flatMap fun i =>
    (List.finRange d).map fun j => .bit r i j)

/-- The full query list depends only on the ambient width. -/
def batch (d : Nat) : List (Query d) :=
  (List.finRange (d + 1)).flatMap (block d)

theorem mem_finRange (i : Fin d) : i ∈ List.finRange d :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mem_batch (q : Query d) : q ∈ batch d := by
  cases q with
  | rank r => exact List.mem_flatMap.mpr ⟨r, mem_finRange r, by simp [block]⟩
  | bit r i j =>
    apply List.mem_flatMap.mpr
    refine ⟨r, mem_finRange r, List.mem_cons_of_mem _ ?_⟩
    exact List.mem_flatMap.mpr ⟨i, mem_finRange i, List.mem_map_of_mem (mem_finRange j)⟩

theorem length_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (k : Nat)
    (h : ∀ x, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [h, ih, Nat.add_mul, Nat.add_comm]

theorem batch_length (d : Nat) : (batch d).length = (d + 1) * (1 + d * d) := by
  rw [batch, length_flatMap_const _ _ (1 + d * d) (fun r => ?_), List.length_finRange]
  simp only [block, List.length_cons]
  rw [length_flatMap_const _ _ d (fun _ => by simp), List.length_finRange, Nat.add_comm]

/-- The concrete witness encoding concatenates the points, coordinate by
coordinate, in tuple order. -/
def witnessBits (w : Witness m r) : List Bool :=
  w.val.flatMap (fun x => List.ofFn x)

theorem witnessBits_length (w : Witness m r) : (witnessBits w).length = r * m := by
  rw [witnessBits, length_flatMap_const _ _ m (fun _ => List.length_ofFn), w.property]

theorem query_witness_bound (q : Query (m + 1)) (w : Witness m q.level.val) :
    (witnessBits w).length ≤ (m + 1) * m := by
  rw [witnessBits_length]
  exact Nat.mul_le_mul_right _ (Nat.le_of_lt_succ q.level.isLt)

/-- A canonical serialization in column-major order. -/
def matrixBits (matrix : Matrix d) : List Bool :=
  (List.ofFn matrix).flatMap (fun col => List.ofFn col)

theorem matrixBits_length (matrix : Matrix d) : (matrixBits matrix).length = d * d := by
  rw [matrixBits, length_flatMap_const _ _ d (fun _ => List.length_ofFn), List.length_ofFn]

theorem ofFn_injective {α : Type} {f g : Fin n → α} (h : List.ofFn f = List.ofFn g) :
    f = g := by
  funext i
  have e := congrArg (fun (xs : List α) => xs[i.val]?) h
  simpa [i.isLt] using e

theorem rowsBits_injective {xs ys : List (Bits n)} (hlen : xs.length = ys.length)
    (h : xs.flatMap (fun x => List.ofFn x) = ys.flatMap (fun y => List.ofFn y)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => exact (List.eq_nil_iff_length_eq_zero.mpr hlen.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.flatMap_cons] at h
      have ⟨he, ht⟩ := List.append_inj h
        (by simp : (List.ofFn x).length = (List.ofFn y).length)
      rw [ofFn_injective he, ih (by simpa using hlen) ht]

theorem witnessBits_injective {u v : Witness m r} (h : witnessBits u = witnessBits v) :
    u = v :=
  Subtype.ext (rowsBits_injective (u.property.trans v.property.symm) h)

theorem matrixBits_injective {M N : Matrix d} (h : matrixBits M = matrixBits N) : M = N :=
  ofFn_injective (rowsBits_injective (by simp) h)

/-- Largest rank marked feasible, returning zero if the table has no yes bit.
For a correct table, rank zero is always feasible. -/
def best : (d : Nat) → (Fin (d + 1) → Bool) → Fin (d + 1)
  | 0, _ => 0
  | d + 1, answers =>
    if answers (Fin.last (d + 1)) then Fin.last (d + 1)
    else (best d (fun r => answers r.castSucc)).castSucc

theorem best_correct (d : Nat) (answers : Fin (d + 1) → Bool) (h0 : answers 0 = true) :
    answers (best d answers) = true ∧ ∀ r, answers r = true → r ≤ best d answers := by
  induction d with
  | zero =>
    exact ⟨h0, fun r _ => Fin.le_last r⟩
  | succ d ih =>
    cases h : answers (Fin.last (d + 1))
    · have hr := ih (fun r => answers r.castSucc) (by simpa using h0)
      simp only [best, h, Bool.false_eq_true, if_false]
      refine ⟨hr.1, fun r hy => ?_⟩
      refine Fin.lastCases (motive := fun r => answers r = true →
        r ≤ (best d (fun r => answers r.castSucc)).castSucc) ?_ ?_ r hy
      · intro he
        rw [h] at he
        contradiction
      · intro r hy
        exact hr.2 r hy
    · simp only [best, h, if_true, true_and]
      exact fun r _ => Fin.le_last r

def rankAnswers (answers : Query d → Bool) (r : Fin (d + 1)) : Bool :=
  answers (.rank r)

/-- Decode a table of answers without any further oracle access. -/
def recover (answers : Query d → Bool) : Matrix d :=
  let r := best d (rankAnswers answers)
  fun i j => answers (.bit r i j)

theorem valid_lifted_basis {S : Bits m → Prop} {r : Fin (m + 2)}
    {w : Witness m r.val} (hw : Valid S w)
    (maximal : ∀ (k : Fin (m + 2)) (u : Witness m k.val), Valid S u → k ≤ r) :
    ∀ v, ListSpan (w.val.map lift) v ↔ Span (Lifted S) v := by
  intro v
  constructor
  · apply Span.mono
    intro u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    exact Span.gen ⟨x, hw.1 x hx, rfl⟩
  · apply Span.mono
    rintro u ⟨x, hx, rfl⟩
    apply Classical.byContradiction
    intro hout
    have hlt := rank_strict_of_outside hout
    obtain ⟨hwidth, hlen⟩ := rank_bounds (lift x :: w.val.map lift)
    have newRank : rank (lift x :: w.val.map lift) = r.val + 1 := by
      rw [hw.2] at hlt
      simp only [List.length_cons, List.length_map, w.property] at hlen
      exact Nat.le_antisymm hlen hlt
    let k : Fin (m + 2) := ⟨r.val + 1, by omega⟩
    let next : Witness m k.val := ⟨x :: w.val, by simp [k, w.property]⟩
    have hn : Valid S next := by
      refine ⟨?_, newRank⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hw.1 y hy
    have hle : k.val ≤ r.val := maximal k next hn
    exact Nat.not_succ_le_self _ hle

def CorrectAnswers (S : Bits m → Prop) (answers : Query (m + 1) → Bool) : Prop :=
  ∀ q, answers q = true ↔ Yes S q

theorem rank_zero_feasible (S : Bits m → Prop) :
    Yes S (.rank 0) := by
  have h := (rank_bounds (n := m + 1) []).2
  have e : rank ([] : List (Bits (m + 1))) = 0 := by simpa using h
  exact ⟨⟨[], rfl⟩, ⟨by simp, e⟩, rfl⟩

/-- The decoded matrix is exactly the encoding of any tuple of maximum
feasible rank. Every such tuple spans every lifted solution. -/
theorem recover_basis {S : Bits m → Prop} {answers : Query (m + 1) → Bool}
    (h : CorrectAnswers S answers) :
    let r := best (m + 1) (rankAnswers answers)
    ∃ w : Witness m r.val, Valid S w ∧
      (∀ v, ListSpan (w.val.map lift) v ↔ Span (Lifted S) v) ∧
      recover answers = encode (w.val.map lift) := by
  dsimp only
  generalize er : best (m + 1) (rankAnswers answers) = r
  have hb := best_correct (m + 1) (rankAnswers answers) ((h _).mpr (rank_zero_feasible S))
  rw [er] at hb
  obtain ⟨w, hw, _⟩ := (h (.rank r)).mp hb.1
  have hm (k : Fin (m + 2)) (u : Witness m k.val) (hu : Valid S u) : k ≤ r :=
    hb.2 k ((h (.rank k)).mpr ⟨u, hu, rfl⟩)
  have hs := valid_lifted_basis hw hm
  refine ⟨w, hw, hs, ?_⟩
  funext i j
  simp only [recover, er]
  suffices eq : answers (.bit r i j) = true ↔ encode (w.val.map lift) i j = true by
    cases h₁ : answers (.bit r i j) <;> cases h₂ : encode (w.val.map lift) i j <;> simp_all
  rw [h]
  constructor
  · rintro ⟨u, hu, he⟩
    have ht := valid_lifted_basis hu hm
    have eq := encode_congr (fun v => (ht v).trans (hs v).symm)
    change encode (u.val.map lift) i j = true at he
    rwa [eq] at he
  · intro e
    exact ⟨w, hw, e⟩

theorem recover_correct {S : Bits m → Prop} {answers : Query (m + 1) → Bool}
    (h : CorrectAnswers S answers) (x : Bits m) :
    Decode (recover answers) x ↔ AffineHull S x := by
  obtain ⟨w, _, hs, he⟩ := recover_basis h
  unfold Decode
  rw [he, decode_span, hs, affineHull_iff_lifted_span]

/-- A finite batch transcript carries the question beside each returned bit.
Lookup is local computation on the transcript. -/
def readAnswer [DecidableEq Q] : List (Q × Bool) → Q → Bool
  | [], _ => false
  | (q, b) :: rest, p => if q = p then b else readAnswer rest p

theorem readAnswer_map [DecidableEq Q] (f : Q → Bool) (qs : List Q) (q : Q) (hq : q ∈ qs) :
    readAnswer (qs.map fun p => (p, f p)) q = f q := by
  induction qs with
  | nil => simp at hq
  | cons p ps ih =>
    by_cases e : p = q
    · simp [readAnswer, e]
    · rw [List.map_cons, readAnswer, if_neg e]
      exact ih ((List.mem_cons.mp hq).resolve_left (Ne.symm e))

def recoverBatch (transcript : List (Query d × Bool)) : Matrix d :=
  recover (readAnswer transcript)

/-- End-to-end recovery from one list of nonadaptive answers, for every
dimension and every solution predicate. -/
theorem recoverBatch_correct (S : Bits m → Prop) (oracle : Query (m + 1) → Bool)
    (h : CorrectAnswers S oracle) (x : Bits m) :
    Decode (recoverBatch ((batch (m + 1)).map fun q => (q, oracle q))) x ↔
      AffineHull S x := by
  apply recover_correct
  intro q
  rw [readAnswer_map oracle _ _ (mem_batch q)]
  exact h q


/-- The specification is realizable for arbitrary predicates as a classical
oracle. When membership in S is decidable, verifyPacked checks its certificates. -/
noncomputable def existentialOracle (S : Bits m → Prop) (q : Query (m + 1)) : Bool :=
  @decide (Yes S q) (Classical.propDecidable _)

theorem existentialOracle_correct (S : Bits m → Prop) :
    CorrectAnswers S (existentialOracle S) := by
  intro q
  simp [existentialOracle]

noncomputable def parallelRecover (S : Bits m → Prop) : Matrix (m + 1) :=
  recoverBatch ((batch (m + 1)).map fun q => (q, existentialOracle S q))

theorem parallelRecover_correct (S : Bits m → Prop) (x : Bits m) :
    Decode (parallelRecover S) x ↔ AffineHull S x :=
  recoverBatch_correct S (existentialOracle S) (existentialOracle_correct S) x

theorem parallelRecover_canonical {S T : Bits m → Prop}
    (h : ∀ v, Span (Lifted S) v ↔ Span (Lifted T) v) :
    parallelRecover S = parallelRecover T := by
  have fromOracle (P : Bits m → Prop) :
      parallelRecover P = recover (existentialOracle P) := by
    unfold parallelRecover recoverBatch
    have e : readAnswer ((batch (m + 1)).map fun q => (q, existentialOracle P q)) =
        existentialOracle P := funext fun q => readAnswer_map _ _ q (mem_batch q)
    rw [e]
  rw [fromOracle, fromOracle]
  obtain ⟨w, _, hw, ew⟩ := recover_basis (existentialOracle_correct S)
  obtain ⟨u, _, hu, eu⟩ := recover_basis (existentialOracle_correct T)
  rw [ew, eu]
  exact encode_congr (fun v => (hw v).trans ((h v).trans (hu v).symm))

theorem lifted_span_of_same_hull {S T : Bits m → Prop}
    (h : ∀ x, AffineHull S x → AffineHull T x) :
    ∀ v, Span (Lifted S) v → Span (Lifted T) v := by
  intro v hv
  apply Span.mono _ hv
  rintro _ ⟨x, hx, rfl⟩
  exact (affineHull_iff_lifted_span T x).mp (h x (affineHull_gen hx))

/-- Equality of canonical output matrices is exactly equality of affine hulls. -/
theorem parallelRecover_eq_iff {S T : Bits m → Prop} :
    parallelRecover S = parallelRecover T ↔ ∀ x, AffineHull S x ↔ AffineHull T x := by
  constructor
  · intro h x
    rw [← parallelRecover_correct S x, ← parallelRecover_correct T x, h]
  · intro h
    apply parallelRecover_canonical
    intro v
    exact ⟨lifted_span_of_same_hull (fun x => (h x).mp) v,
      lifted_span_of_same_hull (fun x => (h x).mpr) v⟩

theorem recover_empty {S : Bits m → Prop} (h : ∀ x, ¬ S x) (x : Bits m) :
    ¬ Decode (parallelRecover S) x := by
  intro hx
  obtain ⟨pts, hp, odd, _⟩ := (parallelRecover_correct S x).mp hx
  cases pts with
  | nil => simp at odd
  | cons y ys => exact h y (hp y (by simp))

theorem recover_singleton (a x : Bits m) :
    Decode (parallelRecover (fun y => y = a)) x ↔ x = a := by
  rw [parallelRecover_correct]
  constructor
  · exact affineHull_minimal (T := fun y => y = a) (fun _ h => h)
      (fun _ _ _ hx hy hz => by simp [hx, hy, hz])
  · exact affineHull_gen (S := fun y => y = a)

end HullRecovery
