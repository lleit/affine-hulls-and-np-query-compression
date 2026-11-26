module

public import Std

/-!
Two proof obligations from the affine-hull SAT argument, in Lean 4.19.
The first uses the description of an affine hull by its valid parity
equations. The second verifies the integer-count conditional-expectation
algorithm, parametrized by the implementation of its prefix counts.
-/

@[expose] public section

namespace AffinePruning

variable {X : Type} (parity : X → X → Bool)

/-- Intersection of every parity hyperplane that contains the witnesses.
For binary vectors, instantiate parity with the mod-two dot product. -/
def hull (S : X → Prop) (x : X) : Prop :=
  ∀ z b, (∀ y, S y → parity z y = b) → parity z x = b

theorem witness_mem {S : X → Prop} {x : X} (hx : S x) : hull parity S x :=
  fun _ _ eqn => eqn x hx

theorem attained_on_witness {S : X → Prop} {x z : X} {b : Bool}
    (hx : hull parity S x) (hb : parity z x = b) :
    ∃ y, S y ∧ parity z y = b := by
  apply Classical.byContradiction
  intro h
  have hc : ∀ y, S y → parity z y = !b := by
    intro y hy
    have hn : parity z y ≠ b := fun he => h ⟨y, hy, he⟩
    cases hval : parity z y <;> cases b <;> simp_all
  have he := hx z (!b) hc
  cases b <;> simp_all

/-- Either chosen side contains a real witness. Its new hull lies in the
old hull, and the other side supplies a point proving strict inclusion. -/
theorem prune {S : X → Prop} {z : X} (b : Bool)
    (both : ∀ v : Bool, ∃ x, hull parity S x ∧ parity z x = v) :
    let T := fun x => S x ∧ parity z x = b
    (∃ x, T x) ∧
    (∀ x, hull parity T x → hull parity S x) ∧
    (∃ x, hull parity S x ∧ ¬ hull parity T x) := by
  dsimp only
  obtain ⟨x, hx, he⟩ := both b
  obtain ⟨y, hy, hf⟩ := both (!b)
  refine ⟨attained_on_witness parity hx he, ?_, y, hy, ?_⟩
  · intro u hu t c h
    exact hu t c (fun v hv => h v hv.1)
  · intro hh
    have hg := hh z b (fun _ hv => hv.2)
    cases b <;> simp_all

/-- Prefixes are stored in reverse order. The cost sums violations with
multiplicity over all masks completing a prefix. -/
def greedy (cost : List Bool → Nat) : Nat → List Bool → List Bool
  | 0, p => p
  | n + 1, p =>
    let q := if cost (false :: p) ≤ cost (true :: p) then false :: p else true :: p
    greedy cost n q

theorem greedy_zero (cost : List Bool → Nat) (n : Nat) (p : List Bool)
    (additive : ∀ q, q.length < p.length + n →
      cost q = cost (false :: q) + cost (true :: q))
    (start : cost p < 2^n) :
    cost (greedy cost n p) = 0 ∧ (greedy cost n p).length = p.length + n := by
  induction n generalizing p with
  | zero => simp_all [greedy]
  | succ n ih =>
    have hp := additive p (by omega)
    rw [Nat.pow_succ] at start
    simp only [greedy]
    have step (b : Bool) (small : cost (b :: p) < 2^n) :
        cost (greedy cost n (b :: p)) = 0 ∧
        (greedy cost n (b :: p)).length = p.length + (n + 1) := by
      have ha : ∀ q : List Bool, q.length < (b :: p).length + n →
          cost q = cost (false :: q) + cost (true :: q) := by
        intro q hq
        apply additive
        simp only [List.length_cons] at hq
        omega
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b :: p) ha small
    split <;> apply step <;> omega

end AffinePruning
