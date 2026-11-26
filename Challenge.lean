module

public import Init

/-!
# Affine hulls and NP query compression

A polynomial-time function of binary strings may produce its entire batch of
queries to a fixed NP language before receiving any answer, or it may query a
fixed NP language adaptively using at most logarithmically many queries. The
first theorem says that inclusion of the batch class in the adaptive class
implies that every NP language is in P. The second gives the equivalence with
equality of the two function classes.

The statement uses the finite register-machine model below. A register holds
a binary word. The program uses a fixed set of addresses, reads or changes
one end of a word, and may copy a word. A finite stack holds queued requests.
A run records both the transition count and the number of actual queries.
The register and tape model correspondence is explained in the README.
-/

@[expose] public section

namespace ComplexityModel

abbrev Word := List Bool
abbrev Language := Word → Prop
abbrev WordFunction := Word → Word

def emptyLanguage : Language := fun _ => False

/-- Shifted monomials dominate ordinary nonnegative polynomial bounds. -/
structure Poly where
  coefficient : Nat
  degree : Nat

def Poly.at (p : Poly) (n : Nat) : Nat := p.coefficient * (n + 1) ^ p.degree

structure State where
  reg : Nat → Word
  queries : List Word

def State.write (s : State) (r : Nat) (w : Word) : State :=
  { s with reg := fun i => if i = r then w else s.reg i }

def State.input (x : Word) (witness : Word := []) : State :=
  ⟨fun i => if i = 0 then x else if i = 1 then witness else [], []⟩

def State.output (s : State) : Word := s.reg 0

def State.push (s : State) (r : Nat) : State :=
  { s with queries := s.reg r :: s.queries }

def State.drop (s : State) : State :=
  { s with queries := s.queries.tail }

inductive Expr
  | empty
  | copy (reg : Nat)
  | tail (reg : Nat)
  | cons (bit : Bool) (reg : Nat)

def Expr.eval (s : State) : Expr → Word
  | .empty => []
  | .copy r => s.reg r
  | .tail r => (s.reg r).tail
  | .cons b r => b :: s.reg r

inductive Test
  | empty (reg : Nat)
  | head (reg : Nat)

def Test.eval (s : State) : Test → Bool
  | .empty r => (s.reg r).isEmpty
  | .head r => (s.reg r).headD false

inductive Source
  | reg (address : Nat)
  | queued

def Source.read (s : State) : Source → Option Word
  | .reg r => some (s.reg r)
  | .queued => s.queries.head?

def Source.advance (s : State) : Source → State
  | .reg _ => s
  | .queued => s.drop

inductive Code
  | skip
  | write (dest : Nat) (expr : Expr)
  | push (reg : Nat)
  | pop (dest : Nat)
  | seq (first second : Code)
  | branch (test : Test) (yes no : Code)
  | loop (test : Test) (body : Code)
  | ask (src : Source) (dest : Nat)
  | callBit (src : Source) (dest : Nat) (body : Code)

/-- Permissions for pushing, querying a register, and asking for a queued
answer. A queued answer consumes the corresponding submitted word. -/
def Code.allowed (push direct queued : Bool) : Code → Prop
  | .push _ => push = true
  | .ask (.reg _) _ => direct = true
  | .ask .queued _ => queued = true
  | .seq a b | .branch _ a b => a.allowed push direct queued ∧ b.allowed push direct queued
  | .loop _ body | .callBit _ _ body => body.allowed push direct queued
  | _ => True

abbrev Code.pure (c : Code) : Prop := c.allowed true false false
abbrev Code.consumer (c : Code) : Prop := c.allowed false false true

/-- A scoped call runs its fixed body on the source word in a fresh state.
It returns a singleton bit testing whether the body's output was exactly
the singleton true word. Runtime includes all instructions of the call.
The last index counts actual oracle queries. -/
inductive Run (A : Language) : Code → State → State → Nat → Nat → Prop
  | skip : Run A .skip s s 1 0
  | write : Run A (.write d e) s (s.write d (e.eval s)) 1 0
  | push : Run A (.push r) s (s.push r) 1 0
  | pop : Run A (.pop d) s (s.drop.write d (s.queries.headD [])) 1 0
  | seq : Run A a s u t₁ q₁ → Run A b u v t₂ q₂ →
      Run A (.seq a b) s v (t₁ + t₂ + 1) (q₁ + q₂)
  | branch : test.eval s = bit →
      Run A (if bit then yes else no) s u t q →
      Run A (.branch test yes no) s u (t + 1) q
  | loopFalse : test.eval s = false → Run A (.loop test body) s s 1 0
  | loopTrue : test.eval s = true →
      Run A body s u t₁ q₁ → Run A (.loop test body) u v t₂ q₂ →
      Run A (.loop test body) s v (t₁ + t₂ + 1) (q₁ + q₂)
  | askEmpty : src.read s = none →
      Run A (.ask src d) s ((src.advance s).write d [false]) 1 0
  | askSome : src.read s = some w → (bit = true ↔ A w) →
      Run A (.ask src d) s ((src.advance s).write d [bit]) 1 1
  | callEmpty : src.read s = none →
      Run A (.callBit src d body) s ((src.advance s).write d [false]) 1 0
  | callSome : src.read s = some w → Run A body (State.input w) u t q →
      Run A (.callBit src d body) s
        ((src.advance s).write d [decide (u.output = [true])]) (t + 1) q

/-- A deterministic polynomial-time word function. -/
def FP (f : WordFunction) : Prop :=
  ∃ c : Code, ∃ p : Poly, c.pure ∧
    ∀ x, ∃ s t, Run emptyLanguage c (State.input x) s t 0 ∧ t ≤ p.at x.length ∧ s.output = f x

def P (A : Language) : Prop :=
  ∃ f, FP f ∧ ∀ x, f x = [true] ↔ A x

/-- A deterministic verifier receives the witness in register one. Runtime is
bounded on all input and witness pairs by their total length. -/
def NP (A : Language) : Prop :=
  ∃ c : Code, ∃ witnessBound timeBound : Poly, c.pure ∧
    (∀ x w, ∃ s t, Run emptyLanguage c (State.input x w) s t 0 ∧
      t ≤ timeBound.at (x.length + w.length)) ∧
    ∀ x, A x ↔ ∃ w : Word, w.length ≤ witnessBound.at x.length ∧
      ∃ s t, Run emptyLanguage c (State.input x w) s t 0 ∧ s.output = [true]

/-- The first program computes the batch. The second may read submitted
answers and discard queries. It cannot submit new queries or query registers.
Requests are stored as a stack, giving a fixed order for reading the batch. -/
def FPParallelNP (f : WordFunction) : Prop :=
  ∃ A : Language, NP A ∧ ∃ producer consumer : Code, ∃ p : Poly,
    producer.pure ∧ consumer.consumer ∧
    ∀ x, ∃ mid out t₁ t₂ q,
      Run emptyLanguage producer (State.input x) mid t₁ 0 ∧
      Run A consumer mid out t₂ q ∧ t₁ + t₂ ≤ p.at x.length ∧ out.output = f x

/-- Adaptive NP queries with a polynomial runtime bound and an integer
logarithmic query cap, including a constant allowance for short inputs. -/
def FPLogNP (f : WordFunction) : Prop :=
  ∃ A : Language, NP A ∧ ∃ c : Code, ∃ p : Poly, ∃ k b : Nat,
    ∀ x, ∃ s t q, Run A c (State.input x) s t q ∧
      t ≤ p.at x.length ∧ q ≤ (x.length + 2).log2 * k + b ∧ s.output = f x

def ClassEquality : Prop := ∀ f, FPParallelNP f ↔ FPLogNP f

def PEqualsNP : Prop := ∀ A, P A ↔ NP A

end ComplexityModel

namespace ComplexityImplication

open ComplexityModel

/-- Compression from a parallel batch to logarithmically many adaptive
NP queries implies that every NP language is decidable in polynomial time. -/
theorem pEqualsNP_of_parallel_le_log
    (compress : ∀ f, FPParallelNP f → FPLogNP f) : PEqualsNP := by
  sorry

/-- The two polynomial-time NP oracle function classes coincide exactly
when P and NP coincide. -/
theorem classEquality_iff_pEqualsNP : ClassEquality ↔ PEqualsNP := by
  sorry

end ComplexityImplication
