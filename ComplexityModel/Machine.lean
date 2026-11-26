module

public import Std

/-!
Uniform complexity over finite binary words. Programs are finite syntax. Word
instructions can inspect a head or emptiness, remove a head, prepend a single
bit, or copy a word. Register addresses are constants in the program.

For a fixed program, only finitely many registers need physical storage.
The state function is a mathematical representation of that register file.
The number and length of queued words and pending call frames grow by at most
one per transition, as checked in ComplexityModel.Workspace. Consequently a
bit-level simulation may copy words and scan the whole workspace on each
instruction and still incur only polynomial overhead. Conversely, a tape
can be stored as two word registers holding fixed-width symbol codes on
either side of the head. Finite control can dispatch on fixed-width codes
in a loop. These tape simulation arguments explain the cost model. The
formal results here concern the register machine itself.
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

theorem Poly.mono (p : Poly) {m n : Nat} (h : m ≤ n) : p.at m ≤ p.at n :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

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

def State.Fits (s : State) (n : Nat) : Prop :=
  (∀ i, (s.reg i).length ≤ n) ∧ ∀ w ∈ s.queries, w.length ≤ n

theorem State.Fits.mono {s : State} {m n : Nat} (h : s.Fits m) (hle : m ≤ n) :
    s.Fits n :=
  ⟨fun i => Nat.le_trans (h.1 i) hle, fun w hw => Nat.le_trans (h.2 w hw) hle⟩

theorem State.input_fits {x w : Word} {n : Nat} (hx : x.length ≤ n) (hw : w.length ≤ n) :
    (State.input x w).Fits n := by
  constructor
  · intro i
    simp only [State.input]
    split
    · exact hx
    · split
      · exact hw
      · exact Nat.zero_le _
  · simp [State.input]

theorem State.write_fits {s : State} {n : Nat} (h : s.Fits n) (hw : w.length ≤ n) :
    (s.write r w).Fits n := by
  refine ⟨?_, h.2⟩
  intro i
  simp only [State.write]
  split
  · exact hw
  · exact h.1 i

theorem State.drop_fits {s : State} {n : Nat} (h : s.Fits n) : s.drop.Fits n :=
  ⟨h.1, fun _ hw => h.2 _ (List.mem_of_mem_tail hw)⟩

theorem State.push_fits {s : State} {n : Nat} (h : s.Fits n) : (s.push r).Fits n := by
  refine ⟨h.1, ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact h.1 r
  · exact h.2 w hw

theorem Expr.eval_fits {s : State} {n : Nat} (e : Expr) (h : s.Fits n) :
    (e.eval s).length ≤ n + 1 := by
  cases e with
  | empty => simp [Expr.eval]
  | copy r => exact Nat.le_succ_of_le (h.1 r)
  | tail r => exact by simpa [Expr.eval] using (show (s.reg r).length - 1 ≤ n + 1 by have := h.1 r; omega)
  | cons b r => exact Nat.succ_le_succ (h.1 r)

theorem Source.advance_fits (src : Source) {s : State} (h : s.Fits n) :
    (src.advance s).Fits n := by
  cases src
  · exact h
  · exact State.drop_fits h

theorem Source.read_fits {src : Source} {s : State}
    (h : s.Fits n) (hr : src.read s = some w) : w.length ≤ n := by
  cases src with
  | reg r =>
    have e : s.reg r = w := Option.some.inj hr
    exact e ▸ h.1 r
  | queued =>
    cases hs : s.queries with
    | nil => simp [Source.read, hs] at hr
    | cons a rest =>
      have e : a = w := Option.some.inj (by simpa only [Source.read, hs, List.head?_cons] using hr)
      exact h.2 w (by simp [hs, e])

theorem State.head_fits {s : State} (h : s.Fits n) : (s.queries.headD []).length ≤ n := by
  cases hs : s.queries with
  | nil => simp [hs]
  | cons a rest =>
    simp only [hs, List.headD_cons]
    exact h.2 a (by simp [hs])

/-- The word length can grow by at most one per instruction. -/
theorem Run.fits (h : Run A c s u t q) (hs : s.Fits n) : u.Fits (n + t) := by
  induction h generalizing n with
  | skip => exact hs.mono (by omega)
  | write => exact State.write_fits (hs.mono (by omega)) (Expr.eval_fits _ hs)
  | push => exact (State.push_fits hs).mono (by omega)
  | pop => exact (State.write_fits (State.drop_fits hs) (State.head_fits hs)).mono (by omega)
  | seq _ _ ih₁ ih₂ => exact (ih₂ (ih₁ hs)).mono (by omega)
  | branch _ _ ih => exact (ih hs).mono (by omega)
  | loopFalse => exact hs.mono (by omega)
  | loopTrue _ _ _ ih₁ ih₂ => exact (ih₂ (ih₁ hs)).mono (by omega)
  | askEmpty | askSome | callEmpty | callSome =>
    exact State.write_fits ((Source.advance_fits _ hs).mono (by omega)) (by simp <;> omega)

theorem Run.queries_le_time (h : Run A c s u t q) : q ≤ t := by
  induction h <;> omega

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
