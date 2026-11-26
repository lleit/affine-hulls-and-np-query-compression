module

public import ComplexityModel.FieldCode

@[expose] public section

namespace HullBatchMachine
open ComplexityModel

infixr:60 " ⨟ " => Code.seq

@[simp] theorem write_same (s : State) (r : Nat) (w : Word) :
    (s.write r w).reg r = w := by simp [State.write]

@[simp] theorem write_ne (s : State) (w : Word) {r i : Nat} (h : i ≠ r) :
    (s.write r w).reg i = s.reg i := by simp [State.write, h]

@[simp] theorem write_queue (s : State) (r : Nat) (w : Word) :
    (s.write r w).queries = s.queries := rfl

theorem extState {s t : State} (hr : ∀ i, s.reg i = t.reg i)
    (hq : s.queries = t.queries) : s = t := by
  cases s
  cases t
  cases funext hr
  cases hq
  rfl

theorem stepWrite (s : State) (r : Nat) (e : Expr) :
    Run emptyLanguage (.write r e) s (s.write r (e.eval s)) 1 0 := .write

def set (r : Nat) (b : Bool) : Code := .write r .empty ⨟ .write r (.cons b r)

theorem runSet (s : State) (r : Nat) (b : Bool) :
    Run emptyLanguage (set r b) s (s.write r [b]) 3 0 := by
  let u := s.write r []
  have eq : u.write r [b] = s.write r [b] := by
    refine extState ?_ rfl
    intro i
    by_cases hi : i = r <;> simp [u, hi]
  rw [← eq]
  have first : Run emptyLanguage (.write r .empty) s u 1 0 := .write
  have second : Run emptyLanguage (.write r (.cons b r)) u (u.write r [b]) 1 0 := by
    simpa [Expr.eval, u] using stepWrite u r (.cons b r)
  exact .seq first second

theorem runTrue {s t : State} {test : Test} {a b : Code} {c : Nat}
    (h : test.eval s = true) (r : Run emptyLanguage a s t c 0) :
    Run emptyLanguage (.branch test a b) s t (c + 1) 0 := .branch h r

theorem runFalse {s t : State} {test : Test} {a b : Code} {c : Nat}
    (h : test.eval s = false) (r : Run emptyLanguage b s t c 0) :
    Run emptyLanguage (.branch test a b) s t (c + 1) 0 := .branch h r

def ones (n : Nat) : Word := List.replicate n true

@[simp] theorem ones_zero : ones 0 = [] := rfl

@[simp] theorem ones_succ (n : Nat) : ones (n + 1) = true :: ones n :=
  List.replicate_succ

@[simp] theorem ones_length (n : Nat) : (ones n).length = n := List.length_replicate

/-- A counted loop. The body can inspect the counter and the loop itself debits
one tick after the body. -/
def forUnary (ctr : Nat) (body : Code) : Code :=
  .loop (.head ctr) (body ⨟ .write ctr (.tail ctr))

theorem forUnary_run {ctr : Nat} {body : Code} {bound : Nat}
    (I : Nat → State → Prop)
    (step : ∀ n s, s.reg ctr = ones (n + 1) → I (n + 1) s →
      ∃ u t, Run emptyLanguage body s u t 0 ∧ t ≤ bound ∧ u.reg ctr = ones (n + 1) ∧
        I n (u.write ctr (ones n)))
    (n : Nat) (s : State) (clock : s.reg ctr = ones n) (start : I n s) :
    ∃ out t, Run emptyLanguage (forUnary ctr body) s out t 0 ∧
      t ≤ (bound + 3) * n + 1 ∧ out.reg ctr = [] ∧ I 0 out := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, 1, .loopFalse (by simp [Test.eval, clock]), by simp, by simpa using clock, start⟩
  | succ n ih =>
    obtain ⟨u, t₁, bodyRun, cost₁, hctr, bodyInv⟩ := step n s clock start
    let v := u.write ctr (ones n)
    have debit : Run emptyLanguage (.write ctr (.tail ctr)) u v 1 0 := by
      simpa [v, Expr.eval, hctr] using stepWrite u ctr (.tail ctr)
    obtain ⟨out, t₂, loopRun, cost₂, hfin, hInv⟩ := ih v (by simp [v]) bodyInv
    refine ⟨out, t₁ + 1 + 1 + t₂ + 1, .loopTrue (by simp [Test.eval, clock])
      (.seq bodyRun debit) loopRun, ?_, hfin, hInv⟩
    rw [Nat.mul_succ]
    omega

/-- Scan bits from an arbitrary word. The body is responsible for advancing
the source, while the outer loop handles the end-of-word check. -/
def scanCore (src flag : Nat) (body : Code) : Code :=
  .loop (.head flag) (.branch (.empty src) (.write flag .empty) body)

theorem scanCore_run {src flag : Nat} {body : Code} {bound : Nat}
    (I : Word → State → Prop)
    (done : ∀ s, I [] s → I [] (s.write flag []))
    (step : ∀ b bs s, s.reg src = b :: bs → s.reg flag = [true] → I (b :: bs) s →
      ∃ u t, Run emptyLanguage body s u t 0 ∧ t ≤ bound ∧ u.reg src = bs ∧
        u.reg flag = [true] ∧ I bs u)
    (input : Word) (s : State) (word : s.reg src = input) (on : s.reg flag = [true])
    (start : I input s) :
    ∃ out t, Run emptyLanguage (scanCore src flag body) s out t 0 ∧
      t ≤ (bound + 2) * input.length + 4 ∧ I [] out := by
  induction input generalizing s with
  | nil =>
    let v := s.write flag []
    have clear : Run emptyLanguage (.write flag .empty) s v 1 0 := .write
    have branch := runTrue (test := .empty src) (b := body) (by simp [Test.eval, word]) clear
    have stop : Run emptyLanguage (scanCore src flag body) v v 1 0 :=
      .loopFalse (by simp [v, Test.eval])
    exact ⟨v, 4, .loopTrue (by simp [Test.eval, on]) branch stop, by simp, done s start⟩
  | cons b bs ih =>
    obtain ⟨u, t₁, bodyRun, cost₁, hu, hon, hI⟩ := step b bs s word on start
    obtain ⟨out, t₂, loopRun, cost₂, result⟩ := ih u hu hon hI
    have branch := runFalse (test := .empty src) (a := .write flag .empty)
      (by simp [Test.eval, word]) bodyRun
    refine ⟨out, t₁ + 1 + t₂ + 1, .loopTrue (by simp [Test.eval, on]) branch loopRun, ?_, result⟩
    rw [List.length_cons, Nat.mul_succ]
    omega

/-- Scan a word into a unary counter, accumulating on the destination. -/
def normalize (src dst flag : Nat) : Code :=
  set flag true ⨟
    scanCore src flag (.write dst (.cons true dst) ⨟ .write src (.tail src))

theorem normalize_run {src dst flag : Nat} (hd : dst ≠ src) (hf : flag ≠ src)
    (hfd : flag ≠ dst) (s : State) :
    ∃ u t, Run emptyLanguage (normalize src dst flag) s u t 0 ∧
      t ≤ 5 * (s.reg src).length + 8 ∧
      u.reg dst = ones (s.reg src).length ++ s.reg dst ∧ u.queries = s.queries ∧
        ∀ r, r ≠ src → r ≠ dst → r ≠ flag → u.reg r = s.reg r := by
  let start := s.write flag [true]
  let I (rem : Word) (state : State) :=
    state.reg dst = ones ((s.reg src).length - rem.length) ++ s.reg dst ∧
    rem.length ≤ (s.reg src).length ∧ state.queries = s.queries ∧
    ∀ r, r ≠ src → r ≠ dst → r ≠ flag → state.reg r = s.reg r
  have done : ∀ u, I [] u → I [] (u.write flag []) := by
    intro u hu
    obtain ⟨a,b,c,d⟩ := hu
    refine ⟨by simpa [Ne.symm hfd] using a, b, c, ?_⟩
    intro r hr₁ hr₂ hr₃
    simpa [hr₃] using d r hr₁ hr₂ hr₃
  have step : ∀ b bs u, u.reg src = b :: bs → u.reg flag = [true] → I (b :: bs) u →
      ∃ v t, Run emptyLanguage (.write dst (.cons true dst) ⨟ .write src (.tail src)) u v t 0 ∧
        t ≤ 3 ∧ v.reg src = bs ∧ v.reg flag = [true] ∧ I bs v := by
    intro b bs u hw hon hI
    let v := u.write dst (true :: u.reg dst)
    let w := v.write src bs
    have pop : Run emptyLanguage (.write src (.tail src)) v w 1 0 := by
      simpa [v, w, Expr.eval, Ne.symm hd, hw] using stepWrite v src (.tail src)
    have push : Run emptyLanguage (.write dst (.cons true dst)) u v 1 0 := .write
    refine ⟨w, 3, .seq push pop, by decide, by simp [w],
      by simp [w, v, hf, hfd, hon], ?_⟩
    obtain ⟨a, hlen, q, other⟩ := hI
    have e : (s.reg src).length - bs.length = (s.reg src).length - (b :: bs).length + 1 := by
      simp only [List.length_cons] at hlen ⊢
      omega
    refine ⟨by simp [w, v, hd, a, e], by simp only [List.length_cons] at hlen; omega, q, ?_⟩
    intro r hr₁ hr₂ hr₃
    simpa [w, v, hr₁, hr₂] using other r hr₁ hr₂ hr₃
  have initial : I (s.reg src) start := by
    refine ⟨by simp [start, Ne.symm hfd], Nat.le_refl _, rfl, ?_⟩
    intro r _ _ h
    simp [start, h]
  obtain ⟨u, t, scan, cost, output, _, q, other⟩ := scanCore_run I done step (s.reg src)
    start (by simp [start, Ne.symm hf]) (by simp [start]) initial
  exact ⟨u, 3 + t + 1, .seq (runSet s flag true) scan, by omega,
    by simpa using output, q, other⟩

end HullBatchMachine
