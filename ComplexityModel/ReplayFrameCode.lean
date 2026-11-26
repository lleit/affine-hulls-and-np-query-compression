module

public import MachineEnumeration
public import ComplexityModel.WordCode

/-! Shift the top-level registers of a replay program away from the tape
iterator. The queue is shared, so the wrapper drains it with a unary counter
whose adequacy follows from the machine's transition bound. -/

@[expose] public section

namespace ComplexityModel.ReplayFrameCode

local infixr:60 " ▷ " => Code.seq

private def offsetExpr (base : Nat) : Expr → Expr
  | .empty => .empty
  | .copy r => .copy (base + r)
  | .tail r => .tail (base + r)
  | .cons b r => .cons b (base + r)

private def offsetTest (base : Nat) : Test → Test
  | .empty r => .empty (base + r)
  | .head r => .head (base + r)

private def offsetSource (base : Nat) : Source → Source
  | .reg r => .reg (base + r)
  | .queued => .queued

def shift (base : Nat) : Code → Code
  | .skip => .skip
  | .write d e => .write (base + d) (offsetExpr base e)
  | .push r => .push (base + r)
  | .pop d => .pop (base + d)
  | .seq a b => .seq (shift base a) (shift base b)
  | .branch t a b => .branch (offsetTest base t) (shift base a) (shift base b)
  | .loop t body => .loop (offsetTest base t) (shift base body)
  | .ask src d => .ask (offsetSource base src) (base + d)
  | .callBit src d body => .callBit (offsetSource base src) (base + d) body

theorem shift_allowed (base : Nat) (code : Code) (push direct queued : Bool) :
    (shift base code).allowed push direct queued ↔ code.allowed push direct queued := by
  induction code <;> simp_all [shift, Code.allowed]
  case ask src d => cases src <;> rfl

/-- Preserve the caller's low registers, and use the shifted state's queue. -/
def embed (base : Nat) (caller internal : State) : State :=
  ⟨fun i => if i < base then caller.reg i else internal.reg (i - base), internal.queries⟩

@[simp] theorem embed_high (base : Nat) (caller state : State) (r : Nat) :
    (embed base caller state).reg (base + r) = state.reg r := by
  simp [embed, Nat.add_sub_cancel_left, show ¬base + r < base by omega]

@[simp] theorem embed_low {base : Nat} (caller state : State) {r : Nat} (hr : r < base) :
    (embed base caller state).reg r = caller.reg r := by simp [embed, hr]

@[simp] theorem embed_queue (base : Nat) (caller state : State) :
    (embed base caller state).queries = state.queries := rfl

private theorem embed_write (base : Nat) (caller internal : State) (r : Nat) (w : Word) :
    embed base caller (internal.write r w) = (embed base caller internal).write (base + r) w := by
  refine State.ext ?_ rfl
  funext i
  by_cases hlow : i < base
  · simp [embed, State.write, hlow, show i ≠ base + r by omega]
  · by_cases eq : i = base + r
    · simp [eq, State.write, embed, Nat.add_sub_cancel_left, show ¬base + r < base by omega]
    · have diff : i - base ≠ r := by omega
      simp [State.write, embed, hlow, eq, diff]

private theorem embed_push (base : Nat) (caller internal : State) (r : Nat) :
    embed base caller (internal.push r) = (embed base caller internal).push (base + r) := by
  refine State.ext rfl ?_
  simp [State.push]

private theorem embed_drop (base : Nat) (caller internal : State) :
    embed base caller internal.drop = (embed base caller internal).drop := rfl

private theorem evalExpr (base : Nat) (caller internal : State) (e : Expr) :
    (offsetExpr base e).eval (embed base caller internal) = e.eval internal := by
  cases e <;> simp [offsetExpr, Expr.eval]

private theorem evalTest (base : Nat) (caller internal : State) (t : Test) :
    (offsetTest base t).eval (embed base caller internal) = t.eval internal := by
  cases t <;> simp [offsetTest, Test.eval]

private theorem readSource (base : Nat) (caller internal : State) (src : Source) :
    (offsetSource base src).read (embed base caller internal) = src.read internal := by
  cases src <;> simp [offsetSource, Source.read]

private theorem advanceSource (base : Nat) (caller internal : State) (src : Source) :
    embed base caller (src.advance internal) =
      (offsetSource base src).advance (embed base caller internal) := by
  cases src <;> rfl

theorem shift_run (base : Nat) (caller : State) (run : Run A c s u t q) :
    Run A (shift base c) (embed base caller s) (embed base caller u) t q := by
  induction run with
  | skip => exact .skip
  | write =>
    rw [shift, embed_write, ← evalExpr]
    exact .write
  | push =>
    rw [shift, embed_push]
    exact .push
  | pop =>
    rw [shift, embed_write, embed_drop, ← embed_queue base caller]
    exact .pop
  | seq _ _ first second => exact .seq first second
  | @branch bit s u t q test yes no h _ branch =>
    have ht : (offsetTest base test).eval (embed base caller s) = bit := by rwa [evalTest]
    apply Run.branch ht
    cases bit <;> simpa using branch
  | loopFalse h =>
    exact .loopFalse (by rwa [evalTest])
  | loopTrue h _ _ step rest =>
    exact .loopTrue (by rwa [evalTest]) step rest
  | askEmpty read =>
    rw [shift, embed_write, advanceSource]
    exact .askEmpty (by rwa [readSource])
  | askSome read correct =>
    rw [shift, embed_write, advanceSource]
    exact .askSome (by rwa [readSource]) correct
  | callEmpty read =>
    rw [shift, embed_write, advanceSource]
    exact .callEmpty (by rwa [readSource])
  | callSome read run _ =>
    rw [shift, embed_write, advanceSource]
    exact .callSome (by rwa [readSource]) run

/-- Calls have fresh registers, so their inner writes do not count toward
the caller's address bound. -/
def maxWrite : Code → Nat
  | .skip | .push _ => 0
  | .write r _ | .pop r | .ask _ r | .callBit _ r _ => r
  | .seq a b | .branch _ a b => max (maxWrite a) (maxWrite b)
  | .loop _ body => maxWrite body

theorem reg_high_unchanged (run : Run A c s u t q) {r : Nat} (high : maxWrite c < r) :
    u.reg r = s.reg r := by
  have unchanged (s : State) (src : Source) : (src.advance s).reg = s.reg := by
    cases src <;> rfl
  induction run with
  | skip | push => rfl
  | write | pop =>
    simp only [maxWrite] at high
    simp only [State.write, State.drop]
    split
    next impossible => omega
    next => rfl
  | seq _ _ first second =>
    simp only [maxWrite, Nat.max_lt] at high
    exact (second high.2).trans (first high.1)
  | @branch bit s u t q test yes no h _ ih =>
    apply ih
    simp only [maxWrite, Nat.max_lt] at high
    cases bit <;> simp [high.1, high.2]
  | loopFalse => rfl
  | loopTrue _ _ _ first rest =>
    exact (rest high).trans (first high)
  | askEmpty | askSome | callEmpty | callSome =>
    simp only [maxWrite] at high
    simp only [State.write, unchanged]
    split
    next impossible => omega
    next => rfl

theorem queue_growth (run : Run A c s u t q) : u.queries.length ≤ s.queries.length + t := by
  have advance (s : State) (src : Source) : (src.advance s).queries.length ≤ s.queries.length := by
    cases src
    · exact Nat.le_refl _
    · simp [Source.advance, State.drop, List.length_tail]
  induction run with
  | push => simp [State.push]
  | pop => simp [State.drop, State.write, List.length_tail]; omega
  | askEmpty | askSome | callEmpty | callSome =>
    simp only [State.write]
    exact Nat.le_trans (advance ..) (Nat.le_add_right ..)
  | seq _ _ ih₁ ih₂ | loopTrue _ _ _ ih₁ ih₂ => omega
  | skip | write | loopFalse => simp [State.write]
  | branch _ _ ih => omega

def clearRange (base : Nat) : Nat → Code
  | 0 => .skip
  | n + 1 => .write (base + n) .empty ▷ clearRange base n

theorem clearRange_allowed (base count : Nat) (push direct queued : Bool) :
    (clearRange base count).allowed push direct queued := by
  induction count <;> simp_all [clearRange, Code.allowed]

theorem clearRange_run (base count : Nat) (s : State) :
    ∃ u, Run emptyLanguage (clearRange base count) s u (2 * count + 1) 0 ∧
      u.queries = s.queries ∧ ∀ r, u.reg r = if base ≤ r ∧ r < base + count then [] else s.reg r := by
  induction count generalizing s with
  | zero =>
    refine ⟨s, .skip, rfl, fun r => ?_⟩
    exact (if_neg (show ¬(base ≤ r ∧ r < base + 0) by omega)).symm
  | succ n ih =>
    let written := s.write (base + n) []
    obtain ⟨u, run, queue, regs⟩ := ih written
    have first : Run emptyLanguage (.write (base + n) .empty) s written 1 0 := .write
    refine ⟨u, ?_, queue, fun r => ?_⟩
    · rw [show 2 * (n + 1) + 1 = 1 + (2 * n + 1) + 1 by omega]
      exact .seq first run
    · rw [regs]
      by_cases h : base ≤ r ∧ r < base + n
      · have inside : base ≤ r ∧ r < base + (n + 1) := by omega
        simp [h, inside]
      · by_cases eq : r = base + n
        · have inside : base ≤ r ∧ r < base + (n + 1) := by omega
          simp [h, inside, written, State.write, eq]
        · have outside : ¬(base ≤ r ∧ r < base + (n + 1)) := by omega
          simp [h, outside, written, State.write, eq]

/-- Run a word-producing subprogram in a separate register interval. It
will see the same state as a fresh top-level invocation. -/
def invoke (base src dst : Nat) (c : Code) : Code :=
  clearRange base (MachineEnumeration.frameWidth c) ▷
    .write base (.copy src) ▷ shift base c ▷ .write dst (.copy base)

theorem invoke_pure (base src dst : Nat) {c : Code} (pure : c.pure) :
    (invoke base src dst c).pure := by
  exact ⟨clearRange_allowed ..,trivial,(shift_allowed base c ..).mpr pure,trivial⟩

theorem invoke_run (s : State) {base src dst : Nat} (belowSrc : src < base)
    (empty : s.queries = []) {c : Code} {u : State} {t : Nat}
    (run : Run emptyLanguage c (State.input (s.reg src)) u t 0) :
    ∃ v, Run emptyLanguage (invoke base src dst c) s v
        (2*MachineEnumeration.frameWidth c + t + 6) 0 ∧
      v.reg dst = u.output ∧ v.queries = u.queries ∧
      ∀ r, r ≠ dst → (r < base ∨ base + MachineEnumeration.frameWidth c ≤ r) → v.reg r = s.reg r := by
  let w := MachineEnumeration.frameWidth c
  let bank : State := ⟨fun r => s.reg (base+r),s.queries⟩
  let initial := State.input (s.reg src)
  have positive : 0 < w := MachineEnumeration.frameWidth_positive c
  obtain ⟨clean,zero,q,regs⟩ := clearRange_run base w s
  let loaded := clean.write base (s.reg src)
  have readSource : clean.reg src = s.reg src := by
    rw [regs,if_neg (by omega)]
  have copy : Run emptyLanguage (.write base (.copy src)) clean loaded 1 0 := by
    simpa [loaded,Expr.eval,readSource] using (Run.write (A:=emptyLanguage) (s:=clean) (d:=base) (e:=.copy src))
  have ready : loaded = embed base s (MachineEnumeration.keepHigh w bank initial) := by
    refine State.ext ?_ (q.trans empty)
    funext r
    by_cases low : r < base
    · rw [embed_low _ _ low]
      simp [loaded,State.write,show r ≠ base by omega,regs,show ¬(base ≤ r ∧ r < base+w) by omega]
    · have pos : base ≤ r := by omega
      obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le pos
      rw [embed_high]
      by_cases eq : i = 0
      · subst i
        simp [loaded,State.write,MachineEnumeration.keepHigh,initial,State.input,positive]
      · have diff : base + i ≠ base := by omega
        by_cases inside : i < w
        · simp [loaded,State.write,diff,MachineEnumeration.keepHigh,initial,State.input,eq,inside,
            regs,show base + i < base + w by omega]
        · simp [loaded,State.write,diff,MachineEnumeration.keepHigh,bank,inside,eq,
            regs,show ¬base + i < base + w by omega]
  let mid := embed base s (MachineEnumeration.keepHigh w bank u)
  have run' := shift_run base s (MachineEnumeration.keepHigh_run (caller:=bank) run
    (MachineEnumeration.frameWidth_uses c))
  rw [← ready] at run'
  let v := mid.write dst u.output
  have result : mid.reg base = u.output := by
    simpa [mid,MachineEnumeration.keepHigh,State.output,positive] using
      (embed_high base s (MachineEnumeration.keepHigh w bank u) 0)
  have store : Run emptyLanguage (.write dst (.copy base)) mid v 1 0 := by
    simpa [v,Expr.eval,result] using (Run.write (A:=emptyLanguage) (s:=mid) (d:=dst) (e:=.copy base))
  refine ⟨v,?_,by simp [v,State.write],rfl,?_⟩
  · have all : Run emptyLanguage (invoke base src dst c) s v _ 0 := .seq zero (.seq copy (.seq run' store))
    rwa [show 2*w+1+(1+(t+1+1)+1)+1 = 2*MachineEnumeration.frameWidth c+t+6 by
      dsimp [w]
      omega] at all
  · intro r diff outside
    simp only [v,State.write,diff,if_false]
    rcases outside with lo | hi
    · exact embed_low _ _ lo
    · have ge : base ≤ r := by omega
      obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le ge
      rw [embed_high]
      simp [MachineEnumeration.keepHigh,bank,show ¬i < w by omega]

private def prune (counter scratch : Nat) : Code :=
  .loop (.head counter) (.pop scratch ▷ .write counter (.tail counter))

private theorem prune_allowed (counter scratch : Nat) : (prune counter scratch).pure := by
  simp [prune, Code.allowed]

private theorem prune_run (s : State) {counter scratch : Nat} (distinct : counter ≠ scratch)
    (n : Nat) (fuel : s.reg counter = List.replicate n true) :
    ∃ u, Run emptyLanguage (prune counter scratch) s u (4 * n + 1) 0 ∧
      u.queries = s.queries.drop n ∧
      ∀ r, r ≠ counter → r ≠ scratch → u.reg r = s.reg r := by
  induction n generalizing s with
  | zero =>
    exact ⟨s, .loopFalse (by simp [Test.eval, fuel]), rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    let popped := s.drop.write scratch (s.queries.headD [])
    let step := popped.write counter (List.replicate n true)
    have pop : Run emptyLanguage (.pop scratch) s popped 1 0 := .pop
    have dec : Run emptyLanguage (.write counter (.tail counter)) popped step 1 0 := by
      have source : popped.reg counter = List.replicate (n + 1) true := by
        simpa [popped, State.write, State.drop, distinct] using fuel
      simpa only [step, Expr.eval, source, List.replicate_succ, List.tail_cons] using
        (Run.write (A := emptyLanguage) (s := popped) (d := counter) (e := .tail counter))
    obtain ⟨u, rest, queue, regs⟩ := ih step (by simp [step, State.write])
    refine ⟨u, ?_, ?_, fun i hc hs => ?_⟩
    · rw [show 4 * (n + 1) + 1 = 3 + (4 * n + 1) + 1 by omega]
      exact .loopTrue (by simp [Test.eval, fuel, List.replicate_succ]) (.seq pop dec) rest
    · simpa [step, popped, State.write, State.drop, List.drop_tail] using queue
    · simpa [step, popped, State.write, State.drop, hc, hs] using regs i hc hs

open MachineEnumeration

def frameSize (c : Code) : Nat := max 1 (maxWrite (replayProgram c)) + 1

def HighClear (c : Code) (s : State) : Prop :=
  ∀ r, 16 + frameSize c ≤ r → s.reg r = []

private def prepare (c : Code) : Code :=
  clearRange 16 (frameSize c) ▷ .write 16 (.copy 0) ▷ .write 17 (.copy 2)

private theorem prepare_run (c : Code) (s : State) (high : HighClear c s)
    (empty : s.queries = []) :
    Run emptyLanguage (prepare c) s
      (embed 16 s (State.input (s.reg 0) (s.reg 2))) (2 * frameSize c + 5) 0 := by
  obtain ⟨mid, run, queue, regs⟩ := clearRange_run 16 (frameSize c) s
  let u := mid.write 16 (s.reg 0)
  let v := u.write 17 (s.reg 2)
  have x : mid.reg 0 = s.reg 0 := by
    simp [regs]
  have w : u.reg 2 = s.reg 2 := by
    simp [u, State.write, regs]
  have first : Run emptyLanguage (.write 16 (.copy 0)) mid u 1 0 := by
    simpa only [u, Expr.eval, x] using (Run.write (A := emptyLanguage) (s := mid)
      (d := 16) (e := .copy 0))
  have second : Run emptyLanguage (.write 17 (.copy 2)) u v 1 0 := by
    simpa only [v, Expr.eval, w] using (Run.write (A := emptyLanguage) (s := u)
      (d := 17) (e := .copy 2))
  have eq : v = embed 16 s (State.input (s.reg 0) (s.reg 2)) := by
    refine State.ext ?_ (queue.trans empty)
    funext r
    by_cases low : r < 16
    · have notIn : ¬(16 ≤ r ∧ r < 16 + frameSize c) := by omega
      simp [v, u, State.write, embed, low, regs, notIn, show r ≠ 16 by omega, show r ≠ 17 by omega]
    · by_cases isZero : r = 16
      · subst r
        rfl
      · by_cases isOne : r = 17
        · subst r
          rfl
        · have z : r - 16 ≠ 0 := by omega
          have o : r - 16 ≠ 1 := by omega
          by_cases inside : 16 ≤ r ∧ r < 16 + frameSize c
          · simp [v, u, State.write, embed, low, regs, inside, State.input, z, o, isZero, isOne]
          · have cleared : s.reg r = [] := high _ (by omega)
            simp [v, u, State.write, embed, low, regs, inside, State.input, z, o, isZero, isOne, cleared]
  rw [← eq, show 2 * frameSize c + 5 = 2 * frameSize c + 1 + (1 + 1 + 1) + 1 by omega]
  exact .seq run (.seq first second)

/-- Run one replay with request in register zero, packed clock and tape in
register two, and a unary bound on the queue size in register 11. The
result is placed in register 10. -/
def replay (c : Code) : Code :=
  prepare c ▷ shift 16 (replayProgram c) ▷ .write 10 (.copy 16) ▷
    .write 13 (.copy 11) ▷ prune 13 12

theorem replay_pure (c : Code) : (replay c).pure := by
  simp [replay, prepare, Code.allowed, clearRange_allowed, shift_allowed,
    replayProgram_pure, prune_allowed]

theorem replay_run (c : Code) (s : State) (tape : Word) (budget : Nat)
    (high : HighClear c s) (empty : s.queries = [])
    (input : s.reg 2 = clockWord (loweringCost (frameWidth c) budget * budget) ++ tape)
    (clock : s.reg 11 = List.replicate (24 * (loweringCost (frameWidth c) budget * budget) + 36) true) :
    let fuel := 24 * (loweringCost (frameWidth c) budget * budget) + 36
    ∃ out t, Run emptyLanguage (replay c) s out t 0 ∧
      t ≤ 2 * frameSize c + 5 * fuel + 15 ∧
      out.reg 10 = ((compiledTapeOutput c (s.reg 0) tape budget).map (true :: ·)).getD [] ∧
      (out.reg 10).length ≤ (s.reg 0).length + (s.reg 2).length + fuel ∧
      out.queries = [] ∧ HighClear c out ∧
      ∀ r, r < 16 → r ≠ 10 → r ≠ 12 → r ≠ 13 → out.reg r = s.reg r := by
  dsimp only
  let fuel := 24 * (loweringCost (frameWidth c) budget * budget) + 36
  have initial := prepare_run c s high empty
  obtain ⟨logical, elapsed, logicalRun, bound, value⟩ :=
    replayProgram_run c (s.reg 0) tape budget
  rw [← input] at logicalRun
  let mid := embed 16 s logical
  have exec := shift_run 16 s logicalRun
  let returned := mid.write 10 logical.output
  have hret : mid.reg 16 = logical.output := by
    simpa [State.output] using embed_high 16 s logical 0
  have copy : Run emptyLanguage (.write 10 (.copy 16)) mid returned 1 0 := by
    simpa only [returned, Expr.eval, hret] using (Run.write (A := emptyLanguage) (s := mid)
      (d := 10) (e := .copy 16))
  let setup := returned.write 13 (List.replicate fuel true)
  have hsetup : returned.reg 11 = List.replicate fuel true := by
    simp [returned, mid, State.write, embed_low s logical (by decide : 11 < 16), clock, fuel]
  have copyClock : Run emptyLanguage (.write 13 (.copy 11)) returned setup 1 0 := by
    simpa only [setup, Expr.eval, hsetup] using (Run.write (A := emptyLanguage) (s := returned)
      (d := 13) (e := .copy 11))
  obtain ⟨out, drain, queue, frame⟩ := prune_run setup (counter := 13) (scratch := 12)
    (by decide) fuel (by simp [setup, State.write])
  refine ⟨out, _, .seq initial (.seq exec (.seq copy (.seq copyClock drain))), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · change elapsed ≤ fuel at bound
    omega
  · rw [frame 10 (by decide) (by decide)]
    simp [setup, returned, State.write, value]
  · rw [frame 10 (by decide) (by decide)]
    have fits : (State.input (s.reg 0) (s.reg 2)).Fits ((s.reg 0).length + (s.reg 2).length) :=
      State.input_fits (Nat.le_add_right ..) (Nat.le_add_left ..)
    have outBound := (logicalRun.fits fits).1 0
    change elapsed ≤ fuel at bound
    change (logical.reg 0).length ≤ (s.reg 0).length + (s.reg 2).length + fuel
    omega
  · rw [queue]
    have grew := queue_growth logicalRun
    change logical.queries.length ≤ 0 + elapsed at grew
    have enough : setup.queries.length ≤ fuel := by
      change logical.queries.length ≤ fuel
      change elapsed ≤ fuel at bound
      omega
    exact List.drop_eq_nil_of_le enough
  · intro r hr
    have lower : ¬r < 16 := by omega
    have index : frameSize c ≤ r - 16 := by omega
    have fresh : maxWrite (replayProgram c) < r - 16 :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_right ..)) index
    have two : 2 ≤ frameSize c := Nat.succ_le_succ (Nat.le_max_left ..)
    have z : r - 16 ≠ 0 := by omega
    have o : r - 16 ≠ 1 := by omega
    rw [frame r (by omega) (by omega)]
    have eq := reg_high_unchanged logicalRun fresh
    simp [setup, returned, mid, State.write, embed, lower, show r ≠ 13 by omega, show r ≠ 10 by omega,
      eq, State.input, z, o]
  · intro r hr h10 h12 h13
    rw [frame r h13 h12]
    simp [setup, returned, mid, State.write, h13, h10, embed_low s logical hr]

end ComplexityModel.ReplayFrameCode
