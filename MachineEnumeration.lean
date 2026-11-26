module

public import ComplexityModelTranscripts
public import ComplexityModelSimulation

@[expose] public section

namespace ComplexityModel

/-- Follow one hypothetical answer tape. The result records the final state,
unused transition fuel, and unread tape. Each question consumes one bit. -/
def Config.replay (clock : Nat) (c : Config) (answers : Word) :
    Option (State × Nat × Word) :=
  match c.step with
  | .halt s => some (s, clock, answers)
  | .next d =>
    match clock with
    | 0 => none
    | k + 1 => d.replay k answers
  | .question _ no yes =>
    match clock, answers with
    | k + 1, bit :: rest => (if bit then yes else no).replay k rest
    | _, _ => none
termination_by clock

theorem Config.replay_budget {c : Config} {clock : Nat} {answers : Word}
    (h : c.replay clock answers = some (s, left, unread)) :
    left ≤ clock ∧ unread.length ≤ answers.length ∧
      answers.length - unread.length ≤ clock - left := by
  induction clock generalizing c answers with
  | zero =>
    rw [Config.replay] at h
    cases e : c.step <;> simp_all
  | succ k ih =>
    rw [Config.replay] at h
    cases e : c.step with
    | halt => simp_all
    | next d =>
      rw [e] at h
      obtain ⟨a, b, bound⟩ := ih h
      exact ⟨by omega, b, by omega⟩
    | question _ no yes =>
      rw [e] at h
      cases answers with
      | nil => simp at h
      | cons bit rest =>
        obtain ⟨a, b, bound⟩ := ih h
        simp only [List.length_cons]
        omega

theorem Config.mem_candidates_iff_replay {c : Config} {clock cap : Nat} {v : Word} :
    v ∈ c.candidates clock cap ↔
      ∃ answers : Word, answers.length = cap ∧ ∃ s left unread,
        c.replay clock answers = some (s, left, unread) ∧ s.output = v := by
  induction clock generalizing c cap with
  | zero =>
    rw [Config.candidates]
    cases e : c.step with
    | halt s =>
      simp only [List.mem_singleton]
      constructor
      · intro hv
        exact ⟨List.replicate cap false, by simp, s, 0, _,
          by rw [Config.replay, e], hv.symm⟩
      · rintro ⟨answers, _, u, left, unread, h, hv⟩
        rw [Config.replay, e] at h
        cases h
        exact hv.symm
    | next d =>
      simp [List.not_mem_nil, Config.replay, e]
    | question w no yes =>
      simp [List.not_mem_nil, Config.replay, e]
  | succ k ih =>
    rw [Config.candidates]
    cases e : c.step with
    | halt s =>
      simp only [List.mem_singleton]
      constructor
      · intro hv
        exact ⟨List.replicate cap false, by simp, s, k + 1, _,
          by rw [Config.replay, e], hv.symm⟩
      · rintro ⟨answers, _, u, left, unread, h, hv⟩
        rw [Config.replay, e] at h
        cases h
        exact hv.symm
    | next d =>
      rw [ih (c := d)]
      constructor
      · rintro ⟨answers, len, s, left, unread, h, hv⟩
        exact ⟨answers, len, s, left, unread, by rwa [Config.replay, e], hv⟩
      · rintro ⟨answers, len, s, left, unread, h, hv⟩
        rw [Config.replay, e] at h
        exact ⟨answers, len, s, left, unread, h, hv⟩
    | question w no yes =>
      cases cap with
      | zero =>
        simp only [List.not_mem_nil, false_iff]
        rintro ⟨answers, len, s, left, unread, h, _⟩
        have empty : answers = [] := List.length_eq_zero_iff.mp len
        subst answers
        rw [Config.replay, e] at h
        contradiction
      | succ l =>
        rw [List.mem_append, ih (c := no), ih (c := yes)]
        constructor
        · intro h
          rcases h with ⟨bits, hlen, s, left, unread, h, out⟩ |
            ⟨bits, hlen, s, left, unread, h, out⟩
          · exact ⟨false :: bits, by simp [hlen], s, left, unread,
              by rwa [Config.replay, e], out⟩
          · exact ⟨true :: bits, by simp [hlen], s, left, unread,
              by rwa [Config.replay, e], out⟩
        · rintro ⟨answers, hlen, s, left, unread, h, out⟩
          cases answers with
          | nil => simp at hlen
          | cons bit rest =>
            have len : rest.length = l := by simpa using hlen
            rw [Config.replay, e] at h
            cases bit
            · exact Or.inl ⟨rest, len, s, left, unread, h, out⟩
            · exact Or.inr ⟨rest, len, s, left, unread, h, out⟩

theorem Run.output_replayed (h : Run A c s u t q) (ht : 2 * t ≤ clock) (hq : q ≤ cap) :
    ∃ answers : Word, answers.length = cap ∧ ∃ v left unread,
      (Config.exec c s []).replay clock answers = some (v, left, unread) ∧
      v.output = u.output :=
  Config.mem_candidates_iff_replay.mp (h.output_mem_candidates ht hq)

end ComplexityModel

namespace ComplexityModel.MachineEnumeration

private theorem reg_write_same (s : State) (r : Nat) (w : Word) :
    (s.write r w).reg r = w := by simp [State.write]

private theorem reg_write_other (s : State) (r i : Nat) (w : Word) (h : i ≠ r) :
    (s.write r w).reg i = s.reg i := by simp [State.write, h]

private def setBit (r : Nat) (b : Bool) : Code :=
  .seq (.write r .empty) (.write r (.cons b r))

private theorem run_setBit (s : State) (r : Nat) (b : Bool) :
    Run emptyLanguage (setBit r b) s (s.write r [b]) 3 0 := by
  have collapse : (s.write r []).write r [b] = s.write r [b] := by
    simp [State.write]
    funext i
    split <;> simp_all
  have h₂ : Run emptyLanguage (.write r (.cons b r)) (s.write r [])
      ((s.write r []).write r [b]) 1 0 := by
    simpa [Expr.eval, reg_write_same] using
      (Run.write (A := emptyLanguage) (s := s.write r []) (e := .cons b r) (d := r))
  rw [← collapse]
  exact .seq (show Run emptyLanguage (.write r .empty) s (s.write r []) 1 0 from .write) h₂

private theorem run_branch_true {test : Test} {s u : State} {a b : Code} {t : Nat}
    (h : test.eval s = true) (hr : Run emptyLanguage a s u t 0) :
    Run emptyLanguage (.branch test a b) s u (t + 1) 0 :=
  .branch h hr

private theorem run_branch_false {test : Test} {s u : State} {a b : Code} {t : Nat}
    (h : test.eval s = false) (hr : Run emptyLanguage b s u t 0) :
    Run emptyLanguage (.branch test a b) s u (t + 1) 0 :=
  .branch h hr

/-- A successful clock has a trailing false marker, even when no ticks
remain. The empty word signals timeout. -/
def clockWord (n : Nat) : Word := List.replicate n true ++ [false]

@[simp] private theorem clockWord_zero : clockWord 0 = [false] := rfl
@[simp] private theorem clockWord_succ (n : Nat) :
    clockWord (n + 1) = true :: clockWord n := by simp [clockWord, List.replicate_succ]
@[simp] theorem clockWord_length (n : Nat) : (clockWord n).length = n + 1 := by
  simp [clockWord]
@[simp] private theorem clockWord_notEmpty (n : Nat) : (clockWord n).isEmpty = false := by
  cases n <;> simp

private def tick (gas : Nat) (body : Code) : Code :=
  .branch (.head gas) (.seq (.write gas (.tail gas)) body) (.write gas .empty)

private def ifLive (gas : Nat) (body : Code) : Code :=
  .branch (.empty gas) .skip body

private def loopStep (gas flag : Nat) (test : Test) (body : Code) : Code :=
  .branch (.head gas)
    (.seq (.write gas (.tail gas))
      (.branch test
        (.seq body (.branch (.empty gas) (.write flag .empty) (setBit flag true)))
        (.write flag .empty)))
    (.seq (.write gas .empty) (.write flag .empty))

/-- Apply a clock to ordinary instruction execution. Scoped calls in this
pass are singleton-output tests on the supplied word. The pass emits no
oracle instructions. -/
def metered (gas flag : Nat) : Code → Code
  | .seq a b => tick gas (.seq (metered gas flag a) (ifLive gas (metered gas flag b)))
  | .branch test yes no => tick gas (.branch test (metered gas flag yes) (metered gas flag no))
  | .loop test body =>
    .seq (setBit flag true) (.loop (.head flag) (loopStep gas flag test (metered gas flag body)))
  | .ask _ _ => tick gas .skip
  | .callBit src d _ => tick gas (.callBit src d .skip)
  | c => tick gas c

theorem metered_pure (gas flag : Nat) (c : Code) : (metered gas flag c).pure := by
  induction c <;> simp_all [metered, tick, ifLive, loopStep, setBit, Code.pure, Code.allowed]

/-- The original instructions may not write the metering registers. Calls
in this fragment test a singleton output using the native scoped skip. -/
def Meterable (gas flag : Nat) : Code → Prop
  | .write d _ | .pop d => d ≠ gas ∧ d ≠ flag
  | .seq a b | .branch _ a b => Meterable gas flag a ∧ Meterable gas flag b
  | .loop _ b => Meterable gas flag b
  | .callBit _ d .skip => d ≠ gas ∧ d ≠ flag
  | .ask _ _ | .callBit _ _ _ => False
  | _ => True

private def ClockValid (s : State) (gas : Nat) : Prop :=
  s.reg gas = [] ∨ ∃ n, s.reg gas = clockWord n

private def ClockRun (gas : Nat) (c : Code) (s : State) (n : Nat) : Prop :=
  ∃ u t, Run emptyLanguage c s u t 0 ∧ ClockValid u gas ∧
    t + 20 * (u.reg gas).length ≤ 20 * (n + 1)

private theorem run_tick_zero (h : s.reg gas = clockWord 0) :
    Run emptyLanguage (tick gas body) s (s.write gas []) 2 0 := by
  exact run_branch_false (by simp [Test.eval, h]) .write

private theorem run_tick_succ (h : s.reg gas = clockWord (n + 1))
    (hr : Run emptyLanguage body (s.write gas (clockWord n)) u t 0) :
    Run emptyLanguage (tick gas body) s u (t + 3) 0 := by
  have dec : Run emptyLanguage (.write gas (.tail gas)) s (s.write gas (clockWord n)) 1 0 := by
    simpa [Expr.eval, h] using
      (Run.write (A := emptyLanguage) (s := s) (d := gas) (e := .tail gas))
  simpa [tick, (show 1 + t + 1 + 1 = t + 3 by omega)] using
    (run_branch_true (test := .head gas) (a := .seq (.write gas (.tail gas)) body) (b := .write gas .empty)
      (by simp [Test.eval, h]) (.seq dec hr))

private theorem run_atomic (gas : Nat) (body : Code)
    (exec : ∀ s, ∃ u t, Run emptyLanguage body s u t 0 ∧ t ≤ 2 ∧ u.reg gas = s.reg gas)
    (h : s.reg gas = clockWord n) :
    ClockRun gas (tick gas body) s n := by
  cases n with
  | zero =>
    refine ⟨_, _, run_tick_zero h, Or.inl (reg_write_same ..), ?_⟩
    simp [reg_write_same]
  | succ n =>
    obtain ⟨u, t, run, cost, same⟩ := exec (s.write gas (clockWord n))
    have hu : u.reg gas = clockWord n := same.trans (reg_write_same ..)
    refine ⟨u, t + 3, run_tick_succ h run, Or.inr ⟨n, hu⟩, ?_⟩
    simp only [hu, clockWord_length]
    omega

private theorem run_loop_metered {gas flag : Nat} (hgf : gas ≠ flag)
    (exec : ∀ (s : State) (n : Nat), s.reg gas = clockWord n → ClockRun gas body s n)
    (s : State) (n : Nat) (hs : s.reg gas = clockWord n)
    (hf : (Test.head flag).eval s = true) :
    ∃ u t, Run emptyLanguage (.loop (.head flag) (loopStep gas flag test body)) s u t 0 ∧
      ClockValid u gas ∧ t + 20 * (u.reg gas).length + 4 ≤ 20 * (n + 1) := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases n with
    | zero =>
      let u := (s.write gas []).write flag []
      have step : Run emptyLanguage (loopStep gas flag test body) s u 4 0 :=
        run_branch_false (by simp [Test.eval, hs]) (.seq .write .write)
      have finish : Run emptyLanguage (.loop (.head flag) (loopStep gas flag test body)) u u 1 0 :=
        .loopFalse (by simp [Test.eval, u, reg_write_same])
      have empty : u.reg gas = [] := by simp [u, reg_write_other, reg_write_same, hgf]
      exact ⟨u, 6, .loopTrue hf step finish, Or.inl empty, by simp [empty]⟩
    | succ n =>
      let a := s.write gas (clockWord n)
      have dec : Run emptyLanguage (.write gas (.tail gas)) s a 1 0 := by
        simpa [a, Expr.eval, hs] using
          (Run.write (A := emptyLanguage) (s := s) (d := gas) (e := .tail gas))
      have enter {v : State} {t : Nat} (run : Run emptyLanguage
          (.branch test
            (.seq body (.branch (.empty gas) (.write flag .empty) (setBit flag true)))
            (.write flag .empty)) a v t 0) :
          Run emptyLanguage (loopStep gas flag test body) s v (t + 3) 0 := by
        simpa [loopStep, (show 1 + t + 1 + 1 = t + 3 by omega)] using
          (run_branch_true (test := .head gas)
            (b := .seq (.write gas .empty) (.write flag .empty))
            (by simp [Test.eval, hs]) (.seq dec run))
      cases he : test.eval a with
      | false =>
        let u := a.write flag []
        have step : Run emptyLanguage (loopStep gas flag test body) s u 5 0 :=
          enter (run_branch_false he .write)
        have finish : Run emptyLanguage (.loop (.head flag) (loopStep gas flag test body)) u u 1 0 :=
          .loopFalse (by simp [Test.eval, u, reg_write_same])
        have hg : u.reg gas = clockWord n := by simp [u, a, reg_write_other, reg_write_same, hgf]
        refine ⟨u, 7, .loopTrue hf step finish, Or.inr ⟨n, hg⟩, ?_⟩
        simp only [hg, clockWord_length]
        omega
      | true =>
        obtain ⟨b, r, run, valid, bound⟩ := exec a n (reg_write_same ..)
        rcases valid with dead | ⟨left, live⟩
        · let u := b.write flag []
          have clear : Run emptyLanguage
              (.branch (.empty gas) (.write flag .empty) (setBit flag true)) b u 2 0 :=
            run_branch_true (by simp [Test.eval, dead]) .write
          have step : Run emptyLanguage (loopStep gas flag test body) s u (r + 7) 0 := by
            simpa only [show r + 2 + 1 + 1 + 3 = r + 7 by omega] using
              enter (run_branch_true he (.seq run clear))
          have finish : Run emptyLanguage (.loop (.head flag) (loopStep gas flag test body)) u u 1 0 :=
            .loopFalse (by simp [Test.eval, u, reg_write_same])
          have hg : u.reg gas = [] := by simp [u, reg_write_other, hgf, dead]
          refine ⟨u, r + 7 + 1 + 1, .loopTrue hf step finish, Or.inl hg, ?_⟩
          simp only [hg, dead, List.length_nil] at *
          omega
        · let v := b.write flag [true]
          have reset : Run emptyLanguage
              (.branch (.empty gas) (.write flag .empty) (setBit flag true)) b v 4 0 :=
            run_branch_false (by simp [Test.eval, live]) (run_setBit b flag true)
          have step : Run emptyLanguage (loopStep gas flag test body) s v (r + 9) 0 := by
            simpa only [show r + 4 + 1 + 1 + 3 = r + 9 by omega] using
              enter (run_branch_true he (.seq run reset))
          have hg : v.reg gas = clockWord left := by simp [v, reg_write_other, hgf, live]
          have hl : left < n + 1 := by simp only [live, clockWord_length] at bound; omega
          obtain ⟨u, t, finish, valid', bound'⟩ :=
            ih left hl v hg (by simp [Test.eval, v, reg_write_same])
          refine ⟨u, r + 9 + t + 1, .loopTrue hf step finish, valid', ?_⟩
          simp only [live, clockWord_length] at bound
          omega


private theorem run_ifLive (s : State) (gas : Nat) (body : Code)
    (valid : ClockValid s gas)
    (exec : ∀ n, s.reg gas = clockWord n → ClockRun gas body s n) :
    ∃ u t, Run emptyLanguage (ifLive gas body) s u t 0 ∧ ClockValid u gas ∧
      t + 20 * (u.reg gas).length ≤ 20 * (s.reg gas).length + 2 := by
  rcases valid with dead | ⟨n, live⟩
  · exact ⟨s, 2, run_branch_true (by simp [ifLive, Test.eval, dead]) .skip,
      Or.inl dead, by simp [dead]⟩
  · obtain ⟨u, t, hr, valid', bound⟩ := exec n live
    refine ⟨u, t + 1, run_branch_false (by simp [ifLive, Test.eval, live]) hr,
      valid', ?_⟩
    simp only [live, clockWord_length]
    omega

private theorem metered_clockRun {gas flag : Nat} (hgf : gas ≠ flag) {c : Code}
    (hc : Meterable gas flag c) (s : State) (n : Nat) (hs : s.reg gas = clockWord n) :
    ClockRun gas (metered gas flag c) s n := by
  induction c generalizing s n with
  | skip =>
    exact run_atomic gas .skip (fun st => ⟨st, 1, .skip, by decide, rfl⟩) hs
  | write d e =>
    exact run_atomic gas (.write d e) (fun st =>
      ⟨_, 1, .write, by decide, reg_write_other _ _ _ _ (Ne.symm hc.1)⟩) hs
  | push r =>
    exact run_atomic gas (.push r) (fun st => ⟨_, 1, .push, by decide, rfl⟩) hs
  | pop d =>
    exact run_atomic gas (.pop d) (fun st =>
      ⟨_, 1, .pop, by decide, reg_write_other _ _ _ _ (Ne.symm hc.1)⟩) hs
  | callBit src d body =>
    cases body <;> simp only [Meterable] at hc
    refine run_atomic gas (.callBit src d .skip) (fun st => ?_) hs
    have same : ∀ b : Bool, ((src.advance st).write d [b]).reg gas = st.reg gas := by
      intro b
      rw [reg_write_other _ _ _ _ (Ne.symm hc.1)]
      cases src <;> rfl
    cases hr : src.read st with
    | none => exact ⟨_, 1, .callEmpty hr, by decide, same _⟩
    | some w => exact ⟨_, 2, .callSome hr .skip, by decide, same _⟩
  | ask => simp [Meterable] at hc
  | seq a b iha ihb =>
    cases n with
    | zero =>
      exact ⟨_, 2, run_tick_zero hs, Or.inl (reg_write_same ..), by simp [reg_write_same]⟩
    | succ n =>
      let st := s.write gas (clockWord n)
      obtain ⟨u, r, ha, valid, haBound⟩ := iha hc.1 st n (reg_write_same ..)
      obtain ⟨v, t, hb, valid', hbBound⟩ :=
        run_ifLive u gas (metered gas flag b) valid (ihb hc.2 u)
      exact ⟨v, r + t + 1 + 3, run_tick_succ hs (.seq ha hb), valid', by omega⟩
  | branch test yes no ihy ihn =>
    cases n with
    | zero =>
      exact ⟨_, 2, run_tick_zero hs, Or.inl (reg_write_same ..), by simp [reg_write_same]⟩
    | succ n =>
      let st := s.write gas (clockWord n)
      cases he : test.eval st with
      | false =>
        obtain ⟨u, t, hr, valid, bound⟩ := ihn hc.2 st n (reg_write_same ..)
        exact ⟨u, t + 1 + 3, run_tick_succ hs (run_branch_false he hr), valid, by omega⟩
      | true =>
        obtain ⟨u, t, hr, valid, bound⟩ := ihy hc.1 st n (reg_write_same ..)
        exact ⟨u, t + 1 + 3, run_tick_succ hs (run_branch_true he hr), valid, by omega⟩
  | loop test body ih =>
    let st := s.write flag [true]
    have hg : st.reg gas = clockWord n := by rw [reg_write_other _ _ _ _ hgf, hs]
    obtain ⟨u, t, run, valid, bound⟩ :=
      run_loop_metered hgf (ih hc) st n hg (by simp [st, Test.eval, reg_write_same])
    exact ⟨u, 3 + t + 1, .seq (run_setBit s flag true) run, valid, by omega⟩

/-- The instrumented program always terminates, even if its supplied program
has diverging loops. A zero-length clock reports that it ran out of ticks. -/
theorem metered_total {gas flag : Nat} (hgf : gas ≠ flag) {c : Code}
    (hc : Meterable gas flag c) (hs : s.reg gas = clockWord n) :
    ∃ u t, Run emptyLanguage (metered gas flag c) s u t 0 ∧
      t + 20 * (u.reg gas).length ≤ 20 * (n + 1) :=
  let ⟨u, t, hr, _, bound⟩ := metered_clockRun hgf hc s n hs
  ⟨u, t, hr, bound⟩


private def Expr.atRegisters (p : Nat → Prop) : Expr → Prop
  | .empty => True
  | .copy r | .tail r | .cons _ r => p r

private def Test.atRegisters (p : Nat → Prop) : Test → Prop
  | .empty r | .head r => p r

private def Source.atRegisters (p : Nat → Prop) : Source → Prop
  | .reg r => p r
  | .queued => True

/-- Every address used by the source program is below the width of one
register frame. Each compiled frame has its own queue depth register. -/
def UsesRegisters (width : Nat) : Code → Prop
  | .skip => True
  | .write d e => d < width ∧ Expr.atRegisters (· < width) e
  | .push r | .pop r => r < width
  | .seq a b => UsesRegisters width a ∧ UsesRegisters width b
  | .branch test a b =>
    Test.atRegisters (· < width) test ∧ UsesRegisters width a ∧ UsesRegisters width b
  | .loop test b => Test.atRegisters (· < width) test ∧ UsesRegisters width b
  | .ask src d => Source.atRegisters (· < width) src ∧ d < width
  | .callBit src d b => Source.atRegisters (· < width) src ∧ d < width ∧ UsesRegisters width b

/-- Keep the registers used by a program from its own state and retain the
unaddressed registers of the caller. The program's queue is shared. -/
def keepHigh (width : Nat) (caller internal : State) : State :=
  ⟨fun r => if r < width then internal.reg r else caller.reg r, internal.queries⟩

theorem keepHigh_run {width : Nat} {caller : State} (run : Run A c s u t q)
    (used : UsesRegisters width c) :
    Run A c (keepHigh width caller s) (keepHigh width caller u) t q := by
  have ext {s u : State} (rr : s.reg = u.reg) (qq : s.queries = u.queries) : s = u := by
    cases s
    cases u
    cases rr
    cases qq
    rfl
  have write (v : State) (d : Nat) (w : Word) (h : d < width) :
      keepHigh width caller (v.write d w) = (keepHigh width caller v).write d w := by
    refine ext ?_ rfl
    funext r
    by_cases same : r = d
    · subst r
      simp [keepHigh,State.write,h]
    · simp [keepHigh,State.write,same]
  have expr (v : State) (e : Expr) (h : Expr.atRegisters (· < width) e) :
      e.eval (keepHigh width caller v) = e.eval v := by
    cases e <;> simp_all [Expr.atRegisters,Expr.eval,keepHigh]
  have test (v : State) (p : Test) (h : Test.atRegisters (· < width) p) :
      p.eval (keepHigh width caller v) = p.eval v := by
    cases p <;> simp_all [Test.atRegisters,Test.eval,keepHigh]
  have read (v : State) (src : Source) (h : Source.atRegisters (· < width) src) :
      src.read (keepHigh width caller v) = src.read v := by
    cases src <;> simp_all [Source.atRegisters,Source.read,keepHigh]
  have advance (v : State) (src : Source) :
      keepHigh width caller (src.advance v) = src.advance (keepHigh width caller v) := by
    cases src <;> rfl
  induction run with
  | skip => exact .skip
  | write =>
    rw [write _ _ _ used.1, ← expr _ _ used.2]
    exact .write
  | @push r s =>
    have same : keepHigh width caller (s.push r) = (keepHigh width caller s).push r := by
      refine ext rfl ?_
      simp [keepHigh,State.push,show r < width from used]
    rw [same]
    exact .push
  | pop =>
    rw [write _ _ _ used]
    exact .pop
  | seq _ _ first second => exact .seq (first used.1) (second used.2)
  | @branch bit s u t q cond yes no h _ ih =>
    apply Run.branch ((test _ _ used.1).trans h)
    apply ih
    cases bit
    · exact used.2.2
    · exact used.2.1
  | loopFalse h => exact .loopFalse ((test _ _ used.1).trans h)
  | loopTrue h _ _ first rest =>
    exact .loopTrue ((test _ _ used.1).trans h) (first used.2) (rest used)
  | askEmpty h =>
    rw [write _ _ _ used.2,advance]
    exact .askEmpty ((read _ _ used.1).trans h)
  | askSome h bit =>
    rw [write _ _ _ used.2,advance]
    exact .askSome ((read _ _ used.1).trans h) bit
  | callEmpty h =>
    rw [write _ _ _ used.2.1,advance]
    exact .callEmpty ((read _ _ used.1).trans h)
  | callSome h body _ =>
    rw [write _ _ _ used.2.1,advance]
    exact .callSome ((read _ _ used.1).trans h) body

private def Expr.rename (f : Nat → Nat) : Expr → Expr
  | .empty => .empty
  | .copy r => .copy (f r)
  | .tail r => .tail (f r)
  | .cons b r => .cons b (f r)

private def Test.rename (f : Nat → Nat) : Test → Test
  | .empty r => .empty (f r)
  | .head r => .head (f r)

private def slot (base r : Nat) : Nat := base + 1 + r

private def child (width base : Nat) : Nat := slot base width

private def clearRange (start : Nat) : Nat → Code
  | 0 => .skip
  | n + 1 => .seq (clearRange start n) (.write (start + n) .empty)

-- Register 0 holds the unread hypothetical answers. Register 1 signals that
-- an answer was missing. Registers 2 and 3 are available for metering.
private def readBit (d : Nat) : Code :=
  .branch (.empty 0)
    (.seq (setBit 1 true) (setBit d false))
    (.seq (.branch (.head 0) (setBit d true) (setBit d false)) (.write 0 (.tail 0)))

private def takeQueue (base d : Nat) : Code :=
  .seq (.write base (.tail base)) (.pop d)

private def cleanQueue (base scratch : Nat) : Code :=
  .loop (.head base) (takeQueue base scratch)

local infixr:60 " ▷ " => Code.seq

/-- Lower a fixed program to an oracle-free program with a shared answer
tape. The real stack is partitioned by the private queue depths of active
frames. Native calls in the result are only used to test a singleton. -/
def lower (width base : Nat) : Code → Code
  | .skip => .skip
  | .write d e => .write (slot base d) (Expr.rename (slot base) e)
  | .push r => .push (slot base r) ▷ .write base (.cons true base)
  | .pop d => .branch (.empty base) (.write (slot base d) .empty) (takeQueue base (slot base d))
  | .seq a b => lower width base a ▷ lower width base b
  | .branch test a b =>
    .branch (Test.rename (slot base) test) (lower width base a) (lower width base b)
  | .loop test b => .loop (Test.rename (slot base) test) (lower width base b)
  | .ask (.reg _) d => readBit (slot base d)
  | .ask .queued d =>
    .branch (.empty base) (setBit (slot base d) false)
      (takeQueue base (slot base d) ▷ readBit (slot base d))
  | .callBit src d body =>
    let next := child width base
    let enter : Code :=
      .write next .empty ▷ clearRange (slot next 1) (width - 1) ▷
      lower width next body ▷ cleanQueue next (child width next) ▷
      .callBit (.reg (slot next 0)) (slot base d) .skip
    match src with
    | .reg r => .write (slot next 0) (.copy (slot base r)) ▷ enter
    | .queued =>
      .branch (.empty base) (setBit (slot base d) false) (takeQueue base (slot next 0) ▷ enter)

theorem lower_pure (width base : Nat) (c : Code) : (lower width base c).pure := by
  have clear (start n : Nat) : (clearRange start n).pure := by
    induction n <;> simp_all [clearRange, Code.pure, Code.allowed]
  induction c generalizing base <;>
    simp_all [lower, takeQueue, cleanQueue, readBit, setBit, Code.pure, Code.allowed]
  · rename_i src d
    cases src <;> simp [lower, takeQueue, readBit, setBit, Code.pure, Code.allowed]
  · rename_i src d body ih
    cases src <;>
      simp [lower, takeQueue, cleanQueue, setBit, Code.pure, Code.allowed, clear, ih]

/-- The flat fragment uses only the permitted addresses and implements calls
by the native singleton test. -/
def FlatUsing (p : Nat → Prop) : Code → Prop
  | .write d e => p d ∧ Expr.atRegisters p e
  | .push r | .pop r => p r
  | .seq a b => FlatUsing p a ∧ FlatUsing p b
  | .branch test a b => Test.atRegisters p test ∧ FlatUsing p a ∧ FlatUsing p b
  | .loop test body => Test.atRegisters p test ∧ FlatUsing p body
  | .callBit src d .skip => Source.atRegisters p src ∧ p d
  | .ask _ _ | .callBit _ _ _ => False
  | .skip => True

private theorem flat_meterable {p : Nat → Prop} {gas flag : Nat}
    (h : ∀ r, p r → r ≠ gas ∧ r ≠ flag) {c : Code} (hc : FlatUsing p c) :
    Meterable gas flag c := by
  induction c with
  | skip | push => trivial
  | write => exact h _ hc.1
  | pop => exact h _ hc
  | seq a b iha ihb => exact ⟨iha hc.1, ihb hc.2⟩
  | branch test a b iha ihb => exact ⟨iha hc.2.1, ihb hc.2.2⟩
  | loop test b ih => exact ih hc.2
  | ask => exact hc
  | callBit src d b =>
    cases b <;> simp only [FlatUsing, Meterable] at *
    exact h _ hc.2

private theorem flat_clearRange {p : Nat → Prop} {start count : Nat}
    (h : ∀ i, i < count → p (start + i)) :
    FlatUsing p (clearRange start count) := by
  induction count with
  | zero => trivial
  | succ n ih => exact ⟨ih (fun i hi => h i (by omega)), h n (by omega), trivial⟩

theorem lower_flat {p : Nat → Prop} (h₀ : p 0) (h₁ : p 1)
    (width base : Nat) (h : ∀ r, base ≤ r → p r) (c : Code) :
    FlatUsing p (lower width base c) := by
  induction c generalizing base
  all_goals
    have addresses (b r : Nat) (hb : base ≤ b) : p (slot b r) :=
      h _ (by unfold slot; omega)
    have hbase : p base := h _ (by omega)
    have dest (r : Nat) : p (slot base r) := addresses _ _ (by omega)
    have eok (e : Expr) : Expr.atRegisters p (Expr.rename (slot base) e) := by
      cases e <;> first | exact dest _ | trivial
    have tok (test : Test) : Test.atRegisters p (Test.rename (slot base) test) := by
      cases test <;> exact dest _
  case skip => trivial
  case write d e => exact ⟨dest d, eok e⟩
  case push r => exact ⟨dest r, hbase, hbase⟩
  case pop d => exact ⟨hbase, ⟨dest d, trivial⟩, ⟨hbase, hbase⟩, dest d⟩
  case seq a b iha ihb => exact ⟨iha base h, ihb base h⟩
  case branch test a b iha ihb => exact ⟨tok test, iha base h, ihb base h⟩
  case loop test b ih => exact ⟨tok test, ih base h⟩
  case ask src d =>
    cases src <;> simp [lower, takeQueue, readBit, setBit, FlatUsing, Expr.atRegisters,
      Test.atRegisters, hbase, dest, h₀, h₁]
  case callBit src d body ih =>
    have nextLe : base ≤ child width base := by unfold child slot; omega
    have hnext : ∀ r, child width base ≤ r → p r := fun r hr => h r (by omega)
    have next : p (child width base) := hnext _ (by omega)
    have nextSlot : ∀ r, p (slot (child width base) r) := fun r => addresses _ r nextLe
    have nextChild : p (child width (child width base)) := nextSlot width
    have clr : FlatUsing p (clearRange (slot (child width base) 1) (width - 1)) :=
      flat_clearRange (fun _ _ => h _ (by unfold child slot; omega))
    cases src <;>
      simp [lower, takeQueue, cleanQueue, setBit, FlatUsing, Expr.atRegisters,
        Test.atRegisters, Source.atRegisters, hbase, dest, next, nextSlot, nextChild, clr,
        ih _ hnext]

theorem lower_meterable (width base : Nat) (hb : 4 ≤ base) (c : Code) :
    Meterable 2 3 (lower width base c) :=
  flat_meterable (p := fun r => r = 0 ∨ r = 1 ∨ base ≤ r)
    (fun r hr => by rcases hr with hr | hr | hr <;> omega)
    (lower_flat (Or.inl rfl) (Or.inr (Or.inl rfl)) width base (fun _ h => Or.inr (Or.inr h)) c)

/-- Concrete oracle-free code for replay, with a supplied unary clock in
register 2 and tape in register 0. Scope initialization is separate. -/
def compiledReplay (width base : Nat) (c : Code) : Code := metered 2 3 (lower width base c)

theorem compiledReplay_pure (width base : Nat) (c : Code) : (compiledReplay width base c).pure :=
  metered_pure 2 3 _

theorem compiledReplay_total (width base : Nat) (hb : 4 ≤ base) (c : Code)
    (h : s.reg 2 = clockWord n) :
    ∃ u t, Run emptyLanguage (compiledReplay width base c) s u t 0 ∧
      t + 20 * (u.reg 2).length ≤ 20 * (n + 1) :=
  metered_total (by decide) (lower_meterable width base hb c) h

/-- Agreement on a set of registers and on the complete physical stack. -/
def AgreeOn (p : Nat → Prop) (s u : State) : Prop :=
  s.queries = u.queries ∧ ∀ r, p r → s.reg r = u.reg r

private theorem AgreeOn.writeLeft {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    {r : Nat} (hr : ¬ p r) (w : Word) : AgreeOn p (a.write r w) b := by
  refine ⟨h.1, fun i hi => ?_⟩
  have neq : i ≠ r := fun e => hr (e ▸ hi)
  rw [reg_write_other _ _ _ _ neq, h.2 _ hi]

private theorem AgreeOn.writeBoth {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    (r : Nat) (w : Word) : AgreeOn p (a.write r w) (b.write r w) :=
  ⟨h.1, fun i hi => by simp [State.write, h.2 i hi]⟩

private theorem AgreeOn.expr {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    (e : Expr) (he : Expr.atRegisters p e) : e.eval a = e.eval b := by
  cases e <;> simp_all [Expr.eval, Expr.atRegisters, AgreeOn]

private theorem AgreeOn.test {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    (test : Test) (ht : Test.atRegisters p test) : test.eval a = test.eval b := by
  cases test <;> simp_all [Test.eval, Test.atRegisters, AgreeOn]

private theorem AgreeOn.read {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    (src : Source) (hs : Source.atRegisters p src) : src.read a = src.read b := by
  cases src <;> simp_all [Source.read, Source.atRegisters, AgreeOn]

private theorem AgreeOn.advance {p : Nat → Prop} {a b : State} (h : AgreeOn p a b)
    (src : Source) : AgreeOn p (src.advance a) (src.advance b) := by
  cases src with
  | reg => exact h
  | queued => exact ⟨congrArg List.tail h.1, h.2⟩

private theorem write_id {s : State} {r : Nat} {w : Word} (h : s.reg r = w) :
    s.write r w = s := by
  cases s with
  | mk reg queries =>
    unfold State.write
    congr
    funext i
    simp only [State.write]
    split
    · rename_i e
      subst i
      exact h.symm
    · rfl

private theorem run_setBit_inv {s u : State} {r t q : Nat} {b : Bool}
    (h : Run emptyLanguage (setBit r b) s u t q) : u = s.write r [b] := by
  cases h with
  | seq h₁ h₂ =>
    cases h₁
    cases h₂
    simp only [Expr.eval, reg_write_same]
    cases s
    simp only [State.write]
    congr
    funext i
    split <;> simp_all

private theorem run_seq_inv (h : Run A (.seq a b) s u t q) :
    ∃ m ta tb qa qb, Run A a s m ta qa ∧ Run A b m u tb qb ∧ q = qa + qb := by
  cases h
  rename_i ha hb
  exact ⟨_, _, _, _, _, ha, hb, rfl⟩

/-- Sufficient ticks preserve the result of any terminating run in the flat
fragment. Scratch registers can differ at entry and at exit. -/
theorem metered_correct {p : Nat → Prop} {gas flag : Nat} (hgf : gas ≠ flag)
    (hg : ¬ p gas) (hf : ¬ p flag)
    (run : Run emptyLanguage c s u t q) (hc : FlatUsing p c)
    (view : AgreeOn p initial s) (hclock : initial.reg gas = clockWord n) (hn : t ≤ n) :
    ∃ out time left, Run emptyLanguage (metered gas flag c) initial out time 0 ∧
      AgreeOn p out u ∧ out.reg gas = clockWord left ∧ n ≤ t + left := by
  induction run generalizing initial n with
  | skip =>
    cases n with
    | zero => omega
    | succ n =>
      exact ⟨_, _, n, run_tick_succ hclock .skip,
        view.writeLeft hg _, reg_write_same .., by omega⟩
  | @write d e s =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      have hwrite : Run emptyLanguage (.write d e) a (a.write d (e.eval s)) 1 0 := by
        rw [← ha.expr e hc.2]
        exact .write
      exact ⟨_, _, n, run_tick_succ hclock hwrite, ha.writeBoth d _,
        (reg_write_other _ _ _ _ (fun e : gas = d => hg (by rw [e]; exact hc.1))).trans (reg_write_same ..),
        by omega⟩
  | @push r s =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      exact ⟨a.push r, _, n, run_tick_succ hclock .push,
        ⟨by simp [State.push, ha.1, ha.2 _ hc], ha.2⟩, reg_write_same .., by omega⟩
  | @pop d s =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      have hd : AgreeOn p a.drop s.drop := ha.advance .queued
      have hpop : Run emptyLanguage (.pop d) a (a.drop.write d (s.queries.headD [])) 1 0 := by
        rw [← ha.1]
        exact .pop
      exact ⟨_, _, n, run_tick_succ hclock hpop, hd.writeBoth d _,
        (reg_write_other _ _ _ _ (fun e : gas = d => hg (by rwa [e]))).trans (reg_write_same ..),
        by omega⟩
  | @seq a s mid t₁ q₁ b u t₂ q₂ _ _ ih₁ ih₂ =>
    cases n with
    | zero => omega
    | succ n =>
      let st := initial.write gas (clockWord n)
      obtain ⟨v, r, l, rv, hv, gl, hl⟩ :=
        ih₁ (n := n) hc.1 (view.writeLeft hg _) (reg_write_same ..) (by omega)
      obtain ⟨w, z, left, rw, hw, gw, hbound⟩ := ih₂ hc.2 hv gl (by omega)
      have second : Run emptyLanguage (ifLive gas (metered gas flag b)) v w (z + 1) 0 :=
        run_branch_false (by simp [Test.eval, gl]) rw
      exact ⟨w, _, left, run_tick_succ hclock (.seq rv second), hw, gw, by omega⟩
  | @branch bit s u t q test yes no he _ ih =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      have htest := (ha.test test hc.1).trans he
      have hchoice : FlatUsing p (if bit then yes else no) := by
        cases bit
        · exact hc.2.2
        · exact hc.2.1
      obtain ⟨v, r, left, hv, agree, gv, bound⟩ :=
        ih (n := n) hchoice ha (reg_write_same ..) (by omega)
      have branch : Run emptyLanguage
          (.branch test (metered gas flag yes) (metered gas flag no)) a v (r + 1) 0 := by
        apply Run.branch htest
        cases bit <;> exact hv
      exact ⟨v, _, left, run_tick_succ hclock branch, agree, gv, by omega⟩
  | @loopFalse test body s he =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write flag [true]
      let b := a.write gas (clockWord n)
      let v := b.write flag []
      have ha : AgreeOn p a s := view.writeLeft hf _
      have hb : AgreeOn p b s := ha.writeLeft hg _
      have head : (Test.head flag).eval a = true := by simp [a, Test.eval, reg_write_same]
      have dec : Run emptyLanguage (.write gas (.tail gas)) a b 1 0 := by
        have headgas : a.reg gas = clockWord (n + 1) :=
          (reg_write_other _ _ _ _ hgf).trans hclock
        simpa [b, Expr.eval, headgas] using
          (Run.write (A := emptyLanguage) (s := a) (d := gas) (e := .tail gas))
      have step : Run emptyLanguage (loopStep gas flag test (metered gas flag body)) a v 5 0 :=
        run_branch_true (by simp [a, Test.eval, reg_write_other, hgf, hclock])
          (.seq dec (run_branch_false ((hb.test test hc.1).trans he) .write))
      refine ⟨v, 11, n, .seq (run_setBit initial flag true) (.loopTrue head step
        (.loopFalse (by simp [v, Test.eval, reg_write_same]))), hb.writeLeft hf _, ?_, by omega⟩
      simp [v, b, reg_write_other, reg_write_same, hgf]
  | @loopTrue body s mid t₁ q₁ test u t₂ q₂ he _ _ ih₁ ih₂ =>
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write flag [true]
      let b := a.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hf _
      have hb : AgreeOn p b s := ha.writeLeft hg _
      have head : (Test.head flag).eval a = true := by simp [a, Test.eval, reg_write_same]
      have headgas : a.reg gas = clockWord (n + 1) :=
        (reg_write_other _ _ _ _ hgf).trans hclock
      have dec : Run emptyLanguage (.write gas (.tail gas)) a b 1 0 := by
        simpa [b, Expr.eval, headgas] using
          (Run.write (A := emptyLanguage) (s := a) (d := gas) (e := .tail gas))
      obtain ⟨v, r, l, rv, hv, gl, hl⟩ :=
        ih₁ (n := n) hc.2 hb (reg_write_same ..) (by omega)
      let w := v.write flag [true]
      have gw : w.reg gas = clockWord l := (reg_write_other _ _ _ _ hgf).trans gl
      have reset : Run emptyLanguage
          (.branch (.empty gas) (.write flag .empty) (setBit flag true)) v w 4 0 :=
        run_branch_false (by simp [Test.eval, gl]) (run_setBit v flag true)
      have step : Run emptyLanguage (loopStep gas flag test (metered gas flag body))
          a w (1 + (r + 4 + 1 + 1) + 1 + 1) 0 :=
        run_branch_true (by simp [Test.eval, headgas]) (.seq dec
          (run_branch_true ((hb.test test hc.1).trans he) (.seq rv reset)))
      obtain ⟨out, z, left, rw, outAgree, outGas, bound⟩ :=
        ih₂ hc (hv.writeLeft hf _) gw (by omega)
      change Run emptyLanguage
        (.seq (setBit flag true) (.loop (.head flag) (loopStep gas flag test (metered gas flag body))))
        w out z 0 at rw
      obtain ⟨_, _, _, qa, qb, pre, rest, eq⟩ := run_seq_inv rw
      have ident := (run_setBit_inv pre).trans (write_id (reg_write_same v flag [true]))
      have qzero : qb = 0 := by omega
      rw [ident, qzero] at rest
      exact ⟨out, _, left, .seq (run_setBit initial flag true) (.loopTrue head step rest),
        outAgree, outGas, by omega⟩
  | askEmpty | askSome => exact False.elim hc
  | @callEmpty src d body s he =>
    cases body <;> simp only [FlatUsing] at hc
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      have hread := (ha.read src hc.1).trans he
      have same : (src.advance a).reg gas = a.reg gas := by cases src <;> rfl
      exact ⟨_, _, n, run_tick_succ hclock (.callEmpty hread),
        (ha.advance src).writeBoth d _,
        (reg_write_other _ _ _ _ (fun e : gas = d => hg (by rw [e]; exact hc.2))).trans
          (same.trans (reg_write_same ..)), by omega⟩
  | @callSome w body u t q src d s he hr ih =>
    cases body <;> simp only [FlatUsing] at hc
    cases hr
    cases n with
    | zero => omega
    | succ n =>
      let a := initial.write gas (clockWord n)
      have ha : AgreeOn p a s := view.writeLeft hg _
      have hread := (ha.read src hc.1).trans he
      have same : (src.advance a).reg gas = a.reg gas := by cases src <;> rfl
      exact ⟨_, _, n, run_tick_succ hclock (.callSome hread .skip),
        (ha.advance src).writeBoth d _,
        (reg_write_other _ _ _ _ (fun e : gas = d => hg (by rw [e]; exact hc.2))).trans
          (same.trans (reg_write_same ..)), by omega⟩


private theorem run_reg_outside {p : Nat → Prop} (run : Run A c s u t q)
    (hc : FlatUsing p c) (h : ¬ p r) : u.reg r = s.reg r := by
  induction run with
  | skip | push | loopFalse => rfl
  | write => exact reg_write_other _ _ _ _ (fun e => h (e ▸ hc.1))
  | pop => exact reg_write_other _ _ _ _ (fun e => h (e ▸ hc))
  | seq _ _ ih₁ ih₂ => exact (ih₂ hc.2).trans (ih₁ hc.1)
  | branch he hr ih =>
    apply ih
    split
    · exact hc.2.1
    · exact hc.2.2
  | loopTrue he hr₁ hr₂ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc.2)
  | askEmpty | askSome => exact False.elim hc
  | @callEmpty src d body s he | @callSome _ body _ _ _ src d s he _ _ =>
    cases body <;> simp only [FlatUsing] at hc
    have hd : r ≠ d := fun e => h (e ▸ hc.2)
    rw [reg_write_other _ _ _ _ hd]
    cases src <;> rfl

/-- The physical stack contains the current frame's pending words in
front of the caller's stack. The depth register prevents empty pops from
touching the caller's words. -/
structure FrameView (width base : Nat) (logical : State) (suffix : List Word)
    (physical : State) : Prop where
  register : ∀ i, i < width → physical.reg (slot base i) = logical.reg i
  marker : physical.reg base = List.replicate logical.queries.length true
  stack : physical.queries = logical.queries ++ suffix

private theorem FrameView.writeFrame (h : FrameView width base s suffix m) (d : Nat) (w : Word) :
    FrameView width base (s.write d w) suffix (m.write (slot base d) w) := by
  refine ⟨fun i hi => ?_, ?_, h.stack⟩
  · simp only [State.write]
    by_cases e : i = d
    · simp [e]
    · have e' : slot base i ≠ slot base d := by unfold slot; omega
      simp [e, e', h.register _ hi]
  · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans h.marker

private theorem FrameView.writeOutside (h : FrameView width base s suffix m)
    {d : Nat} (hb : d ≠ base) (hs : ∀ i, i < width → d ≠ slot base i) (w : Word) :
    FrameView width base s suffix (m.write d w) :=
  ⟨fun i hi => (reg_write_other _ _ _ _ (Ne.symm (hs i hi))).trans (h.register i hi),
    (reg_write_other _ _ _ _ (Ne.symm hb)).trans h.marker, h.stack⟩

private theorem FrameView.renameExpr (h : FrameView width base s suffix m) (e : Expr)
    (he : Expr.atRegisters (· < width) e) :
    (Expr.rename (slot base) e).eval m = e.eval s := by
  cases e with
  | empty => rfl
  | copy r => exact h.register r he
  | tail r => exact congrArg List.tail (h.register r he)
  | cons b r => exact congrArg (List.cons b) (h.register r he)

private theorem FrameView.renameTest (h : FrameView width base s suffix m) (test : Test)
    (ht : Test.atRegisters (· < width) test) :
    (Test.rename (slot base) test).eval m = test.eval s := by
  cases test with
  | empty r => exact congrArg List.isEmpty (h.register r ht)
  | head r => exact congrArg (fun w : Word => w.headD false) (h.register r ht)

private def frameDrop (s : State) (base : Nat) : State :=
  (s.write base (s.reg base).tail).drop

private theorem run_takeQueue {s : State} (base d : Nat) :
    Run emptyLanguage (takeQueue base d) s ((frameDrop s base).write d (s.queries.headD [])) 3 0 :=
  Run.seq (show Run emptyLanguage (.write base (.tail base)) s
    (s.write base (s.reg base).tail) 1 0 from .write) .pop

private theorem FrameView.dropFrame (h : FrameView width base s suffix m)
    (hs : s.queries = w :: rest) :
    FrameView width base s.drop suffix (frameDrop m base) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans (h.register i hi)
  · simp [frameDrop, State.drop, reg_write_same, h.marker, hs, List.replicate_succ]
  · simp [frameDrop, State.drop, State.write, h.stack, hs]

private theorem FrameView.queueEmpty (h : FrameView width base s suffix m)
    (hq : s.queries = []) : (Test.empty base).eval m = true := by
  simp [Test.eval, h.marker, hq]

private theorem FrameView.queueNonempty (h : FrameView width base s suffix m)
    (hq : s.queries = w :: rest) : (Test.empty base).eval m = false := by
  simp [Test.eval, h.marker, hq, List.replicate_succ]

private theorem FrameView.pushFrame (h : FrameView width base s suffix m) (r : Nat)
    (hr : r < width) :
    FrameView width base (s.push r) suffix
      ((m.push (slot base r)).write base (true :: m.reg base)) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans (h.register i hi)
  · simp [reg_write_same, h.marker, State.push, List.replicate_succ]
  · simp [State.write, State.push, h.stack, h.register r hr]

private theorem run_readBit {s : State} (d : Nat) (hd : d ≠ 0)
    (h : s.reg 0 = bit :: rest) :
    Run emptyLanguage (readBit d) s ((s.write d [bit]).write 0 rest) 7 0 := by
  have consume : Run emptyLanguage (.write 0 (.tail 0)) (s.write d [bit])
      ((s.write d [bit]).write 0 rest) 1 0 := by
    have head : (s.write d [bit]).reg 0 = bit :: rest :=
      (reg_write_other _ _ _ _ (Ne.symm hd)).trans h
    simpa [Expr.eval, head] using
      (Run.write (A := emptyLanguage) (s := s.write d [bit]) (d := 0) (e := .tail 0))
  have set : Run emptyLanguage (.branch (.head 0) (setBit d true) (setBit d false))
      s (s.write d [bit]) 4 0 := by
    cases bit
    · exact run_branch_false (by simp [Test.eval, h]) (run_setBit s d false)
    · exact run_branch_true (by simp [Test.eval, h]) (run_setBit s d true)
  exact run_branch_false (by simp [Test.eval, h]) (.seq set consume)

private theorem run_clearRange (s : State) (start count : Nat) :
    ∃ u, Run emptyLanguage (clearRange start count) s u (2 * count + 1) 0 ∧
      u.queries = s.queries ∧ ∀ r,
        u.reg r = if start ≤ r ∧ r < start + count then [] else s.reg r := by
  induction count with
  | zero => exact ⟨s, .skip, rfl, fun r => by rw [if_neg (by omega)]⟩
  | succ n ih =>
    obtain ⟨u, hu, hq, hreg⟩ := ih
    have w : Run emptyLanguage (.write (start + n) .empty) u (u.write (start + n) []) 1 0 := .write
    have seq := Run.seq hu w
    refine ⟨u.write (start + n) [], ?_, hq, fun r => ?_⟩
    · simpa only [clearRange, Nat.add_zero,
        show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by omega] using seq
    · by_cases e : r = start + n
      · subst r
        rw [reg_write_same, if_pos (by omega)]
      · rw [reg_write_other _ _ _ _ e, hreg]
        have same : (start ≤ r ∧ r < start + n) ↔ (start ≤ r ∧ r < start + (n + 1)) := by omega
        simp only [same]

private theorem run_cleanQueue (s : State) (base scratch : Nat) (hs : scratch ≠ base)
    (pending suffix : List Word) (hq : s.queries = pending ++ suffix)
    (hm : s.reg base = List.replicate pending.length true) :
    ∃ u, Run emptyLanguage (cleanQueue base scratch) s u (4 * pending.length + 1) 0 ∧
      u.queries = suffix ∧ ∀ r, r ≠ base → r ≠ scratch → u.reg r = s.reg r := by
  induction pending generalizing s with
  | nil =>
    refine ⟨s, ?_, by simpa using hq, fun _ _ _ => rfl⟩
    exact Run.loopFalse (by simp [Test.eval, hm])
  | cons w rest ih =>
    let mid := (frameDrop s base).write scratch (s.queries.headD [])
    have midQueue : mid.queries = rest ++ suffix := by simp [mid, frameDrop, State.write, State.drop, hq]
    have midMarker : mid.reg base = List.replicate rest.length true := by
      simp [mid, frameDrop, reg_write_other, reg_write_same, State.drop, Ne.symm hs, hm, List.replicate_succ]
    obtain ⟨u, r, uq, ur⟩ := ih mid midQueue midMarker
    have nonempty : (Test.head base).eval s = true := by simp [Test.eval, hm, List.replicate_succ]
    have loop := Run.loopTrue nonempty (run_takeQueue base scratch (s := s)) r
    refine ⟨u, ?_, uq, fun i hb hs => ?_⟩
    · simpa only [cleanQueue, List.length_cons,
        show 3 + (4 * rest.length + 1) + 1 = 4 * (rest.length + 1) + 1 by omega] using loop
    · rw [ur i hb hs, reg_write_other _ _ _ _ hs]
      exact reg_write_other _ _ _ _ hb

private theorem advance_queue_bound (src : Source) (s : State) :
    (src.advance s).queries.length ≤ s.queries.length := by
  cases src with
  | reg => exact Nat.le_refl _
  | queued => simp [Source.advance, State.drop]

private theorem run_queue_bound (h : Run A c s u t q) :
    u.queries.length ≤ s.queries.length + t := by
  induction h with
  | skip | write | loopFalse => exact Nat.le_succ _
  | push => exact Nat.le_refl _
  | @pop d s => exact Nat.le_succ_of_le (advance_queue_bound .queued s)
  | seq _ _ ih₁ ih₂ | loopTrue _ _ _ ih₁ ih₂ => omega
  | branch _ _ ih => omega
  | @askEmpty src d s _ | @askSome _ _ src d s _ _
    | @callEmpty src d _ s _ | @callSome _ _ _ _ _ src d s _ _ _ =>
    exact Nat.le_trans (advance_queue_bound src s) (by omega)

private theorem at_child (base width i : Nat) (hi : i < width) :
    slot base i < child width base := by
  unfold child slot
  omega

private theorem not_child_slot (base width i r : Nat) (hi : i < width) :
    slot base i ≠ slot (child width base) r := by
  have h := at_child base width i hi
  unfold slot at *
  omega

private theorem frame_global (base : Nat) (hb : 4 ≤ base) (r : Nat) (hr : r < 4) :
    r ≠ base ∧ ∀ i, r ≠ slot base i := by
  refine ⟨by omega, fun i => ?_⟩
  unfold slot
  omega

private theorem frame_writeGlobal (h : FrameView width base s suffix m)
    (hb : 4 ≤ base) (r : Nat) (hr : r < 4) (w : Word) :
    FrameView width base s suffix (m.write r w) :=
  h.writeOutside (frame_global base hb r hr).1 (fun i _ => (frame_global base hb r hr).2 i) w

private theorem run_callEntry {u parent initial : State} {width base d cost : Nat}
    {body : Code} {suffix : List Word} {w bits tail : Word}
    (hb : 4 ≤ base) (hw : 0 < width)
    (view : FrameView width base parent suffix initial)
    (input : initial.reg (slot (child width base) 0) = w)
    (htape : initial.reg 0 = bits ++ tail)
    (childSim : ∀ start,
      FrameView width (child width base) (State.input w) initial.queries start →
      start.reg 0 = bits ++ tail →
      ∃ out t, Run emptyLanguage (lower width (child width base) body) start out t 0 ∧
        FrameView width (child width base) u initial.queries out ∧
        out.reg 0 = tail ∧ out.reg 1 = start.reg 1 ∧ t ≤ cost) :
    ∃ out t, Run emptyLanguage
      (.write (child width base) .empty ▷
        clearRange (slot (child width base) 1) (width - 1) ▷
        lower width (child width base) body ▷
        cleanQueue (child width base) (child width (child width base)) ▷
        .callBit (.reg (slot (child width base) 0)) (slot base d) .skip)
      initial out t 0 ∧
      FrameView width base (parent.write d [decide (u.output = [true])]) suffix out ∧
      out.reg 0 = tail ∧ out.reg 1 = initial.reg 1 ∧
      t ≤ cost + (2 * width + 9 + 4 * u.queries.length) := by
  let next := child width base
  have hn : base < next := by unfold next child slot; omega
  let marked := initial.write next []
  have startMark : Run emptyLanguage (.write next .empty) initial marked 1 0 := .write
  obtain ⟨ready, setup, setupStack, setupReg⟩ := run_clearRange marked (slot next 1) (width - 1)
  have preserved (r : Nat) (hr : r < next) : ready.reg r = initial.reg r := by
    rw [setupReg, if_neg (by unfold slot; omega), reg_write_other _ _ _ _ (by omega)]
  have readyView : FrameView width next (State.input w) initial.queries ready := by
    refine ⟨fun i hi => ?_, ?_, by simpa [marked, State.input, State.write] using setupStack⟩
    · cases i with
      | zero =>
        rw [setupReg, if_neg (by unfold slot; omega), reg_write_other _ _ _ _ (by unfold slot; omega)]
        simpa [next, State.input] using input
      | succ i =>
        rw [setupReg, if_pos (by unfold slot; omega)]
        simp [State.input]
    · rw [setupReg, if_neg (by unfold slot; omega), reg_write_same]
      rfl
  obtain ⟨finished, bodyTime, childRun, childView, childTape, childOK, childBound⟩ :=
    childSim ready readyView ((preserved 0 (by omega)).trans htape)
  have flat := lower_flat (p := fun r => r = 0 ∨ r = 1 ∨ next ≤ r)
    (Or.inl rfl) (Or.inr (Or.inl rfl)) width next (fun _ h => Or.inr (Or.inr h)) body
  have childPreserved (r : Nat) (hl : 2 ≤ r) (hr : r < next) :
      finished.reg r = initial.reg r :=
    (run_reg_outside childRun flat (by change ¬ (r = 0 ∨ r = 1 ∨ next ≤ r); omega)).trans (preserved r hr)
  let scratch := child width next
  have hscratch : next < scratch := by unfold scratch child slot; omega
  obtain ⟨cleaned, cleanRun, cleanStack, cleanRegs⟩ :=
    run_cleanQueue finished next scratch (by omega) u.queries initial.queries
      childView.stack childView.marker
  have cleanLocal (r : Nat) (hl : 2 ≤ r) (hr : r < next) :
      cleaned.reg r = initial.reg r :=
    (cleanRegs r (by omega) (by omega)).trans (childPreserved r hl hr)
  have cleanParent : FrameView width base parent suffix cleaned :=
    ⟨fun i hi => (cleanLocal _ (by unfold slot; omega) (at_child base width i hi)).trans
        (view.register i hi),
      (cleanLocal _ (by omega) hn).trans view.marker,
      cleanStack.trans view.stack⟩
  have returnVal : cleaned.reg (slot next 0) = u.output := by
    have ne : slot next 0 ≠ scratch := Nat.ne_of_lt (at_child next width 0 hw)
    rw [cleanRegs (slot next 0) (by unfold slot; omega) ne]
    exact childView.register 0 hw
  let result := cleaned.write (slot base d) [decide (u.output = [true])]
  have ret : Run emptyLanguage (.callBit (.reg (slot next 0)) (slot base d) .skip)
      cleaned result 2 0 := by
    have he : (Source.reg (slot next 0)).read cleaned = some u.output := congrArg some returnVal
    simpa [result, State.output, State.input, Source.advance] using
      (Run.callSome (A := emptyLanguage) (d := slot base d) he
        (Run.skip (A := emptyLanguage) (s := State.input u.output)))
  refine ⟨result, _, .seq startMark (.seq setup (.seq childRun (.seq cleanRun ret))),
    cleanParent.writeFrame d _, ?_, ?_, by omega⟩
  · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans
      ((cleanRegs 0 (by omega) (by omega)).trans childTape)
  · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans
      ((cleanRegs 1 (by omega) (by omega)).trans
        (childOK.trans (preserved 1 (by omega))))


private theorem drop_empty {s : State} (h : s.queries = []) : s.drop = s := by
  cases s with
  | mk regs queries =>
    change queries = [] at h
    subst queries
    rfl

private theorem run_readBit_view (h : FrameView width base s suffix m) (hb : 4 ≤ base)
    (d : Nat) (htape : m.reg 0 = bit :: tail) :
    ∃ out, Run emptyLanguage (readBit (slot base d)) m out 7 0 ∧
      FrameView width base (s.write d [bit]) suffix out ∧
      out.reg 0 = tail ∧ out.reg 1 = m.reg 1 := by
  refine ⟨_, run_readBit _ (by unfold slot; omega) htape,
    frame_writeGlobal (h.writeFrame d [bit]) hb 0 (by decide) tail,
    reg_write_same .., ?_⟩
  rw [reg_write_other _ _ _ _ (by decide), reg_write_other _ _ _ _ (by unfold slot; omega)]

/-- The flattened execution uses at most this many instructions per source
instruction when the source execution is capped by `budget`. The term
linear in `budget` pays for clearing a scoped call's private stack. -/
def loweringCost (width budget : Nat) : Nat := 2 * width + 20 + 4 * budget

private def Simulates (width : Nat) (c : Code) (s u : State) (bits : Word) (cost : Nat) : Prop :=
  ∀ base, 4 ≤ base → ∀ suffix initial tail,
    FrameView width base s suffix initial → initial.reg 0 = bits ++ tail →
    ∃ out t, Run emptyLanguage (lower width base c) initial out t 0 ∧
      FrameView width base u suffix out ∧
      out.reg 0 = tail ∧ out.reg 1 = initial.reg 1 ∧ t ≤ cost

private theorem lower_unmetered_correct (run : Run A c s u t q)
    (width budget : Nat) (hw : 0 < width) (uses : UsesRegisters width c) (ht : t ≤ budget) :
    ∃ bits : Word, bits.length = q ∧ Simulates width c s u bits (loweringCost width budget * t) := by
  let K := loweringCost width budget
  have big : 20 ≤ K := by unfold K loweringCost; omega
  change ∃ bits : Word, bits.length = q ∧ Simulates width c s u bits (K * t)
  induction run with
  | skip =>
    refine ⟨[], rfl, fun base hb suffix m tail h hs => ⟨m, 1, .skip, h, hs, rfl, ?_⟩⟩
    simpa only [Nat.mul_one] using (show 1 ≤ K by omega)
  | @write d e s =>
    refine ⟨[], rfl, fun base hb suffix m tail view tape => ?_⟩
    have written : Run emptyLanguage (.write (slot base d) (Expr.rename (slot base) e))
        m (m.write (slot base d) (e.eval s)) 1 0 := by
      rw [← view.renameExpr e uses.2]
      exact .write
    refine ⟨_, 1, written, view.writeFrame d _, ?_, ?_, ?_⟩
    · exact (reg_write_other _ _ _ _ (by unfold slot; omega)).trans tape
    · exact reg_write_other _ _ _ _ (by unfold slot; omega)
    · simpa only [Nat.mul_one] using (show 1 ≤ K by omega)
  | @push r s =>
    refine ⟨[], rfl, fun base hb suffix m tail view tape => ?_⟩
    have push : Run emptyLanguage (lower width base (.push r)) m
        ((m.push (slot base r)).write base (true :: m.reg base)) 3 0 :=
      .seq (show Run emptyLanguage (.push (slot base r)) m (m.push (slot base r)) 1 0 from .push)
        .write
    refine ⟨_, 3, push, view.pushFrame r uses, ?_, ?_, ?_⟩
    · exact (reg_write_other _ _ _ _ (by omega)).trans tape
    · exact reg_write_other _ _ _ _ (by omega)
    · simpa only [Nat.mul_one] using (show 3 ≤ K by omega)
  | @pop d s =>
    refine ⟨[], rfl, fun base hb suffix m tail view tape => ?_⟩
    cases hq : s.queries with
    | nil =>
      have r : Run emptyLanguage (lower width base (.pop d)) m (m.write (slot base d) []) 2 0 :=
        run_branch_true (view.queueEmpty hq) .write
      have out : FrameView width base (s.drop.write d (s.queries.headD [])) suffix
          (m.write (slot base d) []) := by
        simpa [hq, drop_empty hq] using view.writeFrame d []
      refine ⟨_, 2, r, by simpa only [hq] using out, (reg_write_other _ _ _ _ (by unfold slot; omega)).trans tape,
        reg_write_other _ _ _ _ (by unfold slot; omega), ?_⟩
      simpa only [Nat.mul_one] using (show 2 ≤ K by omega)
    | cons w rest =>
      have head : m.queries.headD [] = w := by simp [view.stack, hq]
      let out := (frameDrop m base).write (slot base d) w
      have r : Run emptyLanguage (lower width base (.pop d)) m out 4 0 :=
        run_branch_false (view.queueNonempty hq) (by simpa only [out, head] using run_takeQueue (s := m) base (slot base d))
      have upd : FrameView width base (s.drop.write d (s.queries.headD [])) suffix out := by
        simpa [out, hq] using (view.dropFrame hq).writeFrame d w
      have outside (i : Nat) (hi : i < 4) : out.reg i = m.reg i := by
        rw [reg_write_other _ _ _ _ (by unfold slot; omega)]
        exact reg_write_other _ _ _ _ (by omega)
      refine ⟨_, 4, r, by simpa only [hq] using upd, (outside 0 (by decide)).trans tape, outside 1 (by decide), ?_⟩
      simpa only [Nat.mul_one] using (show 4 ≤ K by omega)
  | @seq a s mid t₁ q₁ b u t₂ q₂ ra rb iha ihb =>
    obtain ⟨left, lenL, simL⟩ := iha uses.1 (by omega)
    obtain ⟨right, lenR, simR⟩ := ihb uses.2 (by omega)
    refine ⟨left ++ right, by simp [lenL, lenR], fun base hb suffix m tail view tape => ?_⟩
    obtain ⟨v, ta, va, viewL, tapeL, okL, boundL⟩ :=
      simL base hb suffix m (right ++ tail) view (by simpa only [List.append_assoc] using tape)
    obtain ⟨out, tb, vb, viewR, tapeR, okR, boundR⟩ := simR base hb suffix v tail viewL tapeL
    refine ⟨out, ta + tb + 1, .seq va vb, viewR, tapeR, okR.trans okL, ?_⟩
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  | @branch bit s u t q test yes no he ra ih =>
    have choice : UsesRegisters width (if bit then yes else no) := by
      cases bit
      · exact uses.2.2
      · exact uses.2.1
    obtain ⟨bits, len, sim⟩ := ih choice (by omega)
    refine ⟨bits, len, fun base hb suffix m tail view tape => ?_⟩
    obtain ⟨out, cost, hr, ho, tape', ok, bound⟩ := sim base hb suffix m tail view tape
    have branch : Run emptyLanguage (lower width base (.branch test yes no)) m out (cost + 1) 0 := by
      apply Run.branch ((view.renameTest test uses.1).trans he)
      cases bit <;> exact hr
    refine ⟨out, cost + 1, branch, ho, tape', ok, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  | @loopFalse test body s he =>
    refine ⟨[], rfl, fun base hb suffix m tail h hs => ?_⟩
    refine ⟨m, 1, .loopFalse ((h.renameTest test uses.1).trans he), h, hs, rfl, ?_⟩
    simpa only [Nat.mul_one] using (show 1 ≤ K by omega)
  | @loopTrue body s mid t₁ q₁ test u t₂ q₂ he ra rb iha ihb =>
    obtain ⟨left, lenL, simL⟩ := iha uses.2 (by omega)
    obtain ⟨right, lenR, simR⟩ := ihb uses (by omega)
    refine ⟨left ++ right, by simp [lenL, lenR], fun base hb suffix m tail view tape => ?_⟩
    obtain ⟨v, ta, va, viewL, tapeL, okL, boundL⟩ :=
      simL base hb suffix m (right ++ tail) view (by simpa only [List.append_assoc] using tape)
    obtain ⟨out, tb, vb, viewR, tapeR, okR, boundR⟩ := simR base hb suffix v tail viewL tapeL
    refine ⟨out, ta + tb + 1, .loopTrue ((view.renameTest test uses.1).trans he) va vb,
      viewR, tapeR, okR.trans okL, ?_⟩
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  | @askEmpty src d s he =>
    cases src with
    | reg => simp [Source.read] at he
    | queued =>
      have hq : s.queries = [] := by cases h : s.queries <;> simp_all [Source.read]
      refine ⟨[], rfl, fun base hb suffix m tail view tape => ?_⟩
      have r : Run emptyLanguage (lower width base (.ask .queued d)) m
          (m.write (slot base d) [false]) 4 0 :=
        run_branch_true (view.queueEmpty hq) (run_setBit m _ _)
      refine ⟨_, 4, r, ?_, (reg_write_other _ _ _ _ (by unfold slot; omega)).trans tape,
        reg_write_other _ _ _ _ (by unfold slot; omega), ?_⟩
      · simpa [Source.advance, drop_empty hq] using view.writeFrame d [false]
      · simpa only [Nat.mul_one] using (show 4 ≤ K by omega)
  | @askSome w bit src d s he genuine =>
    refine ⟨[bit], rfl, fun base hb suffix m tail view tape => ?_⟩
    cases src with
    | reg =>
      obtain ⟨out, r, ho, tape', ok⟩ := run_readBit_view view hb d tape
      exact ⟨out, 7, r, ho, tape', ok, by simpa only [Nat.mul_one] using (show 7 ≤ K by omega)⟩
    | queued =>
      cases hq : s.queries with
      | nil => simp [Source.read, hq] at he
      | cons z rest =>
        let mid := (frameDrop m base).write (slot base d) (m.queries.headD [])
        have midView := (view.dropFrame hq).writeFrame d (m.queries.headD [])
        have outside (i : Nat) (hi : i < 4) : mid.reg i = m.reg i := by
          rw [reg_write_other _ _ _ _ (by unfold slot; omega)]
          exact reg_write_other _ _ _ _ (by omega)
        obtain ⟨out, r, ho, tape', ok⟩ :=
          run_readBit_view midView hb d ((outside 0 (by decide)).trans tape)
        have rb : Run emptyLanguage (lower width base (.ask .queued d)) m out 12 0 :=
          run_branch_false (view.queueNonempty hq) (.seq (run_takeQueue base (slot base d)) r)
        have overwrite : (s.drop.write d (m.queries.headD [])).write d [bit] = s.drop.write d [bit] := by
          simp only [State.write]
          congr
          funext i
          split <;> simp_all
        rw [overwrite] at ho
        refine ⟨out, 12, rb, ho, tape', ok.trans (outside 1 (by decide)), ?_⟩
        simpa only [Nat.mul_one] using (show 12 ≤ K by omega)
  | @callEmpty src d body s he =>
    cases src with
    | reg => simp [Source.read] at he
    | queued =>
      have hq : s.queries = [] := by cases h : s.queries <;> simp_all [Source.read]
      refine ⟨[], rfl, fun base hb suffix m tail view tape => ?_⟩
      have r : Run emptyLanguage (lower width base (.callBit .queued d body)) m
          (m.write (slot base d) [false]) 4 0 :=
        run_branch_true (view.queueEmpty hq) (run_setBit m _ _)
      refine ⟨_, 4, r, ?_, (reg_write_other _ _ _ _ (by unfold slot; omega)).trans tape,
        reg_write_other _ _ _ _ (by unfold slot; omega), ?_⟩
      · simpa [Source.advance, drop_empty hq] using view.writeFrame d [false]
      · simpa only [Nat.mul_one] using (show 4 ≤ K by omega)
  | @callSome w body u t q src d s he childRun ih =>
    obtain ⟨bits, len, sim⟩ := ih uses.2.2 (by omega)
    have pushed : u.queries.length ≤ budget := by
      have b := run_queue_bound childRun
      simp only [State.input, List.length_nil, Nat.zero_add] at b
      omega
    refine ⟨bits, len, fun base hb suffix m tail view tape => ?_⟩
    let next := child width base
    have nextGreater : base < next := by unfold next child slot; omega
    have nextInputGreater : next < slot next 0 := by unfold slot; omega
    have childSim (a : State) := sim next (by omega) a.queries
    cases src with
    | reg r =>
      have orig : s.reg r = w := Option.some.inj he
      let start := m.write (slot next 0) w
      have move : Run emptyLanguage (.write (slot next 0) (.copy (slot base r))) m start 1 0 := by
        have value : m.reg (slot base r) = w := (view.register r uses.1).trans orig
        simpa [start, Expr.eval, value] using
          (Run.write (A := emptyLanguage) (s := m) (d := slot next 0) (e := .copy (slot base r)))
      have after : FrameView width base s suffix start :=
        view.writeOutside (Nat.ne_of_gt (Nat.lt_trans nextGreater nextInputGreater))
          (fun i hi => Ne.symm (not_child_slot base width i 0 hi)) w
      have itape : start.reg 0 = bits ++ tail := (reg_write_other _ _ _ _ (by omega)).trans tape
      obtain ⟨out, cost, r, final, tape', ok, bound⟩ :=
        run_callEntry (d := d) hb hw after (reg_write_same ..) itape
          (fun m hm htape => childSim start m tail hm htape)
      refine ⟨out, 1 + cost + 1, .seq move r, final, tape',
        ok.trans (reg_write_other _ _ _ _ (by omega)), ?_⟩
      rw [Nat.mul_add, Nat.mul_one]
      unfold K loweringCost at *
      omega
    | queued =>
      cases hq : s.queries with
      | nil => simp [Source.read, hq] at he
      | cons z rest =>
        have orig : z = w := Option.some.inj (by simpa only [Source.read, hq, List.head?_cons] using he)
        have head : m.queries.headD [] = w := by simp [view.stack, hq, orig]
        let start := (frameDrop m base).write (slot next 0) w
        have move : Run emptyLanguage (takeQueue base (slot next 0)) m start 3 0 := by
          simpa only [start, head] using run_takeQueue (s := m) base (slot next 0)
        have after : FrameView width base s.drop suffix start :=
          (view.dropFrame hq).writeOutside (Nat.ne_of_gt (Nat.lt_trans nextGreater nextInputGreater))
            (fun i hi => Ne.symm (not_child_slot base width i 0 hi)) w
        have outside (i : Nat) (hi : i < 4) : start.reg i = m.reg i := by
          rw [reg_write_other _ _ _ _ (by omega)]
          exact reg_write_other _ _ _ _ (by omega)
        obtain ⟨out, cost, r, final, tape', ok, bound⟩ :=
          run_callEntry (d := d) hb hw after (reg_write_same ..)
            ((outside 0 (by decide)).trans tape)
            (fun m hm htape => childSim start m tail hm htape)
        refine ⟨out, 3 + cost + 1 + 1, run_branch_false (view.queueNonempty hq) (.seq move r),
          final, tape', ok.trans (outside 1 (by decide)), ?_⟩
        rw [Nat.mul_add, Nat.mul_one]
        unfold K loweringCost at *
        omega


private def Expr.addresses : Expr → List Nat
  | .empty => []
  | .copy r | .tail r | .cons _ r => [r]

private def Test.addresses : Test → List Nat
  | .empty r | .head r => [r]

private def Source.addresses : Source → List Nat
  | .reg r => [r]
  | .queued => []

private def addresses : Code → List Nat
  | .skip => []
  | .write d e => d :: Expr.addresses e
  | .push r | .pop r => [r]
  | .seq a b => addresses a ++ addresses b
  | .branch test a b => Test.addresses test ++ addresses a ++ addresses b
  | .loop test b => Test.addresses test ++ addresses b
  | .ask src d => Source.addresses src ++ [d]
  | .callBit src d b => Source.addresses src ++ d :: addresses b

/-- Compute the register-frame width from the fixed source syntax. -/
def frameWidth (c : Code) : Nat :=
  (addresses c).foldr (fun i limit => max (i + 1) limit) 1

theorem frameWidth_positive (c : Code) : 0 < frameWidth c := by
  unfold frameWidth
  induction addresses c with
  | nil => decide
  | cons i tail ih => exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

theorem frameWidth_uses (c : Code) : UsesRegisters (frameWidth c) c := by
  have expr (width : Nat) (e : Expr) :
      Expr.atRegisters (· < width) e ↔ ∀ i ∈ Expr.addresses e, i < width := by
    cases e <;> simp [Expr.addresses, Expr.atRegisters]
  have test (width : Nat) (t : Test) :
      Test.atRegisters (· < width) t ↔ ∀ i ∈ Test.addresses t, i < width := by
    cases t <;> simp [Test.addresses, Test.atRegisters]
  have src (width : Nat) (s : Source) :
      Source.atRegisters (· < width) s ↔ ∀ i ∈ Source.addresses s, i < width := by
    cases s <;> simp [Source.addresses, Source.atRegisters]
  have registered (width : Nat) (c : Code) :
      UsesRegisters width c ↔ ∀ i ∈ addresses c, i < width := by
    induction c <;> simp_all [addresses, UsesRegisters, expr, test, src,
      List.forall_mem_append, or_imp, forall_and, and_assoc]
  rw [registered]
  unfold frameWidth
  induction addresses c with
  | nil => simp
  | cons i tail ih =>
    simp only [List.foldr_cons, List.mem_cons]
    intro r h
    rcases h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih _ h) (Nat.le_max_right _ _)

/-- A loadable initial state for a compiled run. The original input lives in
the root frame and the answer tape and clock have dedicated registers.
The stack suffix can hold data belonging to the caller. -/
def replayInput (base : Nat) (x tape : Word) (clock : Nat) (suffix : List Word := []) : State :=
  ⟨fun r => if r = 0 then tape else if r = 2 then clockWord clock else
    if r = slot base 0 then x else [], suffix⟩

theorem replayInput_view (width base : Nat) (hb : 4 ≤ base) (x tape : Word)
    (clock : Nat) (suffix : List Word) :
    FrameView width base (State.input x) suffix (replayInput base x tape clock suffix) := by
  refine ⟨fun i hi => ?_, ?_, rfl⟩
  · have noZero : slot base i ≠ 0 := by unfold slot; omega
    have noTwo : slot base i ≠ 2 := by unfold slot; omega
    have same : slot base i = slot base 0 ↔ i = 0 := by unfold slot; omega
    simp [replayInput, State.input, noZero, noTwo, same]
  · have diff : base ≠ slot base 0 := by unfold slot; omega
    simp [replayInput, State.input, show base ≠ 0 by omega, show base ≠ 2 by omega, diff]

/-- An actual `Run` survives the oracle-free compilation. Its tape depends
only on the source run. The same tape works with any extra unread suffix. -/
theorem compiledReplay_correct (run : Run A c s u t q) (budget base : Nat)
    (hb : 4 ≤ base) (ht : t ≤ budget) :
    let width := frameWidth c
    let clock := loweringCost width budget * budget
    ∃ bits : Word, bits.length = q ∧ ∀ suffix initial remaining,
      FrameView width base s suffix initial →
      initial.reg 0 = bits ++ remaining →
      initial.reg 2 = clockWord clock →
      ∃ out elapsed left, Run emptyLanguage (compiledReplay width base c) initial out elapsed 0 ∧
        FrameView width base u suffix out ∧ out.reg 0 = remaining ∧
        out.reg 1 = initial.reg 1 ∧ out.reg 2 = clockWord left ∧ elapsed ≤ 20 * (clock + 1) := by
  dsimp only
  let width := frameWidth c
  let clock := loweringCost width budget * budget
  obtain ⟨bits, len, sim⟩ := lower_unmetered_correct run width budget
    (frameWidth_positive c) (frameWidth_uses c) ht
  refine ⟨bits, len, fun suffix initial remaining view tape gas => ?_⟩
  obtain ⟨unmetered, time, hrun, hv, unread, miss, bound⟩ :=
    sim base hb suffix initial remaining view tape
  let p (r : Nat) := r = 0 ∨ r = 1 ∨ base ≤ r
  have inFrame (i : Nat) (hi : base ≤ i) : p i := Or.inr (Or.inr hi)
  have flat : FlatUsing p (lower width base c) :=
    lower_flat (Or.inl rfl) (Or.inr (Or.inl rfl)) width base inFrame c
  have enough : time ≤ clock := Nat.le_trans bound (Nat.mul_le_mul_left _ ht)
  obtain ⟨out, elapsed, left, replay, agree, leftClock, _⟩ :=
    metered_correct (by decide : 2 ≠ 3)
      (by change ¬ (2 = 0 ∨ 2 = 1 ∨ base ≤ 2); omega)
      (by change ¬ (3 = 0 ∨ 3 = 1 ∨ base ≤ 3); omega)
      hrun flat ⟨rfl, fun _ _ => rfl⟩ gas enough
  obtain ⟨other, otherTime, otherRun, otherBound⟩ :=
    compiledReplay_total width base hb c gas
  obtain ⟨_, eqTime, _⟩ := replay.deterministic otherRun
  refine ⟨out, elapsed, left, replay,
    ⟨fun i hi => (agree.2 _ (inFrame _ (by unfold slot; omega))).trans (hv.register i hi),
      (agree.2 _ (inFrame _ (by omega))).trans hv.marker, agree.1.trans hv.stack⟩,
    (agree.2 _ (Or.inl rfl)).trans unread, (agree.2 _ (Or.inr (Or.inl rfl))).trans miss,
    leftClock, ?_⟩
  omega

/-- On genuine machine input, there is a same-length padded tape for which
the concrete oracle-free replay returns the source program's output. -/
theorem compiledReplay_genuine (run : Run A c (State.input x) u t q)
    (base budget cap : Nat) (hb : 4 ≤ base) (ht : t ≤ budget) (hq : q ≤ cap) :
    let width := frameWidth c
    let clock := loweringCost width budget * budget
    ∃ tape : Word, tape.length = cap ∧ ∀ suffix,
      ∃ out elapsed left,
        Run emptyLanguage (compiledReplay width base c) (replayInput base x tape clock suffix)
          out elapsed 0 ∧
        out.reg (slot base 0) = u.output ∧ out.reg 1 = [] ∧
        out.reg 2 = clockWord left ∧ elapsed ≤ 20 * (clock + 1) := by
  dsimp only
  obtain ⟨bits, len, replay⟩ := compiledReplay_correct run budget base hb ht
  let rest := List.replicate (cap - q) false
  let tape := bits ++ rest
  refine ⟨tape, by simp [tape, rest, len]; omega, fun suffix => ?_⟩
  let width := frameWidth c
  let clock := loweringCost width budget * budget
  obtain ⟨out, elapsed, left, hr, view, _, hm, hleft, htime⟩ :=
    replay suffix (replayInput base x tape clock suffix) rest
      (replayInput_view width base hb x tape clock suffix)
      (by simp [replayInput, tape]) (by rfl)
  refine ⟨out, elapsed, left, hr, view.register 0 (frameWidth_positive c), ?_, hleft, htime⟩
  rw [hm]
  simp [replayInput, show 1 ≠ slot base 0 by unfold slot; omega]


/-- Every tape of a fixed width, including the empty tape at width zero. -/
def tapes : Nat → List Word
  | 0 => [[]]
  | n + 1 => (tapes n).map (false :: ·) ++ (tapes n).map (true :: ·)

theorem mem_tapes {tape : Word} {cap : Nat} : tape ∈ tapes cap ↔ tape.length = cap := by
  induction cap generalizing tape with
  | zero => simp [tapes]
  | succ n ih =>
    cases tape with
    | nil => simp [tapes]
    | cons b w =>
      cases b <;> simp [tapes, List.mem_map, ih]

theorem tapes_length (cap : Nat) : (tapes cap).length = 2 ^ cap := by
  induction cap with
  | zero => rfl
  | succ n ih => simp [tapes, ih, Nat.pow_succ, Nat.mul_two]

private theorem replay_zero_queries (path : Path A c d t q) (hq : q = 0)
    (stop : d.step = .halt s) (enough : t ≤ clock) :
    c.replay clock [] = some (s, clock - t, []) := by
  induction path generalizing clock with
  | refl => rw [Config.replay, stop, Nat.sub_zero]
  | @next d e t q c hs path ih =>
    cases clock with
    | zero => omega
    | succ clock =>
      rw [Config.replay, hs]
      have enough' : t ≤ clock := Nat.le_of_succ_le_succ enough
      change d.replay clock [] = some (s, clock + 1 - (t + 1), [])
      rw [show clock + 1 - (t + 1) = clock - t by omega]
      exact ih (clock := clock) hq stop enough'
  | ask => omega

-- The model implements register updates as functions layered over older
-- states. Cache the addresses used by the fixed code after a transition so
-- executable replay does not recurse through the whole update history.
private def cacheRegisters (used : List Nat) (s : State) : State :=
  let values := used.map (fun r => (r, s.reg r))
  ⟨fun r =>
    match values.find? (fun entry => entry.1 == r) with
    | none => s.reg r
    | some entry => entry.2, s.queries⟩

private theorem cacheRegisters_eq (used : List Nat) (s : State) : cacheRegisters used s = s := by
  cases s with
  | mk reg queries =>
    dsimp only [cacheRegisters]
    congr
    funext i
    split
    · rfl
    · rename_i entry found
      have mem := List.mem_of_find?_eq_some found
      obtain ⟨r, _, same⟩ := List.mem_map.mp mem
      have key := List.find?_some found
      rw [← same] at key ⊢
      simp_all

private def cacheConfig (used : List Nat) : Config → Config
  | .exec c s frames => .exec c (cacheRegisters used s) frames
  | .resume s frames => .resume (cacheRegisters used s) frames

private theorem cacheConfig_eq (used : List Nat) (c : Config) : cacheConfig used c = c := by
  cases c <;> simp [cacheConfig, cacheRegisters_eq]

private def cachedReplay (used : List Nat) (clock : Nat) (c : Config) (answers : Word) :
    Option (State × Nat × Word) :=
  match (cacheConfig used c).step with
  | .halt s => some (s, clock, answers)
  | .next d =>
    match clock with
    | 0 => none
    | k + 1 => cachedReplay used k d answers
  | .question _ no yes =>
    match clock, answers with
    | k + 1, bit :: rest => cachedReplay used k (if bit then yes else no) rest
    | _, _ => none
termination_by clock

private theorem cachedReplay_eq (used : List Nat) (clock : Nat) (c : Config) (answers : Word) :
    cachedReplay used clock c answers = c.replay clock answers := by
  induction clock generalizing c answers with
  | zero => rw [cachedReplay, cacheConfig_eq, Config.replay]
  | succ k ih =>
    rw [cachedReplay, cacheConfig_eq, Config.replay]
    cases c.step with
    | halt => rfl
    | next => exact ih _ _
    | question =>
      cases answers with
      | nil => rfl
      | cons => exact ih _ _

/-- Replay fixed code with a cache of its registers and any additional
addresses that the caller will read from the returned state. -/
def replayCode (c : Code) (s : State) (clock : Nat) (answers : Word)
    (readBack : List Nat := [0]) : Option (State × Nat × Word) :=
  cachedReplay (readBack ++ addresses c).eraseDups clock (.exec c s []) answers

theorem replayCode_eq (c : Code) (s : State) (clock : Nat) (answers : Word)
    (readBack : List Nat) :
    replayCode c s clock answers readBack = (Config.exec c s []).replay clock answers :=
  cachedReplay_eq ..

/-- Oracle-free computations can be executed without knowing their accepting
predicates. The replay clock accounts for control frames as well as steps. -/
theorem replayCode_of_run {c : Code} {s u : State} {t clock : Nat}
    (run : Run emptyLanguage c s u t 0) (enough : 2 * t ≤ clock) :
    ∃ left, replayCode c s clock [] = some (u, left, []) := by
  obtain ⟨k, hk, path⟩ := run.toPath []
  exact ⟨clock - k, by
    rw [replayCode_eq]
    exact replay_zero_queries path rfl rfl (Nat.le_trans hk enough)⟩

/-- Execute the concrete oracle-free replay program and report its word
when both clocks permit the path to finish. The argument `budget` is the
source runtime used to size the compiled program's instruction clock. -/
def compiledTapeOutput (c : Code) (x tape : Word) (budget : Nat) : Option Word :=
  let width := frameWidth c
  let clock := loweringCost width budget * budget
  let program := compiledReplay width 4 c
  let start := replayInput 4 x tape clock
  match replayCode program start (2 * (20 * (clock + 1))) [] [1, 2, slot 4 0] with
  | none => none
  | some (out, _, _) =>
    if out.reg 1 = [] ∧ out.reg 2 ≠ [] then some (out.reg (slot 4 0)) else none

theorem compiledTapeOutput_run {c : Code} {x tape : Word} {budget : Nat}
    (run : Run emptyLanguage (compiledReplay (frameWidth c) 4 c)
      (replayInput 4 x tape (loweringCost (frameWidth c) budget * budget)) u t 0)
    (ht : t ≤ 20 * (loweringCost (frameWidth c) budget * budget + 1)) :
    compiledTapeOutput c x tape budget =
      if u.reg 1 = [] ∧ u.reg 2 ≠ [] then some (u.reg (slot 4 0)) else none := by
  obtain ⟨k, hk, path⟩ := run.toPath []
  have hs := replay_zero_queries path rfl rfl (Nat.le_trans hk (Nat.mul_le_mul_left 2 ht))
  simp only [compiledTapeOutput, replayCode_eq, hs]

/-- Each output here comes from a run of a concrete register-machine program
on one tape. Tape generation and collection are Lean list operations. -/
def compiledCandidates (c : Code) (x : Word) (budget cap : Nat) : List Word :=
  (tapes cap).filterMap (fun tape => compiledTapeOutput c x tape budget)

theorem compiledCandidates_length (c : Code) (x : Word) (budget cap : Nat) :
    (compiledCandidates c x budget cap).length ≤ 2 ^ cap := by
  rw [← tapes_length cap]
  exact List.length_filterMap_le ..

theorem run_mem_compiledCandidates (run : Run A c (State.input x) u t q)
    (ht : t ≤ budget) (hq : q ≤ cap) :
    u.output ∈ compiledCandidates c x budget cap := by
  obtain ⟨tape, len, compiled⟩ := compiledReplay_genuine run 4 budget cap (by decide) ht hq
  obtain ⟨out, elapsed, left, hrun, hval, hmiss, hclock, htime⟩ := compiled []
  refine List.mem_filterMap.mpr ⟨tape, mem_tapes.mpr len, ?_⟩
  change compiledTapeOutput c x tape budget = some u.output
  rw [compiledTapeOutput_run hrun htime]
  have live : clockWord left ≠ [] := by intro e; have len := clockWord_length left; simp [e] at len
  simp [hmiss, hclock, live, hval]


private def loadClock : Code :=
  .loop (.head 1) (.write 1 (.tail 1) ▷ .write 2 (.cons true 2))

private theorem run_loadClock (s : State) (n prior : Nat) (tail : Word)
    (pack : s.reg 1 = clockWord n ++ tail) (fuel : s.reg 2 = clockWord prior) :
    ∃ u, Run emptyLanguage loadClock s u (4 * n + 1) 0 ∧
      u.reg 1 = false :: tail ∧ u.reg 2 = clockWord (n + prior) ∧
      u.queries = s.queries ∧ ∀ r, r ≠ 1 → r ≠ 2 → u.reg r = s.reg r := by
  induction n generalizing s prior with
  | zero =>
    have h : (Test.head 1).eval s = false := by simp [Test.eval, pack]
    exact ⟨s, .loopFalse h, by simpa using pack, by simpa using fuel, rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    let step := (s.write 1 (clockWord n ++ tail)).write 2 (clockWord (prior + 1))
    have pop : Run emptyLanguage (.write 1 (.tail 1)) s
        (s.write 1 (clockWord n ++ tail)) 1 0 := by
      simpa [Expr.eval, pack] using
        (Run.write (A := emptyLanguage) (s := s) (d := 1) (e := .tail 1))
    have push : Run emptyLanguage (.write 2 (.cons true 2))
        (s.write 1 (clockWord n ++ tail)) step 1 0 := by
      simpa [step, Expr.eval, reg_write_other, show 2 ≠ 1 by decide, fuel] using
        (Run.write (A := emptyLanguage) (s := s.write 1 (clockWord n ++ tail)) (d := 2)
          (e := .cons true 2))
    have hp : step.reg 1 = clockWord n ++ tail := by
      simp [step, reg_write_other, reg_write_same, show 1 ≠ 2 by decide]
    obtain ⟨u, loop, out, gas, queue, rest⟩ := ih step (prior + 1) hp (reg_write_same ..)
    have head : (Test.head 1).eval s = true := by simp [Test.eval, pack]
    have run := Run.loopTrue head (Run.seq pop push) loop
    refine ⟨u, ?_, out, ?_, queue, fun r h1 h2 => ?_⟩
    · simpa only [loadClock, show 1 + 1 + 1 + (4 * n + 1) + 1 = 4 * (n + 1) + 1 by omega]
        using run
    · simpa only [show n + (prior + 1) = n + 1 + prior by omega] using gas
    · rw [rest r h1 h2, reg_write_other _ _ _ _ h2, reg_write_other _ _ _ _ h1]

private def loadReplay : Code :=
  .write (slot 4 0) (.copy 0) ▷ setBit 2 false ▷ loadClock ▷
    .write 0 (.tail 1) ▷ .write 1 .empty

private theorem loadReplay_run (x tape : Word) (clock : Nat) :
    Run emptyLanguage loadReplay (State.input x (clockWord clock ++ tape))
      (replayInput 4 x tape clock) (4 * clock + 11) 0 := by
  let s := State.input x (clockWord clock ++ tape)
  let pos := slot 4 0
  let input := s.write pos x
  let ready := input.write 2 [false]
  have save : Run emptyLanguage (.write pos (.copy 0)) s input 1 0 := .write
  have packed : ready.reg 1 = clockWord clock ++ tape := by
    simp [ready, input, s, pos, slot, State.input, State.write]
  obtain ⟨u, run, htape, hgas, hstack, hother⟩ :=
    run_loadClock ready clock 0 tape packed (reg_write_same ..)
  have unpack : Run emptyLanguage (.write 0 (.tail 1)) u (u.write 0 tape) 1 0 := by
    simpa [Expr.eval, htape] using
      (Run.write (A := emptyLanguage) (s := u) (d := 0) (e := .tail 1))
  let result := (u.write 0 tape).write 1 []
  have clear : Run emptyLanguage (.write 1 .empty) (u.write 0 tape) result 1 0 := .write
  have loaded : result = replayInput 4 x tape clock := by
    have hregs : result.reg = (replayInput 4 x tape clock).reg := by
      funext i
      by_cases h0 : i = 0
      · subst i
        simp [result, State.write, replayInput]
      by_cases h1 : i = 1
      · subst i
        simp [result, State.write, replayInput, slot]
      by_cases h2 : i = 2
      · subst i
        simp [result, State.write, replayInput, hgas]
      rw [show result.reg i = u.reg i by simp [result, State.write, h0, h1]]
      rw [hother i h1 h2]
      simp [ready, input, s, pos, State.write, State.input, replayInput, h0, h1, h2]
    have hqueues : result.queries = (replayInput 4 x tape clock).queries := hstack
    have equal (a b : State) (hr : a.reg = b.reg) (hq : a.queries = b.queries) : a = b := by
      cases a
      cases b
      cases hr
      cases hq
      rfl
    exact equal _ _ hregs hqueues
  rw [← loaded]
  have loadedRun := Run.seq save
    (Run.seq (run_setBit input 2 false) (Run.seq run (Run.seq unpack clear)))
  simpa only [loadReplay, pos,
    show 1 + (3 + ((4 * clock + 1) + (1 + 1 + 1) + 1) + 1) + 1 = 4 * clock + 11 by omega]
    using loadedRun

private def finishReplay : Code :=
  .branch (.empty 1)
    (.branch (.empty 2) (.write 0 .empty) (.write 0 (.cons true (slot 4 0))))
    (.write 0 .empty)

/-- Load a clock and tape from the witness register, run the compiled
program, and encode success as a true bit followed by the resulting word.
An empty output represents timeout or a missing answer. -/
def replayProgram (c : Code) : Code :=
  loadReplay ▷ compiledReplay (frameWidth c) 4 c ▷ finishReplay

theorem replayProgram_pure (c : Code) : (replayProgram c).pure := by
  simpa [replayProgram, loadReplay, loadClock, finishReplay, setBit, Code.pure, Code.allowed]
    using compiledReplay_pure (frameWidth c) 4 c

private theorem run_finishReplay (s : State) :
    ∃ u time, Run emptyLanguage finishReplay s u time 0 ∧ time ≤ 3 ∧
      u.output = if s.reg 1 = [] ∧ s.reg 2 ≠ [] then true :: s.reg (slot 4 0) else [] := by
  by_cases hm : s.reg 1 = []
  · have test : (Test.empty 1).eval s = true := by simp [Test.eval, hm]
    by_cases hg : s.reg 2 = []
    · have clock : (Test.empty 2).eval s = true := by simp [Test.eval, hg]
      exact ⟨s.write 0 [], 3, run_branch_true test (run_branch_true clock .write),
        by decide, by simp [hm, hg, State.output, reg_write_same]⟩
    · have clock : (Test.empty 2).eval s = false := by simp [Test.eval, hg]
      exact ⟨s.write 0 (true :: s.reg (slot 4 0)), 3,
        run_branch_true test (run_branch_false clock .write), by decide,
        by simp [hm, hg, State.output, reg_write_same]⟩
  · have test : (Test.empty 1).eval s = false := by simp [Test.eval, hm]
    exact ⟨s.write 0 [], 2, run_branch_false test .write, by decide,
      by simp [hm, State.output, reg_write_same]⟩

/-- The replay subroutine is an actual machine program on ordinary
`State.input` inputs. The witness packages the clock before the tape. -/
theorem replayProgram_run (c : Code) (x tape : Word) (budget : Nat) :
    let clock := loweringCost (frameWidth c) budget * budget
    ∃ out time, Run emptyLanguage (replayProgram c)
      (State.input x (clockWord clock ++ tape)) out time 0 ∧
      time ≤ 24 * clock + 36 ∧
      out.output = ((compiledTapeOutput c x tape budget).map (true :: ·)).getD [] := by
  dsimp only
  let clock := loweringCost (frameWidth c) budget * budget
  obtain ⟨mid, cost, replay, bound⟩ :=
    compiledReplay_total (frameWidth c) 4 (by decide) c
      (s := replayInput 4 x tape clock) (n := clock) rfl
  have enough : cost ≤ 20 * (clock + 1) := by omega
  obtain ⟨out, finishing, finish, finishBound, output⟩ := run_finishReplay mid
  refine ⟨out, _, .seq (loadReplay_run x tape clock) (.seq replay finish), by omega, ?_⟩
  rw [compiledTapeOutput_run replay enough, output]
  split <;> rfl

/-- The sum of machine instructions for all tapes, including each program's
input and output handling, is bounded by the per-tape cost times the
number of tapes. -/
theorem compiledCandidates_work (c : Code) (x : Word) (budget cap : Nat) :
    let clock := loweringCost (frameWidth c) budget * budget
    ∃ work : List (Word × Nat),
      work.map Prod.fst = tapes cap ∧
      (∀ entry ∈ work, ∃ out, Run emptyLanguage (replayProgram c)
        (State.input x (clockWord clock ++ entry.1)) out entry.2 0) ∧
      (work.map Prod.snd).sum ≤ (24 * clock + 36) * 2 ^ cap := by
  dsimp only
  let clock := loweringCost (frameWidth c) budget * budget
  let cost := 24 * clock + 36
  have build (ls : List Word) : ∃ work : List (Word × Nat),
      work.map Prod.fst = ls ∧
      (∀ entry ∈ work, ∃ out, Run emptyLanguage (replayProgram c)
        (State.input x (clockWord clock ++ entry.1)) out entry.2 0) ∧
      (work.map Prod.snd).sum ≤ cost * ls.length := by
    induction ls with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons tape rest ih =>
      obtain ⟨out, time, run, bound, _⟩ := replayProgram_run c x tape budget
      obtain ⟨work, hw, hrun, total⟩ := ih
      refine ⟨(tape, time) :: work, by simp [hw], ?_, ?_⟩
      · intro entry mem
        rcases List.mem_cons.mp mem with rfl | hm
        · exact ⟨out, run⟩
        · exact hrun entry hm
      · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
        change time ≤ cost at bound
        omega
  obtain ⟨work, hlist, hrun, bound⟩ := build (tapes cap)
  rw [tapes_length] at bound
  exact ⟨work, hlist, hrun, bound⟩

/-- The computed list agrees with the successful executions of the actual
replay program on all tapes of the requested width. -/
theorem compiledCandidates_iff_replayProgram {c : Code} {x v : Word} {budget cap : Nat} :
    let clock := loweringCost (frameWidth c) budget * budget
    v ∈ compiledCandidates c x budget cap ↔
      ∃ tape : Word, tape.length = cap ∧ ∃ out time,
        Run emptyLanguage (replayProgram c) (State.input x (clockWord clock ++ tape)) out time 0 ∧
        time ≤ 24 * clock + 36 ∧ out.output = true :: v := by
  dsimp only
  constructor
  · intro h
    obtain ⟨tape, inside, result⟩ := List.mem_filterMap.mp h
    obtain ⟨out, time, run, bound, result'⟩ := replayProgram_run c x tape budget
    refine ⟨tape, mem_tapes.mp inside, out, time, run, bound, ?_⟩
    simpa [result] using result'
  · rintro ⟨tape, len, out, time, run, _, result⟩
    obtain ⟨other, elapsed, otherRun, _, result'⟩ := replayProgram_run c x tape budget
    have same := (run.deterministic otherRun).1
    have encoded : ((compiledTapeOutput c x tape budget).map (true :: ·)).getD [] = true :: v :=
      result'.symm.trans (same ▸ result)
    refine List.mem_filterMap.mpr ⟨tape, mem_tapes.mpr len, ?_⟩
    cases h : compiledTapeOutput c x tape budget with
    | none => simp [h] at encoded
    | some w =>
      simp [h] at encoded
      simp [h, encoded]

end ComplexityModel.MachineEnumeration

namespace ComplexityModel

/-- A polynomially bounded list of outputs from concrete oracle-free replays
contains the genuine result of every logarithmic-query computation. -/
theorem FPLogNP.compiled_candidate_bound {f : WordFunction} (hf : FPLogNP f) :
    ∃ c : Code, ∃ p : Poly, ∃ k b : Nat, ∀ x,
      let budget := p.at x.length
      let cap := (x.length + 2).log2 * k + b
      let candidates := MachineEnumeration.compiledCandidates c x budget cap
      f x ∈ candidates ∧ candidates.length ≤ (x.length + 2) ^ k * 2 ^ b := by
  obtain ⟨A, _, c, p, k, b, run⟩ := hf
  refine ⟨c, p, k, b, fun x => ?_⟩
  dsimp only
  obtain ⟨u, t, q, hrun, htime, hcap, hval⟩ := run x
  exact ⟨hval ▸ MachineEnumeration.run_mem_compiledCandidates hrun htime hcap,
    Nat.le_trans (MachineEnumeration.compiledCandidates_length ..) (pow_log_cap ..)⟩

end ComplexityModel
