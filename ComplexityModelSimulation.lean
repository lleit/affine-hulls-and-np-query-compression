module

public import ComplexityModel.Machine

@[expose] public section

namespace ComplexityModel

theorem Run.deterministic (h : Run A c s u t q) (h' : Run A c s u' t' q') :
    u = u' ∧ t = t' ∧ q = q' := by
  induction h generalizing u' t' q' with
  | skip | write | push | pop => cases h'; exact ⟨rfl, rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl, rfl⟩
  | branch he _ ih =>
    cases h' with
    | branch he' hr =>
      have e := he.symm.trans he'
      subst e
      obtain ⟨rfl, rfl, rfl⟩ := ih hr
      exact ⟨rfl, rfl, rfl⟩
  | loopFalse he =>
    cases h' with
    | loopFalse => exact ⟨rfl, rfl, rfl⟩
    | loopTrue he' => simp_all
  | loopTrue he _ _ ih₁ ih₂ =>
    cases h' with
    | loopFalse he' => simp_all
    | loopTrue _ h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl, rfl⟩
  | askEmpty he =>
    cases h' with
    | askEmpty => exact ⟨rfl, rfl, rfl⟩
    | askSome => simp_all
  | askSome he hb =>
    cases h' with
    | askEmpty => simp_all
    | askSome he' hb' =>
      have ew := Option.some.inj (he.symm.trans he')
      subst ew
      have eb := Bool.eq_iff_iff.mpr (hb.trans hb'.symm)
      subst eb
      exact ⟨rfl, rfl, rfl⟩
  | callEmpty he =>
    cases h' with
    | callEmpty => exact ⟨rfl, rfl, rfl⟩
    | callSome => simp_all
  | callSome he _ ih =>
    cases h' with
    | callEmpty => simp_all
    | callSome he' hr =>
      have ew := Option.some.inj (he.symm.trans he')
      subst ew
      obtain ⟨rfl, rfl, rfl⟩ := ih hr
      exact ⟨rfl, rfl, rfl⟩

/-- Any execution with zero oracle queries is oracle-independent. -/
theorem Run.transfer (h : Run A c s u t q) (hq : q = 0) (B : Language) :
    Run B c s u t q := by
  induction h with
  | skip => exact .skip
  | write => exact .write
  | push => exact .push
  | pop => exact .pop
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ (by omega)) (ih₂ (by omega))
  | branch he _ ih => exact .branch he (ih hq)
  | loopFalse he => exact .loopFalse he
  | loopTrue he _ _ ih₁ ih₂ => exact .loopTrue he (ih₁ (by omega)) (ih₂ (by omega))
  | askEmpty he => exact .askEmpty he
  | askSome => omega
  | callEmpty he => exact .callEmpty he
  | callSome he _ ih => exact .callSome he (ih hq)

theorem Run.pure_queries (h : Run A c s u t q) (hp : c.pure) : q = 0 := by
  induction h with
  | seq _ _ ih₁ ih₂ => rw [ih₁ hp.1, ih₂ hp.2]
  | branch he _ ih =>
    apply ih
    split
    · exact hp.1
    · exact hp.2
  | loopTrue _ _ _ ih₁ ih₂ => rw [ih₁ hp, ih₂ hp]
  | askSome =>
    rename_i src d s he hb
    cases src <;> simp [Code.pure, Code.allowed] at hp
  | callSome _ _ ih => exact ih hp
  | skip | write | push | pop | loopFalse | askEmpty | callEmpty => rfl

theorem Source.advance_queries (src : Source) (s : State) :
    (src.advance s).queries.Sublist s.queries := by
  cases src
  · exact List.Sublist.refl _
  · exact List.tail_sublist _

/-- The consumer only needs the oracle's answers on the precomputed batch.
It pops at least one queued word per actual query. A scoped call inside the
consumer starts with an empty queue, so it cannot make additional queries. -/
theorem Run.consumer_preasked (h : Run A c s u t q) (hc : c.consumer) (B : Language)
    (agree : ∀ w ∈ s.queries, A w ↔ B w) :
    Run B c s u t q ∧ u.queries.Sublist s.queries ∧ q + u.queries.length ≤ s.queries.length := by
  induction h with
  | skip => exact ⟨.skip, .refl _, by simp⟩
  | write => exact ⟨.write, .refl _, by simp [State.write]⟩
  | push => simp [Code.consumer, Code.allowed] at hc
  | @pop d s =>
    have sub := List.tail_sublist s.queries
    exact ⟨.pop, sub, by simpa only [Nat.zero_add, State.write, State.drop] using sub.length_le⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨r₁, sub₁, count₁⟩ := ih₁ hc.1 agree
    obtain ⟨r₂, sub₂, count₂⟩ := ih₂ hc.2 (fun w hw => agree w (sub₁.subset hw))
    exact ⟨.seq r₁ r₂, sub₂.trans sub₁, by omega⟩
  | branch he _ ih =>
    obtain ⟨r, sub, count⟩ := ih (by split; exact hc.1; exact hc.2) agree
    exact ⟨.branch he r, sub, count⟩
  | loopFalse he => exact ⟨.loopFalse he, .refl _, by simp⟩
  | loopTrue he _ _ ih₁ ih₂ =>
    obtain ⟨r₁, sub₁, count₁⟩ := ih₁ hc agree
    obtain ⟨r₂, sub₂, count₂⟩ := ih₂ hc (fun w hw => agree w (sub₁.subset hw))
    exact ⟨.loopTrue he r₁ r₂, sub₂.trans sub₁, by omega⟩
  | @askEmpty src d s hr =>
    have sub := src.advance_queries s
    exact ⟨.askEmpty hr, sub, by simpa only [Nat.zero_add, State.write] using sub.length_le⟩
  | @askSome w bit src d s hr hb =>
    cases src with
    | reg r => simp [Code.consumer, Code.allowed] at hc
    | queued =>
      cases hs : s.queries with
      | nil => simp [Source.read, hs] at hr
      | cons a rest =>
        have e : a = w := Option.some.inj (by simpa only [Source.read, hs, List.head?_cons] using hr)
        refine ⟨.askSome hr (hb.trans (agree w (by simp [hs, e]))), ?_, ?_⟩
        · simpa only [State.write, ← hs] using Source.advance_queries .queued s
        · simp [Source.advance, State.write, State.drop, hs, Nat.add_comm]
  | @callEmpty src d body s hr =>
    have sub := src.advance_queries s
    exact ⟨.callEmpty hr, sub, by simpa only [Nat.zero_add, State.write] using sub.length_le⟩
  | @callSome w body u t q src d s hr _ ih =>
    obtain ⟨r, _, count⟩ := ih hc (by simp [State.input])
    have zero : q = 0 := by simp only [State.input, List.length_nil] at count; omega
    have sub := src.advance_queries s
    exact ⟨.callSome hr r, sub, by simpa only [zero, Nat.zero_add, State.write] using sub.length_le⟩

/-- Substitute a fixed oracle-free decider at every query instruction. -/
def Code.replaceOracle (c decider : Code) : Code :=
  match c with
  | .seq a b => .seq (replaceOracle a decider) (replaceOracle b decider)
  | .branch test a b => .branch test (replaceOracle a decider) (replaceOracle b decider)
  | .loop test body => .loop test (replaceOracle body decider)
  | .callBit src d body => .callBit src d (replaceOracle body decider)
  | .ask src d => .callBit src d decider
  | c => c

theorem Code.replaceOracle_pure (decider : Code) (hp : decider.pure) (c : Code) :
    (c.replaceOracle decider).pure := by
  induction c <;> simp_all [Code.pure, Code.allowed, Code.replaceOracle]

/-- Compile one execution using a uniform bound on the decider for all queries
that can occur in it. The simulated execution preserves the entire final state. -/
theorem Run.replaceOracle (h : Run A c s u t q) (hs : s.Fits n)
    (decider : Code) (cost : Nat)
    (decision : ∀ w : Word, w.length ≤ n + t → ∃ v d,
      Run emptyLanguage decider (State.input w) v d 0 ∧ d ≤ cost ∧
        (v.output = [true] ↔ A w)) :
    ∃ r, Run emptyLanguage (c.replaceOracle decider) s u r 0 ∧ r ≤ t + q * cost := by
  induction h generalizing n with
  | skip => exact ⟨_, .skip, by simp⟩
  | write => exact ⟨_, .write, by simp⟩
  | push => exact ⟨_, .push, by simp⟩
  | pop => exact ⟨_, .pop, by simp⟩
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, hr₁, hb₁⟩ := ih₁ hs (fun w hw => decision w (by omega))
    obtain ⟨r₂, hr₂, hb₂⟩ := ih₂ (h₁.fits hs) (fun w hw => decision w (by omega))
    refine ⟨_, .seq hr₁ hr₂, ?_⟩
    rw [Nat.add_mul]
    omega
  | branch he _ ih =>
    obtain ⟨r, hr, hb⟩ := ih hs (fun w hw => decision w (by omega))
    refine ⟨r + 1, Run.branch he ?_, by omega⟩
    split <;> simpa only [Code.replaceOracle, Bool.false_eq_true, ite_true, ite_false, *] using hr
  | loopFalse he => exact ⟨_, .loopFalse he, by simp⟩
  | loopTrue he h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, hr₁, hb₁⟩ := ih₁ hs (fun w hw => decision w (by omega))
    obtain ⟨r₂, hr₂, hb₂⟩ := ih₂ (h₁.fits hs) (fun w hw => decision w (by omega))
    refine ⟨_, .loopTrue he hr₁ hr₂, ?_⟩
    rw [Nat.add_mul]
    omega
  | askEmpty he => exact ⟨_, .callEmpty he, by simp⟩
  | askSome he hb =>
    obtain ⟨v, d, hv, hd, ha⟩ := decision _ (Nat.le_succ_of_le (Source.read_fits hs he))
    have bitCorrect := Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans (ha.trans hb.symm))
    refine ⟨d + 1, ?_, by simp only [Nat.one_mul]; omega⟩
    simpa only [Code.replaceOracle, bitCorrect] using Run.callSome he hv
  | callEmpty he => exact ⟨_, .callEmpty he, by simp⟩
  | callSome he _ ih =>
    have hw := Source.read_fits hs he
    obtain ⟨r, hr, hb⟩ := ih (State.input_fits hw (Nat.zero_le _)) (fun w hw => decision w (by omega))
    exact ⟨_, .callSome he hr, by omega⟩

end ComplexityModel
