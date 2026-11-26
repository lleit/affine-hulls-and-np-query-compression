module

public import ComplexityModelClasses
public import ComplexityModel.BatchCode
public import FixedVerifier
public import HullQueryLanguage
public import HullBatchProducer
public import HullVerifierCode
public import ReplayParameters
public import CandidatePipeline
public import SearchRoundProgram

/-! The class equivalence in the polynomial-time register-machine model.
The hull query verifier, parallel batch and deterministic search all have
checked machine code and polynomial bounds. -/

@[expose] public section

namespace ComplexityImplication

open ComplexityModel

abbrev Checker := Word → Word → Bool

/-- A pure register program implementing a Boolean checker on all input
pairs, with an explicit polynomial bound on the number of steps. -/
def CheckerCode (check : Checker) : Prop :=
  ∃ c : Code, ∃ time : Poly, c.pure ∧ ∀ s w, ∃ out t,
    Run emptyLanguage c (State.input s w) out t 0 ∧ t ≤ time.at (s.length + w.length) ∧
      (out.output = [true] ↔ check s w = true)

theorem fixedVerifier_code {c : Code} {time : Poly} (pure : c.pure)
    (halts : FixedVerifier.HaltsWithin c time) : CheckerCode (FixedVerifier.check c time) :=
  ⟨FixedVerifier.compile c, time.plus ⟨40, 1⟩, FixedVerifier.compile_pure c pure,
    FixedVerifier.compile_correct halts⟩

/-- The bit-level verifier of an encoded query can call the original
checker on each decoded assignment in the certificate. -/
abbrev QueryVerifierCode (check : Checker) : Prop :=
  CheckerCode (HullQueryLanguage.verifyWord check)

theorem queryVerifier_code (check : Checker) (input : CheckerCode check) : QueryVerifierCode check := by
  obtain ⟨c, time, pure, exec⟩ := input
  refine ⟨HullVerifierCode.compile c, HullVerifierCode.compileTime time,
    HullVerifierCode.compile_pure pure, fun s cert => ?_⟩
  obtain ⟨out, t, run, bound, result⟩ := HullVerifierCode.compile_run exec s cert
  exact ⟨out, t, run, bound, by simp [result]⟩

theorem queryLanguage_np (check : Checker) (compiled : QueryVerifierCode check) :
    NP (HullQueryLanguage.language check) := by
  obtain ⟨c, time, pure, exec⟩ := compiled
  let witnessBound : Poly := ⟨2, 2⟩
  refine ⟨c, witnessBound, time, pure, ?_, ?_⟩
  · intro s w
    obtain ⟨out, t, run, bound, _⟩ := exec s w
    exact ⟨out, t, run, bound⟩
  · intro s
    constructor
    · intro yes
      obtain ⟨w, short, accepted⟩ := (HullQueryLanguage.language_bounded check s).mp yes
      obtain ⟨out, t, run, _, ok⟩ := exec s w
      have bound : (s.length + 1) * (2 * s.length + 1) ≤ witnessBound.at s.length := by
        dsimp [witnessBound, Poly.at]
        rw [Nat.pow_two, Nat.mul_left_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      exact ⟨w, Nat.le_trans short bound, out, t, run, ok.mpr accepted⟩
    · rintro ⟨w, _, out, t, run, accepts⟩
      obtain ⟨u, _, other, _, ok⟩ := exec s w
      exact ⟨w, ok.mp ((run.deterministic other).1 ▸ accepts)⟩

/-- The producer queues exactly the batch, and the consumer assembles its
answers. Quantify over arbitrary languages to express that both programs
follow the same computation for any oracle. -/
def HullBatchCode : Prop :=
  ∃ producer consumer : Code, ∃ time : Poly,
    producer.pure ∧ consumer.consumer ∧ ∀ s (A : Language) (answer : Word → Bool),
      (∀ q ∈ HullQueryLanguage.questions s, answer q = true ↔ A q) →
      ∃ mid out t₁ t₂ q,
        Run emptyLanguage producer (State.input s) mid t₁ 0 ∧
        mid.queries = HullQueryLanguage.questions s ∧
        Run A consumer mid out t₂ q ∧ t₁ + t₂ ≤ time.at s.length ∧
        out.output = HullQueryLanguage.assemble s ((HullQueryLanguage.questions s).map answer)

/-- The remaining batch programs build the questions and assemble already
collected answers. The calls to the oracle use the verified queue consumer. -/
def HullBatchParts : Prop :=
  ∃ producer assembler : Code, ∃ produceTime assembleTime : Poly,
    producer.pure ∧ assembler.allowed false false false ∧
    (∀ s, ∃ t, Run emptyLanguage producer (State.input s)
      (BatchCode.input s (HullQueryLanguage.questions s)) t 0 ∧ t ≤ produceTime.at s.length) ∧
    (∀ s (answer : Word → Bool),
      let replies := (HullQueryLanguage.questions s).map answer
      ∃ out t, Run emptyLanguage assembler (State.input s replies) out t 0 ∧
        t ≤ assembleTime.at s.length ∧ out.output = HullQueryLanguage.assemble s replies)

theorem hullBatchParts : HullBatchParts :=
  ⟨HullBatchProducer.producer, HullBatchPrograms.assembler, ⟨10000, 4⟩, ⟨200, 3⟩,
    HullBatchProducer.producer_pure, HullBatchPrograms.assembler_local,
    HullBatchProducer.producer_run, HullBatchPrograms.assembler_run⟩

theorem batch_of_parts (parts : HullBatchParts) : HullBatchCode := by
  obtain ⟨producer, assembler, produceTime, assembleTime, pure, assemblerLocal, produce, assemble⟩ := parts
  let collectTime : Poly := ⟨70, 3⟩
  refine ⟨producer, .seq BatchCode.collect assembler, (produceTime.plus collectTime).plus assembleTime,
    pure, ⟨BatchCode.collect_consumer, ?_⟩, ?_⟩
  · have aux (c : Code) (h : c.allowed false false false) : c.consumer := by
      change c.allowed false false true
      induction c <;> try simp_all [Code.allowed]
      case ask src dst =>
        cases src <;> simp_all [Code.allowed]
    exact aux assembler assemblerLocal
  · intro s A answer answers
    let qs := HullQueryLanguage.questions s
    obtain ⟨t₁, before, cost₁⟩ := produce s
    obtain ⟨out, t, after, cost, result⟩ := assemble s answer
    have collect := BatchCode.collect_run A answer s qs answers
    let stepCount := 13 * qs.length + 14
    refine ⟨BatchCode.input s qs, out, t₁, stepCount + t + 1, qs.length, before, rfl,
      .seq collect (after.transfer rfl A), ?_, result⟩
    have count : qs.length ≤ 4 * (s.length + 1) ^ 3 := HullQueryLanguage.questions_count_bound s
    have cube : 0 < (s.length + 1) ^ 3 := Nat.pow_pos (Nat.succ_pos _)
    have cost₂ : stepCount + 1 ≤ collectTime.at s.length := by
      change 13 * qs.length + 15 ≤ 70 * (s.length + 1) ^ 3
      omega
    have sum₁ := Poly.plus_bound produceTime collectTime s.length
    have sum₂ := Poly.plus_bound (produceTime.plus collectTime) assembleTime s.length
    omega

theorem hull_parallel (check : Checker) (verifier : QueryVerifierCode check)
    (batch : HullBatchCode) : FPParallelNP (QueryEncoding.hullWord check) := by
  classical
  let A := HullQueryLanguage.language check
  let answer (q : Word) : Bool := decide (A q)
  have answers (s : Word) : ∀ q ∈ HullQueryLanguage.questions s, answer q = true ↔ A q := by
    intro q _
    simp [answer]
  obtain ⟨producer, consumer, time, hp, hc, runs⟩ := batch
  refine ⟨A, queryLanguage_np check verifier, producer, consumer, time, hp, hc, ?_⟩
  intro s
  obtain ⟨mid, out, t₁, t₂, q, hr₁, _, hr₂, timeBound, result⟩ := runs s A answer (answers s)
  exact ⟨mid, out, t₁, t₂, q, hr₁, hr₂, timeBound,
    result.trans (HullQueryLanguage.assemble_correct check s answer (answers s))⟩

/-- Compression supplies an actual polynomial-time machine for listing
possible hulls, with the authentic hull present on every input. -/
theorem hull_list_of_parallel_le_log (check : Checker) (verifier : CheckerCode check)
    (compress : ∀ f, FPParallelNP f → FPLogNP f) :
    ∃ g : WordFunction, FP g ∧ ∃ size : Poly, ∀ x,
      ∃ words : List Word, g x = QueryEncoding.pack words ∧ words.length ≤ size.at x.length ∧
        QueryEncoding.hullWord check x ∈ words :=
  ReplayParameters.list_of_log
    (compress _ (hull_parallel check (queryVerifier_code check verifier) (batch_of_parts hullBatchParts)))

/-- The compressed hull algorithm gives a polynomial-time list of decoded
candidates. Every satisfiable restriction has its genuine hull in the list. -/
theorem hull_decoded_machine_of_parallel_le_log (check : Checker) (verifier : CheckerCode check)
    (compress : ∀ f, FPParallelNP f → FPLogNP f) :
    ∃ code : Code, ∃ time : Poly, code.pure ∧ SearchRoundProgram.CandidateLister check code time := by
  have oracle := compress _
    (hull_parallel check (queryVerifier_code check verifier) (batch_of_parts hullBatchParts))
  obtain ⟨c,p,a,b,contains⟩ := FPLogNP.compiled_candidate_bound oracle
  obtain ⟨code,time,pure,list⟩ := CandidatePipeline.decoded_machine c p a b
  refine ⟨code,time,pure,fun x k hs => ?_⟩
  let request := QueryEncoding.requestWord x k hs
  obtain ⟨out,t,words,run,clock,queue,data,_,mem⟩ := list request
  have fields : QueryEncoding.readRequest request = ⟨x,k,hs⟩ := QueryEncoding.read_requestWord ..
  rw [fields] at data
  refine ⟨out,t,(CandidateReadCode.decodeList k words).reverse,run,clock,queue,data,?_,?_⟩
  · intro A hA
    exact CandidateReadCode.decodeList_shape (List.mem_reverse.mp hA)
  · intro sat
    have genuine := CandidateReadCode.decodeList_genuine check words x k hs
      ((mem _).mpr (contains request).1) sat
    simpa only [List.mem_reverse] using genuine

/-- The inclusion of one-batch functions in logarithmic-query functions
suffices to construct a deterministic decider for every NP language. -/
theorem pEqualsNP_of_parallel_le_log
    (compress : ∀ f, FPParallelNP f → FPLogNP f) : PEqualsNP := by
  intro A
  refine ⟨p_subset_np, fun h => ?_⟩
  obtain ⟨c, p, t, pure, halts, models⟩ := FixedVerifier.represents h
  let check := FixedVerifier.check c t
  have verifier : CheckerCode check := fixedVerifier_code pure halts
  obtain ⟨lister,listTime,listPure,list⟩ := hull_decoded_machine_of_parallel_le_log check verifier compress
  obtain ⟨code,time,codePure,verify⟩ := verifier
  let decision (x : Word) := [RoundSemantics.answer (check x) (FixedVerifier.width p x) []]
  refine ⟨decision, SearchRoundProgram.decide_fp verify codePure list listPure p, fun x => ?_⟩
  change [RoundSemantics.answer (check x) (FixedVerifier.width p x) []] = [true] ↔ A x
  simp only [List.cons.injEq, and_true, RoundSemantics.answer_eq_true]
  exact (RoundSemantics.initial_iff (check x) (FixedVerifier.width p x)).trans (models x).symm

theorem classEquality_iff_pEqualsNP : ClassEquality ↔ PEqualsNP :=
  ⟨fun h => pEqualsNP_of_parallel_le_log (fun f => (h f).mp), classEquality_of_pEqualsNP⟩

end ComplexityImplication
