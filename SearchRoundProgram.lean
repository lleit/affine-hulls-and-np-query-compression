module

public import CandidateClassifyCode
public import CandidateCutoffCode
public import RoundSemantics
public import SearchRoundIO
public import SearchInitCode

@[expose] public section

namespace SearchRoundProgram

open ComplexityModel
open HullBatchMachine (ones stepWrite runTrue runFalse)

abbrev Checker := CertificateCode.Checker

def CandidateLister (check : Checker) (code : Code) (time : Poly) : Prop :=
  ∀ x k hs, let req := QueryEncoding.requestWord x k hs
    ∃ (out : State) (t : Nat) (cs : List AffineSearch.Candidate), Run emptyLanguage code (State.input req) out t 0 ∧
      t ≤ time.at req.length ∧ out.queries = [] ∧
      out.output = QueryEncoding.pack (cs.map CandidateReadCode.candidateWord) ∧
      (∀ A ∈ cs, AffineSearch.Shaped k A.pivots ∧ A.base.length = k) ∧
      (RoundSemantics.Sat (check x) k hs →
        ∃ A ∈ cs, AffineSearch.Genuine (AffineSearch.Models (check x) k hs) A)

private def halt : Code := .write 3 .empty

private def decideOrCut : Code :=
  .branch (.head 4) halt
    (.seq SearchRoundIO.pickMask (.branch (.head 175) SearchRoundIO.installCut halt))

private theorem decideOrCut_pure : decideOrCut.pure :=
  ⟨trivial,SearchRoundIO.pickMask_pure,SearchRoundIO.installCut_pure,trivial⟩

private def positiveRound (c lister : Code) : Code :=
  .seq (.write 81 (.copy 1))
    (.seq (ReplayFrameCode.invoke 200 95 150 lister)
      (.seq CandidateCutoffCode.cutoff
        (.seq (CandidateClassifyCode.classify (RestrictedVerifier.compile c)) decideOrCut)))

def compile (c lister : Code) : Code :=
  .seq SearchRoundIO.requestCode (.branch (.empty 1) (SearchRoundIO.terminal c) (positiveRound c lister))

theorem compile_pure {c lister : Code} (checker : c.pure) (list : lister.pure) : (compile c lister).pure := by
  exact ⟨SearchRoundIO.requestCode_pure,SearchRoundIO.terminal_pure checker,trivial,
    ReplayFrameCode.invoke_pure 200 95 150 list,CandidateCutoffCode.cutoff_pure,
    CandidateClassifyCode.classify_pure (RestrictedVerifier.compile_pure checker),decideOrCut_pure⟩

private noncomputable def answer (check : Checker) : SearchLoopCode.Decision :=
  fun x k hs => RoundSemantics.answer (check x) k hs

private def Outcome (check : Checker) (x : Word) (k : Nat) (hs : List Word) (u : State) : Prop :=
  (u.reg 3 = [] ∧ u.reg 4 = [answer check x k hs]) ∨
    ∃ n z, k = n + 1 ∧ z.length = k ∧ true ∈ z ∧ SearchLoopCode.Active x n (z :: hs) u ∧
      answer check x n (z :: hs) = answer check x k hs

private theorem active_of_frame {s u : State} {changed : List Nat} {x : Word} {k : Nat} {hs : List Word}
    (active : SearchLoopCode.Active x k hs s) (frame : WordCode.Preserves s u changed)
    (h₀ : 0 ∉ changed) (h₁ : 1 ∉ changed) (h₂ : 2 ∉ changed) (h₃ : 3 ∉ changed) :
    SearchLoopCode.Active x k hs u :=
  ⟨(frame.2 0 h₀).trans active.1,(frame.2 1 h₁).trans active.2.1,
    (frame.2 2 h₂).trans active.2.2.1,(frame.2 3 h₃).trans active.2.2.2.1,
    frame.1.trans active.2.2.2.2⟩

private theorem decideOrCut_run (s : State) (check : Checker) (x : Word) (n : Nat) (hs : List Word)
    (K : Nat) (cs : List AffineSearch.Candidate) (active : SearchLoopCode.Active x (n+1) hs s)
    (formed : ∀ A ∈ cs, AffineSearch.Shaped (n+1) A.pivots ∧ A.base.length = n+1)
    (count : cs.length ≤ K)
    (contains : RoundSemantics.Sat (check x) (n+1) hs →
      ∃ A ∈ cs, AffineSearch.Genuine (AffineSearch.Models (check x) (n+1) hs) A)
    (found : s.reg 4 = [RoundSemantics.found (check x) hs K cs])
    (items : s.reg 124 = SplitBranchCode.candidatesWord ((RoundSemantics.large K cs).map AffineSearch.pack)) :
    ∃ u t, Run emptyLanguage decideOrCut s u t 0 ∧
      t ≤ 650*(n+1+(s.reg 124).length+1)^3 ∧ Outcome check x (n+1) hs u := by
  let B := n+1+(s.reg 124).length+1
  have bPos : 0 < B := by dsimp [B]; omega
  have cubed : B ≤ B^3 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right bPos (show 1 ≤ 3 by decide)
  cases tested : RoundSemantics.found (check x) hs K cs with
  | true =>
    let u := s.write 3 []
    have yes : (Test.head 4).eval s = true := by simp [Test.eval,found,tested]
    have accept : answer check x (n+1) hs = true :=
      RoundSemantics.answer_eq_true.mpr (RoundSemantics.found_sound formed tested)
    exact ⟨u,2,runTrue yes .write,by change 2 ≤ 650*B^3; omega,
      Or.inl ⟨by simp [u],by simp [u,found,tested,accept]⟩⟩
  | false =>
    let z := RoundSemantics.mask (n+1) K cs
    have no : (Test.head 4).eval s = false := by simp [Test.eval,found,tested]
    have law := RoundSemantics.round_spec formed count contains tested
    change z.length = n+1 ∧ _ at law
    obtain ⟨v,t,greedy,cost,bits,result,keep⟩ := SearchRoundIO.pickMask_run s (n+1)
      ((RoundSemantics.large K cs).map AffineSearch.pack) active.2.1 items
    rw [← items] at cost
    change t ≤ 600*B^3 at cost
    change v.reg 113 = z at bits
    change v.reg 175 = [z.contains true] at result
    by_cases nonzero : true ∈ z
    · have yes : (Test.head 175).eval v = true := by
        simpa only [Test.eval,result,List.headD_cons] using List.contains_iff_mem.mpr nonzero
      have ready := active_of_frame active keep (by decide) (by decide) (by decide) (by decide)
      obtain ⟨u,install,next,_⟩ := SearchRoundIO.installCut_run v x n hs z ready bits
      have nb : n+1 ≤ B := by dsimp [B]; omega
      refine ⟨u,_,runFalse no (.seq greedy (runTrue yes install)),?_,
        Or.inr ⟨n,z,rfl,law.1,nonzero,next,RoundSemantics.answer_congr (law.2.1 nonzero)⟩⟩
      rw [law.1]
      change _ ≤ 650*B^3
      omega
    · have zfalse : z.contains true = false := by
        cases e : z.contains true
        · rfl
        · exact False.elim (nonzero (List.contains_iff_mem.mp e))
      have noMask : (Test.head 175).eval v = false := by
        simpa only [Test.eval,result,List.headD_cons] using zfalse
      let u := v.write 3 []
      have reject : answer check x (n+1) hs = false := RoundSemantics.answer_eq_false.mpr (law.2.2 nonzero)
      exact ⟨u,_,runFalse no (.seq greedy (runFalse noMask .write)),
        by change _ ≤ 650*B^3; omega,Or.inl ⟨by simp [u],by simp [u,keep.2 4 (by decide),found,tested,reject]⟩⟩

private theorem weighted_length (K : Nat) (cs : List AffineSearch.Candidate) :
    (SplitBranchCode.candidatesWord ((RoundSemantics.large K cs).map AffineSearch.pack)).length ≤
      5*(QueryEncoding.pack (cs.map CandidateReadCode.candidateWord)).length := by
  simp only [RoundSemantics.large,SplitBranchCode.candidatesWord,List.map_map]
  let packet := SplitBranchCode.packet ∘ AffineSearch.pack
  change (QueryEncoding.pack ((cs.filter (fun a => !AffineSearch.small K a)).reverse.map packet)).length ≤ _
  have appendLength (ws : List Word) (w : Word) :
      (QueryEncoding.pack (ws++[w])).length = (QueryEncoding.pack ws).length+2*w.length+1 := by
    induction ws with
    | nil => simp [QueryEncoding.pack,QueryEncoding.put_length]
    | cons h tail ih =>
      simp only [List.cons_append,QueryEncoding.pack,QueryEncoding.put_length,ih]
      omega
  induction cs with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    have inputLen : (QueryEncoding.pack ((a::as).map CandidateReadCode.candidateWord)).length =
        2*(CandidateReadCode.candidateWord a).length+1+
          (QueryEncoding.pack (as.map CandidateReadCode.candidateWord)).length := by
      simp only [List.map_cons,QueryEncoding.pack,QueryEncoding.put_length]
    have record : (packet a).length ≤ (CandidateReadCode.candidateWord a).length+2 := by
      simp [packet,SplitBranchCode.packet,AffineSearch.pack,CandidateReadCode.candidateWord,
        CandidateReadCode.packedPivots,QueryEncoding.put_length]
      omega
    rw [inputLen]
    cases h : AffineSearch.small K a with
    | true =>
      simp only [List.filter_cons,h,Bool.not_true,Bool.false_eq_true,if_false]
      omega
    | false =>
      simp only [List.filter_cons,h,Bool.not_false,if_true,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
      rw [appendLength]
      omega

private def baseEnvelope (p : Poly) : Poly := (SearchInitCode.widthBound p).plus ⟨1,1⟩

private def requestEnvelope (p : Poly) : Poly := (Poly.mk 10 2).comp (baseEnvelope p)

private theorem request_bound (p : Poly) (x : Word) {k : Nat} {hs : List Word}
    (hist : AffineSearch.History (FixedVerifier.width p x) k hs) :
    (QueryEncoding.requestWord x k hs).length ≤ (requestEnvelope p).at x.length := by
  let n := FixedVerifier.width p x
  let B := (baseEnvelope p).at x.length
  have sum := Poly.plus_bound (SearchInitCode.widthBound p) ⟨1,1⟩ x.length
  rw [show (Poly.mk 1 1).at x.length = x.length+1 by simp [Poly.at]] at sum
  have wn := SearchInitCode.width_bound p x
  have room : n+x.length+2 ≤ B := by dsimp [n,B,baseEnvelope]; omega
  have sq := Nat.mul_le_mul (show n ≤ B+1 by omega) (show n ≤ B+1 by omega)
  rw [← Nat.pow_two (B+1)] at sq
  change n*n ≤ (B+1)^2 at sq
  have lin : B+1 ≤ (B+1)^2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (n:=B+1) (by omega) (show 1 ≤ 2 by decide)
  have inputLen := QueryEncoding.request_size hist x
  change (QueryEncoding.requestWord x k hs).length ≤ 2*x.length+2*n*n+3*n+2 at inputLen
  rw [Nat.mul_assoc] at inputLen
  have comp := Poly.comp_bound ⟨10,2⟩ (baseEnvelope p) x.length
  change 10*(B+1)^2 ≤ (requestEnvelope p).at x.length at comp
  have linear : 2*x.length+3*n+2 ≤ 5*B := by
    change FixedVerifier.width p x+x.length+2 ≤ B at room
    change n+x.length+2 ≤ B at room
    omega
  omega

private def workEnvelope (lister : Poly) : Poly := lister.plus ⟨4,1⟩

private def positiveTime (c : Code) (listTime checkTime : Poly) : Poly :=
  let env := workEnvelope listTime
  ((((listTime.plus (CandidateCutoffCode.cutoffTime.comp env)).plus
    ((CandidateClassifyCode.classifyTime (SearchRoundIO.restrictedTime checkTime)).comp env)).plus
      ((Poly.mk 81250 3).comp env)).plus ⟨2*MachineEnumeration.frameWidth c+12,0⟩)

private theorem positiveRound_run {c lister : Code} {checkTime listTime : Poly} {check : Checker}
    (verify : CertificateCode.Implements c checkTime check) (list : CandidateLister check lister listTime)
    (s : State) (x : Word) (n : Nat) (hs : List Word) (active : SearchLoopCode.Active x (n+1) hs s)
    (request : s.reg 95 = QueryEncoding.requestWord x (n+1) hs) :
    ∃ u t, Run emptyLanguage (positiveRound c lister) s u t 0 ∧
      t ≤ (positiveTime lister listTime checkTime).at (s.reg 95).length ∧ Outcome check x (n+1) hs u := by
  let req := QueryEncoding.requestWord x (n+1) hs
  let m := req.length
  let a := s.write 81 (ones (n+1))
  have copy : Run emptyLanguage (.write 81 (.copy 1)) s a 1 0 := by
    simpa [a,Expr.eval,active.2.1] using stepWrite s 81 (.copy 1)
  have prepared : a.reg 95 = req := by simp [a,req,request]
  obtain ⟨out,t₀,cs,listed,listCost,empty,packed,formed,genuine⟩ := list x (n+1) hs
  have listed' : Run emptyLanguage lister (State.input (a.reg 95)) out t₀ 0 := by rwa [prepared]
  obtain ⟨b,invoke,data,queue,keep⟩ := ReplayFrameCode.invoke_run a
    (base:=200) (src:=95) (dst:=150) (by decide) (by simpa [a] using active.2.2.2.2) listed'
  let L := (QueryEncoding.pack (cs.map CandidateReadCode.candidateWord)).length
  let K := L+2
  have listWord : b.reg 150 = QueryEncoding.pack (cs.map CandidateReadCode.candidateWord) := data.trans packed
  have listLen : (b.reg 150).length = L := congrArg List.length listWord
  have count : cs.length ≤ L := by
    simpa only [List.length_map,L] using CandidateCutoffCode.pack_count_le (cs.map CandidateReadCode.candidateWord)
  obtain ⟨d,t₁,cutoff,cutoffCost,cap,frame⟩ := CandidateCutoffCode.cutoff_run b
  have kept (r : Nat) (notChanged : r ∉ [21,22,23,24,25,151,152,153,154]) (diff : r ≠ 150) (low : r < 200) :
      d.reg r = a.reg r := (frame.2 r notChanged).trans (keep r diff (Or.inl low))
  have raw : d.reg 150 = QueryEncoding.pack (cs.map CandidateReadCode.candidateWord) :=
    (frame.2 150 (by decide)).trans listWord
  have rawLen : (d.reg 150).length = L := congrArg List.length raw
  have log : d.reg 151 = ones K.log2 := by simpa [K,listLen] using cap
  have dimension : d.reg 81 = ones (n+1) := by rw [kept _ (by decide) (by decide) (by decide)]; simp [a]
  have original : d.reg 95 = req := (kept _ (by decide) (by decide) (by decide)).trans prepared
  obtain ⟨e,t₂,classify,classCost,found,weighted,h₀,h₁,h₂,h₃,hq⟩ :=
    CandidateClassifyCode.classify_run (SearchRoundIO.restrictedImplements verify) d cs (n+1) K req
      (by dsimp [K]; omega) formed raw dimension original log
  have live : SearchLoopCode.Active x (n+1) hs e :=
    ⟨h₀.trans ((kept _ (by decide) (by decide) (by decide)).trans (by simp [a,active.1])),h₁,
      h₂.trans ((kept _ (by decide) (by decide) (by decide)).trans (by simp [a,active.2.2.1])),
      h₃.trans ((kept _ (by decide) (by decide) (by decide)).trans (by simp [a,active.2.2.2.1])),
      hq.trans (frame.1.trans (queue.trans empty))⟩
  have found' : e.reg 4 = [RoundSemantics.found (check x) hs K cs] := by
    have test : RestrictedVerifier.check check req = fun w => check x (AffineSearch.decode hs w) := by
      funext w
      simp [RestrictedVerifier.check,req]
    simpa only [RoundSemantics.found,test] using found
  obtain ⟨u,t₃,cut,cutCost,result⟩ := decideOrCut_run e check x n hs K cs live formed
    (by dsimp [K]; omega) genuine found' weighted
  let env := workEnvelope listTime
  let B := env.at m
  have fits := (listed.fits (State.input_fits (x:=req) (w:=[]) (n:=m) (Nat.le_refl _) (by simp))).1 0
  change out.output.length ≤ m+t₀ at fits
  have bytes : L ≤ m+t₀ := by simpa only [packed,L] using fits
  have wi : n+1 ≤ m := by
    simpa [req,m] using HullQueryLanguage.width_le req
  have envGe := Poly.plus_bound listTime ⟨4,1⟩ m
  rw [show (Poly.mk 4 1).at m = 4*(m+1) by simp [Poly.at]] at envGe
  change listTime.at m + 4*(m+1) ≤ B at envGe
  change t₀ ≤ listTime.at m at listCost
  have room : n+1+m+L+2 ≤ B := by omega
  have size : L ≤ B := by omega
  have cutoffUpper : t₁ ≤ (CandidateCutoffCode.cutoffTime.comp env).at m := by
    rw [listLen] at cutoffCost
    exact Nat.le_trans cutoffCost (Nat.le_trans (CandidateCutoffCode.cutoffTime.mono size) (Poly.comp_bound ..))
  let probeTime := CandidateClassifyCode.classifyTime (SearchRoundIO.restrictedTime checkTime)
  have classifyUpper : t₂ ≤ (probeTime.comp env).at m := by
    rw [rawLen] at classCost
    exact Nat.le_trans classCost (Nat.le_trans
      (CandidateClassifyCode.classifyBound _ room (Nat.le_trans count size)) (Poly.comp_bound ..))
  have maskUpper : t₃ ≤ ((Poly.mk 81250 3).comp env).at m := by
    have expanded := weighted_length K cs
    rw [weighted] at cutCost
    change _ ≤ 5*L at expanded
    have scaled := Nat.mul_le_mul_left 650 (Nat.pow_le_pow_left
      (show n+1+(SplitBranchCode.candidatesWord ((RoundSemantics.large K cs).map AffineSearch.pack)).length+1
        ≤ 5*(B+1) by omega) 3)
    rw [Nat.mul_pow,← Nat.mul_assoc] at scaled
    change _ ≤ 81250*(B+1)^3 at scaled
    exact Nat.le_trans cutCost (Nat.le_trans scaled (Poly.comp_bound ⟨81250,3⟩ env m))
  refine ⟨u,_,.seq copy (.seq invoke (.seq cutoff (.seq classify cut))),?_,result⟩
  rw [request]
  let tAB := listTime.plus (CandidateCutoffCode.cutoffTime.comp env)
  let tABC := tAB.plus (probeTime.comp env)
  let tABCD := tABC.plus ((Poly.mk 81250 3).comp env)
  have ab := Poly.plus_bound listTime (CandidateCutoffCode.cutoffTime.comp env) m
  have abc := Poly.plus_bound tAB (probeTime.comp env) m
  have abcd := Poly.plus_bound tABC ((Poly.mk 81250 3).comp env) m
  change listTime.at m+(CandidateCutoffCode.cutoffTime.comp env).at m ≤ tAB.at m at ab
  change tAB.at m+(probeTime.comp env).at m ≤ tABC.at m at abc
  change tABC.at m+((Poly.mk 81250 3).comp env).at m ≤ tABCD.at m at abcd
  have overhead := Poly.add_const_bound tABCD (2*MachineEnumeration.frameWidth lister+12) m
  change _ ≤ (positiveTime lister listTime checkTime).at m at overhead ⊢
  omega

private def roundTime (lister : Code) (listTime checkTime width : Poly) : Poly :=
  let input := requestEnvelope width
  (((SearchRoundIO.terminalTime checkTime).comp input).plus
    ((positiveTime lister listTime checkTime).comp input)).plus ((Poly.mk 63 1).comp input)

theorem round_run {c lister : Code} {checkTime listTime : Poly} {check : Checker}
    (verify : CertificateCode.Implements c checkTime check) (list : CandidateLister check lister listTime)
    (p : Poly) : SearchLoopCode.Round (answer check) (FixedVerifier.width p) (compile c lister)
      (roundTime lister listTime checkTime p) := by
  intro x k hs s history active
  let req := QueryEncoding.requestWord x k hs
  let m := req.length
  let input := requestEnvelope p
  let terminal := (SearchRoundIO.terminalTime checkTime).comp input
  let positive := (positiveTime lister listTime checkTime).comp input
  let request := (Poly.mk 63 1).comp input
  let time := roundTime lister listTime checkTime p
  have reqBound : m ≤ input.at x.length := request_bound p x history
  have len : x.length+k ≤ m := by
    dsimp [m,req,QueryEncoding.requestWord]
    simp only [QueryEncoding.put_length,List.length_replicate]
    omega
  have setupBound : 14*(x.length+k)+51 ≤ request.at x.length := by
    have comp := Poly.comp_bound ⟨63,1⟩ input x.length
    rw [show (Poly.mk 63 1).at (input.at x.length) = 63*(input.at x.length+1) by simp [Poly.at]] at comp
    change 63*(input.at x.length+1) ≤ request.at x.length at comp
    omega
  have branchTotal := Poly.plus_bound terminal positive x.length
  have sum := Poly.plus_bound (terminal.plus positive) request x.length
  change (terminal.plus positive).at x.length + request.at x.length ≤ time.at x.length at sum
  obtain ⟨a,setup,encoded,frame⟩ := SearchRoundIO.requestCode_run s x k hs active
  have live := active_of_frame active frame (by decide) (by decide) (by decide) (by decide)
  cases k with
  | zero =>
    have empty : (Test.empty 1).eval a = true := by simp [Test.eval,live.2.1,ones]
    obtain ⟨u,t,run,bound,stopped,result⟩ := SearchRoundIO.terminal_run verify a _ encoded
    have bounded : t ≤ terminal.at x.length := Nat.le_trans bound
      (Nat.le_trans ((SearchRoundIO.terminalTime checkTime).mono reqBound) (Poly.comp_bound ..))
    refine ⟨u,_,.seq setup (runTrue empty run),?_,Or.inl ⟨stopped,?_⟩⟩
    · change _ ≤ time.at x.length
      simp only [Nat.add_zero] at setupBound
      omega
    · simpa [answer,RestrictedVerifier.check,RoundSemantics.answer_zero] using result
  | succ n =>
    have nonempty : (Test.empty 1).eval a = false := by simp [Test.eval,live.2.1,ones]
    obtain ⟨u,t,run,bound,result⟩ := positiveRound_run verify list a x n hs live encoded
    rw [encoded] at bound
    have bounded : t ≤ positive.at x.length := Nat.le_trans bound
      (Nat.le_trans ((positiveTime lister listTime checkTime).mono reqBound) (Poly.comp_bound ..))
    refine ⟨u,_,.seq setup (runFalse nonempty run),?_,result⟩
    change _ ≤ time.at x.length
    omega

/-- Search the restricted instances until a witness is tested or the
remaining instance is certified empty. All rounds have a uniform clock. -/
theorem decide_fp {c lister : Code} {checkTime listTime : Poly} {check : Checker}
    (verify : CertificateCode.Implements c checkTime check) (code : c.pure)
    (list : CandidateLister check lister listTime) (listCode : lister.pure) (p : Poly) :
    FP (fun x => [RoundSemantics.answer (check x) (FixedVerifier.width p x) []]) :=
  SearchLoopCode.fp_of_round (SearchInitCode.setup_pure p) (compile_pure code listCode)
    (SearchInitCode.setup_run p) (round_run verify list p) (SearchInitCode.width_bound p)

end SearchRoundProgram
