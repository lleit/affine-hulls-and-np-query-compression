module

public import ReplayParameters
public import CandidateReadCode
public import QueryHeaderCode

@[expose] public section

namespace CandidatePipeline

open ComplexityModel
open HullBatchMachine (ones stepWrite)

private def decodeOutputs : Code :=
  .seq (.write 2 (.copy 0))
    (.seq QueryHeaderCode.widthFromRequest
      (.seq (.write 81 (.copy 4))
        (.seq (.write 99 (.copy 14))
          (.seq CandidateReadCode.readCandidateList (.write 0 (.copy 100))))))

private theorem decodeOutputs_pure : decodeOutputs.pure := by
  simp [decodeOutputs,Code.allowed,QueryHeaderCode.widthFromRequest_pure,
    CandidateReadCode.readCandidateList_pure]

private theorem decodeOutputs_run (s : State) (request : Word) (words : List Word)
    (input : s.reg 0 = request) (outputs : s.reg 14 = QueryEncoding.pack words) :
    let k := (QueryEncoding.readRequest request).width
    ∃ out t, Run emptyLanguage decodeOutputs s out t 0 ∧
      t ≤ 21*request.length+600*(k+(s.reg 14).length+1)^3+38 ∧
      out.output = QueryEncoding.pack ((CandidateReadCode.decodeList k words).reverse.map
        CandidateReadCode.candidateWord) ∧ out.queries = s.queries := by
  dsimp only
  let k := (QueryEncoding.readRequest request).width
  let a := s.write 2 request
  have stage : Run emptyLanguage (.write 2 (.copy 0)) s a 1 0 := by
    simpa [a,Expr.eval,input] using stepWrite s 2 (.copy 0)
  obtain ⟨b,t₁,parser,cost₁,width,q,frame⟩ := QueryHeaderCode.widthFromRequest_run a
  have source : a.reg 2 = request := by simp [a]
  rw [source] at width cost₁
  let c := b.write 81 (ones k)
  have copyWidth : Run emptyLanguage (.write 81 (.copy 4)) b c 1 0 := by
    simpa [c,Expr.eval,width,k] using stepWrite b 81 (.copy 4)
  have saved : c.reg 14 = s.reg 14 := by
    simp [c,a,frame 14 (by decide) (by decide) (by decide) (by decide)]
  let d := c.write 99 (s.reg 14)
  have copyRaw : Run emptyLanguage (.write 99 (.copy 14)) c d 1 0 := by
    simpa [d,Expr.eval,saved] using stepWrite c 99 (.copy 14)
  obtain ⟨e,t₂,decoding,cost₂,result,_,keep⟩ := CandidateReadCode.readCandidateList_run d k words
    (by simp [d,c]) (by simp [d,outputs])
  let out := e.write 0 (e.reg 100)
  have output : Run emptyLanguage (.write 0 (.copy 100)) e out 1 0 := .write
  refine ⟨out,_,.seq stage (.seq parser (.seq copyWidth (.seq copyRaw (.seq decoding output)))),
    ?_,?_,?_⟩
  · simp only [d,HullBatchMachine.write_same] at cost₂
    change _ ≤ 21*request.length+600*(k+(s.reg 14).length+1)^3+38
    omega
  · simpa only [out,State.output,HullBatchMachine.write_same] using result
  · exact keep.1.trans q

/-- A complete polynomial-time machine for preparing the affine candidate
list. The output is a packed list of offsets and triangular schedules. -/
theorem decoded_machine (c : Code) (p : Poly) (a b : Nat) :
    ∃ code : Code, ∃ time : Poly, code.pure ∧ ∀ request,
      let k := (QueryEncoding.readRequest request).width
      let cap := (request.length+2).log2*a+b
      ∃ out ticks words, Run emptyLanguage code (State.input request) out ticks 0 ∧
        ticks ≤ time.at request.length ∧ out.queries = [] ∧
        out.output = QueryEncoding.pack ((CandidateReadCode.decodeList k words).reverse.map
          CandidateReadCode.candidateWord) ∧ words.length ≤ 2^cap ∧
        ∀ w, w ∈ words ↔ w ∈ MachineEnumeration.compiledCandidates c request (p.at request.length) cap := by
  obtain ⟨setupTime,prepBound⟩ := ReplayParameters.prepareBound_poly c p a b
  obtain ⟨runTime,runBound⟩ := ReplayListCode.collectionBound_poly c p a b
  let replayTime := setupTime.plus runTime
  let envelope := replayTime.plus ⟨3,1⟩
  let decodeTime := (Poly.mk 700 3).comp envelope
  let time := (replayTime.plus decodeTime).plus ⟨2,0⟩
  let code : Code := .seq (ReplayParameters.prepare c p a b)
    (.seq (ReplayListCode.collectCandidates c) decodeOutputs)
  have pure : code.pure := ⟨ReplayParameters.prepare_pure ..,ReplayListCode.collectCandidates_pure c,
    decodeOutputs_pure⟩
  refine ⟨code,time,pure,fun request => ?_⟩
  dsimp only
  let n := request.length
  let k := (QueryEncoding.readRequest request).width
  obtain ⟨s,t₀,prep,time₀,input,cap,clock,queueBound,empty,high⟩ :=
    ReplayParameters.prepare_run c p a b request
  obtain ⟨u,t₁,words,list,time₁,data,empty',preserve,count,member⟩ :=
    ReplayListCode.collectCandidates_run c s (p.at n) ((n+2).log2*a+b) clock queueBound cap empty high
  rw [input] at time₁ member
  obtain ⟨out,t₂,decode,time₂,result,queue⟩ := decodeOutputs_run u request words (preserve.trans input) data
  have tBefore : t₀+t₁ ≤ replayTime.at n := by
    have a₀ := Nat.le_trans time₀ (prepBound n)
    have a₁ := Nat.le_trans time₁ (runBound request)
    have add := Poly.plus_bound setupTime runTime n
    change t₁ ≤ runTime.at n at a₁
    change setupTime.at n + runTime.at n ≤ replayTime.at n at add
    omega
  have stored := ((Run.seq prep list).fits (State.input_fits (x:=request) (w:=[])
    (n:=n) (Nat.le_refl _) (by simp))).1 14
  have dim : k ≤ n := HullQueryLanguage.width_le request
  have env := Poly.plus_bound replayTime ⟨3,1⟩ n
  rw [show (Poly.mk 3 1).at n = 3*(n+1) by simp [Poly.at]] at env
  change replayTime.at n + 3*(n+1) ≤ envelope.at n at env
  have room : k+(u.reg 14).length ≤ envelope.at n := by omega
  have len : n ≤ envelope.at n := by omega
  have qpower : envelope.at n + 1 ≤ (envelope.at n+1)^3 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (show 1 ≤ envelope.at n+1 by omega)
      (show 1 ≤ 3 by decide)
  have polyClock : t₂ ≤ decodeTime.at n := by
    have a := Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left (show k+(u.reg 14).length+1 ≤ envelope.at n+1 by omega) 3)
    have b := Poly.comp_bound ⟨700,3⟩ envelope n
    change t₂ ≤ 21*n+600*(k+(u.reg 14).length+1)^3+38 at time₂
    change 700*(envelope.at n+1)^3 ≤ decodeTime.at n at b
    omega
  refine ⟨out,_,words,.seq prep (.seq list decode),?_,queue.trans empty',result,count,member⟩
  have sum := Poly.plus_bound replayTime decodeTime n
  have extra := Poly.plus_bound (replayTime.plus decodeTime) ⟨2,0⟩ n
  rw [show (Poly.mk 2 0).at n = 2 by simp [Poly.at]] at extra
  change (replayTime.plus decodeTime).at n + 2 ≤ time.at n at extra
  change _ ≤ time.at n
  omega

theorem decoded_fp (c : Code) (p : Poly) (a b : Nat) :
    ∃ f : WordFunction, FP f ∧ ∀ request,
      let k := (QueryEncoding.readRequest request).width
      let cap := (request.length+2).log2*a+b
      ∃ words : List Word,
        f request = QueryEncoding.pack ((CandidateReadCode.decodeList k words).reverse.map
          CandidateReadCode.candidateWord) ∧ words.length ≤ 2^cap ∧
        ∀ w, w ∈ words ↔ w ∈ MachineEnumeration.compiledCandidates c request (p.at request.length) cap := by
  classical
  obtain ⟨code,time,pure,runs⟩ := decoded_machine c p a b
  let output (request : Word) : State := Classical.choose (runs request)
  let f (request : Word) : Word := (output request).output
  refine ⟨f,⟨code,time,pure,fun x => ?_⟩,fun x => ?_⟩
  · obtain ⟨t,_,run,bound,_⟩ := Classical.choose_spec (runs x)
    exact ⟨output x,t,run,bound,rfl⟩
  · obtain ⟨_,words,_,_,_,data,count,member⟩ := Classical.choose_spec (runs x)
    exact ⟨words,data,count,member⟩

end CandidatePipeline
