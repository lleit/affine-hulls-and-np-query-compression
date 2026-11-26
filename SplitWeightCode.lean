module

public import CandidateReadCode
public import ComplexityModel.ParityCode
public import SearchSplitter

@[expose] public section

namespace SplitWeightCode

open ComplexityModel
open QueryEncoding (pack take)
open CandidateReadCode (pivotWord)
open HullBatchMachine (ones stepWrite runFalse runTrue normalize normalize_run)
open WordCode (Preserves preserves_write)

private def multiplyWeight : Code :=
  .seq (.write 122 (.copy 112)) (normalize 122 112 123)

private def update : Code :=
  .branch (.head 114)
    (.branch (.head 120) multiplyWeight (.write 112 .empty))
    (.branch (.head 120) (.write 112 .empty) multiplyWeight)

private theorem multiplyWeight_run (s : State) (w : Nat) (weight : s.reg 112 = ones w) :
    ∃ out t, Run emptyLanguage multiplyWeight s out t 0 ∧ t ≤ 5*w+10 ∧
      out.reg 112 = ones (w+w) ∧ Preserves s out [112,122,123] := by
  let a := s.write 122 (ones w)
  have load : Run emptyLanguage (.write 122 (.copy 112)) s a 1 0 := by
    simpa [a,Expr.eval,weight] using stepWrite s 122 (.copy 112)
  obtain ⟨out,t,state,bound,acc,q,frame⟩ :=
    normalize_run (src:=122) (dst:=112) (flag:=123) (by decide) (by decide) (by decide) a
  refine ⟨out,_,.seq load state,?_,?_,?_⟩
  · simp [a] at bound
    omega
  · simpa [a,weight,ones] using acc
  · exact ((preserves_write s 122 _).mono (by simp)).trans
      ⟨q,fun r hr => by
        simp at hr
        simpa [a,hr.2.1] using frame r hr.2.1 hr.1 hr.2.2⟩

private theorem update_run (s : State) (w : Nat) (bit parity : Bool)
    (choice : s.reg 114 = [bit]) (dot : s.reg 120 = [parity])
    (weight : s.reg 112 = ones w) :
    ∃ out t, Run emptyLanguage update s out t 0 ∧ t ≤ 5*w+12 ∧
      out.reg 112 = ones (if bit == parity then w+w else 0) ∧ Preserves s out [112,122,123] := by
  have left : (Test.head 114).eval s = bit := by simp [Test.eval,choice]
  have right : (Test.head 120).eval s = parity := by simp [Test.eval,dot]
  have clear : Run emptyLanguage (.write 112 .empty) s (s.write 112 []) 1 0 := .write
  obtain ⟨out,t,multiply,bound,data,frame⟩ := multiplyWeight_run s w weight
  cases bit <;> cases parity
  · exact ⟨out,t+2,runFalse left (runFalse right multiply),by omega,data,frame⟩
  · exact ⟨s.write 112 [],3,runFalse left (runTrue right clear),by omega,
      by simp,(preserves_write ..).mono (by simp)⟩
  · exact ⟨s.write 112 [],3,runTrue left (runFalse right clear),by omega,
      by simp,(preserves_write ..).mono (by simp)⟩
  · exact ⟨out,t+2,runTrue left (runTrue right multiply),by omega,data,frame⟩

private def pivotStep : Code :=
  .seq (.write 118 (.copy 113))
    (.seq (.write 119 (.tail 115))
      (.seq (ParityCode.dot 118 119 120 121) update))

/-- Advance one weighted candidate in the greedy splitter. The scheduled
rows are in register 111, the unary weight in 112, the known suffix in
113, and the proposed next bit in 114. -/
def advance : Code :=
  .seq (FieldCode.takeField 111 115 116 117)
    (.branch (.empty 115) .skip pivotStep)

theorem advance_pure : advance.pure := by
  simp [advance,pivotStep,update,multiplyWeight,normalize,HullBatchMachine.set,
    HullBatchMachine.scanCore,Code.allowed,ParityCode.dot_allowed,FieldCode.takeField_pure]

def footprint : List Nat :=
  [111,112,115,116,117,118,119,120,121,122,123]

theorem advance_run (s : State) (c : Splitter.Candidate) (bit : Bool) (suffix : Word)
    (data : s.reg 111 = pack (c.steps.map pivotWord))
    (weight : s.reg 112 = ones c.weight) (bits : s.reg 113 = suffix) (choice : s.reg 114 = [bit]) :
    let next := Splitter.advance bit suffix c
    ∃ out t, Run emptyLanguage advance s out t 0 ∧
      t ≤ 14*(s.reg 111).length+13*suffix.length+5*c.weight+50 ∧
      out.reg 111 = pack (next.steps.map pivotWord) ∧ out.reg 112 = ones next.weight ∧
      Preserves s out footprint := by
  dsimp only
  obtain ⟨a,t₁,decode,parseTime,rest,field,queue,kept⟩ :=
    FieldCode.takeField_run s (src:=111) (dst:=115) (scratch:=116) (flag:=117)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have first : Preserves s a footprint := ⟨queue,fun r hr => by
    simp [footprint] at hr
    exact kept r (by omega) (by omega) (by omega) (by omega)⟩
  have initial : a.reg 112 = ones c.weight :=
    (kept 112 (by decide) (by decide) (by decide) (by decide)).trans weight
  have flag : a.reg 114 = [bit] := (first.2 114 (by decide)).trans choice
  cases order : c.steps with
  | nil =>
    have none : (Test.empty 115).eval a = true := by
      simp [Test.eval,field,data,order,pack,take]
    exact ⟨a,_,.seq decode (runTrue none .skip),by omega,
      by simp [rest,data,order,pack,take,Splitter.advance],by simpa [Splitter.advance,order] using initial,first⟩
  | cons p ps =>
    have htake : take (s.reg 111) = (pivotWord p,pack (ps.map pivotWord)) := by
      rw [data,order,List.map_cons,pack,QueryEncoding.take_put]
    rw [htake] at field rest
    cases p with
    | none =>
      have none : (Test.empty 115).eval a = true := by simp [Test.eval,field,pivotWord]
      exact ⟨a,_,.seq decode (runTrue none .skip),by omega,
        by simpa [Splitter.advance,order] using rest,by simpa [Splitter.advance,order] using initial,first⟩
    | some row =>
      have present : (Test.empty 115).eval a = false := by simp [Test.eval,field,pivotWord]
      let b := a.write 118 suffix
      let d := b.write 119 row
      have storeSuffix : Run emptyLanguage (.write 118 (.copy 113)) a b 1 0 := by
        simpa [b,Expr.eval,first.2 113 (by decide),bits] using stepWrite a 118 (.copy 113)
      have storeRow : Run emptyLanguage (.write 119 (.tail 115)) b d 1 0 := by
        simpa [b,d,Expr.eval,field,pivotWord] using stepWrite b 119 (.tail 115)
      obtain ⟨mid,t₂,dot,time₂,value,saved⟩ :=
        ParityCode.dot_run d (a:=118) (b:=119) (dst:=120) (flag:=121)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have decoded : mid.reg 120 = [Splitter.dot row suffix] := by
        simpa [d,b,AffineSearch.dot_swap_model] using value
      have midWeight : mid.reg 112 = ones c.weight := by
        simp [saved.2 112 (by decide),d,b,initial]
      have midChoice : mid.reg 114 = [bit] := by
        simp [saved.2 114 (by decide),d,b,flag]
      obtain ⟨out,t₃,action,time₃,answer,frame⟩ :=
        update_run mid c.weight bit (Splitter.dot row suffix) midChoice decoded midWeight
      have middle : Preserves a mid footprint :=
        ((preserves_write a 118 _).mono (by simp [footprint])).trans
          (((preserves_write b 119 _).mono (by simp [footprint])).trans
            (saved.mono (by intro r hr; simp [footprint] at hr ⊢; omega)))
      refine ⟨out,_,.seq decode (runFalse present (.seq storeSuffix (.seq storeRow (.seq dot action)))),
        ?_,?_,by simpa [Splitter.advance,order] using answer,
        first.trans (middle.trans (frame.mono (by simp [footprint])))⟩
      · simp [d,b] at time₂
        omega
      · rw [frame.2 111 (by decide),saved.2 111 (by decide)]
        simpa [d,b,Splitter.advance,order] using rest

end SplitWeightCode
