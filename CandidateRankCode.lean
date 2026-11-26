module

public import CandidateReadCode
public import QueryHeaderCode
public import SearchSplitter

@[expose] public section

namespace CandidateRankCode

open ComplexityModel
open QueryEncoding (pack take)
open CandidateReadCode (pivotWord packedPivots)
open HullBatchMachine (ones stepWrite runFalse runTrue)
open WordCode (Preserves preserves_write)

private def countField : Code :=
  .branch (.empty 98) .skip (.write 1 (.cons true 1))

private def count_run (s : State) (p : Option Word) (field : s.reg 98 = (pivotWord p).reverse) :
    ∃ u t, Run emptyLanguage countField s u t 0 ∧ t ≤ 2 ∧
      u.reg 1 = ones (Splitter.rank [p]) ++ s.reg 1 ∧ Preserves s u [1] := by
  cases p with
  | none =>
    exact ⟨s,2,runTrue (by simp [Test.eval,field,pivotWord]) .skip,by decide,rfl,⟨rfl,fun _ _ => rfl⟩⟩
  | some row =>
    let u := s.write 1 (true :: s.reg 1)
    have present : (Test.empty 98).eval s = false := by
      simp [Test.eval,field,pivotWord]
    exact ⟨u,2,runFalse present .write,by decide,by simp [u,Splitter.rank],preserves_write ..⟩

private def scan : Code :=
  .loop (.head 107)
    (.seq (FieldCode.takeReverse 97 98) (.seq countField (.write 107 (.tail 107))))

private def rankRegs : List Nat := [1,97,98,107]

private theorem scan_run (s : State) (ps : List (Option Word)) (cap : Nat)
    (input : s.reg 97 = pack (ps.map pivotWord))
    (fuel : s.reg 107 = ones ps.length) (size : (s.reg 97).length ≤ cap) :
    ∃ u t, Run emptyLanguage scan s u t 0 ∧ t ≤ (8*cap+12)*ps.length+1 ∧
      u.reg 1 = ones (Splitter.rank ps) ++ s.reg 1 ∧ Preserves s u rankRegs := by
  induction ps generalizing s with
  | nil =>
    exact ⟨s,1,.loopFalse (by simp [Test.eval,fuel]),by simp,rfl,⟨rfl,fun _ _ => rfl⟩⟩
  | cons p rest ih =>
    obtain ⟨a,t₁,takeRun,time₁,tail,word,queue,kept⟩ :=
      FieldCode.takeReverse_run s (src:=97) (dst:=98) (by decide)
    have takeField : take (s.reg 97) = (pivotWord p,pack (rest.map pivotWord)) := by
      rw [input,List.map_cons,pack,QueryEncoding.take_put]
    rw [takeField] at tail word
    obtain ⟨b,t₂,count,time₂,new,frame⟩ := count_run a p word
    let v := b.write 107 (ones rest.length)
    have exactFuel : b.reg 107 = ones (p::rest).length :=
      (frame.2 107 (by decide)).trans ((kept 107 (by decide) (by decide)).trans fuel)
    have debit : Run emptyLanguage (.write 107 (.tail 107)) b v 1 0 := by
      simpa [v,Expr.eval,exactFuel,List.length_cons] using stepWrite b 107 (.tail 107)
    have remaining : v.reg 97 = pack (rest.map pivotWord) := by simp [v,frame.2 97 (by decide),tail]
    have noGrowth : (v.reg 97).length ≤ cap := by
      have narrow := QueryEncoding.take_lengths (s.reg 97)
      rw [takeField] at narrow
      rw [remaining]
      simp at narrow
      omega
    obtain ⟨u,t,loop,time,answer,others⟩ := ih v remaining (by simp [v]) noGrowth
    refine ⟨u,_,.loopTrue (by simp [Test.eval,fuel,List.length_cons])
      (.seq takeRun (.seq count debit)) loop,?_ ,?_,?_⟩
    · rw [List.length_cons,Nat.mul_succ]
      omega
    · cases p <;> simp [answer, v, new, kept 1 (by decide) (by decide),
        ones, Splitter.rank, List.replicate_succ', List.append_assoc]
    · have first : Preserves s a rankRegs := ⟨queue,fun r hr => by
        simp [rankRegs] at hr
        exact kept r (by omega) (by omega)⟩
      exact first.trans ((frame.mono (by simp [rankRegs])).trans
        (((preserves_write b 107 _).mono (by simp [rankRegs])).trans others))

/-- Count the true pivot rows and write the rank in unary into register 1.
Read the packed reverse schedule in register 94 and its width in 81. -/
def rankCode : Code :=
  .seq (.write 97 (.copy 94))
    (.seq (.write 107 (.copy 81)) (.seq (.write 1 .empty) scan))

theorem rankCode_pure : rankCode.pure := by
  simp [rankCode,scan,countField,Code.allowed,FieldCode.takeReverse_pure]

theorem rankCode_run (s : State) (ps : List (Option Word))
    (width : s.reg 81 = ones ps.length) (packed : s.reg 94 = packedPivots ps) :
    ∃ out t, Run emptyLanguage rankCode s out t 0 ∧
      t ≤ (8*(s.reg 94).length+12)*ps.length+7 ∧
      out.reg 1 = ones (Splitter.rank ps) ∧ Preserves s out rankRegs := by
  let a := s.write 97 (s.reg 94)
  let b := a.write 107 (ones ps.length)
  let v := b.write 1 []
  have copy : Run emptyLanguage (.write 97 (.copy 94)) s a 1 0 := .write
  have meter : Run emptyLanguage (.write 107 (.copy 81)) a b 1 0 := by
    simpa [b,a,Expr.eval,width] using stepWrite a 107 (.copy 81)
  have clear : Run emptyLanguage (.write 1 .empty) b v 1 0 := .write
  obtain ⟨out,t,loop,time,ans,frame⟩ := scan_run v ps.reverse (s.reg 94).length
    (by simp [v,b,a,packed,packedPivots]) (by simp [v,b]) (by simp [v,b,a])
  refine ⟨out,_,.seq copy (.seq meter (.seq clear loop)),?_,
    by simpa [v,Splitter.rank_reverse] using ans,?_⟩
  · rw [List.length_reverse] at time
    omega
  · exact ((preserves_write s 97 _).mono (by simp [rankRegs])).trans
      (((preserves_write a 107 _).mono (by simp [rankRegs])).trans
        (((preserves_write b 1 _).mono (by simp [rankRegs])).trans frame))

end CandidateRankCode
