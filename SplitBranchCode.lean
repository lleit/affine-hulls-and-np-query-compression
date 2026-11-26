module

public import SplitWeightCode

@[expose] public section

namespace SplitBranchCode

open ComplexityModel
open QueryEncoding (pack put take)
open CandidateReadCode (pivotWord)
open HullBatchMachine (ones stepWrite normalize normalize_run)
open WordCode (Preserves preserves_write putField setBit setBit_run)
open Splitter (Candidate)

def packet (c : Candidate) : Word := put (ones c.weight) (pack (c.steps.map pivotWord))

def candidatesWord (cs : List Candidate) : Word := pack (cs.map packet)

private def scanOne (register destination : Nat) : Code := FieldCode.takeField register destination 133 134

private def one : Code :=
  .seq (scanOne 124 132)
    (.seq (scanOne 132 112)
      (.seq (.write 111 (.copy 132))
        (.seq SplitWeightCode.advance
          (.seq (.write 135 (.copy 111))
            (.seq (putField 112 135 136 137 138)
              (.seq (putField 135 126 136 137 138)
                (.seq (.write 137 (.copy 112)) (normalize 137 127 138))))))))

private def slots : List Nat :=
  SplitWeightCode.footprint ++ [124,126,127,132,133,134,135,136,137,138]

private theorem one_pure : one.pure := by
  simp [one,scanOne,Code.allowed,FieldCode.takeField_pure,SplitWeightCode.advance_pure,
    WordCode.putField_allowed,normalize,HullBatchMachine.set,HullBatchMachine.scanCore]

private theorem one_run (s : State) (C : Candidate) (tail : List Candidate) (suffix : Word)
    (bit : Bool) (input : s.reg 124 = candidatesWord (C::tail))
    (known : s.reg 113 = suffix) (mode : s.reg 114 = [bit]) :
    let next := Splitter.advance bit suffix C
    ∃ out t, Run emptyLanguage one s out t 0 ∧
      t ≤ 180*(s.reg 124).length+13*suffix.length+185 ∧
      out.reg 124 = candidatesWord tail ∧ out.reg 126 = put (packet next) (s.reg 126) ∧
      out.reg 127 = ones next.weight ++ s.reg 127 ∧ Preserves s out slots := by
  dsimp only
  let next := Splitter.advance bit suffix C
  let P := pack (C.steps.map pivotWord)
  have read : take (s.reg 124) = (packet C,candidatesWord tail) := by
    simp [input,candidatesWord,pack]
  obtain ⟨a,t₁,head,cost₁,left,data,q,keep⟩ :=
    FieldCode.takeField_run s (src:=124) (dst:=132) (scratch:=133) (flag:=134)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [read] at left data
  obtain ⟨b,t₂,payload,cost₂,rows,weight,q₂,keep₂⟩ :=
    FieldCode.takeField_run a (src:=132) (dst:=112) (scratch:=133) (flag:=134)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [data] at rows weight cost₂
  simp only [packet,QueryEncoding.take_put] at rows weight
  let initial := b.write 111 P
  have stage : Run emptyLanguage (.write 111 (.copy 132)) b initial 1 0 := by
    simpa [initial,P,Expr.eval,rows] using stepWrite b 111 (.copy 132)
  have f₁ : Preserves s a slots := ⟨q,fun r hr => by
    simp [slots,SplitWeightCode.footprint] at hr
    exact keep r (by omega) (by omega) (by omega) (by omega)⟩
  have f₂ : Preserves a b slots := ⟨q₂,fun r hr => by
    simp [slots,SplitWeightCode.footprint] at hr
    exact keep₂ r (by omega) (by omega) (by omega) (by omega)⟩
  have initialFrame : Preserves s initial slots := f₁.trans (f₂.trans ((preserves_write b 111 P).mono
    (by simp [slots,SplitWeightCode.footprint])))
  obtain ⟨u,t₃,advanced,cost₃,newRows,newWeight,f₃⟩ :=
    SplitWeightCode.advance_run initial C bit suffix (by simp [initial,P]) (by simpa [initial] using weight)
      ((initialFrame.2 113 (by decide)).trans known) ((initialFrame.2 114 (by decide)).trans mode)
  have frame : Preserves s u slots :=
    initialFrame.trans (f₃.mono (fun r h => List.mem_append_left _ h))
  let field := u.write 135 (u.reg 111)
  have reserve : Run emptyLanguage (.write 135 (.copy 111)) u field 1 0 := .write
  obtain ⟨v,sealRun, sealed,sealFrame⟩ :=
    WordCode.putField_run field (src:=112) (dst:=135) (tmp:=136) (rev:=137) (flag:=138)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have vw : field.reg 112 = ones next.weight := by simpa [field,next] using newWeight
  have item : v.reg 135 = packet next := by
    simpa [field,packet,newWeight,newRows,next] using sealed
  obtain ⟨w,packed,outWord,outFrame⟩ :=
    WordCode.putField_run v (src:=135) (dst:=126) (tmp:=136) (rev:=137) (flag:=138)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have wweight : w.reg 112 = ones next.weight := by
    rw [outFrame.2 112 (by decide),sealFrame.2 112 (by decide),vw]
  let z := w.write 137 (ones next.weight)
  have save : Run emptyLanguage (.write 137 (.copy 112)) w z 1 0 := by
    simpa [z,Expr.eval,wweight] using stepWrite w 137 (.copy 112)
  obtain ⟨out,t₄,summing,cost₄,score,q₄,f₄⟩ :=
    normalize_run (src:=137) (dst:=127) (flag:=138) (by decide) (by decide) (by decide) z
  have stability (r : Nat) (fixed : r ∉ [135,136,137,138,126]) : w.reg r = u.reg r := by
    have h := outFrame.2 r (by simp at fixed ⊢; omega)
    rw [h,sealFrame.2 r (by simp at fixed ⊢; omega)]
    have ne : r ≠ 135 := by simp at fixed; omega
    simp [field,ne]
  have e₀ : (field.reg 112).length = next.weight := by rw [vw]; simp
  have e₁ : (v.reg 135).length = (packet next).length := by rw [item]
  have e₂ : (z.reg 137).length = next.weight := by simp [z]
  rw [e₀] at sealRun
  rw [e₁] at packed
  rw [e₂] at cost₄
  refine ⟨out,_,.seq head (.seq payload (.seq stage (.seq advanced
    (.seq reserve (.seq sealRun (.seq packed (.seq save summing))))))),?_,?_,?_,?_,?_⟩
  · have original : C.weight ≤ (s.reg 124).length ∧ P.length ≤ (s.reg 124).length ∧
        (packet C).length ≤ (s.reg 124).length := by
      simp only [input,candidatesWord,List.map_cons,pack,QueryEncoding.put_length]
      have h : (packet C).length = 2*C.weight+1+P.length := by simp [packet,QueryEncoding.put_length,P]
      omega
    have controls :
        next.weight ≤ 2*C.weight ∧ (pack (next.steps.map pivotWord)).length ≤ P.length := by
      cases e : C.steps with
      | nil => simp [next,Splitter.advance,e,P]; omega
      | cons h t =>
        cases h with
        | none => simp [next,Splitter.advance,e,P,pack,QueryEncoding.put_length]; omega
        | some row =>
          simp [next,Splitter.advance,e,P,pack,QueryEncoding.put_length]
          split <;> omega
    have packetSize : (packet next).length = 2*next.weight+1+(pack (next.steps.map pivotWord)).length := by
      simp [packet,QueryEncoding.put_length]
    simp [initial] at cost₃
    change t₂ ≤ 14*(packet C).length+17 at cost₂
    omega
  · rw [f₄ 124 (by decide) (by decide) (by decide)]
    simp [z,stability 124 (by decide),f₃.2 124 (by decide),initial,
      keep₂ 124 (by decide) (by decide) (by decide) (by decide), left]
  · rw [f₄ 126 (by decide) (by decide) (by decide)]
    have same : v.reg 126 = s.reg 126 := by
      rw [sealFrame.2 126 (by decide)]
      simp [field,f₃.2 126 (by decide),initial,
        keep₂ 126 (by decide) (by decide) (by decide) (by decide),
        keep 126 (by decide) (by decide) (by decide) (by decide)]
    simp [z,outWord,item,same,next]
  · rw [score]
    simp [z,next,stability 127 (by decide), f₃.2 127 (by decide), initial,
      keep₂ 127 (by decide) (by decide) (by decide) (by decide),
      keep 127 (by decide) (by decide) (by decide) (by decide)]
  · have g₁ : Preserves u field slots := (preserves_write u 135 _).mono (by simp [slots])
    have g₂ : Preserves field v slots := sealFrame.mono (by intro r hr; simp [slots] at hr ⊢; omega)
    have g₃ : Preserves v w slots := outFrame.mono (by intro r hr; simp [slots] at hr ⊢; omega)
    have g₄ : Preserves w z slots := (preserves_write w 137 _).mono (by simp [slots])
    have g₅ : Preserves z out slots := ⟨q₄,fun r hr => by
      simp [slots,SplitWeightCode.footprint] at hr
      exact f₄ r (by omega) (by omega) (by omega)⟩
    exact frame.trans (g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅))))


private def packInto : List Candidate → Word → Word
  | [], suffix => suffix
  | c::cs, suffix => put (packet c) (packInto cs suffix)

private theorem packInto_append (x y : List Candidate) (rest : Word) :
    packInto (x++y) rest = packInto x (packInto y rest) := by
  induction x <;> simp_all [packInto]

private theorem packInto_empty (cs : List Candidate) : packInto cs [] = candidatesWord cs := by
  induction cs <;> simp_all [packInto,candidatesWord,pack]

private def sweep : Code := .loop (.head 139) (.branch (.empty 124) (.write 139 .empty) one)

def branchFootprint : List Nat := 139 :: slots

private theorem sweep_run (s : State) (cs : List Candidate) (suffix : Word) (bit : Bool) (L : Nat)
    (data : s.reg 124 = candidatesWord cs) (bits : s.reg 113 = suffix) (mode : s.reg 114 = [bit])
    (ready : s.reg 139 = [true]) (size : (s.reg 124).length ≤ L) :
    ∃ u t, Run emptyLanguage sweep s u t 0 ∧ t ≤ (180*L+13*suffix.length+187)*cs.length+4 ∧
      u.reg 126 = packInto (Splitter.branch bit suffix cs).reverse (s.reg 126) ∧
      u.reg 127 = ones (Splitter.score (Splitter.branch bit suffix cs)) ++ s.reg 127 ∧
      Preserves s u branchFootprint := by
  induction cs generalizing s with
  | nil =>
    let u := s.write 139 []
    have done : Run emptyLanguage sweep u u 1 0 := .loopFalse (by simp [u,Test.eval])
    have body : Run emptyLanguage (.branch (.empty 124) (.write 139 .empty) one) s u 2 0 :=
      HullBatchMachine.runTrue (by simp [data,Test.eval,candidatesWord,pack]) .write
    exact ⟨u,4,.loopTrue (by simp [Test.eval,ready]) body done,by simp,
      by simp [u,Splitter.branch,packInto], by simp [u,Splitter.branch,Splitter.score],
      (preserves_write ..).mono (by simp [branchFootprint])⟩
  | cons C cs ih =>
    have packed : s.reg 124 = put (packet C) (candidatesWord cs) := by
      simpa [candidatesWord,pack] using data
    have live : (Test.empty 124).eval s = false := by
      rw [Test.eval,packed]
      cases packet C <;> rfl
    obtain ⟨v,oneTime,iteration,cap,left,state,total,frame⟩ := one_run s C cs suffix bit data bits mode
    have ok : (v.reg 124).length ≤ L := by
      rw [packed, QueryEncoding.put_length] at size
      rw [left]
      omega
    obtain ⟨u,t,loop,clock,states,scores,kept⟩ := ih v left
      ((frame.2 113 (by decide)).trans bits) ((frame.2 114 (by decide)).trans mode)
      ((frame.2 139 (by decide)).trans ready) ok
    refine ⟨u,_,.loopTrue (by simp [Test.eval,ready])
      (HullBatchMachine.runFalse live iteration) loop,?_,?_,?_ ,
      (frame.mono (fun _ h => List.mem_cons_of_mem _ h)).trans kept⟩
    · rw [List.length_cons,Nat.mul_succ]
      omega
    · rw [states,state]
      simp [Splitter.branch,List.reverse_cons,packInto_append,packInto]
    · rw [scores,total]
      simp [ones,Splitter.score,Splitter.branch,← List.append_assoc, Nat.add_comm]

/-- Form the weighted candidates for a proposed bit and sum their weights.
The resulting list is reversed and register 127 holds its total in unary. -/
def branch : Code :=
  .seq (.write 126 .empty) (.seq (.write 127 .empty) (.seq (setBit 139 true) sweep))

theorem branch_pure : branch.pure := by
  simp [branch,sweep,setBit,Code.allowed,one_pure]

theorem branch_run (s : State) (cs : List Candidate) (suffix : Word) (bit : Bool)
    (data : s.reg 124 = candidatesWord cs) (bits : s.reg 113 = suffix) (mode : s.reg 114 = [bit]) :
    ∃ u t, Run emptyLanguage branch s u t 0 ∧
      t ≤ (180*(s.reg 124).length+13*suffix.length+187)*cs.length+12 ∧
      u.reg 126 = candidatesWord (Splitter.branch bit suffix cs).reverse ∧
      u.reg 127 = ones (Splitter.score (Splitter.branch bit suffix cs)) ∧
      Preserves s u branchFootprint := by
  let a := s.write 126 []
  let b := a.write 127 []
  let start := b.write 139 [true]
  have first : Run emptyLanguage (.write 126 .empty) s a 1 0 := .write
  have second : Run emptyLanguage (.write 127 .empty) a b 1 0 := .write
  have third : Run emptyLanguage (setBit 139 true) b start 3 0 := setBit_run ..
  obtain ⟨u,t,loop,clock,values,score,frame⟩ := sweep_run start cs suffix bit (s.reg 124).length
    (by simpa [start,b,a] using data) (by simpa [start,b,a] using bits) (by simpa [start,b,a] using mode)
    (by simp [start]) (by simp [start,b,a])
  refine ⟨u,_,.seq first (.seq second (.seq third loop)),by omega,?_,?_ ,?_⟩
  · simpa [start,b,a,packInto_empty] using values
  · simpa [start,b] using score
  · exact ((preserves_write s 126 _).mono (by simp [branchFootprint,slots])).trans
      (((preserves_write a 127 _).mono (by simp [branchFootprint,slots])).trans
        (((preserves_write b 139 _).mono (by simp [branchFootprint])).trans frame))

end SplitBranchCode
