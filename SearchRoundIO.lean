module

public import SearchLoopCode
public import RestrictedVerifier
public import GreedySplitterCode
public import CertificateCode

@[expose] public section

namespace SearchRoundIO

open ComplexityModel
open HullBatchMachine (ones stepWrite runTrue runFalse)
open WordCode (Preserves preserves_write putField putField_run setBit setBit_run)

def requestCode : Code :=
  .seq (.write 95 (.copy 2))
    (.seq (putField 1 95 146 147 148) (putField 0 95 146 147 148))

theorem requestCode_pure : requestCode.pure := by
  exact ⟨trivial,WordCode.putField_allowed ..,WordCode.putField_allowed ..⟩

theorem requestCode_run (s : State) (x : Word) (k : Nat) (history : List Word)
    (active : SearchLoopCode.Active x k history s) :
    ∃ u, Run emptyLanguage requestCode s u (14*(x.length+k)+49) 0 ∧
      u.reg 95 = QueryEncoding.requestWord x k history ∧ Preserves s u [95,146,147,148] := by
  let a := s.write 95 (QueryEncoding.pack history)
  have copy : Run emptyLanguage (.write 95 (.copy 2)) s a 1 0 := by
    simpa [a,Expr.eval,active.2.2.1] using stepWrite s 95 (.copy 2)
  obtain ⟨b,width,value,frame⟩ := putField_run a (src:=1) (dst:=95) (tmp:=146) (rev:=147) (flag:=148)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨u,input,result,keep⟩ := putField_run b (src:=0) (dst:=95) (tmp:=146) (rev:=147) (flag:=148)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx : b.reg 0 = x := by simp [frame.2 0 (by decide),a,active.1]
  have hk : a.reg 1 = ones k := by simp [a,active.2.1]
  rw [hx] at input result
  rw [hk] at width value
  refine ⟨u,?_,?_,((preserves_write s 95 _).mono (by simp)).trans (frame.trans keep)⟩
  · rw [show 14*(x.length+k)+49 = 1+((14*k+23)+(14*x.length+23)+1)+1 by omega]
    exact .seq copy (.seq (by simpa using width) input)
  · simpa [QueryEncoding.requestWord,ones,value,a] using result

def installCut : Code :=
  .seq (putField 113 2 146 147 148) (.write 1 (.tail 1))

theorem installCut_pure : installCut.pure := ⟨WordCode.putField_allowed ..,trivial⟩

theorem installCut_run (s : State) (x : Word) (k : Nat) (history : List Word) (mask : Word)
    (active : SearchLoopCode.Active x (k+1) history s) (bits : s.reg 113 = mask) :
    ∃ u, Run emptyLanguage installCut s u (14*mask.length+25) 0 ∧
      SearchLoopCode.Active x k (mask::history) u ∧ Preserves s u [1,2,146,147,148] := by
  obtain ⟨a,append,output,frame⟩ := putField_run s (src:=113) (dst:=2) (tmp:=146) (rev:=147) (flag:=148)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let u := a.write 1 (ones k)
  have width : a.reg 1 = ones (k+1) := (frame.2 1 (by decide)).trans active.2.1
  have dec : Run emptyLanguage (.write 1 (.tail 1)) a u 1 0 := by
    simpa [u,Expr.eval,width,HullBatchMachine.ones_succ] using stepWrite a 1 (.tail 1)
  rw [bits] at append output
  refine ⟨u,?_,?_,(frame.mono (by simp)).trans ((preserves_write a 1 _).mono (by simp))⟩
  · have total := Run.seq append dec
    simpa [installCut,Nat.add_assoc] using total
  · exact ⟨by simp [u,frame.2 0 (by decide),active.1],by simp [u],
      by simp [u,output,active.2.2.1,QueryEncoding.pack],
      by simp [u,frame.2 3 (by decide),active.2.2.2.1],frame.1.trans active.2.2.2.2⟩

def restrictedTime (time : Poly) : Poly := (time.plus ⟨43,1⟩).plus ⟨300,2⟩

theorem restrictedImplements {c : Code} {time : Poly} {check : CertificateCode.Checker}
    (spec : CertificateCode.Implements c time check) :
    CertificateCode.Implements (RestrictedVerifier.compile c) (restrictedTime time)
      (RestrictedVerifier.check check) := by
  intro req w
  obtain ⟨u,t,run,bound,result⟩ := RestrictedVerifier.compile_run spec req w
  exact ⟨u,t,run,bound,by simp [result]⟩

def terminal (c : Code) : Code :=
  .seq (.write 149 .empty)
    (.seq (putField 95 149 146 147 148)
      (.seq (PairCode.call 149 4 (RestrictedVerifier.compile c)) (.write 3 .empty)))

theorem terminal_pure {c : Code} (pure : c.pure) : (terminal c).pure := by
  exact ⟨trivial,WordCode.putField_allowed ..,
    PairCode.call_pure _ _ (RestrictedVerifier.compile_pure pure),trivial⟩

def terminalTime (p : Poly) : Poly := ((restrictedTime p).plus ⟨43,1⟩).plus ⟨51,1⟩

theorem terminal_run {c : Code} {p : Poly} {check : CertificateCode.Checker}
    (spec : CertificateCode.Implements c p check) (s : State) (req : Word) (hr : s.reg 95 = req) :
    ∃ u t, Run emptyLanguage (terminal c) s u t 0 ∧ t ≤ (terminalTime p).at req.length ∧
      u.reg 3 = [] ∧ u.reg 4 = [RestrictedVerifier.check check req []] := by
  let a := s.write 149 []
  have empty : Run emptyLanguage (.write 149 .empty) s a 1 0 := .write
  obtain ⟨b,pack,packet,frame⟩ := putField_run a (src:=95) (dst:=149) (tmp:=146) (rev:=147) (flag:=148)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rq : a.reg 95 = req := by simp [a,hr]
  rw [rq] at pack packet
  have packet' : b.reg 149 = QueryEncoding.put req [] := by simpa [a] using packet
  obtain ⟨t,call,budget⟩ := PairCode.call_check (restrictedImplements spec) b (dst:=4) packet'
  let mid := b.write 4 [RestrictedVerifier.check check req []]
  let u := mid.write 3 []
  have done : Run emptyLanguage (.write 3 .empty) mid u 1 0 := .write
  have add := Poly.plus_bound ((restrictedTime p).plus ⟨43,1⟩) ⟨51,1⟩ req.length
  rw [show (Poly.mk 51 1).at req.length = 51*(req.length+1) by simp [Poly.at]] at add
  change ((restrictedTime p).plus ⟨43,1⟩).at req.length+51*(req.length+1) ≤
    (terminalTime p).at req.length at add
  simp only [List.length_nil,Nat.add_zero] at budget
  exact ⟨u,_,.seq empty (.seq pack (.seq call done)),by omega,by simp [u],by simp [u,mid]⟩

private def maskStep : Code :=
  .seq (.branch (.head 174) (setBit 175 true) .skip) (.write 174 (.tail 174))

private def maskScan : Code :=
  .seq (.write 174 (.copy 113)) (.seq (setBit 175 false)
    (.seq (setBit 176 true) (HullBatchMachine.scanCore 174 176 maskStep)))

private theorem maskScan_pure : maskScan.pure := by
  simp [maskScan,maskStep,HullBatchMachine.scanCore,setBit,Code.allowed]

private theorem maskScan_run (s : State) (mask : Word) (bits : s.reg 113 = mask) :
    ∃ u t, Run emptyLanguage maskScan s u t 0 ∧ t ≤ 8*mask.length+14 ∧
      u.reg 175 = [mask.contains true] ∧ Preserves s u [174,175,176] := by
  let a := s.write 174 mask
  let b := a.write 175 [false]
  let start := b.write 176 [true]
  have copy : Run emptyLanguage (.write 174 (.copy 113)) s a 1 0 := by
    simpa [a,Expr.eval,bits] using stepWrite s 174 (.copy 113)
  let I (rem : Word) (v : State) :=
    ∃ acc : Bool, v.reg 175 = [acc] ∧ (acc || rem.contains true) = mask.contains true ∧
      Preserves s v [174,175,176]
  have step : ∀ bit rem v, v.reg 174 = bit::rem → v.reg 176 = [true] → I (bit::rem) v →
      ∃ u t, Run emptyLanguage maskStep v u t 0 ∧ t ≤ 6 ∧ u.reg 174 = rem ∧
        u.reg 176 = [true] ∧ I rem u := by
    intro bit rem v word on ⟨acc,found,ok,frame⟩
    let next := if bit then v.write 175 [true] else v
    let u := next.write 174 rem
    have eval : (Test.head 174).eval v = bit := by simp [Test.eval,word]
    have flag : ∃ t, Run emptyLanguage (.branch (.head 174) (setBit 175 true) .skip) v next t 0 ∧ t ≤ 4 := by
      cases bit
      · exact ⟨2,runFalse eval .skip,by decide⟩
      · exact ⟨4,runTrue eval (setBit_run ..),by decide⟩
    obtain ⟨t,flag,cost⟩ := flag
    have debit : Run emptyLanguage (.write 174 (.tail 174)) next u 1 0 := by
      cases bit <;> simpa [u,next,Expr.eval,word] using stepWrite next 174 (.tail 174)
    have part : Preserves v next [174,175,176] := by
      cases bit
      · exact ⟨rfl,fun _ _ => rfl⟩
      · exact (preserves_write v 175 _).mono (by simp)
    refine ⟨u,_,.seq flag debit,by omega,by simp [u],?_,?_⟩
    · cases bit <;> simp [u,next,on]
    · refine ⟨acc || bit,?_,?_,frame.trans (part.trans ((preserves_write next 174 _).mono (by simp)))⟩
      · cases bit <;> simp [u,next,found]
      · cases acc <;> cases bit <;> simpa using ok
  have init : I mask start := by
    refine ⟨false,by simp [start,b],rfl,?_⟩
    exact ((preserves_write s 174 _).mono (by simp)).trans
      (((preserves_write a 175 _).mono (by simp)).trans ((preserves_write b 176 _).mono (by simp)))
  obtain ⟨u,t,scan,cost,acc,found,answer,frame⟩ := HullBatchMachine.scanCore_run I
    (fun v ⟨acc,f,ok,keep⟩ => ⟨acc,by simp [f],ok,keep.trans ((preserves_write v 176 _).mono (by simp))⟩)
    step mask start (by simp [start,b,a]) (by simp [start]) init
  have value : acc = mask.contains true := by simpa using answer
  exact ⟨u,_,.seq copy (.seq (setBit_run ..) (.seq (setBit_run ..) scan)),by omega,value ▸ found,frame⟩

def pickMask : Code :=
  .seq (.write 113 .empty) (.seq (.write 140 (.copy 1)) (.seq GreedySplitterCode.greedy maskScan))

theorem pickMask_pure : pickMask.pure := ⟨trivial,trivial,GreedySplitterCode.greedy_pure,maskScan_pure⟩

def maskFootprint : List Nat := GreedySplitterCode.greedyFootprint ++ [113,140,174,175,176]

private theorem search_length (n : Nat) (suffix : Word) (cs : List Splitter.Candidate) :
    (Splitter.search n suffix cs).1.length = n+suffix.length := by
  induction n generalizing suffix cs with
  | zero => simp [Splitter.search]
  | succ n ih =>
    change (Splitter.search n ((Splitter.choose suffix cs).1::suffix) (Splitter.choose suffix cs).2).1.length = _
    rw [ih,List.length_cons]
    omega

theorem pickMask_run (s : State) (n : Nat) (cs : List Splitter.Candidate)
    (dim : s.reg 1 = ones n) (items : s.reg 124 = SplitBranchCode.candidatesWord cs) :
    let mask := (Splitter.search n [] cs).1
    let L := (SplitBranchCode.candidatesWord cs).length
    ∃ u t, Run emptyLanguage pickMask s u t 0 ∧ t ≤ 600*(n+L+1)^3 ∧
      u.reg 113 = mask ∧ u.reg 175 = [mask.contains true] ∧ Preserves s u maskFootprint := by
  dsimp only
  let mask := (Splitter.search n [] cs).1
  let L := (SplitBranchCode.candidatesWord cs).length
  let a := s.write 113 []
  let b := a.write 140 (ones n)
  have clear : Run emptyLanguage (.write 113 .empty) s a 1 0 := .write
  have copy : Run emptyLanguage (.write 140 (.copy 1)) a b 1 0 := by
    simpa [a,b,Expr.eval,dim] using stepWrite a 140 (.copy 1)
  obtain ⟨v,t₀,makeMask,cost₀,bits,frame⟩ := GreedySplitterCode.greedy_run b n [] cs
    (by simp [b]) (by simp [b,a]) (by simp [b,a,items])
  obtain ⟨u,t₁,test,cost₁,result,keep⟩ := maskScan_run v mask bits
  have len : mask.length = n := by simpa [mask] using search_length n [] cs
  refine ⟨u,_,.seq clear (.seq copy (.seq makeMask test)),?_,(keep.2 113 (by decide)).trans bits,result,?_⟩
  · let B := n+L+1
    change t₀ ≤ (2*((180*L+13*(n+0)+187)*L)+14*L+56+3)*n+1 at cost₀
    have p₁ := Nat.mul_le_mul (show 180*L+13*(n+0)+187 ≤ 187*B by dsimp [B]; omega)
      (show L ≤ B by dsimp [B]; omega)
    have area : 0 < B := by dsimp [B]; omega
    have p₂ : B ≤ B*B := Nat.le_mul_of_pos_right _ area
    have q : 2*((180*L+13*(n+0)+187)*L)+14*L+56+3 ≤ 450*(B*B) := by
      rw [Nat.mul_assoc] at p₁
      have h : L ≤ B*B := Nat.le_trans (by dsimp [B]; omega) p₂
      have pos : 1 ≤ B*B := Nat.le_trans area p₂
      omega
    have nb : n ≤ B := by dsimp [B]; omega
    have product := Nat.mul_le_mul q nb
    rw [Nat.mul_assoc 450,← Nat.pow_two,← Nat.pow_succ] at product
    change _ ≤ 450*B^3 at product
    have cubed : B ≤ B^3 := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right area (show 1 ≤ 3 by decide)
    rw [len] at cost₁
    change t₁ ≤ 8*n+14 at cost₁
    change _ ≤ 600*B^3
    omega
  · exact ((preserves_write s 113 _).mono (by simp [maskFootprint])).trans
      (((preserves_write a 140 _).mono (by simp [maskFootprint])).trans
        ((frame.mono (by intro r h; simp [maskFootprint,h])).trans (keep.mono (by simp [maskFootprint]))))

end SearchRoundIO
