module

public import LinearPointCode
public import ReplayListCode
public import ComplexityModel.PairCode
public import CertificateCode

@[expose] public section

namespace CandidateProbeCode

open ComplexityModel
open QueryEncoding (put)
open AffineSearch (Candidate Shaped translate)
open HullBatchMachine (ones stepWrite)
open WordCode (Preserves preserves_write putField setBit setBit_run)

private def accumulated : Code := .branch (.head 32) (setBit 96 true) .skip

private theorem accumulated_run (s : State) (old new : Bool)
    (flag : s.reg 32 = [new]) (acc : s.reg 96 = [old]) :
    ∃ out t, Run emptyLanguage accumulated s out t 0 ∧ t ≤ 4 ∧
      out.reg 96 = [old || new] ∧ Preserves s out [96] := by
  cases new
  · exact ⟨s,2,HullBatchMachine.runFalse (by simp [Test.eval,flag]) .skip,by decide,
      by simpa using acc,⟨rfl,fun _ _ => rfl⟩⟩
  · exact ⟨s.write 96 [true],4,HullBatchMachine.runTrue (by simp [Test.eval,flag]) (setBit_run ..),
      by decide,by simp,preserves_write ..⟩

private def probe (c : Code) : Code :=
  .seq (.write 83 (.copy 94))
    (.seq (.write 92 (.copy 3))
      (.seq LinearPointCode.pointCode
        (.seq (.write 27 (.copy 90))
          (.seq (putField 95 27 28 29 30)
            (.seq (PairCode.call 27 32 c) accumulated)))))

private def probeFootprint : List Nat :=
  LinearPointCode.pointFootprint ++ [83,92,27,28,29,30,32,96]

private theorem probe_pure {c : Code} (pure : c.pure) : (probe c).pure := by
  simp [probe,Code.allowed,LinearPointCode.pointCode_pure,WordCode.putField_allowed,
    PairCode.call_pure _ _ pure,accumulated,setBit]

def selectedPoint (A : Candidate) (tape : Word) : Word :=
  translate A.base (LinearPointCode.select A.pivots.reverse tape []).1

theorem selected_mem (A : Candidate) (tape : Word) : selectedPoint A tape ∈ A.points :=
  List.mem_map.mpr ⟨_,LinearPointCode.select_mem A.pivots tape,rfl⟩

theorem selection_complete (A : Candidate) {w : Word} (member : w ∈ A.points) :
    ∃ tape, tape.length = Splitter.rank A.pivots ∧ selectedPoint A tape = w := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp member
  obtain ⟨t,len,he⟩ := LinearPointCode.select_complete hv
  exact ⟨t,len,by simp [selectedPoint,he]⟩

def pointBudget (p : Poly) (n packet request : Nat) : Nat :=
  (14*packet+15*n+58)*n+15*n+14*request+80 +
    (p.plus ⟨43,1⟩).at (request+n)

private theorem probe_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check)
    (s : State) (A : Candidate) (n : Nat) (req tape : Word) (old : Bool)
    (shape : Shaped n A.pivots) (width : A.base.length = n)
    (dim : s.reg 81 = ones n) (origin : s.reg 82 = A.base)
    (pivots : s.reg 94 = CandidateReadCode.packedPivots A.pivots)
    (original : s.reg 95 = req) (bits : s.reg 3 = tape) (flag : s.reg 96 = [old]) :
    ∃ out t, Run emptyLanguage (probe c) s out t 0 ∧
      t ≤ pointBudget time n (s.reg 94).length req.length ∧
      out.reg 96 = [old || check req (selectedPoint A tape)] ∧ Preserves s out probeFootprint := by
  let pivot := CandidateReadCode.packedPivots A.pivots
  let a := s.write 83 pivot
  let b := a.write 92 tape
  have copyPivots : Run emptyLanguage (.write 83 (.copy 94)) s a 1 0 := by
    simpa [a,Expr.eval,pivots,pivot] using stepWrite s 83 (.copy 94)
  have copyTape : Run emptyLanguage (.write 92 (.copy 3)) a b 1 0 := by
    simpa [a,b,Expr.eval,bits] using stepWrite a 92 (.copy 3)
  obtain ⟨v,t₁,point,pointTime,outPoint,saved⟩ :=
    LinearPointCode.pointCode_run b A n tape shape width
      (by simp [a,b,dim]) (by simp [a,b,origin]) (by simp [a,b,pivot]) (by simp [b])
  let w := selectedPoint A tape
  let d := v.write 27 w
  have save : Run emptyLanguage (.write 27 (.copy 90)) v d 1 0 := by
    simpa [d,Expr.eval,outPoint,selectedPoint,w] using stepWrite v 27 (.copy 90)
  obtain ⟨e,pack,packet,frame⟩ := WordCode.putField_run d
    (src:=95) (dst:=27) (tmp:=28) (rev:=29) (flag:=30)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have reqKept : d.reg 95 = req := by simp [d,saved.2 95 (by decide),b,a,original]
  have enc : e.reg 27 = put req w := by rw [packet,reqKept]; simp [d]
  obtain ⟨t₂,checkRun,checkTime⟩ := PairCode.call_check program e (dst:=32) enc
  let f := e.write 32 [check req w]
  have oldFlag : f.reg 96 = [old] := by
    simp [f,frame.2 96 (by decide),d,saved.2 96 (by decide),b,a,flag]
  obtain ⟨out,t₃,merge,mergeTime,result,kept⟩ :=
    accumulated_run f old (check req w) (by simp [f]) oldFlag
  have pointLen : w.length = n := by
    unfold w selectedPoint
    rw [AffineSearch.translate_length, width, shape.points_width (LinearPointCode.select_mem _ _)]
    simp
  have pv : (b.reg 83).length = (s.reg 94).length := by simp [a,b,pivot,pivots]
  refine ⟨out,_,.seq copyPivots (.seq copyTape (.seq point (.seq save (.seq pack (.seq checkRun merge))))),
    ?_,result,?_⟩
  · rw [pointLen] at checkTime
    rw [pv] at pointTime
    unfold pointBudget
    rw [reqKept]
    omega
  · have frame₁ := saved.mono (more := probeFootprint) (fun r h => List.mem_append_left _ h)
    have frame₂ : Preserves d e probeFootprint := frame.mono (by
      intro r h
      exact List.mem_append_right _ (by simp at h ⊢; omega))
    exact ((preserves_write s 83 _).mono (by simp [probeFootprint])).trans
      (((preserves_write a 92 _).mono (by simp [probeFootprint])).trans
        (frame₁.trans (((preserves_write v 27 _).mono (by simp [probeFootprint])).trans
          (frame₂.trans (((preserves_write e 32 _).mono (by simp [probeFootprint])).trans
            (kept.mono (by simp [probeFootprint])))))))


/-- Test every point in an affine candidate using exactly one tape bit per
pivot. Call this only after the dimension test has bounded the tape count. -/
def probeCandidate (c : Code) : Code :=
  .seq (setBit 96 false) (ReplayListCode.enumerate (probe c))

theorem probeCandidate_pure {c : Code} (pure : c.pure) : (probeCandidate c).pure := by
  simp [probeCandidate,Code.allowed,setBit,ReplayListCode.enumerate_pure (probe_pure pure)]

theorem probeCandidate_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check)
    (s : State) (A : Candidate) (n : Nat) (req : Word)
    (shape : Shaped n A.pivots) (width : A.base.length = n)
    (dim : s.reg 81 = ones n) (origin : s.reg 82 = A.base)
    (pivots : s.reg 94 = CandidateReadCode.packedPivots A.pivots) (original : s.reg 95 = req)
    (count : s.reg 1 = ones (Splitter.rank A.pivots)) :
    let rank := Splitter.rank A.pivots
    let cost := pointBudget time n (s.reg 94).length req.length
    ∃ out t, Run emptyLanguage (probeCandidate c) s out t 0 ∧
      t ≤ (cost+8*rank+33)*2^rank + 4*rank + 17 ∧
      out.reg 96 = [A.points.any (check req)] := by
  dsimp only
  let test (tape : Word) := check req (selectedPoint A tape)
  let cost := pointBudget time n (s.reg 94).length req.length
  let rank := Splitter.rank A.pivots
  let Valid (seen : List Word) (u : State) :=
    u.reg 81 = ones n ∧ u.reg 82 = A.base ∧ u.reg 94 = s.reg 94 ∧ u.reg 95 = req ∧
      u.reg 96 = [seen.any test]
  let start := s.write 96 [false]
  have beginRun : Run emptyLanguage (setBit 96 false) s start 3 0 := setBit_run ..
  have first : Valid [] start := by simp [Valid,start,dim,origin,original]
  have invariant : ReplayListCode.VisitInvariant (probe c) rank cost Valid := by
    constructor
    · intro visited tape u _ stored data
      obtain ⟨next,t,ran,cost',result,frame⟩ := probe_run program u A n req tape (visited.any test)
        shape width data.1 data.2.1 (data.2.2.1.trans pivots) data.2.2.2.1 stored data.2.2.2.2
      refine ⟨next,t,ran,by simpa only [data.2.2.1] using cost',
        (frame.2 3 (by decide)).trans stored,?_⟩
      refine ⟨(frame.2 81 (by decide)).trans data.1,(frame.2 82 (by decide)).trans data.2.1,
        (frame.2 94 (by decide)).trans data.2.2.1,
        (frame.2 95 (by decide)).trans data.2.2.2.1,?_⟩
      simpa [test,Bool.or_comm] using result
    · intro visited u v data frame
      refine ⟨(frame.2 81 (by decide)).trans data.1,(frame.2 82 (by decide)).trans data.2.1,
        (frame.2 94 (by decide)).trans data.2.2.1,(frame.2 95 (by decide)).trans data.2.2.2.1,
        (frame.2 96 (by decide)).trans data.2.2.2.2⟩
  obtain ⟨out,t,seen,scan,bound,valid,_,complete⟩ :=
    ReplayListCode.enumerate_run invariant start (by simpa [start,ones] using count) first
  have sameAnswer : seen.any test = A.points.any (check req) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro yes
      obtain ⟨tape,_,passed⟩ := List.any_eq_true.mp yes
      exact List.any_eq_true.mpr ⟨_,selected_mem A tape,passed⟩
    · intro yes
      obtain ⟨w,mem,passing⟩ := List.any_eq_true.mp yes
      obtain ⟨tape,hlen,data⟩ := selection_complete A mem
      have tapemem := MachineEnumeration.mem_tapes.mpr hlen
      refine List.any_eq_true.mpr ⟨tape,(complete tape).mpr tapemem,?_⟩
      simpa [test,data] using passing
  refine ⟨out,_,.seq beginRun scan,?_ , by simpa only [sameAnswer] using valid.2.2.2.2⟩
  change _ ≤ (cost+8*rank+33)*2^rank+4*rank+17
  omega

end CandidateProbeCode
