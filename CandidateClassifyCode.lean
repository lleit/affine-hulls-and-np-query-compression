module

public import CandidateProbeCode
public import CandidateRankCode
public import QueryHeaderCode
public import SplitBranchCode
public import SearchSplitter

@[expose] public section

namespace CandidateClassifyCode

open ComplexityModel
open HullBatchMachine (ones stepWrite runTrue runFalse)
open WordCode (putField putField_run setBit setBit_run)
open AffineSearch (Candidate Shaped small)
open QueryEncoding (pack put take)
open CandidateReadCode (candidateWord packedPivots)
open SplitBranchCode (packet candidatesWord)

/-- Record a successful probe without erasing an earlier success. -/
private def remember : Code := .branch (.head 96) (setBit 152 true) .skip

private def testSmall (c : Code) : Code := CandidateProbeCode.probeCandidate c ⨟ remember

/-- Insert the affine schedule into the splitter list with unit weight. -/
private def emitLarge : Code :=
  .write 156 (.copy 94) ⨟ setBit 157 true ⨟
    putField 157 156 154 155 158 ⨟ putField 156 124 154 155 158

private def readItem : Code :=
  FieldCode.takeField 150 156 154 158 ⨟ FieldCode.takeField 156 82 154 158 ⨟
    .write 94 (.copy 156)

private def classifyOne (c : Code) : Code :=
  readItem ⨟ CandidateRankCode.rankCode ⨟ QueryHeaderCode.compare 1 151 159 ⨟
    .branch (.head 159) (testSmall c) emitLarge

private def sweep (c : Code) : Code :=
  .loop (.head 160) (.branch (.empty 150) (.write 160 .empty) (classifyOne c))

/-- Register 150 supplies the packed candidate list, 81 its width, 95 the
request and 151 the logarithmic cutoff. Register 4 indicates whether a
small candidate supplied a witness. Register 124 holds the large ones. -/
def classify (c : Code) : Code :=
  .write 153 (.copy 3) ⨟ .write 124 .empty ⨟ setBit 152 false ⨟ setBit 160 true ⨟
    sweep c ⨟ .write 1 (.copy 81) ⨟ .write 3 (.copy 153) ⨟ .write 4 (.copy 152)

theorem classify_pure {c : Code} (pure : c.pure) : (classify c).pure := by
  simp [classify,sweep,classifyOne,readItem,testSmall,remember,emitLarge,Code.allowed,
    FieldCode.takeField_pure,CandidateRankCode.rankCode_pure,QueryHeaderCode.compare_pure,
    CandidateProbeCode.probeCandidate_pure pure,WordCode.putField_allowed,setBit]

/-- Check that an operation preserves a register and the caller's queue.
A scoped register call receives a fresh queue. -/
private def keeps (r : Nat) : Code → Bool
  | .skip => true
  | .write d _ => r != d
  | .push _ | .pop _ | .ask _ _ | .callBit .queued _ _ => false
  | .seq a b | .branch _ a b => keeps r a && keeps r b
  | .loop _ b => keeps r b
  | .callBit (.reg _) d _ => r != d

private theorem keeps_run {r : Nat} {c : Code} {s u : State} {t q : Nat}
    (run : Run emptyLanguage c s u t q) (keep : keeps r c = true) :
    u.reg r = s.reg r ∧ u.queries = s.queries := by
  induction run with
  | skip | loopFalse => exact ⟨rfl,rfl⟩
  | write =>
    simp only [keeps,bne_iff_ne] at keep
    exact ⟨by simp [State.write,keep],rfl⟩
  | push | pop | askEmpty | askSome => simp [keeps] at keep
  | seq _ _ h₁ h₂ =>
    simp only [keeps,Bool.and_eq_true] at keep
    have first := h₁ keep.1
    have second := h₂ keep.2
    exact ⟨second.1.trans first.1,second.2.trans first.2⟩
  | loopTrue _ _ _ h₁ h₂ =>
    have first := h₁ keep
    have second := h₂ keep
    exact ⟨second.1.trans first.1,second.2.trans first.2⟩
  | @branch b s u t q test yes no _ _ ih =>
    simp only [keeps,Bool.and_eq_true] at keep
    apply ih
    cases b
    · exact keep.2
    · exact keep.1
  | @callEmpty src d _ s _ | @callSome _ _ _ _ _ src d s _ _ _ =>
    cases src
    · simp only [keeps,bne_iff_ne] at keep
      exact ⟨by simp [Source.advance,State.write,keep],rfl⟩
    · simp [keeps] at keep

private theorem readItem_run (s : State) (a : Candidate) (as : List Candidate)
    (source : s.reg 150 = pack ((a::as).map candidateWord)) :
    ∃ u t, Run emptyLanguage readItem s u t 0 ∧
      t ≤ 28*(s.reg 150).length+37 ∧
      u.reg 150 = pack (as.map candidateWord) ∧ u.reg 82 = a.base ∧
      u.reg 94 = packedPivots a.pivots ∧
      (packedPivots a.pivots).length ≤ (s.reg 150).length := by
  obtain ⟨v,t₁,parse,cost₁,tail,item,_,_⟩ := FieldCode.takeField_run s
    (src:=150) (dst:=156) (scratch:=154) (flag:=158)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have first : take (s.reg 150) = (candidateWord a,pack (as.map candidateWord)) := by
    rw [source]
    simp [pack]
  rw [first] at tail item
  obtain ⟨z,t₂,data,cost₂,rest,base,_,frame⟩ := FieldCode.takeField_run v
    (src:=156) (dst:=82) (scratch:=154) (flag:=158)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have second : take (v.reg 156) = (a.base,packedPivots a.pivots) := by simp [item,candidateWord]
  rw [second] at rest base
  let out := z.write 94 (packedPivots a.pivots)
  have persist : Run emptyLanguage (.write 94 (.copy 156)) z out 1 0 := by
    simpa [out,Expr.eval,rest] using stepWrite z 94 (.copy 156)
  have inLen := QueryEncoding.take_data_le (s.reg 150)
  have pivotLen := QueryEncoding.take_lengths (v.reg 156)
  rw [first] at inLen
  rw [second,item] at pivotLen
  refine ⟨out,_,.seq parse (.seq data persist),?_,?_,by simp [out,base],by simp [out],by simp at inLen pivotLen; omega⟩
  · rw [item] at cost₂
    simp only [Prod.fst] at inLen cost₂
    omega
  · simpa [out,frame 150 (by decide) (by decide) (by decide) (by decide)] using tail

private theorem emitLarge_run (s : State) (a : Candidate)
    (pivots : s.reg 94 = packedPivots a.pivots) :
    ∃ u t, Run emptyLanguage emitLarge s u t 0 ∧
      t ≤ 14*(s.reg 94).length+110 ∧ u.reg 124 = put (packet (AffineSearch.pack a)) (s.reg 124) := by
  let x := s.write 156 (s.reg 94)
  let y := x.write 157 [true]
  have copy : Run emptyLanguage (.write 156 (.copy 94)) s x 1 0 := .write
  have arm : Run emptyLanguage (setBit 157 true) x y 3 0 := setBit_run ..
  obtain ⟨z,attach,attached,frame⟩ := putField_run y (src:=157) (dst:=156) (tmp:=154) (rev:=155) (flag:=158)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have item : z.reg 156 = packet (AffineSearch.pack a) := by
    simpa [x,y,pivots,packet,AffineSearch.pack,packedPivots,ones] using attached
  obtain ⟨u,insert,result,_⟩ := putField_run z (src:=156) (dst:=124) (tmp:=154) (rev:=155) (flag:=158)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨u,_,.seq copy (.seq arm (.seq attach insert)),?_,?_⟩
  · have zlen : (z.reg 156).length = (s.reg 94).length+3 := by
      rw [item,pivots]
      simp [packet,AffineSearch.pack,packedPivots,QueryEncoding.put_length,ones]
      omega
    have times₁ : (y.reg 157).length = 1 := by simp [y]
    simp only [times₁,zlen]
    omega
  · simpa [item,frame.2 124 (by decide),y,x] using result

private theorem remember_run (s : State) (old new : Bool)
    (acc : s.reg 152 = [old]) (flag : s.reg 96 = [new]) :
    ∃ u t, Run emptyLanguage remember s u t 0 ∧ t ≤ 4 ∧ u.reg 152 = [old || new] := by
  cases new
  · exact ⟨s,2,runFalse (by simp [Test.eval,flag]) .skip,by decide,by simpa using acc⟩
  · exact ⟨s.write 152 [true],4,runTrue (by simp [Test.eval,flag]) (setBit_run ..),by decide,by simp⟩

/-- Uniform cost of processing one candidate in a list of the given size. -/
def candidateBudget (time : Poly) (n request bytes K : Nat) : Nat :=
  (CandidateProbeCode.pointBudget time n bytes request + 8*n+33)*K + 4*n+17 +
    (50*bytes+(8*bytes+12)*n+7*n+180)

private theorem classifyOne_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check) (s : State)
    (a : Candidate) (as : List Candidate) (n K bytes : Nat) (req : Word) (old : Bool)
    (positive : K ≠ 0) (shape : Shaped n a.pivots) (width : a.base.length = n)
    (source : s.reg 150 = pack ((a::as).map candidateWord)) (fits : (s.reg 150).length ≤ bytes)
    (dim : s.reg 81 = ones n) (original : s.reg 95 = req)
    (threshold : s.reg 151 = ones K.log2) (acc : s.reg 152 = [old]) :
    ∃ u t, Run emptyLanguage (classifyOne c) s u t 0 ∧
      t ≤ candidateBudget time n req.length bytes K ∧ u.reg 150 = pack (as.map candidateWord) ∧
      u.reg 152 = [old || (small K a && a.points.any (check req))] ∧
      u.reg 124 = (if small K a then s.reg 124 else put (packet (AffineSearch.pack a)) (s.reg 124)) := by
  obtain ⟨v,t₁,parse,cost₁,tail,base,pivots,size⟩ := readItem_run s a as source
  let P := (packedPivots a.pivots).length
  have hp : P ≤ bytes := Nat.le_trans size fits
  obtain ⟨z,t₂,rank,cost₂,rankWord,rankFrame⟩ := CandidateRankCode.rankCode_run v a.pivots
    (by rw [shape.length,(keeps_run (r:=81) parse (by decide)).1,dim]) pivots
  let r := Splitter.rank a.pivots
  have rk : r ≤ n := shape.length ▸ Splitter.rank_le_length a.pivots
  have bound : z.reg 151 = ones K.log2 := by
    rw [rankFrame.2 151 (by decide),(keeps_run (r:=151) parse (by decide)).1,threshold]
  obtain ⟨b,t₃,compare,cost₃,flag,_,comparison⟩ := QueryHeaderCode.compare_run z
    (lhs:=1) (rhs:=151) (dst:=159) (by decide) (by decide) (by decide) r K.log2 rankWord bound
  have common (i : Nat) (h : keeps i readItem = true) (hn : i ∉ [1,97,98,107])
      (hd : i ≠ 159) (ha : i ≠ 30) (hb : i ≠ 31) : b.reg i = s.reg i := by
    rw [comparison i hd ha hb,rankFrame.2 i hn,(keeps_run parse h).1]
  have fromParsed (i : Nat) (hn : i ∉ [1,97,98,107]) (hd : i ≠ 159) (ha : i ≠ 30) (hb : i ≠ 31) :
      b.reg i = v.reg i := by
    rw [comparison i hd ha hb,rankFrame.2 i hn]
  have rem : b.reg 150 = pack (as.map candidateWord) := by
    rw [fromParsed 150 (by decide) (by decide) (by decide) (by decide),tail]
  have largeSaved : b.reg 124 = s.reg 124 := common 124 (by decide) (by decide) (by decide) (by decide) (by decide)
  have oldSaved : b.reg 152 = [old] := (common 152 (by decide) (by decide) (by decide) (by decide) (by decide)).trans acc
  have pivotSaved : b.reg 94 = packedPivots a.pivots := (fromParsed 94 (by decide) (by decide) (by decide) (by decide)).trans pivots
  have rankSaved : b.reg 1 = ones r := (comparison 1 (by decide) (by decide) (by decide)).trans rankWord
  have sml : small K a = decide (r ≤ K.log2) := by
    unfold small
    rw [AffineSearch.Candidate.basis,AffineSearch.directions_length]
    change decide (2^r ≤ K) = _
    apply Bool.eq_iff_iff.mpr
    simpa using (Nat.le_log2 (k:=r) positive).symm
  have mul := Nat.mul_le_mul_right n (show 8*P+12 ≤ 8*bytes+12 by omega)
  rw [pivots,shape.length] at cost₂
  have readBudget : t₁+t₂+t₃ ≤ 28*bytes+(8*bytes+12)*n+7*n+53 := by
    change t₃ ≤ 7*r+9 at cost₃
    change t₂ ≤ (8*P+12)*n+7 at cost₂
    omega
  by_cases h : r ≤ K.log2
  · have smallYes : small K a = true := by simp [sml,h]
    have branchFlag : (Test.head 159).eval b = true := by simp [Test.eval,flag,h]
    obtain ⟨p,t₄,tested,cost₄,success⟩ := CandidateProbeCode.probeCandidate_run program b a n req shape width
      ((common 81 (by decide) (by decide) (by decide) (by decide) (by decide)).trans dim)
      ((fromParsed 82 (by decide) (by decide) (by decide) (by decide)).trans base) pivotSaved
      ((common 95 (by decide) (by decide) (by decide) (by decide) (by decide)).trans original) rankSaved
    obtain ⟨u,t₅,saved,cost₅,answer⟩ := remember_run p old (a.points.any (check req))
      ((keeps_run (r:=152) tested rfl).1.trans oldSaved) success
    have done : Run emptyLanguage (testSmall c) b u (t₄+t₅+1) 0 := .seq tested saved
    refine ⟨u,_,.seq parse (.seq rank (.seq compare (runTrue branchFlag done))),?_,?_,?_,?_⟩
    · have cube := Nat.mul_le_mul_right n (show 14*P+15*n+58 ≤ 14*bytes+15*n+58 by omega)
      have point : CandidateProbeCode.pointBudget time n P req.length ≤
          CandidateProbeCode.pointBudget time n bytes req.length := by
        unfold CandidateProbeCode.pointBudget
        omega
      have product := Nat.mul_le_mul
        (show CandidateProbeCode.pointBudget time n P req.length+8*r+33 ≤
          CandidateProbeCode.pointBudget time n bytes req.length+8*n+33 by omega)
        ((Nat.le_log2 positive).mp h)
      rw [pivotSaved] at cost₄
      change t₄ ≤ (CandidateProbeCode.pointBudget time n P req.length+8*r+33)*2^r+4*r+17 at cost₄
      unfold candidateBudget
      omega
    · exact (keeps_run (r:=150) done rfl).1.trans rem
    · simpa only [smallYes,Bool.true_and] using answer
    · simpa only [smallYes,if_true] using (keeps_run (r:=124) done rfl).1.trans largeSaved
  · have smallNo : small K a = false := by simp [sml,h]
    have branchFlag : (Test.head 159).eval b = false := by simp [Test.eval,flag,h]
    obtain ⟨u,t₄,emit,cost₄,packet⟩ := emitLarge_run b a pivotSaved
    refine ⟨u,_,.seq parse (.seq rank (.seq compare (runFalse branchFlag emit))),?_,?_,?_,?_⟩
    · rw [pivotSaved] at cost₄
      change t₄ ≤ 14*P+110 at cost₄
      unfold candidateBudget
      omega
    · exact (keeps_run (r:=150) emit (by decide)).1.trans rem
    · simpa only [smallNo,Bool.false_and,Bool.or_false] using (keeps_run (r:=152) emit (by decide)).1.trans oldSaved
    · simpa only [smallNo,Bool.false_eq_true,if_false,largeSaved] using packet

private def accepts (check : Word → Bool) (K : Nat) (cs : List Candidate) : Bool :=
  (cs.filter (small K)).any (fun a => a.points.any check)

private def weighted (K : Nat) (cs : List Candidate) : List Splitter.Candidate :=
  (cs.filter (fun a => !small K a)).reverse.map AffineSearch.pack

private theorem sweep_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check) (s : State)
    (cs : List Candidate) (n K bytes : Nat) (req : Word) (old : Bool) (prev : List Splitter.Candidate)
    (positive : K ≠ 0) (shape : ∀ a ∈ cs, Shaped n a.pivots ∧ a.base.length = n)
    (source : s.reg 150 = pack (cs.map candidateWord)) (fits : (s.reg 150).length ≤ bytes)
    (dim : s.reg 81 = ones n) (original : s.reg 95 = req) (threshold : s.reg 151 = ones K.log2)
    (acc : s.reg 152 = [old]) (items : s.reg 124 = candidatesWord prev) (active : s.reg 160 = [true]) :
    ∃ u t, Run emptyLanguage (sweep c) s u t 0 ∧
      t ≤ (candidateBudget time n req.length bytes K + 2)*cs.length+4 ∧
      u.reg 152 = [old || accepts (check req) K cs] ∧ u.reg 124 = candidatesWord (weighted K cs ++ prev) := by
  induction cs generalizing s old prev with
  | nil =>
    let u := s.write 160 []
    have done : Run emptyLanguage (.write 160 .empty) s u 1 0 := .write
    have first : (Test.empty 150).eval s = true := by simp [Test.eval,source,pack]
    have stop : (Test.head 160).eval u = false := by simp [Test.eval,u]
    refine ⟨u,4,.loopTrue (by simp [Test.eval,active]) (runTrue first done) (.loopFalse stop),?_,?_,?_⟩
    · simp
    · simpa [u,accepts] using acc
    · simpa [u,weighted] using items
  | cons a cs ih =>
    have shaped := shape a (by simp)
    have tailShape : ∀ v ∈ cs, Shaped n v.pivots ∧ v.base.length = n :=
      fun v mem => shape v (List.mem_cons_of_mem _ mem)
    obtain ⟨v,t₁,one,cost₁,tail,answer,newItems⟩ := classifyOne_run program s a cs n K bytes req old
      positive shaped.1 shaped.2 source fits dim original threshold acc
    let recorded := old || (small K a && a.points.any (check req))
    let accumulated := if small K a then prev else AffineSearch.pack a::prev
    have accumulatedReg : v.reg 124 = candidatesWord accumulated := by
      cases h : small K a <;> simp [accumulated,h,newItems,items,candidatesWord,pack]
    have nextDim := (keeps_run (r:=81) one rfl).1.trans dim
    have nextReq := (keeps_run (r:=95) one rfl).1.trans original
    have nextCap := (keeps_run (r:=151) one rfl).1.trans threshold
    have nextActive := (keeps_run (r:=160) one rfl).1.trans active
    have restFits : (v.reg 150).length ≤ bytes := by
      rw [tail]
      have sourceLen : (s.reg 150).length = 2*(candidateWord a).length+1+(pack (cs.map candidateWord)).length := by
        rw [source,List.map_cons,pack,QueryEncoding.put_length]
      omega
    obtain ⟨u,t₂,rest,cost₂,found,out⟩ := ih v recorded accumulated tailShape tail restFits
      nextDim nextReq nextCap answer accumulatedReg nextActive
    have first : (Test.empty 150).eval s = false := by
      cases h : candidateWord a <;> simp [Test.eval,source,pack,QueryEncoding.put,h]
    refine ⟨u,_,.loopTrue (by simp [Test.eval,active]) (runFalse first one) rest,?_,?_,?_⟩
    · rw [List.length_cons,Nat.mul_succ]
      omega
    · cases h : small K a <;> simpa [recorded,accepts,h,List.filter_cons,Bool.or_assoc] using found
    · cases h : small K a <;>
        simpa [weighted,accumulated,h,List.filter_cons,List.reverse_cons,List.map_append,List.append_assoc] using out

/-- Test all low-rank candidates and produce precisely the reversed list of
higher-rank schedules. The active input, restrictions and queue are preserved. -/
theorem classify_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check) (s : State)
    (cs : List Candidate) (n K : Nat) (req : Word) (positive : K ≠ 0)
    (shaped : ∀ a ∈ cs, Shaped n a.pivots ∧ a.base.length = n)
    (source : s.reg 150 = pack (cs.map candidateWord))
    (dim : s.reg 81 = ones n) (original : s.reg 95 = req) (threshold : s.reg 151 = ones K.log2) :
    ∃ u t, Run emptyLanguage (classify c) s u t 0 ∧
      t ≤ (candidateBudget time n req.length (s.reg 150).length K + 2)*cs.length+24 ∧
      u.reg 4 = [(cs.filter (small K)).any (fun a => a.points.any (check req))] ∧
      u.reg 124 = candidatesWord ((cs.filter (fun a => !small K a)).reverse.map AffineSearch.pack) ∧
      u.reg 0 = s.reg 0 ∧ u.reg 1 = ones n ∧ u.reg 2 = s.reg 2 ∧ u.reg 3 = s.reg 3 ∧
      u.queries = s.queries := by
  let a := s.write 153 (s.reg 3)
  let b := a.write 124 []
  let d := b.write 152 [false]
  let v := d.write 160 [true]
  have save : Run emptyLanguage (.write 153 (.copy 3)) s a 1 0 := .write
  have clear : Run emptyLanguage (.write 124 .empty) a b 1 0 := .write
  have no : Run emptyLanguage (setBit 152 false) b d 3 0 := setBit_run ..
  have arm : Run emptyLanguage (setBit 160 true) d v 3 0 := setBit_run ..
  obtain ⟨w,t,scan,cost,answer,large⟩ := sweep_run program v cs n K (s.reg 150).length req false [] positive shaped
    (by simp [v,d,b,a,source]) (by simp [v,d,b,a]) (by simp [v,d,b,a,dim])
    (by simp [v,d,b,a,original]) (by simp [v,d,b,a,threshold])
    (by simp [v,d]) (by simp [v,d,b,candidatesWord,pack]) (by simp [v])
  let x := w.write 1 (ones n)
  let y := x.write 3 (s.reg 3)
  let u := y.write 4 [accepts (check req) K cs]
  have hw : w.reg 81 = ones n := by simp [(keeps_run (r:=81) scan rfl).1,v,d,b,a,dim]
  have hf : x.reg 153 = s.reg 3 := by simp [x,(keeps_run (r:=153) scan rfl).1,v,d,b,a]
  have result : y.reg 152 = [accepts (check req) K cs] := by simp [y,x,answer]
  have restoreWidth : Run emptyLanguage (.write 1 (.copy 81)) w x 1 0 := by
    simpa [x,Expr.eval,hw] using stepWrite w 1 (.copy 81)
  have restoreFlag : Run emptyLanguage (.write 3 (.copy 153)) x y 1 0 := by
    simpa [y,Expr.eval,hf] using stepWrite x 3 (.copy 153)
  have output : Run emptyLanguage (.write 4 (.copy 152)) y u 1 0 := by
    simpa [u,Expr.eval,result] using stepWrite y 4 (.copy 152)
  refine ⟨u,_,.seq save (.seq clear (.seq no (.seq arm (.seq scan (.seq restoreWidth (.seq restoreFlag output)))))),
    by omega,by simp [u,accepts],by simpa [u,y,x,weighted] using large,?_,by simp [u,y,x],?_,by simp [u,y],?_⟩
  · simp [u,y,x,(keeps_run (r:=0) scan rfl).1,v,d,b,a]
  · simp [u,y,x,(keeps_run (r:=2) scan rfl).1,v,d,b,a]
  · exact (keeps_run (r:=153) scan rfl).2

private def checkEnvelope (time : Poly) : Poly := (time.plus ⟨43,1⟩).comp ⟨2,1⟩

/-- A common input-size bound for the width, request and packed candidates
suffices to bound the complete classification step. -/
def classifyTime (time : Poly) : Poly :=
  (((checkEnvelope time).plus ⟨600,2⟩).times ⟨2,2⟩).plus ⟨24,0⟩

theorem classifyTime_bound (time : Poly) {n request bytes K count N : Nat}
    (width : n ≤ N) (req : request ≤ N) (size : bytes ≤ N) (number : count ≤ N)
    (positive : 0 < K) (cutoff : K ≤ N+2) :
    (candidateBudget time n request bytes K + 2)*count+24 ≤ (classifyTime time).at N := by
  let work := CandidateProbeCode.pointBudget time n bytes request+8*n+33
  let extra := 4*n+17+(50*bytes+(8*bytes+12)*n+7*n+180)+2
  let total := (checkEnvelope time).plus ⟨600,2⟩
  have square : N+1 ≤ (N+1)^2 := by
    simpa only [Nat.pow_one] using (Nat.pow_le_pow_right (n:=N+1) (by omega) (show 1 ≤ 2 by decide))
  have rows := Nat.mul_le_mul (show 14*bytes+15*n+58 ≤ 87*(N+1) by omega)
    (show n ≤ N+1 by omega)
  have pointers := Nat.mul_le_mul (show 8*bytes+12 ≤ 20*(N+1) by omega)
    (show n ≤ N+1 by omega)
  rw [Nat.mul_assoc 87,← Nat.pow_two] at rows
  rw [Nat.mul_assoc 20,← Nat.pow_two] at pointers
  have check := Nat.le_trans ((time.plus ⟨43,1⟩).mono (show request+n ≤ (Poly.mk 2 1).at N by
    simp [Poly.at]
    omega)) (Poly.comp_bound (time.plus ⟨43,1⟩) ⟨2,1⟩ N)
  have both : work+extra ≤ total.at N := by
    have merged := Poly.plus_bound (checkEnvelope time) ⟨600,2⟩ N
    change (checkEnvelope time).at N+600*(N+1)^2 ≤ total.at N at merged
    change (time.plus ⟨43,1⟩).at (request+n) ≤ (checkEnvelope time).at N at check
    dsimp [work,extra,CandidateProbeCode.pointBudget]
    omega
  have absorb := Nat.mul_le_mul_left extra (show 1 ≤ K by omega)
  simp only [Nat.mul_one] at absorb
  have cost : candidateBudget time n request bytes K+2 ≤ (work+extra)*K := by
    unfold candidateBudget
    change work*K+4*n+17+(50*bytes+(8*bytes+12)*n+7*n+180)+2 ≤ _
    have combine : work*K+4*n+17+(50*bytes+(8*bytes+12)*n+7*n+180)+2 = work*K+extra := by
      simp only [extra, Nat.add_assoc]
    rw [combine,Nat.add_mul work extra K]
    exact Nat.add_le_add_left absorb _
  have loops := Nat.mul_le_mul (show K ≤ 2*(N+1) by omega) (show count ≤ N+1 by omega)
  rw [Nat.mul_assoc 2,← Nat.pow_two] at loops
  calc
    (candidateBudget time n request bytes K+2)*count+24 ≤ ((work+extra)*K)*count+24 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right count cost) 24
    _ = (work+extra)*(K*count)+24 := by rw [Nat.mul_assoc]
    _ ≤ total.at N*(2*(N+1)^2)+24 := Nat.add_le_add_right (Nat.mul_le_mul both loops) 24
    _ ≤ (classifyTime time).at N := by
      have exactTime := Poly.times_at total ⟨2,2⟩ N
      have overhead := Poly.add_const_bound (total.times ⟨2,2⟩) 24 N
      rw [exactTime] at overhead
      exact overhead

theorem classifyBound (time : Poly) {n request bytes count B : Nat}
    (size : n+request+bytes+2 ≤ B) (number : count ≤ B) :
    (candidateBudget time n request bytes (bytes+2) + 2)*count+24 ≤ (classifyTime time).at B :=
  classifyTime_bound time (by omega) (by omega) (by omega) number (by omega) (by omega)

end CandidateClassifyCode
