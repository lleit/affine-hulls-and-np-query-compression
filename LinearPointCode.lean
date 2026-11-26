module

public import CandidateReadCode
public import EliminationCode
public import SearchSplitter

@[expose] public section

namespace LinearPointCode

open ComplexityModel
open AffineSearch (linearPoints translate Candidate Shaped)
open QueryEncoding (pack put take)
open CandidateReadCode (pivotWord packedPivots)
open HullBatchMachine (ones forUnary forUnary_run stepWrite runTrue runFalse)
open WordCode (Preserves preserves_write)

def select : List (Option Word) → Word → Word → Word × Word
  | [], tape, acc => (acc,tape)
  | none::rest, tape, acc => select rest tape (false::acc)
  | some row::rest, tape, acc =>
    if tape.headD false then select rest tape.tail (true::translate row acc)
    else select rest tape.tail (false::acc)

theorem select_append (ps qs : List (Option Word)) (tape acc : Word) :
    select (ps++qs) tape acc =
      let (point, remaining) := select ps tape acc
      select qs remaining point := by
  induction ps generalizing tape acc with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | none => exact ih ..
    | some row => simp only [List.cons_append, select]; split <;> exact ih ..

private theorem select_extend (ps : List (Option Word)) (tape suffix acc : Word)
    (length : tape.length = Splitter.rank ps) :
    select ps (tape++suffix) acc = ((select ps tape acc).1,suffix) := by
  induction ps generalizing tape acc with
  | nil => cases tape <;> simp_all [Splitter.rank, select]
  | cons p ps ih =>
    cases p with
    | none => exact ih tape _ length
    | some row =>
      cases tape with
      | nil => simp [Splitter.rank] at length
      | cons bit rest =>
        have rlen : rest.length = Splitter.rank ps := by simpa [Splitter.rank] using length
        cases bit <;> simpa only [select, List.cons_append, List.headD_cons, Bool.false_eq_true,
          ↓reduceIte, List.tail_cons] using ih rest _ rlen

theorem select_mem (ps : List (Option Word)) (tape : Word) :
    (select ps.reverse tape []).1 ∈ linearPoints ps := by
  induction ps generalizing tape with
  | nil => simp [select,linearPoints]
  | cons p ps ih =>
    rw [List.reverse_cons, select_append]
    cases e : select ps.reverse tape [] with
    | mk point left =>
      have origin := ih tape
      rw [e] at origin
      cases p with
      | none =>
        exact List.mem_map.mpr ⟨_,origin,rfl⟩
      | some row =>
        cases h : left.headD false with
        | false =>
          have bt : (left.head?).getD false = false := by simpa using h
          simpa [select,linearPoints,bt] using
            (List.mem_append_left _ (List.mem_map.mpr ⟨point,origin,rfl⟩) :
              false :: point ∈ (linearPoints ps).map (false :: ·) ++
                (linearPoints ps).map (fun x => true :: translate row x))
        | true =>
          have bt : (left.head?).getD false = true := by simpa using h
          simpa [select,linearPoints,bt] using
            (List.mem_append_right _ (List.mem_map.mpr ⟨point,origin,rfl⟩) :
              true :: translate row point ∈ (linearPoints ps).map (false :: ·) ++
                (linearPoints ps).map (fun x => true :: translate row x))

theorem select_complete {ps : List (Option Word)} {v : Word} (member : v ∈ linearPoints ps) :
    ∃ tape, tape.length = Splitter.rank ps ∧ (select ps.reverse tape []).1 = v := by
  induction ps generalizing v with
  | nil =>
    have : v = [] := by simpa [linearPoints] using member
    exact ⟨[],rfl,this.symm⟩
  | cons p ps ih =>
    cases p with
    | none =>
      obtain ⟨sub,hs,rfl⟩ := List.mem_map.mp member
      obtain ⟨t,hlen,out⟩ := ih hs
      refine ⟨t,hlen,?_⟩
      rw [List.reverse_cons,select_append]
      cases e : select ps.reverse t [] with
      | mk x rest => simp [e,select] at out ⊢; exact out
    | some row =>
      have step (b : Bool) (w : Word) (h : w ∈ linearPoints ps)
          (eq : (if b then true :: translate row w else false :: w) = v) :
          ∃ tape, tape.length = Splitter.rank (some row :: ps) ∧
            (select (some row :: ps).reverse tape []).1 = v := by
        obtain ⟨t,hlen,out⟩ := ih h
        have hr : t.length = Splitter.rank ps.reverse := by rw [Splitter.rank_reverse,hlen]
        refine ⟨t++[b], by simp [hlen,Splitter.rank],?_⟩
        rw [List.reverse_cons,select_append,select_extend _ _ _ _ hr,out]
        cases b <;> simpa [select] using eq
      rcases List.mem_append.mp member with h | h
      · obtain ⟨w,hw,e⟩ := List.mem_map.mp h
        exact step false w hw e
      · obtain ⟨w,hw,e⟩ := List.mem_map.mp h
        exact step true w hw e

/-- Describe the increasing row widths when visiting a pivot schedule from
right to left. -/
private def Growing : Nat → List (Option Word) → Prop
  | _, [] => True
  | k, p::ps => (∀ row, p = some row → row.length = k) ∧ Growing (k+1) ps

private theorem growing_snoc {k : Nat} {ps : List (Option Word)} (shape : Growing k ps)
    (p : Option Word) (len : ∀ row, p = some row → row.length = k + ps.length) :
    Growing k (ps ++ [p]) := by
  induction ps generalizing k with
  | nil => exact ⟨by simpa using len,trivial⟩
  | cons a ps ih =>
    refine ⟨shape.1, ih shape.2 ?_⟩
    intro r hr
    have := len r hr
    simp only [List.length_cons] at this
    omega

private theorem growing_of_shaped {k : Nat} {ps : List (Option Word)} (shape : Shaped k ps) :
    Growing 0 ps.reverse := by
  induction shape with
  | nil => trivial
  | free h ih =>
    rw [List.reverse_cons]
    exact growing_snoc ih none (by simp)
  | pivot hlen tail ih =>
    rw [List.reverse_cons]
    apply growing_snoc ih
    intro r hr
    cases hr
    simpa [tail.length] using hlen


private def usePivot : Code :=
  .seq (.write 50 (.tail 85))
    (.seq (.write 51 (.copy 90))
      (.seq EliminationCode.xorRows (.write 90 (.cons true 52))))

private def advance : Code :=
  .branch (.empty 85) (.write 90 (.cons false 90))
    (.seq (.branch (.head 92) usePivot (.write 90 (.cons false 90)))
      (.write 92 (.tail 92)))

private def advanceRegs : List Nat := [50,51,52,53,54,90,92]

private theorem advance_pure : advance.pure := by
  simp [advance,usePivot,Code.allowed,EliminationCode.xorRows_pure]

private theorem advance_run (s : State) (p : Option Word) (h : s.reg 85 = pivotWord p)
    (tape acc : Word) (tp : s.reg 92 = tape) (ac : s.reg 90 = acc)
    (shape : ∀ w, p = some w → w.length = acc.length) :
    ∃ out t, Run emptyLanguage advance s out t 0 ∧ t ≤ 15*acc.length+33 ∧
      out.reg 90 = (select [p] tape acc).1 ∧ out.reg 92 = (select [p] tape acc).2 ∧
      Preserves s out advanceRegs := by
  cases p with
  | none =>
    let u := s.write 90 (false::acc)
    have write : Run emptyLanguage (.write 90 (.cons false 90)) s u 1 0 := by
      simpa [u,Expr.eval,ac] using stepWrite s 90 (.cons false 90)
    have empty : (Test.empty 85).eval s = true := by simp [Test.eval,h,pivotWord]
    exact ⟨u,2,runTrue empty write,by omega,by simp [u,select],by simp [u,select,tp],
      (preserves_write s 90 _).mono (by simp [advanceRegs])⟩
  | some row =>
    have found : (Test.empty 85).eval s = false := by simp [Test.eval,h,pivotWord]
    have selected (v : State) (t : Nat) (run : Run emptyLanguage
        (.branch (.head 92) usePivot (.write 90 (.cons false 90))) s v t 0)
        (cost : t ≤ 15*acc.length+30) (coef : v.reg 92 = tape)
        (point : v.reg 90 = (select [some row] tape acc).1) (kept : Preserves s v advanceRegs) :
        ∃ out t, Run emptyLanguage advance s out t 0 ∧ t ≤ 15*acc.length+33 ∧
          out.reg 90 = (select [some row] tape acc).1 ∧ out.reg 92 = (select [some row] tape acc).2 ∧
          Preserves s out advanceRegs := by
      let u := v.write 92 tape.tail
      have debit : Run emptyLanguage (.write 92 (.tail 92)) v u 1 0 := by
        simpa [u,Expr.eval,coef] using stepWrite v 92 (.tail 92)
      refine ⟨u,t+3,runFalse found (.seq run debit),by omega,by simp [u,point],?_,
        kept.trans ((preserves_write v 92 _).mono (by simp [advanceRegs]))⟩
      cases b : (tape.head?).getD false <;> simp [u,select,b]
    cases bit : (tape.head?).getD false with
    | false =>
      let v := s.write 90 (false :: acc)
      have write : Run emptyLanguage (.write 90 (.cons false 90)) s v 1 0 := by
        simpa [v,Expr.eval,ac] using stepWrite s 90 (.cons false 90)
      exact selected v 2 (runFalse (by simp only [Test.eval,tp,List.headD_eq_head?_getD,bit]) write) (by omega)
        (by simp [v,tp]) (by simp [v,select,bit])
        ((preserves_write s 90 _).mono (by simp [advanceRegs]))
    | true =>
      let a := s.write 50 row
      let b := a.write 51 acc
      have copyRow : Run emptyLanguage (.write 50 (.tail 85)) s a 1 0 := by
        simpa [a,Expr.eval,h,pivotWord] using stepWrite s 50 (.tail 85)
      have copyAcc : Run emptyLanguage (.write 51 (.copy 90)) a b 1 0 := by
        simpa [a,b,Expr.eval,ac] using stepWrite a 51 (.copy 90)
      obtain ⟨c, sum, rowSum, saved⟩ := EliminationCode.xorRows_run b
        (by simp [a,b]) (by simp [b]) (shape row rfl)
      let v := c.write 90 (true :: translate row acc)
      have write : Run emptyLanguage (.write 90 (.cons true 52)) c v 1 0 := by
        simpa [v,Expr.eval,rowSum,translate] using stepWrite c 90 (.cons true 52)
      have run : Run emptyLanguage usePivot s v _ 0 := .seq copyRow (.seq copyAcc (.seq sum write))
      have frame : Preserves s v advanceRegs :=
        ((preserves_write s 50 _).mono (by simp [advanceRegs])).trans
          (((preserves_write a 51 _).mono (by simp [advanceRegs])).trans
            ((saved.mono (by intro r hr; simp [advanceRegs] at hr ⊢; omega)).trans
              ((preserves_write c 90 _).mono (by simp [advanceRegs]))))
      have yes : (Test.head 92).eval s = true := by simp only [Test.eval,tp,List.headD_eq_head?_getD,bit]
      have resolved : Run emptyLanguage
        (.branch (.head 92) usePivot (.write 90 (.cons false 90))) s v _ 0 := runTrue yes run
      exact selected v _ resolved (by have := shape row rfl; omega)
        (by simp [v,saved.2 92 (by decide),b,a,tp]) (by simp [v,select,bit]) frame


private def loopBody : Code :=
  .seq (FieldCode.takeField 83 85 86 87) (.seq advance (.write 93 (.tail 93)))

private def loop : Code := .loop (.head 93) loopBody

def pointFootprint : List Nat := advanceRegs ++ [83,85,86,87,93]

private theorem one_len (p : Option Word) (tape acc : Word)
    (shape : ∀ r, p = some r → r.length = acc.length) :
    (select [p] tape acc).1.length = acc.length+1 := by
  cases p with
  | none => rfl
  | some row =>
    have width := shape row rfl
    unfold select
    split
    · simp [select, width]
    · rfl

private theorem loop_run (s : State) (ps : List (Option Word)) (tape acc : Word) (width limit : Nat)
    (fuel : s.reg 93 = ones ps.length) (fields : s.reg 83 = pack (ps.map pivotWord))
    (bits : s.reg 92 = tape) (point : s.reg 90 = acc) (form : Growing acc.length ps)
    (ambient : acc.length+ps.length ≤ width) (space : (s.reg 83).length ≤ limit) :
    ∃ out t, Run emptyLanguage loop s out t 0 ∧
      t ≤ (14*limit + 15*width+58)*ps.length+1 ∧
      out.reg 90 = (select ps tape acc).1 ∧ out.reg 92 = (select ps tape acc).2 ∧
      Preserves s out pointFootprint := by
  induction ps generalizing s tape acc with
  | nil =>
    exact ⟨s,1,.loopFalse (by simp [Test.eval,fuel]),by simp,point,bits,⟨rfl,fun _ _ => rfl⟩⟩
  | cons p rest ih =>
    obtain ⟨a,t₁,takeRun,parseCost,restFields,field,queue,preserve⟩ :=
      FieldCode.takeField_run s (src:=83) (dst:=85) (scratch:=86) (flag:=87)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have cut : take (s.reg 83) = (pivotWord p,pack (rest.map pivotWord)) := by
      rw [fields,List.map_cons,pack,QueryEncoding.take_put]
    rw [cut] at restFields field
    have tape' : a.reg 92 = tape :=
      (preserve 92 (by decide) (by decide) (by decide) (by decide)).trans bits
    have acc' : a.reg 90 = acc :=
      (preserve 90 (by decide) (by decide) (by decide) (by decide)).trans point
    obtain ⟨b,t₂,perform,performCost,result,unread,kept⟩ := advance_run a p field tape acc tape' acc' form.1
    let next := b.write 93 (ones rest.length)
    have bc : b.reg 93 = ones (p::rest).length :=
      (kept.2 93 (by decide)).trans ((preserve 93 (by decide) (by decide) (by decide) (by decide)).trans fuel)
    have debit : Run emptyLanguage (.write 93 (.tail 93)) b next 1 0 := by
      simpa [next,Expr.eval,bc,List.length_cons] using stepWrite b 93 (.tail 93)
    have leftover : next.reg 83 = pack (rest.map pivotWord) := by
      simp [next,kept.2 83 (by decide),restFields]
    have newSpace : (next.reg 83).length ≤ limit := by
      have shorten := QueryEncoding.take_lengths (s.reg 83)
      rw [cut] at shorten
      rw [leftover]
      simp at shorten
      omega
    have len := one_len p tape acc form.1
    obtain ⟨out,t,work,cost,final,rem,frame⟩ := ih next _ _
      (by simp [next]) leftover (by simpa [next] using unread) (by simpa [next] using result)
      (by rw [len]; exact form.2)
      (by simpa only [List.length_cons,len,Nat.add_assoc,Nat.add_comm 1] using ambient) newSpace
    have selectEq : select (p::rest) tape acc =
        select rest (select [p] tape acc).2 (select [p] tape acc).1 := by
      have h := select_append [p] rest tape acc
      cases e : select [p] tape acc
      simpa [e] using h
    have active : (Test.head 93).eval s = true := by simp [Test.eval,fuel,List.length_cons]
    refine ⟨out,_,.loopTrue active (.seq takeRun (.seq perform debit)) work, ?_,
      by rw [selectEq]; exact final, by rw [selectEq]; exact rem,?_⟩
    · rw [List.length_cons,Nat.mul_succ]
      simp only [List.length_cons] at ambient
      omega
    · have first : Preserves s a pointFootprint := ⟨queue,fun r hr => by
        simp [pointFootprint,advanceRegs] at hr
        exact preserve r (by omega) (by omega) (by omega) (by omega)⟩
      exact first.trans ((kept.mono (fun r h => List.mem_append_left _ h)).trans
        (((preserves_write b 93 _).mono (by simp [pointFootprint])).trans frame))

/-- Compute the affine point for one coefficient tape. The reverse schedule,
offset, tape, and ambient width are held in 83, 82, 92, and 81. -/
def pointCode : Code :=
  .seq (.write 90 .empty)
    (.seq (.write 93 (.copy 81))
      (.seq loop
        (.seq (.write 50 (.copy 82))
          (.seq (.write 51 (.copy 90))
            (.seq EliminationCode.xorRows (.write 90 (.copy 52)))))))

theorem pointCode_pure : pointCode.pure := by
  simp [pointCode,loop,loopBody,Code.allowed,FieldCode.takeField_pure,advance_pure,
    EliminationCode.xorRows_pure]

theorem pointCode_run (s : State) (A : Candidate) (n : Nat) (tape : Word)
    (shape : Shaped n A.pivots) (width : A.base.length = n)
    (dim : s.reg 81 = ones n) (origin : s.reg 82 = A.base)
    (pivots : s.reg 83 = packedPivots A.pivots) (bits : s.reg 92 = tape) :
    ∃ out t, Run emptyLanguage pointCode s out t 0 ∧
      t ≤ (14*(s.reg 83).length+15*n+58)*n+15*n+35 ∧
      out.reg 90 = translate A.base (select A.pivots.reverse tape []).1 ∧
      Preserves s out pointFootprint := by
  let a := s.write 90 []
  let start := a.write 93 (ones n)
  have clear : Run emptyLanguage (.write 90 .empty) s a 1 0 := .write
  have clock : Run emptyLanguage (.write 93 (.copy 81)) a start 1 0 := by
    simpa [a,start,Expr.eval,dim] using stepWrite a 93 (.copy 81)
  have size : A.pivots.reverse.length = n := by simp [shape.length]
  obtain ⟨u,t,choose,cost,result,_,kept⟩ := loop_run start A.pivots.reverse tape [] n (s.reg 83).length
    (by simp [start,size]) (by simpa [start,a,packedPivots] using pivots)
    (by simp [start,a,bits]) (by simp [start,a]) (growing_of_shaped shape)
    (by simp [size]) (by simp [start,a])
  let chosen := (select A.pivots.reverse tape []).1
  have chosenLength : chosen.length = n := shape.points_width (select_mem A.pivots tape)
  have off : u.reg 82 = A.base := by
    simpa [a,start,origin] using kept.2 82 (by decide)
  let x := u.write 50 A.base
  let y := x.write 51 chosen
  have xrun : Run emptyLanguage (.write 50 (.copy 82)) u x 1 0 := by
    simpa [x,off,Expr.eval] using stepWrite u 50 (.copy 82)
  have yrun : Run emptyLanguage (.write 51 (.copy 90)) x y 1 0 := by
    simpa [x,y,result,Expr.eval] using stepWrite x 51 (.copy 90)
  obtain ⟨z,sum,answer,frame⟩ := EliminationCode.xorRows_run y (by simp [x,y])
    (by simp [y]) (width.trans chosenLength.symm)
  let out := z.write 90 (z.reg 52)
  have finish : Run emptyLanguage (.write 90 (.copy 52)) z out 1 0 := .write
  rw [width] at sum
  refine ⟨out,_,.seq clear (.seq clock (.seq choose (.seq xrun (.seq yrun (.seq sum finish))))),
    by rw [size] at cost; omega, by simp [out,answer,translate,chosen], ?_⟩
  exact ((preserves_write s 90 _).mono (by simp [pointFootprint,advanceRegs])).trans
    (((preserves_write a 93 _).mono (by simp [pointFootprint])).trans
      (kept.trans (((preserves_write u 50 _).mono (by simp [pointFootprint,advanceRegs])).trans
        (((preserves_write x 51 _).mono (by simp [pointFootprint,advanceRegs])).trans
          ((frame.mono (by intro r hr; simp [pointFootprint,advanceRegs] at hr ⊢; omega)).trans
            ((preserves_write z 90 _).mono (by simp [pointFootprint,advanceRegs])))))))

end LinearPointCode
