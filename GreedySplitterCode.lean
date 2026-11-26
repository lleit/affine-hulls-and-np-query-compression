module

public import SplitBranchCode
public import QueryHeaderCode

@[expose] public section

namespace GreedySplitterCode

open ComplexityModel
open HullBatchMachine (ones stepWrite)
open WordCode (Preserves preserves_write setBit setBit_run)
open SplitBranchCode (candidatesWord)
open Splitter (Candidate score search)

private theorem sum_perm {xs ys : List Nat} (perm : xs.Perm ys) : xs.sum = ys.sum := by
  induction perm <;> simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem score_perm {xs ys : List Candidate} (perm : xs.Perm ys) : score xs = score ys :=
  sum_perm (perm.map Candidate.weight)

private theorem search_perm (n : Nat) (suffix : Word) {xs ys : List Candidate} (perm : xs.Perm ys) :
    (search n suffix xs).1 = (search n suffix ys).1 := by
  induction n generalizing suffix xs ys with
  | zero => rfl
  | succ n ih =>
    have p₀ : (Splitter.branch false suffix xs).Perm (Splitter.branch false suffix ys) := perm.map _
    have p₁ : (Splitter.branch true suffix xs).Perm (Splitter.branch true suffix ys) := perm.map _
    simp only [search,Splitter.choose]
    rw [score_perm p₀,score_perm p₁]
    split <;> exact ih _ (by first | exact p₀ | exact p₁)

private def rows (c : Candidate) : Nat :=
  (QueryEncoding.pack (c.steps.map CandidateReadCode.pivotWord)).length

private theorem packed_length (cs : List Candidate) :
    (candidatesWord cs).length = 4*score cs + 3*cs.length + 2*(cs.map rows).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (QueryEncoding.put (SplitBranchCode.packet c) (candidatesWord cs)).length = _
    rw [QueryEncoding.put_length,ih]
    simp [SplitBranchCode.packet,QueryEncoding.put_length,rows,score]
    omega

private theorem advance_rows (suffix : Word) (bit : Bool) (c : Candidate) :
    rows (Splitter.advance bit suffix c) ≤ rows c := by
  cases h : c.steps with
  | nil => simp [Splitter.advance,h]
  | cons s steps =>
    cases s <;> simp [Splitter.advance,h,rows,QueryEncoding.pack,QueryEncoding.put_length] <;> omega

private theorem branch_rows (suffix : Word) (bit : Bool) (cs : List Candidate) :
    ((Splitter.branch bit suffix cs).map rows).sum ≤ (cs.map rows).sum := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    have bound := advance_rows suffix bit c
    simpa only [Splitter.branch,List.map_cons,List.sum_cons] using Nat.add_le_add bound ih

private theorem selected_length (suffix : Word) (cs : List Candidate) :
    (candidatesWord (Splitter.choose suffix cs).2.reverse).length ≤ (candidatesWord cs).length := by
  have total := Splitter.score_branches suffix cs
  simp only [Splitter.choose]
  split <;> rename_i choice
  · simp only [Prod.snd,packed_length,List.length_reverse]
    have h := branch_rows suffix false cs
    have s := score_perm (List.reverse_perm (Splitter.branch false suffix cs))
    have w := sum_perm ((List.reverse_perm (Splitter.branch false suffix cs)).map rows)
    have l : (Splitter.branch false suffix cs).length = cs.length := by simp [Splitter.branch]
    omega
  · simp only [Prod.snd,packed_length,List.length_reverse]
    have h := branch_rows suffix true cs
    have s := score_perm (List.reverse_perm (Splitter.branch true suffix cs))
    have w := sum_perm ((List.reverse_perm (Splitter.branch true suffix cs)).map rows)
    have l : (Splitter.branch true suffix cs).length = cs.length := by simp [Splitter.branch]
    omega

private def saveFalse : Code :=
  .seq (.write 142 (.copy 126)) (.seq (.write 143 (.copy 127)) (.write 124 (.copy 141)))

private def select : Code :=
  .branch (.head 144)
    (.seq (.write 124 (.copy 142)) (.write 113 (.cons false 113)))
    (.seq (.write 124 (.copy 126)) (.write 113 (.cons true 113)))

def choose : Code :=
  .seq (.write 141 (.copy 124))
    (.seq (setBit 114 false)
      (.seq SplitBranchCode.branch
        (.seq saveFalse
          (.seq (setBit 114 true)
            (.seq SplitBranchCode.branch
              (.seq (QueryHeaderCode.compare 143 127 144) select))))))

theorem choose_pure : choose.pure := by
  simp [choose,saveFalse,select,setBit,Code.allowed,SplitBranchCode.branch_pure,
    QueryHeaderCode.compare_pure]

def chooseFootprint : List Nat :=
  SplitBranchCode.branchFootprint ++ [113,114,124,30,31,141,142,143,144]

private theorem select_run (s : State) (b : Bool) (x y suffix : Word)
    (flag : s.reg 144 = [b]) (l : s.reg 142 = x) (r : s.reg 126 = y) (acc : s.reg 113 = suffix) :
    ∃ out, Run emptyLanguage select s out 4 0 ∧
      out.reg 124 = (if b then x else y) ∧ out.reg 113 = (!b) :: suffix ∧
      Preserves s out [113,124] := by
  have test : (Test.head 144).eval s = b := by simp [Test.eval,flag]
  let a := s.write 124 (if b then x else y)
  let u := a.write 113 ((!b)::suffix)
  have left : Run emptyLanguage (.write 124 (if b then .copy 142 else .copy 126)) s a 1 0 := by
    cases b
    · simpa [a,Expr.eval,r] using stepWrite s 124 (.copy 126)
    · simpa [a,Expr.eval,l] using stepWrite s 124 (.copy 142)
  have finish : Run emptyLanguage (.write 113 (.cons (!b) 113)) a u 1 0 := by
    simpa [u,a,Expr.eval,acc] using stepWrite a 113 (.cons (!b) 113)
  refine ⟨u,?_,by simp [u,a],by simp [u],?_⟩
  · cases b
    · exact HullBatchMachine.runFalse test (.seq left finish)
    · exact HullBatchMachine.runTrue test (.seq left finish)
  · exact ((preserves_write s 124 _).mono (by simp)).trans ((preserves_write a 113 _).mono (by simp))

/-- Compute a single greedy bit and restore the input register for the
next bit with precisely the candidates selected by the comparison. -/
theorem choose_run (s : State) (suffix : Word) (cs : List Candidate)
    (bits : s.reg 113 = suffix) (data : s.reg 124 = candidatesWord cs) :
    let next := Splitter.choose suffix cs
    ∃ u t, Run emptyLanguage choose s u t 0 ∧
      t ≤ 2*(180*(candidatesWord cs).length+13*suffix.length+187)*cs.length+
        14*(candidatesWord cs).length+56 ∧
      u.reg 113 = next.1 :: suffix ∧ u.reg 124 = candidatesWord next.2.reverse ∧
      (u.reg 124).length ≤ (s.reg 124).length ∧ Preserves s u chooseFootprint := by
  dsimp only
  let a := s.write 141 (s.reg 124)
  let b := a.write 114 [false]
  have copy : Run emptyLanguage (.write 141 (.copy 124)) s a 1 0 := .write
  have zero := setBit_run emptyLanguage a 114 false
  obtain ⟨f,t₀,run₀,cost₀,list₀,score₀,frame₀⟩ := SplitBranchCode.branch_run b cs suffix false
    (by simp [b,a,data]) (by simp [b,a,bits]) (by simp [b])
  let ls := Splitter.branch false suffix cs
  let rs := Splitter.branch true suffix cs
  let c := f.write 142 (candidatesWord ls.reverse)
  let d := c.write 143 (ones (score ls))
  let e := d.write 124 (candidatesWord cs)
  have saveList : Run emptyLanguage (.write 142 (.copy 126)) f c 1 0 := by
    simpa [c,ls,list₀,Expr.eval] using stepWrite f 142 (.copy 126)
  have saveScore : Run emptyLanguage (.write 143 (.copy 127)) c d 1 0 := by
    simpa [c,d,ls,score₀,Expr.eval] using stepWrite c 143 (.copy 127)
  have saved : f.reg 141 = candidatesWord cs := by
    rw [frame₀.2 141 (by decide)]
    simp [b,a,data]
  have restore : Run emptyLanguage (.write 124 (.copy 141)) d e 1 0 := by
    simpa [e,d,c,saved,Expr.eval] using stepWrite d 124 (.copy 141)
  have stage : Run emptyLanguage saveFalse f e 5 0 := .seq saveList (.seq saveScore restore)
  let g := e.write 114 [true]
  have one := setBit_run emptyLanguage e 114 true
  have held : g.reg 113 = suffix := by
    simp [g,e,d,c,frame₀.2 113 (by decide),b,a,bits]
  obtain ⟨j,t₁,run₁,cost₁,list₁,score₁,frame₁⟩ := SplitBranchCode.branch_run g cs suffix true
    (by simp [g,e]) held (by simp [g])
  have leftScore : j.reg 143 = ones (score ls) := by
    rw [frame₁.2 143 (by decide)]
    simp [g,e,d]
  obtain ⟨m,t₂,cmp,cost₂,flag,q,keep⟩ := QueryHeaderCode.compare_run j
    (lhs:=143) (rhs:=127) (dst:=144) (by decide) (by decide) (by decide)
    (score ls) (score rs) leftScore score₁
  have before : m.reg 142 = candidatesWord ls.reverse := by
    rw [keep 142 (by decide) (by decide) (by decide),frame₁.2 142 (by decide)]
    simp [g,e,d,c]
  have after : m.reg 126 = candidatesWord rs.reverse := by
    rw [keep 126 (by decide) (by decide) (by decide),list₁]
  have mask : m.reg 113 = suffix := by
    rw [keep 113 (by decide) (by decide) (by decide),frame₁.2 113 (by decide),held]
  obtain ⟨u,run₂,list,bits',frame₂⟩ := select_run m _ _ _ suffix flag before after mask
  have next : Splitter.choose suffix cs =
      (if score ls ≤ score rs then (false,ls) else (true,rs)) := rfl
  have test : u.reg 124 = candidatesWord (Splitter.choose suffix cs).2.reverse := by
    rw [next]
    by_cases h : score ls ≤ score rs <;> simpa [h] using list
  refine ⟨u,_,.seq copy (.seq zero (.seq run₀ (.seq stage (.seq one (.seq run₁ (.seq cmp run₂)))))),
    ?_,?_,test,?_,?_⟩
  · have a₀ := Splitter.score_branches suffix cs
    have h₀ := packed_length cs
    change score ls+score rs = 2*score cs at a₀
    simp only [b,a,g,e,HullBatchMachine.write_same,State.write,data] at cost₀ cost₁
    change t₀ ≤ (180*(candidatesWord cs).length+13*suffix.length+187)*cs.length+12 at cost₀
    change t₁ ≤ (180*(candidatesWord cs).length+13*suffix.length+187)*cs.length+12 at cost₁
    rw [Nat.mul_assoc]
    omega
  · rw [next]
    by_cases h : score ls ≤ score rs <;> simpa [h] using bits'
  · rw [test,data]
    exact selected_length suffix cs
  · have writes : Preserves s b [141,114] :=
      ((preserves_write s 141 _).mono (by simp)).trans ((preserves_write a 114 _).mono (by simp))
    have saves : Preserves f g [142,143,124,114] :=
      ((preserves_write f 142 _).mono (by simp)).trans
        (((preserves_write c 143 _).mono (by simp)).trans
        (((preserves_write d 124 _).mono (by simp)).trans
          ((preserves_write e 114 _).mono (by simp))))
    have comparison : Preserves j m [144,30,31] :=
      ⟨q,fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
        exact keep r hr.1 hr.2.1 hr.2.2⟩
    exact (writes.mono (by simp [chooseFootprint])).trans
      ((frame₀.mono (by intro r h; simp [chooseFootprint,h])).trans
      ((saves.mono (by simp [chooseFootprint])).trans
      ((frame₁.mono (by intro r h; simp [chooseFootprint,h])).trans
      ((comparison.mono (by simp [chooseFootprint])).trans (frame₂.mono (by simp [chooseFootprint]))))))

def greedy : Code := HullBatchMachine.forUnary 140 choose

theorem greedy_pure : greedy.pure := by
  simp [greedy,HullBatchMachine.forUnary,Code.allowed,choose_pure]

def greedyFootprint : List Nat := 140 :: chooseFootprint

/-- Compute all bits of the greedy mask. The selected packet never grows,
and the suffix contains at most the specified number of bits. -/
theorem greedy_run (s : State) (n : Nat) (suffix : Word) (cs : List Candidate)
    (clock : s.reg 140 = ones n) (bits : s.reg 113 = suffix) (data : s.reg 124 = candidatesWord cs) :
    let L := (candidatesWord cs).length
    let bound := 2*((180*L+13*(n+suffix.length)+187)*L)+14*L+56
    ∃ u t, Run emptyLanguage greedy s u t 0 ∧ t ≤ (bound+3)*n+1 ∧
      u.reg 113 = (search n suffix cs).1 ∧ Preserves s u greedyFootprint := by
  dsimp only
  let L := (candidatesWord cs).length
  let W := n+suffix.length
  let goal := (search n suffix cs).1
  let budget := 2*((180*L+13*W+187)*L)+14*L+56
  let I (i : Nat) (v : State) := ∃ rest cs', v.reg 113 = rest ∧ v.reg 124 = candidatesWord cs' ∧
    (candidatesWord cs').length ≤ L ∧ i+rest.length ≤ W ∧ (search i rest cs').1 = goal ∧
    Preserves s v greedyFootprint
  have step : ∀ i v, v.reg 140 = ones (i + 1) → I (i + 1) v →
      ∃ u t, Run emptyLanguage choose v u t 0 ∧ t ≤ budget ∧ u.reg 140 = ones (i + 1) ∧
        I i (u.write 140 (ones i)) := by
    intro i v tick ⟨rest,cs',mask,packet,hlen,wlen,result,holds⟩
    obtain ⟨u,t,run,time,suffix',data',size',frame⟩ := choose_run v rest cs' mask packet
    have count : cs'.length ≤ L := by
      have packetSize := packed_length cs'
      omega
    have mul := Nat.mul_le_mul (show 180*(candidatesWord cs').length+13*rest.length+187 ≤
      180*L+13*W+187 by omega) count
    have value := search_perm i ((Splitter.choose rest cs').1::rest)
      (List.reverse_perm (Splitter.choose rest cs').2)
    refine ⟨u,t,run,?_,(frame.2 140 (by decide)).trans tick,?_⟩
    · change t ≤ 2*((180*L+13*W+187)*L)+14*L+56
      change t ≤ 2*(180*(candidatesWord cs').length+13*rest.length+187)*cs'.length+
        14*(candidatesWord cs').length+56 at time
      rw [Nat.mul_assoc] at time
      omega
    · refine ⟨_,_,by simpa using suffix',by simpa using data',?_,?_,?_,?_⟩
      · rw [data',packet] at size'
        exact Nat.le_trans size' hlen
      · simp only [List.length_cons]
        omega
      · rw [value]
        exact result
      · exact holds.trans ((frame.mono (by intro r h; simp [greedyFootprint,h])).trans
          ((preserves_write u 140 _).mono (by simp [greedyFootprint])))
  have start : I n s := ⟨suffix,cs,bits,data,Nat.le_refl _,Nat.le_refl _,rfl,⟨rfl,fun _ _ => rfl⟩⟩
  obtain ⟨u,t,run,time,_,rest,cs',mask,_,_,_,res,frame⟩ :=
    HullBatchMachine.forUnary_run I step n s clock start
  exact ⟨u,t,run,time,mask.trans res,frame⟩

end GreedySplitterCode
