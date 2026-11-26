module

public import HullBatchMachine
public import HullQueryLanguage

@[expose] public section

namespace QueryHeaderCode

open ComplexityModel HullBatchMachine
open QueryEncoding (take readRequest)
open HullRecovery (Query)

structure Header where
  request : Word
  width : Nat
  rank : Nat
  col : Nat
  row : Nat
  isBit : Bool
  valid : Bool

/-- Independent of the dependent query type, so the same layout describes
both successful and unsuccessful parses. -/
def header (s : Word) : Header :=
  let fields := take s
  let width := (readRequest fields.1).width
  let rank := take fields.2.tail
  let col := take rank.2
  let row := take col.2
  let bit := fields.2.headD false
  ⟨fields.1, width, rank.1.length, col.1.length, row.1.length, bit,
    !fields.2.isEmpty && decide (rank.1.length ≤ width+1) &&
      (!bit || (decide (col.1.length ≤ width) && decide (row.1.length ≤ width)))⟩

private theorem tail_le (w : Word) : w.tail.length ≤ w.length := by simp

private theorem rest_le (w : Word) : (take w).2.length ≤ w.length := by
  have h := QueryEncoding.take_lengths w
  omega

private def takeLen (src dst : Nat) : Code :=
  FieldCode.takeReverse src 24 ⨟ .write dst .empty ⨟ normalize 24 dst 25

private theorem takeLen_run (s : State) {src dst : Nat}
    (hds : dst ≠ src) (hd24 : dst ≠ 24) (hd25 : dst ≠ 25)
    (hs24 : src ≠ 24) (hs25 : src ≠ 25) :
    ∃ u t, Run emptyLanguage (takeLen src dst) s u t 0 ∧ t ≤ 13*(s.reg src).length+17 ∧
      u.reg src = (take (s.reg src)).2 ∧ u.reg dst = ones (take (s.reg src)).1.length ∧
      u.queries = s.queries ∧
      ∀ r, r ≠ src → r ≠ dst → r ≠ 24 → r ≠ 25 → u.reg r = s.reg r := by
  obtain ⟨a,t₁,run₁,c₁,rest,data,q₁,keep₁⟩ :=
    FieldCode.takeReverse_run s (src := src) (dst := 24) (Ne.symm hs24)
  let start := a.write dst []
  have clear : Run emptyLanguage (.write dst .empty) a start 1 0 := .write
  obtain ⟨u,t₂,run₂,c₂,value,q₂,keep₂⟩ :=
    normalize_run (dst := dst) (src := 24) (flag := 25) hd24 (by decide) (Ne.symm hd25) start
  have data' : start.reg 24 = (take (s.reg src)).1.reverse := by simpa [start,Ne.symm hd24] using data
  refine ⟨u,_,.seq run₁ (.seq clear run₂),?_,?_,?_,q₂.trans q₁,?_⟩
  · have sz := QueryEncoding.take_data_le (s.reg src)
    simp only [data',List.length_reverse] at c₂
    omega
  · rw [keep₂ src hs24 (Ne.symm hds) hs25,write_ne _ _ (Ne.symm hds),rest]
  · simpa [start,data'] using value
  · intro r h1 h2 h3 h4
    rw [keep₂ r h3 h2 h4,write_ne _ _ h2,keep₁ r h1 h3]

def widthFromRequest : Code :=
  .write 26 (.copy 2) ⨟ FieldCode.takeReverse 26 24 ⨟ takeLen 26 4

theorem widthFromRequest_pure : widthFromRequest.pure := by
  simp [widthFromRequest, takeLen, normalize, HullBatchMachine.set, HullBatchMachine.scanCore,
    FieldCode.takeReverse_pure, Code.allowed]

theorem widthFromRequest_run (s : State) :
    ∃ u t, Run emptyLanguage widthFromRequest s u t 0 ∧ t ≤ 21*(s.reg 2).length+26 ∧
      u.reg 4 = ones (readRequest (s.reg 2)).width ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 4 → r ≠ 24 → r ≠ 25 → r ≠ 26 → u.reg r = s.reg r := by
  let v := s.write 26 (s.reg 2)
  have copy : Run emptyLanguage (.write 26 (.copy 2)) s v 1 0 := .write
  obtain ⟨a,t₁,run₁,c₁,hrest,_,q₁,keep₁⟩ :=
    FieldCode.takeReverse_run v (src := 26) (dst := 24) (by decide)
  obtain ⟨u,t₂,run₂,c₂,_,w,q₂,keep₂⟩ :=
    takeLen_run a (src := 26) (dst := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [v,write_same] at hrest c₁
  refine ⟨u,_,.seq copy (.seq run₁ run₂),?_,?_,q₂.trans q₁,?_⟩
  · rw [hrest] at c₂
    have e := rest_le (s.reg 2)
    omega
  · have e : (readRequest (s.reg 2)).width = (take ((take (s.reg 2)).2)).1.length := by
      unfold readRequest
      cases take (s.reg 2)
      rfl
    rw [w,hrest,e]
  · intro r h4 h24 h25 h26
    rw [keep₂ r h26 h4 h24 h25,keep₁ r h26 h24,write_ne _ _ h26]

private def cmpStep (dst : Nat) : Code :=
  .branch (.head 31) (.write 31 (.tail 31)) (set dst false)

def compare (lhs rhs dst : Nat) : Code :=
  .write 30 (.copy lhs) ⨟ .write 31 (.copy rhs) ⨟ set dst true ⨟ forUnary 30 (cmpStep dst)

theorem compare_pure (lhs rhs dst : Nat) : (compare lhs rhs dst).pure := by
  simp [compare,cmpStep,forUnary,HullBatchMachine.set,Code.allowed]

private theorem cmpLoop_run (s : State) {dst : Nat} (hd30 : dst ≠ 30) (hd31 : dst ≠ 31)
    (a b : Nat) (ha : s.reg 30 = ones a) (hb : s.reg 31 = ones b) (dstInit : s.reg dst = [true]) :
    ∃ u t, Run emptyLanguage (forUnary 30 (cmpStep dst)) s u t 0 ∧ t ≤ 7*a+1 ∧
      u.reg dst = [decide (a ≤ b)] ∧ u.queries = s.queries ∧
      ∀ r, r ≠ dst → r ≠ 30 → r ≠ 31 → u.reg r = s.reg r := by
  let I (k : Nat) (v : State) :=
    k ≤ a ∧ v.reg 31 = ones (b-(a-k)) ∧
    v.reg dst = [decide (a-k ≤ b)] ∧ v.queries = s.queries ∧
      ∀ r, r ≠ dst → r ≠ 30 → r ≠ 31 → v.reg r = s.reg r
  have step : ∀ k v, v.reg 30 = ones (k+1) → I (k+1) v →
      ∃ u t, Run emptyLanguage (cmpStep dst) v u t 0 ∧ t ≤ 4 ∧
        u.reg 30 = ones (k+1) ∧ I k (u.write 30 (ones k)) := by
    intro k v hc inv
    obtain ⟨hk,clock,bit,q,regs⟩ := inv
    have decr : a-k = a-(k+1)+1 := by omega
    cases h : b-(a-(k+1)) with
    | zero =>
      let u := v.write dst [false]
      have run : Run emptyLanguage (cmpStep dst) v u 4 0 :=
        runFalse (test := .head 31) (a := .write 31 (.tail 31))
          (by simp [Test.eval,clock,h]) (runSet v dst false)
      refine ⟨u,4,run,by decide,by simpa [u,Ne.symm hd30] using hc,by omega,?_,?_,q,?_⟩
      · have rhs : b-(a-k) = 0 := by omega
        simp [u,Ne.symm hd31,clock,h,rhs]
      · have rhs : ¬a-k ≤ b := by omega
        simp [u,hd30,rhs]
      · intro r h1 h2 h3
        simpa [u,h2,h1] using regs r h1 h2 h3
    | succ p =>
      let u := v.write 31 (ones p)
      have tailRun : Run emptyLanguage (.write 31 (.tail 31)) v u 1 0 := by
        simpa [u,clock,h,Expr.eval,ones_succ] using stepWrite v 31 (.tail 31)
      have run : Run emptyLanguage (cmpStep dst) v u 2 0 :=
        runTrue (test := .head 31) (b := set dst false) (by simp [Test.eval,clock,h]) tailRun
      refine ⟨u,2,run,by decide,by simpa [u] using hc,by omega,?_,?_,q,?_⟩
      · have rhs : b-(a-k) = p := by omega
        simp [u,rhs]
      · have left : a-(k+1) ≤ b := by omega
        have right : a-k ≤ b := by omega
        simp [u,hd30,hd31,bit,left,right]
      · intro r h1 h2 h3
        simpa [u,h2,h3] using regs r h1 h2 h3
  have init : I a s := by
    simp [I,hb,dstInit]
  obtain ⟨u,t,run,cost,_,_,_,bit,queue,regs⟩ := forUnary_run I step a s ha init
  exact ⟨u,t,run,cost,by simpa using bit,queue,regs⟩

theorem compare_run (s : State) {lhs rhs dst : Nat}
    (hl : rhs ≠ 30) (hd30 : dst ≠ 30) (hd31 : dst ≠ 31)
    (a b : Nat) (ha : s.reg lhs = ones a) (hb : s.reg rhs = ones b) :
    ∃ u t, Run emptyLanguage (compare lhs rhs dst) s u t 0 ∧ t ≤ 7*a+9 ∧
      u.reg dst = [decide (a ≤ b)] ∧ u.queries = s.queries ∧
      ∀ r, r ≠ dst → r ≠ 30 → r ≠ 31 → u.reg r = s.reg r := by
  let x := s.write 30 (ones a)
  let y := x.write 31 (ones b)
  let start := y.write dst [true]
  have copyA : Run emptyLanguage (.write 30 (.copy lhs)) s x 1 0 := by
    simpa [x,ha,Expr.eval] using stepWrite s 30 (.copy lhs)
  have copyB : Run emptyLanguage (.write 31 (.copy rhs)) x y 1 0 := by
    simpa [x,y,hl,hb,Expr.eval] using stepWrite x 31 (.copy rhs)
  obtain ⟨u,t,run,cost,val,queue,keep⟩ := cmpLoop_run start hd30 hd31 a b
    (by simp [x,y,start,Ne.symm hd30]) (by simp [y,start,Ne.symm hd31]) (by simp [start])
  refine ⟨u,_,.seq copyA (.seq copyB (.seq (runSet y dst true) run)),by omega,val,queue,?_⟩
  intro r h1 h2 h3
  rw [keep r h1 h2 h3]
  simp [start,y,x,h1,h2,h3]

private def readTag : Code :=
  .branch (.empty 0) (set 9 false) (set 9 true) ⨟
  .branch (.head 0) (set 8 true) (set 8 false) ⨟ .write 0 (.tail 0)

private theorem readTag_run (s : State) :
    ∃ u, Run emptyLanguage readTag s u 11 0 ∧ u.reg 9 = [!(s.reg 0).isEmpty] ∧
      u.reg 8 = [(s.reg 0).headD false] ∧ u.reg 0 = (s.reg 0).tail ∧
      u.queries = s.queries ∧ ∀ r, r ≠ 0 → r ≠ 8 → r ≠ 9 → u.reg r = s.reg r := by
  let a := s.write 9 [!(s.reg 0).isEmpty]
  let b := a.write 8 [(s.reg 0).headD false]
  let u := b.write 0 (s.reg 0).tail
  have present : Run emptyLanguage (.branch (.empty 0) (set 9 false) (set 9 true)) s a 4 0 := by
    cases h : (s.reg 0).isEmpty
    · simpa [a,h] using runFalse (test := .empty 0) (a := set 9 false)
        (by simpa [Test.eval] using h) (runSet s 9 true)
    · simpa [a,h] using runTrue (test := .empty 0) (b := set 9 true)
        (by simpa [Test.eval] using h) (runSet s 9 false)
  have kind : Run emptyLanguage (.branch (.head 0) (set 8 true) (set 8 false)) a b 4 0 := by
    have h : (Test.head 0).eval a = (s.reg 0).headD false := by simp [a,Test.eval]
    cases k : (s.reg 0).headD false
    · rw [show b = a.write 8 [false] from by rw [show b = a.write 8 [(s.reg 0).headD false] from rfl,k]]
      exact runFalse (h.trans k) (runSet a 8 false)
    · rw [show b = a.write 8 [true] from by rw [show b = a.write 8 [(s.reg 0).headD false] from rfl,k]]
      exact runTrue (h.trans k) (runSet a 8 true)
  have tail : Run emptyLanguage (.write 0 (.tail 0)) b u 1 0 := by
    simpa [u,b,a,Expr.eval] using stepWrite b 0 (.tail 0)
  exact ⟨u,.seq present (.seq kind tail),by simp [u,b,a],by simp [u,b],by simp [u],rfl,
    fun r h0 h8 h9 => by simp [u,b,a,h0,h8,h9]⟩

private def readIndices : Code :=
  readTag ⨟ takeLen 0 5 ⨟ takeLen 0 6 ⨟ takeLen 0 7

private theorem readIndices_run (s : State) :
    let x := s.reg 0
    let rank := take x.tail
    let col := take rank.2
    let row := take col.2
    ∃ u t, Run emptyLanguage readIndices s u t 0 ∧ t ≤ 39*x.length+65 ∧
      u.reg 5 = ones rank.1.length ∧ u.reg 6 = ones col.1.length ∧ u.reg 7 = ones row.1.length ∧
      u.reg 8 = [x.headD false] ∧ u.reg 9 = [!x.isEmpty] ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 0 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 24 → r ≠ 25 →
        u.reg r = s.reg r := by
  dsimp only
  obtain ⟨a,run₀,present,tag,tail,q₀,o₀⟩ := readTag_run s
  obtain ⟨b,t₁,run₁,c₁,x₁,v₁,q₁,o₁⟩ := takeLen_run a (src := 0) (dst := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c,t₂,run₂,c₂,x₂,v₂,q₂,o₂⟩ := takeLen_run b (src := 0) (dst := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨u,t₃,run₃,c₃,_,v₃,q₃,o₃⟩ := takeLen_run c (src := 0) (dst := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [tail] at x₁ c₁ v₁
  rw [x₁] at x₂ c₂ v₂
  rw [x₂] at c₃ v₃
  refine ⟨u,_,.seq run₀ (.seq run₁ (.seq run₂ run₃)),?_,?_,?_,v₃,?_,?_,
    q₃.trans (q₂.trans (q₁.trans q₀)),?_⟩
  · have b₀ := tail_le (s.reg 0)
    have b₁ := rest_le (s.reg 0).tail
    have b₂ := rest_le (take (s.reg 0).tail).2
    omega
  · rw [o₃ 5 (by decide) (by decide) (by decide) (by decide),
      o₂ 5 (by decide) (by decide) (by decide) (by decide),v₁]
  · rw [o₃ 6 (by decide) (by decide) (by decide) (by decide),v₂]
  · rw [o₃ 8 (by decide) (by decide) (by decide) (by decide),
      o₂ 8 (by decide) (by decide) (by decide) (by decide),
      o₁ 8 (by decide) (by decide) (by decide) (by decide),tag]
  · rw [o₃ 9 (by decide) (by decide) (by decide) (by decide),
      o₂ 9 (by decide) (by decide) (by decide) (by decide),
      o₁ 9 (by decide) (by decide) (by decide) (by decide),present]
  · intro r h0 h5 h6 h7 h8 h9 h24 h25
    rw [o₃ r h0 h7 h24 h25,o₂ r h0 h6 h24 h25,o₁ r h0 h5 h24 h25,o₀ r h0 h8 h9]

private def and9 (src : Nat) : Code := .branch (.head src) .skip (set 9 false)

private def andState (s : State) (b : Bool) : State := if b then s else s.write 9 [false]

private theorem and9_run (s : State) {src : Nat} {p b : Bool}
    (hp : s.reg 9 = [p]) (hb : s.reg src = [b]) :
    ∃ t, Run emptyLanguage (and9 src) s (andState s b) t 0 ∧ t ≤ 4 ∧
      (andState s b).reg 9 = [p && b] := by
  cases b
  · exact ⟨4,runFalse (test := .head src) (a := .skip) (by simp [Test.eval,hb]) (runSet s 9 false),
       by decide,by simp [andState]⟩
  · exact ⟨2,runTrue (test := .head src) (b := set 9 false) (by simp [Test.eval,hb]) .skip,
       by decide,by simp [andState,hp]⟩

@[simp] private theorem andQueue (s : State) (b : Bool) :
    (andState s b).queries = s.queries := by cases b <;> rfl

private theorem andKept (s : State) (b : Bool) (r : Nat) (h : r ≠ 9) :
    (andState s b).reg r = s.reg r := by cases b <;> simp [andState,h]

private def finalize : Code := and9 32 ⨟ .branch (.head 8) (and9 33 ⨟ and9 34) .skip

private theorem finalize_run (s : State) (p b p₀ p₁ p₂ : Bool)
    (hp : s.reg 9 = [p]) (hb : s.reg 8 = [b]) (h₀ : s.reg 32 = [p₀])
    (h₁ : s.reg 33 = [p₁]) (h₂ : s.reg 34 = [p₂]) :
    ∃ u t, Run emptyLanguage finalize s u t 0 ∧ t ≤ 15 ∧
      u.reg 9 = [p && p₀ && (!b || (p₁ && p₂))] ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 9 → u.reg r = s.reg r := by
  let a := andState s p₀
  obtain ⟨t₀,run₀,c₀,v₀⟩ := and9_run s hp h₀
  have tag : a.reg 8 = [b] := (andKept s p₀ 8 (by decide)).trans hb
  cases b
  · have skip : Run emptyLanguage (.branch (.head 8) (and9 33 ⨟ and9 34) .skip) a a 2 0 :=
      runFalse (test := .head 8) (a := and9 33 ⨟ and9 34) (by simp [Test.eval,tag]) .skip
    exact ⟨a,_,.seq run₀ skip,by omega,by simpa using v₀,andQueue ..,andKept s p₀⟩
  · let x := andState a p₁
    let u := andState x p₂
    have col : a.reg 33 = [p₁] := (andKept s p₀ 33 (by decide)).trans h₁
    have row : x.reg 34 = [p₂] :=
      (andKept a p₁ 34 (by decide)).trans ((andKept s p₀ 34 (by decide)).trans h₂)
    obtain ⟨t₁,run₁,c₁,v₁⟩ := and9_run a v₀ col
    obtain ⟨t₂,run₂,c₂,v₂⟩ := and9_run x v₁ row
    have done : Run emptyLanguage (.branch (.head 8) (and9 33 ⨟ and9 34) .skip) a u (t₁+t₂+1+1) 0 :=
      runTrue (test := .head 8) (b := .skip) (by simp [Test.eval,tag]) (.seq run₁ run₂)
    refine ⟨u,_,.seq run₀ done,by omega,by simpa [Bool.and_assoc] using v₂,by simp [u,x,a],?_⟩
    intro r hr
    rw [andKept x p₂ r hr,andKept a p₁ r hr,andKept s p₀ r hr]

private def checkIndices : Code :=
  .write 26 (.cons true 4) ⨟ compare 5 26 32 ⨟ compare 6 4 33 ⨟ compare 7 4 34 ⨟ finalize

private theorem checkIndices_run (s : State) (w r c j : Nat) (bit present : Bool)
    (hw : s.reg 4 = ones w) (hr : s.reg 5 = ones r)
    (hc : s.reg 6 = ones c) (hj : s.reg 7 = ones j)
    (hbit : s.reg 8 = [bit]) (hpres : s.reg 9 = [present]) :
    ∃ u t, Run emptyLanguage checkIndices s u t 0 ∧ t ≤ 7*(r+c+j)+47 ∧
      u.reg 9 = [present && decide (r≤w+1) && (!bit || (decide (c≤w) && decide (j≤w)))] ∧
      u.queries = s.queries ∧
      ∀ i, i ≠ 9 → i ≠ 26 → i ≠ 30 → i ≠ 31 → i ≠ 32 → i ≠ 33 → i ≠ 34 → u.reg i = s.reg i := by
  let a := s.write 26 (ones (w+1))
  have ext : Run emptyLanguage (.write 26 (.cons true 4)) s a 1 0 := by
    simpa [a,Expr.eval,hw] using stepWrite s 26 (.cons true 4)
  obtain ⟨b,t₁,run₁,c₁,vr,q₁,o₁⟩ := compare_run a (lhs := 5) (rhs := 26) (dst := 32)
    (by decide) (by decide) (by decide) r (w+1) (by simpa [a] using hr) (by simp [a])
  have wb : b.reg 4 = ones w := by
    simpa [a,o₁ 4 (by decide) (by decide) (by decide)] using hw
  obtain ⟨d,t₂,run₂,c₂,vc,q₂,o₂⟩ := compare_run b (lhs := 6) (rhs := 4) (dst := 33)
    (by decide) (by decide) (by decide) c w
    (by simpa [a,o₁ 6 (by decide) (by decide) (by decide)] using hc) wb
  have wd : d.reg 4 = ones w := (o₂ 4 (by decide) (by decide) (by decide)).trans wb
  obtain ⟨f,t₃,run₃,c₃,vj,q₃,o₃⟩ := compare_run d (lhs := 7) (rhs := 4) (dst := 34)
    (by decide) (by decide) (by decide) j w
    (by simpa [a,o₂ 7 (by decide) (by decide) (by decide),o₁ 7 (by decide) (by decide) (by decide)]
      using hj) wd
  have misc (i : Nat) (ni : i ≠ 26) (n₁ : i ≠ 30) (n₂ : i ≠ 31) (n₃ : i ≠ 32)
      (n₄ : i ≠ 33) (n₅ : i ≠ 34) : f.reg i = s.reg i := by
    rw [o₃ i n₅ n₁ n₂,o₂ i n₄ n₁ n₂,o₁ i n₃ n₁ n₂]
    exact write_ne _ _ ni
  obtain ⟨u,t₄,run₄,c₄,out,q₄,o₄⟩ := finalize_run f present bit (decide (r≤w+1))
    (decide (c≤w)) (decide (j≤w))
    ((misc 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpres)
    ((misc 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbit)
    ((o₃ 32 (by decide) (by decide) (by decide)).trans ((o₂ 32 (by decide) (by decide) (by decide)).trans vr))
    ((o₃ 33 (by decide) (by decide) (by decide)).trans vc) vj
  refine ⟨u,_,.seq ext (.seq run₁ (.seq run₂ (.seq run₃ run₄))),by omega,
    out,q₄.trans (q₃.trans (q₂.trans q₁)),?_⟩
  intro i n₀ n₁ n₂ n₃ n₄ n₅ n₆
  exact (o₄ i n₀).trans (misc i n₁ n₂ n₃ n₄ n₅ n₆)

/-- Decode the request and the query tag and coordinates. Register 1 is
the untouched certificate, and registers 8 and 9 hold singleton flags
for the query kind and for validity. -/
def parse : Code := FieldCode.takeField 0 2 24 25 ⨟ widthFromRequest ⨟ readIndices ⨟ checkIndices

theorem parse_pure : parse.pure := by
  repeat' constructor

theorem parse_run (s cert : Word) :
    let h := header s
    ∃ u t, Run emptyLanguage parse (State.input s cert) u t 0 ∧ t ≤ 200*(s.length+1) ∧
      u.reg 1 = cert ∧ u.reg 2 = h.request ∧ u.reg 4 = ones h.width ∧
      u.reg 5 = ones h.rank ∧ u.reg 6 = ones h.col ∧ u.reg 7 = ones h.row ∧
      u.reg 8 = [h.isBit] ∧ u.reg 9 = [h.valid] ∧ u.queries = [] := by
  dsimp only
  let start := State.input s cert
  obtain ⟨a,t₁,run₁,c₁,tail,request,q₁,o₁⟩ :=
    FieldCode.takeField_run start (src := 0) (dst := 2) (scratch := 24) (flag := 25)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨b,t₂,run₂,c₂,width,q₂,o₂⟩ := widthFromRequest_run a
  have h₀ : b.reg 0 = (take s).2 := (o₂ 0 (by decide) (by decide) (by decide) (by decide)).trans tail
  obtain ⟨c,t₃,run₃,c₃,rank,col,row,tag,present,q₃,o₃⟩ := readIndices_run b
  rw [h₀] at rank col row tag present c₃
  have req : a.reg 2 = (header s).request := request
  have wd : c.reg 4 = ones (header s).width := by
    rw [o₃ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),width,req]
    rfl
  let h := header s
  obtain ⟨u,t₄,run₄,c₄,result,q₄,o₄⟩ := checkIndices_run c h.width h.rank h.col h.row h.isBit
    (!(take s).2.isEmpty) wd rank col row tag present
  have wi (i : Nat) (n : i < 9) : u.reg i = c.reg i :=
    o₄ i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨u,_,.seq run₁ (.seq run₂ (.seq run₃ run₄)),?_,?_,?_,(wi 4 (by decide)).trans wd,
    (wi 5 (by decide)).trans rank,(wi 6 (by decide)).trans col,(wi 7 (by decide)).trans row,
    (wi 8 (by decide)).trans tag,result,q₄.trans (q₃.trans (q₂.trans q₁))⟩
  · change t₁ ≤ 14*s.length+17 at c₁
    rw [req] at c₂
    have x := QueryEncoding.take_data_le s
    have l := rest_le s
    have l₁ := tail_le (take s).2
    have l₂ := rest_le ((take s).2.tail)
    have l₃ := rest_le (take ((take s).2.tail)).2
    have l₄ := QueryEncoding.take_data_le ((take s).2.tail)
    have l₅ := QueryEncoding.take_data_le (take ((take s).2.tail)).2
    have l₆ := QueryEncoding.take_data_le (take (take ((take s).2.tail)).2).2
    simp only [h,header] at c₂ c₄
    omega
  · rw [wi 1 (by decide),o₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),o₂ 1 (by decide) (by decide) (by decide) (by decide),
      o₁ 1 (by decide) (by decide) (by decide) (by decide)]
    rfl
  · rw [wi 2 (by decide),o₃ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),o₂ 2 (by decide) (by decide) (by decide) (by decide),req]

def Header.Matches (h : Header) (q : Query (h.width+1)) : Prop :=
  h.rank = q.level.val ∧ match q with
  | .rank _ => h.isBit = false
  | .bit _ i j => h.isBit = true ∧ h.col = i.val ∧ h.row = j.val

private theorem readRankDef (w : Nat) (suffix : Word) :
    HullQueryLanguage.readQuery (w+1) (false :: suffix) =
      if h : (take suffix).1.length < w+2 then some (.rank ⟨_,h⟩) else none := by
  simp only [HullQueryLanguage.readQuery, HullQueryLanguage.takeIndex]

private theorem readBitDef (w : Nat) (suffix : Word) :
    HullQueryLanguage.readQuery (w+1) (true :: suffix) =
      let r := take suffix
      let c := take r.2
      let j := take c.2
      if hr : r.1.length < w+2 then
        if hc : c.1.length < w+1 then
          if hj : j.1.length < w+1 then
            some (.bit ⟨_,hr⟩ ⟨_,hc⟩ ⟨_,hj⟩)
          else none
        else none
      else none := by
  simp only [HullQueryLanguage.readQuery, HullQueryLanguage.takeIndex]

theorem valid_iff_query (s : Word) :
    (header s).valid = true ↔
      ∃ q : Query ((header s).width+1), HullQueryLanguage.readQuery ((header s).width+1) (take s).2 = some q := by
  cases hz : (take s).2 with
  | nil => simp [header,hz,HullQueryLanguage.readQuery]
  | cons b bs =>
    cases b
    · rw [readRankDef]
      by_cases h : (take bs).1.length ≤ (readRequest (take s).1).width+1 <;>
        simp [header,hz,h,Nat.lt_succ_iff]
    · rw [readBitDef]
      by_cases hr : (take bs).1.length ≤ (readRequest (take s).1).width+1 <;>
        by_cases hc : (take (take bs).2).1.length ≤ (readRequest (take s).1).width <;>
        by_cases hj : (take (take (take bs).2).2).1.length ≤ (readRequest (take s).1).width <;>
        simp [header,hz,hr,hc,hj,Nat.lt_succ_iff]

theorem query_matches (s : Word) (q : Query ((header s).width+1))
    (read : HullQueryLanguage.readQuery ((header s).width+1) (take s).2 = some q) :
    (header s).Matches q := by
  cases hz : (take s).2 with
  | nil => simp [hz,HullQueryLanguage.readQuery] at read
  | cons b bs =>
    cases b
    · rw [hz,readRankDef] at read
      split at read
      · cases read
        simp [Header.Matches,header,hz,Query.level]
      · contradiction
    · rw [hz,readBitDef] at read
      dsimp only at read
      split at read
      · split at read
        · split at read
          · cases read
            simp [Header.Matches,header,hz,Query.level]
          · contradiction
        · contradiction
      · contradiction

end QueryHeaderCode
