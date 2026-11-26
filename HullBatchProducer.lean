module

public import HullBatchPrograms
public import ComplexityModel.WordCode

@[expose] public section

namespace HullBatchProducer

open ComplexityModel HullBatchMachine HullBatchPrograms HullRecovery HullQueryLanguage
open QueryEncoding (readRequest put)

private def putIndex (ctr : Nat) : Code :=
  .write 16 (.tail ctr) ⨟ WordCode.putField 16 12 13 14 15

private theorem putIndex_run (s : State) (ctr : Nat) :
    ∃ u t, Run emptyLanguage (putIndex ctr) s u t 0 ∧ t ≤ 14*(s.reg ctr).length+25 ∧
      u.reg 12 = put (s.reg ctr).tail (s.reg 12) ∧
      WordCode.Preserves s u [12,13,14,15,16] := by
  let a := s.write 16 (s.reg ctr).tail
  have copy : Run emptyLanguage (.write 16 (.tail ctr)) s a 1 0 := .write
  obtain ⟨u,run,payload,frame⟩ := WordCode.putField_run a (src := 16) (dst := 12) (tmp := 13)
    (rev := 14) (flag := 15) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨u, _, .seq copy run, ?_, by simpa [a] using payload, ?_⟩
  · have ha : (a.reg 16).length ≤ (s.reg ctr).length := by simp [a]
    omega
  · exact ((WordCode.preserves_write ..).mono (by simp)).trans
      (frame.mono (by simp (config := { decide := true })))

private def indices : List Nat → Code
  | [] => .skip
  | r :: rs => putIndex r ⨟ indices rs

private theorem indices_run (s : State) (which : List Nat) (N : Nat)
    (regs : ∀ r ∈ which, r ∉ [12,13,14,15,16] ∧ (s.reg r).length ≤ N) :
    ∃ u t, Run emptyLanguage (indices which) s u t 0 ∧ t ≤ (14*N+26)*which.length+1 ∧
      u.reg 12 = which.foldl (fun acc r => put (s.reg r).tail acc) (s.reg 12) ∧
      WordCode.Preserves s u [12,13,14,15,16] := by
  induction which generalizing s with
  | nil => exact ⟨s,1,.skip,by simp,rfl,⟨rfl,fun _ _ => rfl⟩⟩
  | cons r rs ih =>
    obtain ⟨v,t,run,cost,w,frame⟩ := putIndex_run s r
    obtain ⟨u,t',run',cost',w',frame'⟩ := ih v (fun i hi => by
      obtain ⟨hr, hlen⟩ := regs i (List.mem_cons_of_mem _ hi)
      exact ⟨hr, by rw [frame.2 i hr]; exact hlen⟩)
    have max := (regs r List.mem_cons_self).2
    refine ⟨u,_,.seq run run',?_,?_,frame.trans frame'⟩
    · simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [w',w,List.foldl_cons]
      have rew (is : List Nat) (a : Word) (h : ∀ i ∈ is, i ∉ [12,13,14,15,16]) :
          is.foldl (fun acc i => put (v.reg i).tail acc) a =
            is.foldl (fun acc i => put (s.reg i).tail acc) a := by
        induction is generalizing a with
        | nil => rfl
        | cons i is ih' =>
          rw [List.foldl_cons,List.foldl_cons,frame.2 i (h i List.mem_cons_self)]
          exact ih' _ (fun j hj => h j (List.mem_cons_of_mem _ hj))
      exact rew rs _ (fun i hi => (regs i (List.mem_cons_of_mem _ hi)).1)

private def emit (tag : Bool) (which : List Nat) : Code :=
  .write 12 .empty ⨟ indices which ⨟ .write 12 (.cons tag 12) ⨟
    WordCode.putField 0 12 13 14 15 ⨟ .push 12 ⨟ .write 1 (.cons true 1)

private theorem emit_run (s : State) (tag : Bool) (which : List Nat) (N : Nat)
    (n : (s.reg 0).length + 1 ≤ N)
    (regs : ∀ r ∈ which, r ∉ [12,13,14,15,16] ∧ (s.reg r).length ≤ N)
    (size : which.length ≤ 3) (count : s.reg 1 = ones s.queries.length) :
    ∃ u t, Run emptyLanguage (emit tag which) s u t 0 ∧ t ≤ 200*N ∧
      u.queries = put (s.reg 0) (tag :: which.foldl (fun acc r => put (s.reg r).tail acc) []) :: s.queries ∧
      u.reg 1 = ones u.queries.length ∧
      ∀ r, r ∉ [1,12,13,14,15,16] → u.reg r = s.reg r := by
  let a := s.write 12 []
  have clear : Run emptyLanguage (.write 12 .empty) s a 1 0 := .write
  obtain ⟨b,t,run,cost,payload,frame⟩ := indices_run a which N (fun r hr => by
    obtain ⟨hreg, hlen⟩ := regs r hr
    have neq : r ≠ 12 := fun e => hreg (by simp [e])
    exact ⟨hreg, by simpa [a, neq] using hlen⟩)
  let c := b.write 12 (tag :: b.reg 12)
  have tagged : Run emptyLanguage (.write 12 (.cons tag 12)) b c 1 0 := .write
  obtain ⟨d,wrap,encoded,frame'⟩ := WordCode.putField_run c (src := 0) (dst := 12) (tmp := 13) (rev := 14)
    (flag := 15) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let e := d.push 12
  let u := e.write 1 (true :: e.reg 1)
  have push : Run emptyLanguage (.push 12) d e 1 0 := .push
  have inc : Run emptyLanguage (.write 1 (.cons true 1)) e u 1 0 := .write
  have c₀ : c.reg 0 = s.reg 0 := by
    simp [c,frame.2 0 (by decide),a]
  have allOther (r : Nat) (h : r ∉ [12,13,14,15,16]) : d.reg r = s.reg r := by
    have hc : r ≠ 12 := fun eq => h (by simp [eq])
    rw [frame'.2 r (by intro hin; exact h (by simp at hin ⊢; omega)), write_ne _ _ hc,
      frame.2 r h, write_ne _ _ hc]
  have que : u.queries = d.reg 12 :: s.queries := by
    simp [u,e,State.push,frame'.1,c,frame.1,a]
  have payloadEq (is : List Nat) (buf : Word) (h : ∀ i ∈ is, i ∉ [12,13,14,15,16]) :
      is.foldl (fun acc r => put (a.reg r).tail acc) buf =
        is.foldl (fun acc r => put (s.reg r).tail acc) buf := by
    induction is generalizing buf with
    | nil => rfl
    | cons i is ih =>
      have hi : i ≠ 12 := fun eq => h i List.mem_cons_self (by simp [eq])
      rw [List.foldl_cons,List.foldl_cons,write_ne _ _ hi]
      exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))
  refine ⟨u,_,.seq clear (.seq run (.seq tagged (.seq wrap (.seq push inc)))),?_,?_,?_,?_⟩
  · have costBig := Nat.mul_le_mul_left (14*N+26) size
    simp only [c₀]
    simp only [Nat.mul_succ, Nat.mul_zero] at costBig
    omega
  · rw [que,encoded,c₀]
    simp only [c,write_same,payload]
    rw [payloadEq _ _ (fun i hi => (regs i hi).1)]
    rfl
  · rw [que]
    simp [u,e,State.push,allOther 1 (by decide),count]
  · intro r hr
    have h1 : r ≠ 1 := fun eq => hr (by simp [eq])
    have hframe : r ∉ [12,13,14,15,16] := fun hi => hr (List.mem_cons_of_mem _ hi)
    simpa [u,e,State.push,h1] using allOther r hframe

private theorem pushLoop_run {ctr : Nat} {body : Code} {bound : Nat}
    (n : Nat) (rows : Nat → List Word) (keep : State → Prop)
    (step : ∀ k s, k+1 ≤ n → s.reg ctr = ones (k+1) → keep s → s.reg 1 = ones s.queries.length →
      ∃ u t, Run emptyLanguage body s u t 0 ∧ t ≤ bound ∧ u.reg ctr = ones (k+1) ∧
        keep (u.write ctr (ones k)) ∧ u.queries = rows k ++ s.queries ∧
        (u.write ctr (ones k)).reg 1 = ones u.queries.length)
    (s : State) (hu : s.reg ctr = ones n) (hs : keep s)
    (count : s.reg 1 = ones s.queries.length) :
    ∃ u t, Run emptyLanguage (forUnary ctr body) s u t 0 ∧ t ≤ (bound+3)*n+1 ∧
      keep u ∧ u.queries = (List.range n).flatMap rows ++ s.queries ∧
      u.reg 1 = ones u.queries.length := by
  let I (k : Nat) (v : State) :=
    k ≤ n ∧ keep v ∧ (List.range k).flatMap rows ++ v.queries = (List.range n).flatMap rows ++ s.queries ∧
      v.reg 1 = ones v.queries.length
  have one : ∀ k v, v.reg ctr = ones (k+1) → I (k+1) v →
      ∃ u t, Run emptyLanguage body v u t 0 ∧ t ≤ bound ∧ u.reg ctr = ones (k+1) ∧
        I k (u.write ctr (ones k)) := by
    intro k v hc hi
    obtain ⟨hkn,keepV,e,countV⟩ := hi
    obtain ⟨u,t,run,cost,clock,hkeep,hqs,hcount⟩ := step k v hkn hc keepV countV
    refine ⟨u,t,run,cost,clock,by omega,hkeep,?_,hcount⟩
    rw [write_queue, hqs]
    simpa [List.range_succ,List.append_assoc] using e
  obtain ⟨u,t,run,cost,_,_,hkeep,que,hcount⟩ := forUnary_run I one n s hu ⟨Nat.le_refl _,hs,rfl,count⟩
  exact ⟨u,t,run,cost,hkeep,by simpa using que,hcount⟩

private def idx (n : Nat) (tail : Word) := put (ones n) tail
private def bitQ (s : Word) (r i j : Nat) : Word :=
  put s (true :: idx r (idx i (idx j [])))
private def rankQ (s : Word) (r : Nat) : Word := put s (false :: idx r [])

private def rowWords (s : Word) (r i n : Nat) : List Word :=
  (List.range n).map (bitQ s r i)

private def columnWords (s : Word) (r d n : Nat) : List Word :=
  (List.range n).flatMap (fun i => rowWords s r i d)

private def rankWords (s : Word) (d r : Nat) : List Word :=
  rankQ s r :: columnWords s r d d

private def rowLoop : Code := forUnary 4 (emit true [4,5,8])

private theorem rowLoop_run (s : State) (r i n N : Nat)
    (hr : s.reg 8 = ones (r+1)) (hi : s.reg 5 = ones (i+1)) (hn : s.reg 4 = ones n)
    (b0 : (s.reg 0).length+1 ≤ N) (br : r+1 ≤ N) (bi : i+1 ≤ N) (bn : n ≤ N)
    (count : s.reg 1 = ones s.queries.length) :
    ∃ u t, Run emptyLanguage rowLoop s u t 0 ∧ t ≤ (200*N+3)*n+1 ∧
      u.queries = rowWords (s.reg 0) r i n ++ s.queries ∧ u.reg 1 = ones u.queries.length ∧
      ∀ j, j ∉ [1,4,12,13,14,15,16] → u.reg j = s.reg j := by
  let keep (u : State) := ∀ j, j ∉ [1,4,12,13,14,15,16] → u.reg j = s.reg j
  have step : ∀ k v, k+1 ≤ n → v.reg 4 = ones (k+1) → keep v →
      v.reg 1 = ones v.queries.length →
      ∃ u t, Run emptyLanguage (emit true [4,5,8]) v u t 0 ∧ t ≤ 200*N ∧
        u.reg 4 = ones (k+1) ∧ keep (u.write 4 (ones k)) ∧
        u.queries = [bitQ (s.reg 0) r i k] ++ v.queries ∧
        (u.write 4 (ones k)).reg 1 = ones u.queries.length := by
    intro k v hk hv keepV cnt
    have h0 : v.reg 0 = s.reg 0 := keepV 0 (by decide)
    have h8 : v.reg 8 = _ := (keepV 8 (by decide)).trans hr
    have h5 : v.reg 5 = _ := (keepV 5 (by decide)).trans hi
    have inputs : ∀ j ∈ [4,5,8], j ∉ [12,13,14,15,16] ∧ (v.reg j).length ≤ N := by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨by decide, by rw [hv,ones_length]; omega⟩
      · exact ⟨by decide, by simpa only [h5,ones_length] using bi⟩
      · exact ⟨by decide, by simpa only [h8,ones_length] using br⟩
    obtain ⟨u,t,run,cost,queue,one,frame⟩ := emit_run v true [4,5,8] N
      (by rw [h0]; exact b0) inputs (by decide) cnt
    refine ⟨u,t,run,cost,(frame 4 (by decide)).trans hv,?_,?_,by simpa using one⟩
    · intro j hj
      have ne : j ≠ 4 := fun e => hj (by simp [e])
      rw [write_ne _ _ ne, frame j (by intro e; apply hj; simp at e ⊢; omega)]
      exact keepV j hj
    · simpa [bitQ,idx,h0,h8,h5,hv] using queue
  obtain ⟨u,t,run,cost,frame,queue,one⟩ := pushLoop_run n
    (fun k => [bitQ (s.reg 0) r i k]) keep step s hn (fun _ _ => rfl) count
  refine ⟨u,t,run,cost,?_,one,frame⟩
  have flat {α β : Type} (xs : List α) (f : α → β) :
      xs.flatMap (fun x => [f x]) = xs.map f := by
    induction xs <;> simp [*]
  simpa [flat, rowWords] using queue

private def stepColumn : Code := .write 4 (.copy 2) ⨟ rowLoop
private def columnLoop : Code := forUnary 5 stepColumn

private theorem columnLoop_run (s : State) (r d n N : Nat)
    (hr : s.reg 8 = ones (r+1)) (hd : s.reg 2 = ones d) (hn : s.reg 5 = ones n)
    (b0 : (s.reg 0).length+1 ≤ N) (br : r+1 ≤ N) (bd : d ≤ N) (bn : n ≤ N)
    (count : s.reg 1 = ones s.queries.length) :
    ∃ u t, Run emptyLanguage columnLoop s u t 0 ∧ t ≤ ((200*N+3)*d+6)*n+1 ∧
      u.queries = columnWords (s.reg 0) r d n ++ s.queries ∧ u.reg 1 = ones u.queries.length ∧
      ∀ j, j ∉ [1,4,5,12,13,14,15,16] → u.reg j = s.reg j := by
  let keep (u : State) := ∀ j, j ∉ [1,4,5,12,13,14,15,16] → u.reg j = s.reg j
  have step : ∀ k v, k+1 ≤ n → v.reg 5 = ones (k+1) → keep v →
      v.reg 1 = ones v.queries.length →
      ∃ u t, Run emptyLanguage stepColumn v u t 0 ∧ t ≤ (200*N+3)*d+3 ∧
        u.reg 5 = ones (k+1) ∧ keep (u.write 5 (ones k)) ∧
        u.queries = rowWords (s.reg 0) r k d ++ v.queries ∧
        (u.write 5 (ones k)).reg 1 = ones u.queries.length := by
    intro k v hk hv keepV cnt
    let w := v.write 4 (ones d)
    have newClock : Run emptyLanguage (.write 4 (.copy 2)) v w 1 0 := by
      simpa [w,Expr.eval,keepV 2 (by decide),hd] using stepWrite v 4 (.copy 2)
    obtain ⟨u,t,run,cost,queue,one,frame⟩ := rowLoop_run w r k d N
      (by simpa [w,keepV 8 (by decide)] using hr) (by simpa [w] using hv)
      (by simp [w]) (by simpa [w,keepV 0 (by decide)] using b0) br (by omega) bd
      (by simpa [w] using cnt)
    refine ⟨u,_,.seq newClock run,by omega,?_,?_,?_,by simpa using one⟩
    · simpa [w,frame 5 (by decide)] using hv
    · intro j hj
      have h4 : j ≠ 4 := fun e => hj (by simp [e])
      have h5 : j ≠ 5 := fun e => hj (by simp [e])
      rw [write_ne _ _ h5, frame j (by intro e; apply hj; simp at e ⊢; omega),
        write_ne _ _ h4]
      exact keepV j hj
    · simpa [w,keepV 0 (by decide)] using queue
  obtain ⟨u,t,run,cost,frame,qs,ones⟩ := pushLoop_run n (fun k => rowWords (s.reg 0) r k d) keep step
    s hn (fun _ _ => rfl) count
  exact ⟨u,t,run,cost,qs,ones,frame⟩

private def stepRankProducer : Code := .write 5 (.copy 2) ⨟ columnLoop ⨟ emit false [8]
private def rankLoop : Code := forUnary 8 stepRankProducer

private theorem rankLoop_run (s : State) (d n N : Nat) (hd : s.reg 2 = ones d) (hn : s.reg 8 = ones n)
    (b0 : (s.reg 0).length+1 ≤ N) (bd : d ≤ N) (bn : n ≤ N)
    (count : s.reg 1 = ones s.queries.length) :
    ∃ u t, Run emptyLanguage rankLoop s u t 0 ∧ t ≤
      (((200*N+3)*d+6)*d+200*N+8)*n+1 ∧
      u.queries = (List.range n).flatMap (rankWords (s.reg 0) d) ++ s.queries ∧
      u.reg 1 = ones u.queries.length ∧
      ∀ j, j ∉ [1,4,5,8,12,13,14,15,16] → u.reg j = s.reg j := by
  let keep (u : State) := ∀ j, j ∉ [1,4,5,8,12,13,14,15,16] → u.reg j = s.reg j
  have step : ∀ k v, k+1 ≤ n → v.reg 8 = ones (k+1) → keep v →
      v.reg 1 = ones v.queries.length →
      ∃ u t, Run emptyLanguage stepRankProducer v u t 0 ∧
        t ≤ ((200*N+3)*d+6)*d+200*N+5 ∧ u.reg 8 = ones (k+1) ∧
        keep (u.write 8 (ones k)) ∧ u.queries = rankWords (s.reg 0) d k ++ v.queries ∧
        (u.write 8 (ones k)).reg 1 = ones u.queries.length := by
    intro k v hk hv keepV cnt
    let w := v.write 5 (ones d)
    have newClock : Run emptyLanguage (.write 5 (.copy 2)) v w 1 0 := by
      simpa [w,Expr.eval,keepV 2 (by decide),hd] using stepWrite v 5 (.copy 2)
    obtain ⟨a,t₁,run₁,c₁,qa,ca,ra⟩ := columnLoop_run w k d d N
      (by simpa [w] using hv) (by simpa [w,keepV 2 (by decide)] using hd)
      (by simp [w]) (by simpa [w,keepV 0 (by decide)] using b0) (by omega) bd bd
      (by simpa [w] using cnt)
    have ar : a.reg 8 = ones (k+1) := by simpa [w,ra 8 (by decide)] using hv
    have ax : a.reg 0 = s.reg 0 := by simp [w,ra 0 (by decide),keepV 0 (by decide)]
    have inputs : ∀ j ∈ [8], j ∉ [12,13,14,15,16] ∧ (a.reg j).length ≤ N := by
      intro j hj
      have : j = 8 := List.mem_singleton.mp hj
      subst j
      exact ⟨by decide, by rw [ar,ones_length];omega⟩
    obtain ⟨u,t₂,run₂,c₂,qu,cu,ru⟩ := emit_run a false [8] N (by rw [ax]; exact b0)
      inputs (by decide) ca
    refine ⟨u,_,.seq newClock (.seq run₁ run₂),by omega,(ru 8 (by decide)).trans ar,?_,?_,
      by simpa using cu⟩
    · intro j hj
      have h5 : j ≠ 5 := fun e => hj (by simp [e])
      have h8 : j ≠ 8 := fun e => hj (by simp [e])
      rw [write_ne _ _ h8, ru j (by intro e; apply hj; simp at e ⊢; omega),
        ra j (by intro e; apply hj; simp at e ⊢; omega), write_ne _ _ h5]
      exact keepV j hj
    · simp [qu,qa,ax,ar,w,rankWords,rankQ,idx,keepV 0 (by decide)]
  obtain ⟨u,t,run,cost,frame,qs,ones⟩ := pushLoop_run n (rankWords (s.reg 0) d) keep step
    s hn (fun _ _ => rfl) count
  exact ⟨u,t,run,cost,qs,ones,frame⟩

private theorem rangeFin (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp

private theorem rowWords_eq (s : Word) (r : Fin ((readRequest s).width.succ+1))
    (i : Fin (readRequest s).width.succ) :
    rowWords s r i (readRequest s).width.succ =
      (List.finRange (readRequest s).width.succ).map (fun j => questionWord s (.bit r i j)) := by
  unfold rowWords
  rw [rangeFin,List.map_map]
  rfl

private theorem rankWords_eq (s : Word) (r : Fin ((readRequest s).width.succ+1)) :
    rankWords s (readRequest s).width.succ r =
      (block (readRequest s).width.succ r).map (questionWord s) := by
  unfold rankWords block
  rw [List.map_cons]
  congr 1
  unfold columnWords
  rw [rangeFin,List.flatMap_map,List.map_flatMap]
  apply congrArg (fun f => (List.finRange (readRequest s).width.succ).flatMap f)
  funext i
  rw [rowWords_eq,List.map_map]
  rfl

private theorem questions_eq (s : Word) :
    (List.range ((readRequest s).width.succ+1)).flatMap (rankWords s (readRequest s).width.succ) =
      questions s := by
  unfold questions batch
  rw [rangeFin,List.flatMap_map,List.map_flatMap]
  apply congrArg (fun f => (List.finRange ((readRequest s).width.succ+1)).flatMap f)
  funext r
  exact rankWords_eq s r

private def clearRegs : List Nat → Code
  | [] => .skip
  | r :: rs => .write r .empty ⨟ clearRegs rs

private theorem clearRegs_run (s : State) (rs : List Nat) :
    ∃ u, Run emptyLanguage (clearRegs rs) s u (2*rs.length+1) 0 ∧ u.queries = s.queries ∧
      ∀ r, u.reg r = if r ∈ rs then [] else s.reg r := by
  induction rs generalizing s with
  | nil => exact ⟨s,.skip,rfl,by simp⟩
  | cons j js ih =>
    let v := s.write j []
    have clear : Run emptyLanguage (.write j .empty) s v 1 0 := .write
    obtain ⟨u,run,queue,spec⟩ := ih v
    let time := 2 * js.length + 1
    have h : 1 + time + 1 = 2 * (j :: js).length + 1 := by
      simp [time, Nat.mul_succ];omega
    refine ⟨u,?_,queue,?_⟩
    · rw [← h]
      exact .seq clear run
    · intro r
      by_cases eq : r = j <;> by_cases mem : r ∈ js <;> simp [v,spec,eq,mem]

/-- Generate the fixed batch in reverse iteration order, so pushes leave the
same ascending ordering that the answer collector expects. -/
def producer : Code :=
  computeDimension ⨟ .write 8 (.cons true 2) ⨟ rankLoop ⨟ clearRegs (List.range' 2 15)

theorem producer_pure : producer.pure := by
  repeat' constructor

theorem producer_run (s : Word) :
    ∃ t, Run emptyLanguage producer (State.input s) (BatchCode.input s (questions s)) t 0 ∧
      t ≤ 10000 * (s.length + 1)^4 := by
  let init := State.input s
  let d := (readRequest s).width.succ
  let X := s.length+1
  let N := 2*X
  obtain ⟨a,t₁,run₁,c₁,dim,q₁,r₁⟩ := computeDimension_run init
  change a.reg 2 = ones d at dim
  let start := a.write 8 (ones (d+1))
  have load : Run emptyLanguage (.write 8 (.cons true 2)) a start 1 0 := by
    simpa [start,Expr.eval,dim] using stepWrite a 8 (.cons true 2)
  have h0 : start.reg 0 = s := by simp [start,r₁ 0 (by decide) (by decide) (by decide) (by decide),init,State.input]
  have h1 : start.reg 1 = [] := by simp [start,r₁ 1 (by decide) (by decide) (by decide) (by decide),init,State.input]
  have empty : start.queries = [] := by simp [start,q₁,init,State.input]
  have hD : d ≤ X := Nat.succ_le_succ (width_le s)
  have hX : 1 ≤ X := by dsimp [X];omega
  have hN : 1 ≤ N := by dsimp [N];omega
  have xN : X ≤ N := by dsimp [N];omega
  have bn : d+1 ≤ N := by dsimp [N];omega
  obtain ⟨b,t₂,run₂,c₂,q₂,count,frame⟩ := rankLoop_run start d (d+1) N
    (by simp [start,dim]) (by simp [start]) (by rw [h0]; exact xN) (by omega) bn
    (by simp [empty,h1])
  have ordered : b.queries = questions s := by
    rw [h0,empty,List.append_nil] at q₂
    exact q₂.trans (questions_eq s)
  obtain ⟨out,run₃,queue,final⟩ := clearRegs_run b (List.range' 2 15)
  have clean : out = BatchCode.input s (questions s) := by
    apply extState _ (queue.trans ordered)
    intro j
    have hmem : j ∈ List.range' 2 15 ↔ 2 ≤ j ∧ j < 17 := List.mem_range'_1
    by_cases h0j : j = 0
    · subst j
      rw [final,if_neg (by decide),frame 0 (by decide),h0]
      rfl
    by_cases h1j : j = 1
    · subst j
      rw [final,if_neg (by decide),count,ordered]
      rfl
    by_cases hj : j < 17
    · rw [final,if_pos (hmem.mpr ⟨by omega,hj⟩)]
      simp [BatchCode.input,State.input,h0j,h1j]
    · have untouched (k : Nat) (hk : 17 ≤ k) : start.reg k = [] := by
        have hk2 : k ≠ 2 := by omega
        have hk8 : k ≠ 8 := by omega
        have hk9 : k ≠ 9 := by omega
        have hk10 : k ≠ 10 := by omega
        have hk11 : k ≠ 11 := by omega
        rw [show start = a.write 8 (ones (d+1)) from rfl, write_ne _ _ hk8, r₁ k hk2 hk9 hk10 hk11]
        simp [init,State.input,show k ≠ 0 by omega,show k ≠ 1 by omega]
      rw [final,if_neg (fun h => hj (hmem.mp h).2),frame j (by simp;omega),untouched j (by omega)]
      simp [BatchCode.input,State.input,h0j,h1j]
  have run := Run.seq run₁ (Run.seq load (Run.seq run₂ run₃))
  rw [clean] at run
  refine ⟨_,run,?_⟩
  · change t₁ ≤ 30*s.length+30 at c₁
    have c₁' : t₁ ≤ 30*X := by dsimp [X];omega
    have leD : d ≤ N := by omega
    have term₁ : (200*N+3)*d ≤ (200*N+3)*N := Nat.mul_le_mul_left _ leD
    have term₂ : ((200*N+3)*d+6)*d ≤ ((200*N+3)*N+6)*N :=
      Nat.mul_le_mul (Nat.add_le_add_right term₁ 6) leD
    have term₃ : (((200*N+3)*d+6)*d+200*N+8)*(d+1) ≤
        (((200*N+3)*N+6)*N+200*N+8)*N :=
      Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add_right term₂ (200*N)) 8) bn
    have p1 : N ≤ N*N :=
      calc
        N = N*1 := (Nat.mul_one N).symm
        _ ≤ N*N := Nat.mul_le_mul_left _ hN
    have p2 := Nat.mul_le_mul_left N p1
    have p3 := Nat.mul_le_mul_left N p2
    have nE : N*N*N*N = 16*(X^4) := by
      calc
        N*N*N*N = N^4 := by simp [Nat.pow_succ]
        _ = 16*(X^4) := Nat.mul_pow 2 X 4
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one] at term₃ p2 p3 c₂
    have p3' : N*(N*(N*N)) = 16*(X^4) := by simpa [Nat.mul_assoc] using nE
    have h16 := p3'
    simp only [List.length_range']
    change _ ≤ 10000*X^4
    omega

end HullBatchProducer
