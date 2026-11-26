module

public import HullBatchMachine
public import HullQueryLanguage
public import ComplexityModel.BatchCode

@[expose] public section

namespace HullBatchPrograms

open ComplexityModel HullBatchMachine HullRecovery HullQueryLanguage
open QueryEncoding (readRequest matrixWord put pack take)

-- Registers 0 and 1 hold the request and the remaining replies. Register 2
-- holds the dimension. Registers 3–8 are the block decoder's workspace.
private def appendBit : Code :=
  .write 3 (.cons true 3) ⨟
  .branch (.head 1) (.write 3 (.cons true 3)) (.write 3 (.cons false 3)) ⨟
  .write 1 (.tail 1)

private def bitsInto : Nat → Word → Word → Word × Word
  | 0, bs, acc => (bs, acc)
  | n+1, bs, acc => bitsInto n bs.tail (bs.head?.getD false :: true :: acc)

private theorem appendBit_run (s : State) :
    ∃ u, Run emptyLanguage appendBit s u 6 0 ∧ u.reg 1 = (s.reg 1).tail ∧
      u.reg 3 = (s.reg 1).head?.getD false :: true :: s.reg 3 ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 1 → r ≠ 3 → u.reg r = s.reg r := by
  let a := s.write 3 (true :: s.reg 3)
  let b := a.write 3 ((s.reg 1).head?.getD false :: true :: s.reg 3)
  let u := b.write 1 (s.reg 1).tail
  have first : Run emptyLanguage (.write 3 (.cons true 3)) s a 1 0 := .write
  have append : Run emptyLanguage
      (.branch (.head 1) (.write 3 (.cons true 3)) (.write 3 (.cons false 3))) a b 2 0 := by
    have ht : (Test.head 1).eval a = (s.reg 1).head?.getD false := by simp [a, Test.eval]
    apply Run.branch ht
    have go (bit : Bool) : Run emptyLanguage (.write 3 (.cons bit 3)) a
        (a.write 3 (bit :: true :: s.reg 3)) 1 0 := by
      simpa [a, Expr.eval] using stepWrite a 3 (.cons bit 3)
    cases hh : (s.reg 1).head?.getD false
    · simpa [b, hh] using go false
    · simpa [b, hh] using go true
  have advance : Run emptyLanguage (.write 1 (.tail 1)) b u 1 0 := by
    simpa [u, b, a, Expr.eval] using stepWrite b 1 (.tail 1)
  refine ⟨u, ?_, by simp [u], by simp [u, b], by simp [u, b, a], ?_⟩
  · exact .seq first (.seq append advance)
  · intro r h1 h3
    simp [u, b, a, h1, h3]

private theorem consumeBits_run (s : State) (n : Nat) (hn : s.reg 4 = ones n) :
    ∃ u t, Run emptyLanguage (forUnary 4 appendBit) s u t 0 ∧ t ≤ 9*n + 1 ∧
      (u.reg 1, u.reg 3) = bitsInto n (s.reg 1) (s.reg 3) ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → u.reg r = s.reg r := by
  let I (k : Nat) (v : State) :=
    bitsInto k (v.reg 1) (v.reg 3) = bitsInto n (s.reg 1) (s.reg 3) ∧
    v.queries = s.queries ∧ ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → v.reg r = s.reg r
  have step : ∀ k v, v.reg 4 = ones (k + 1) → I (k + 1) v →
      ∃ u t, Run emptyLanguage appendBit v u t 0 ∧ t ≤ 6 ∧ u.reg 4 = ones (k + 1) ∧
        I k (u.write 4 (ones k)) := by
    intro k v hv hI
    obtain ⟨u, run, rem, acc, qs, same⟩ := appendBit_run v
    refine ⟨u, 6, run, Nat.le_refl _, (same 4 (by decide) (by decide)).trans hv, ?_⟩
    obtain ⟨inv, qv, hv⟩ := hI
    refine ⟨by simpa [rem, acc, bitsInto] using inv, qs.trans qv, ?_⟩
    intro r h1 h3 h4
    simpa only [write_ne _ _ h4] using (same r h1 h3).trans (hv r h1 h3 h4)
  obtain ⟨u, t, run, cost, _, output, qs, regs⟩ := forUnary_run I step n s hn
    ⟨rfl, rfl, fun _ _ _ _ => rfl⟩
  exact ⟨u, t, run, cost, output, qs, regs⟩

private def readColumn : Code :=
  .write 4 (.copy 2) ⨟ forUnary 4 appendBit ⨟ .write 3 (.cons false 3)

private def columnsInto (d : Nat) : Nat → Word → Word → Word × Word
  | 0, bs, acc => (bs, acc)
  | n+1, bs, acc =>
    let col := bitsInto d bs acc
    columnsInto d n col.1 (false :: col.2)

private theorem readColumn_run (s : State) (d : Nat) (hd : s.reg 2 = ones d) :
    ∃ u t, Run emptyLanguage readColumn s u t 0 ∧ t ≤ 9*d + 5 ∧
      (u.reg 1, u.reg 3) = ((bitsInto d (s.reg 1) (s.reg 3)).1,
          false :: (bitsInto d (s.reg 1) (s.reg 3)).2) ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → u.reg r = s.reg r := by
  let v := s.write 4 (ones d)
  have setClock : Run emptyLanguage (.write 4 (.copy 2)) s v 1 0 := by
    simpa [v, hd, Expr.eval] using stepWrite s 4 (.copy 2)
  obtain ⟨w, t, run, cost, value, qs, other⟩ := consumeBits_run v d (by simp [v])
  let u := w.write 3 (false :: w.reg 3)
  have endCol : Run emptyLanguage (.write 3 (.cons false 3)) w u 1 0 := .write
  refine ⟨u, 1 + (t + 1 + 1) + 1, .seq setClock (.seq run endCol), by omega, ?_, qs, ?_⟩
  · simpa [u, v] using congrArg (fun p : Word × Word => (p.1, false :: p.2)) value
  · intro r h1 h3 h4
    simpa [u, v, h3, h4] using other r h1 h3 h4

private theorem consumeColumns_run (s : State) (d n : Nat) (hd : s.reg 2 = ones d)
    (hn : s.reg 5 = ones n) :
    ∃ u t, Run emptyLanguage (forUnary 5 readColumn) s u t 0 ∧ t ≤ (9*d+8)*n+1 ∧
      (u.reg 1, u.reg 3) = columnsInto d n (s.reg 1) (s.reg 3) ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → u.reg r = s.reg r := by
  let I (k : Nat) (v : State) :=
    columnsInto d k (v.reg 1) (v.reg 3) = columnsInto d n (s.reg 1) (s.reg 3) ∧
    v.reg 2 = ones d ∧ v.queries = s.queries ∧
    ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → v.reg r = s.reg r
  have step : ∀ k v, v.reg 5 = ones (k + 1) → I (k + 1) v →
      ∃ u t, Run emptyLanguage readColumn v u t 0 ∧ t ≤ 9*d+5 ∧ u.reg 5 = ones (k + 1) ∧
        I k (u.write 5 (ones k)) := by
    intro k v hv hI
    obtain ⟨inv, hvd, qv, frame⟩ := hI
    obtain ⟨u, t, run, cost, value, qs, same⟩ := readColumn_run v d hvd
    refine ⟨u, t, run, cost, (same 5 (by decide) (by decide) (by decide)).trans hv, ?_⟩
    refine ⟨?_, (same 2 (by decide) (by decide) (by decide)).trans hvd, qs.trans qv, ?_⟩
    · change columnsInto d k (u.reg 1) (u.reg 3) = _
      have h₁ := congrArg Prod.fst value
      have h₃ := congrArg Prod.snd value
      simp only at h₁ h₃
      rw [h₁, h₃]
      exact inv
    · intro r h1 h3 h4 h5
      simpa only [write_ne _ _ h5] using (same r h1 h3 h4).trans (frame r h1 h3 h4 h5)
  obtain ⟨u, t, run, cost, _, output, _, qs, regs⟩ := forUnary_run I step n s hn
    ⟨rfl, hd, rfl, fun _ _ _ _ _ => rfl⟩
  exact ⟨u, t, run, cost, output, qs, regs⟩

private def readBlock : Code :=
  .write 6 (.copy 1) ⨟ .write 1 (.tail 1) ⨟ .write 3 .empty ⨟ .write 5 (.copy 2) ⨟
    forUnary 5 readColumn

private theorem readBlock_run (s : State) (d : Nat) (hd : s.reg 2 = ones d) :
    ∃ u t, Run emptyLanguage readBlock s u t 0 ∧ t ≤ (9*d+8)*d+9 ∧
      (u.reg 1, u.reg 3) = columnsInto d d (s.reg 1).tail [] ∧ u.reg 6 = s.reg 1 ∧
      u.queries = s.queries ∧ ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 →
        u.reg r = s.reg r := by
  let a := s.write 6 (s.reg 1)
  let b := a.write 1 (s.reg 1).tail
  let c := b.write 3 []
  let v := c.write 5 (ones d)
  have first : Run emptyLanguage (.write 6 (.copy 1)) s a 1 0 := .write
  have pop : Run emptyLanguage (.write 1 (.tail 1)) a b 1 0 := by
    simpa [a, b, Expr.eval] using stepWrite a 1 (.tail 1)
  have clear : Run emptyLanguage (.write 3 .empty) b c 1 0 := .write
  have init : Run emptyLanguage (.write 5 (.copy 2)) c v 1 0 := by
    simpa [a, b, c, v, hd, Expr.eval] using stepWrite c 5 (.copy 2)
  obtain ⟨u,t,run,cost,value,queue,regs⟩ := consumeColumns_run v d d
    (by simp [v,c,b,a,hd]) (by simp [v])
  refine ⟨u, _, .seq first (.seq pop (.seq clear (.seq init run))), ?_,
    by simpa [v,c,b,a] using value, ?_, queue, ?_⟩
  · omega
  · rw [regs 6 (by decide) (by decide) (by decide) (by decide)]
    simp [v,c,b,a]
  · intro r h1 h3 h4 h5 h6
    rw [regs r h1 h3 h4 h5]
    simp [v,c,b,a,h1,h3,h5,h6]

private def stepRank : Code :=
  readBlock ⨟ .branch (.head 6) (.write 7 (.copy 3)) .skip

private def throughRanks (d : Nat) : Nat → Word → Word → Word × Word
  | 0, bs, acc => (bs, acc)
  | n+1, bs, acc =>
    let next := columnsInto d d bs.tail []
    throughRanks d n next.1 (if bs.head?.getD false then next.2 else acc)

private theorem stepRank_run (s : State) (d : Nat) (hd : s.reg 2 = ones d) :
    ∃ u t, Run emptyLanguage stepRank s u t 0 ∧ t ≤ (9*d+8)*d+12 ∧
      (u.reg 1, u.reg 7) = throughRanks d 1 (s.reg 1) (s.reg 7) ∧
      u.queries = s.queries ∧ ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 →
        u.reg r = s.reg r := by
  obtain ⟨v,t,run,cost,value,original,queue,regs⟩ := readBlock_run s d hd
  let u := if (s.reg 1).head?.getD false then v.write 7 (v.reg 3) else v
  have h₁ := congrArg Prod.fst value
  have h₃ := congrArg Prod.snd value
  have h₇ := regs 7 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only at h₁ h₃
  have changeBest : Run emptyLanguage (.branch (.head 6) (.write 7 (.copy 3)) .skip) v u 2 0 := by
    have readFlag : (Test.head 6).eval v = (s.reg 1).head?.getD false := by simp [Test.eval, original]
    cases h : (s.reg 1).head?.getD false
    · simpa [u,h] using runFalse (a := .write 7 (.copy 3)) (readFlag.trans h) (Run.skip (A := emptyLanguage) (s := v))
    · simpa [u,h,Expr.eval] using runTrue (b := .skip) (readFlag.trans h) (stepWrite v 7 (.copy 3))
  refine ⟨u,t+2+1,.seq run changeBest,by omega,?_,?_,?_⟩
  · cases h : (s.reg 1).head?.getD false <;> simp [throughRanks,h,u,h₁,h₃,h₇]
  · cases h : (s.reg 1).head?.getD false <;> simp [h,u,queue]
  · intro r h1 h3 h4 h5 h6 h7
    cases h : (s.reg 1).head?.getD false <;> simp [h,u,h7,regs r h1 h3 h4 h5 h6]

private theorem consumeRanks_run (s : State) (d n : Nat) (hd : s.reg 2 = ones d)
    (hn : s.reg 8 = ones n) :
    ∃ u t, Run emptyLanguage (forUnary 8 stepRank) s u t 0 ∧
      t ≤ ((9*d+8)*d+15)*n+1 ∧
      (u.reg 1, u.reg 7) = throughRanks d n (s.reg 1) (s.reg 7) := by
  let I (k : Nat) (v : State) :=
    throughRanks d k (v.reg 1) (v.reg 7) = throughRanks d n (s.reg 1) (s.reg 7) ∧
      v.reg 2 = ones d
  have step : ∀ k v, v.reg 8 = ones (k + 1) → I (k + 1) v →
      ∃ u t, Run emptyLanguage stepRank v u t 0 ∧ t ≤ (9*d+8)*d+12 ∧ u.reg 8 = ones (k + 1) ∧
        I k (u.write 8 (ones k)) := by
    intro k v hv hI
    obtain ⟨inv, dv⟩ := hI
    obtain ⟨u,t,run,cost,value,_,same⟩ := stepRank_run v d dv
    refine ⟨u,t,run,cost,(same 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hv,?_,
      (same 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans dv⟩
    have h₁ := congrArg Prod.fst value
    have h₇ := congrArg Prod.snd value
    change throughRanks d k (u.reg 1) (u.reg 7) = _
    simp only at h₁ h₇
    rw [h₁,h₇]
    exact inv
  obtain ⟨u,t,run,cost,_,spec,_⟩ := forUnary_run I step n s hn ⟨rfl,hd⟩
  exact ⟨u,t,run,cost,spec⟩

private theorem put_append (w tail : Word) : put w tail = put w [] ++ tail := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [put, ih]

private theorem bitsInto_word (w tail acc : Word) :
    ((bitsInto w.length (w ++ tail) acc).1, false :: (bitsInto w.length (w ++ tail) acc).2) =
      (tail, (put w []).reverse ++ acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons b w ih =>
    simpa [bitsInto, put, List.reverse_cons, List.append_assoc] using ih (b :: true :: acc)

private theorem columnsInto_words {d : Nat} (ws : List Word) (tail acc : Word)
    (hlen : ∀ w ∈ ws, w.length = d) :
    columnsInto d ws.length (ws.flatten ++ tail) acc = (tail, (pack ws).reverse ++ acc) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    have h := bitsInto_word w (ws.flatten ++ tail) acc
    rw [hlen w List.mem_cons_self] at h
    simp only [List.length_cons, columnsInto, List.flatten_cons, List.append_assoc]
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only at h₁ h₂
    rw [h₁, h₂, ih _ (fun v hv => hlen v (List.mem_cons_of_mem _ hv))]
    simp only [QueryEncoding.pack, put_append w (QueryEncoding.pack ws), List.reverse_append, List.append_assoc]

private theorem mapFinRange {α : Type} {d : Nat} (f : Fin d → α) :
    (List.finRange d).map f = List.ofFn f := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [List.getElem_finRange]

private theorem mapOfFn {α β : Type} {d : Nat} (f : Fin d → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (fun i => g (f i)) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

private def payload (truth : Query d → Bool) (r : Fin (d+1)) : Word :=
  (matrixWord (fun i j => truth (.bit r i j))).reverse

private theorem rankBlock (d : Nat) (truth : Query d → Bool) (r : Fin (d+1))
    (tail : Word) :
    (columnsInto d d (((block d r).map truth ++ tail).tail) []) = (tail, payload truth r) := by
  let ws : List Word := List.ofFn (fun (i : Fin d) => List.ofFn (fun (j : Fin d) => truth (.bit r i j)))
  have fold : ((List.finRange d).flatMap (fun i =>
      (List.finRange d).map (fun j => Query.bit r i j))).map truth = ws.flatten := by
    simp [ws, List.flatMap, List.map_flatten, List.map_map, mapFinRange, mapOfFn, Function.comp_def]
  have hl : ∀ w ∈ ws, w.length = d := by
    intro w hw
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hw
    rw [← hi]
    exact List.length_ofFn
  have hw : ws.length = d := List.length_ofFn
  have h := columnsInto_words ws tail [] hl
  rw [hw, List.append_nil] at h
  change columnsInto d d (((block d r).map truth ++ tail).tail) [] =
    (tail, (pack ws).reverse)
  simpa [block, fold] using h

private def newest (truth : Query d → Bool) (acc : Word) (r : Fin (d+1)) : Word :=
    if truth (.rank r) then payload truth r else acc

private def wireRanks (truth : Query d → Bool) (rs : List (Fin (d+1))) : Word :=
  (rs.flatMap (block d)).map truth

private theorem throughRanks_wire (d : Nat) (truth : Query d → Bool)
    (rs : List (Fin (d+1))) (tail acc : Word) :
    throughRanks d rs.length (wireRanks truth rs ++ tail) acc =
      (tail, rs.foldl (newest truth) acc) := by
  induction rs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    have unfoldWire : wireRanks truth (r :: rs) ++ tail =
        (block d r).map truth ++ (wireRanks truth rs ++ tail) := by
      simp [wireRanks, List.append_assoc]
    rw [List.length_cons, unfoldWire, throughRanks, rankBlock]
    have hflag : ((block d r).map truth ++ (wireRanks truth rs ++ tail)).head?.getD false =
        truth (.rank r) := by simp [block]
    rw [hflag]
    exact ih _

private theorem foldl_best (m : Nat) (flags : Fin (m+1) → Bool) (rows : Fin (m+1) → Word) :
    (List.finRange (m+1)).foldl (fun acc r => if flags r then rows r else acc) (rows 0) =
      rows (best m flags) := by
  induction m with
  | zero =>
    simp [List.finRange_succ, best]
  | succ m ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    change (if flags (Fin.last (m+1)) then rows (Fin.last (m+1)) else
      (List.finRange (m+1)).foldl
        (fun acc (r : Fin (m+1)) => if flags r.castSucc then rows r.castSucc else acc) (rows 0)) =
      rows (best (m+1) flags)
    have h := ih (fun r => flags r.castSucc) (fun r => rows r.castSucc)
    cases he : flags (Fin.last (m+1))
    · simpa [best, he] using h
    · simp [best, he]

private def assembled (d : Nat) (replies : Word) : Word :=
  let first := columnsInto d d replies.tail []
  (throughRanks d d first.1 first.2).2.reverse

private theorem assembled_table (d : Nat) (truth : Query d → Bool) :
    assembled d ((batch d).map truth) = matrixWord (recover truth) := by
  let rs := (List.finRange (d+1)).tail
  have decomp : (batch d).map truth = (block d 0).map truth ++ wireRanks truth rs := by
    simp [batch, wireRanks, rs, List.finRange_succ]
  have hfirst := rankBlock d truth 0 (wireRanks truth rs)
  have hr : rs.length = d := by simp [rs]
  rw [assembled, decomp, hfirst]
  dsimp only
  have ht := throughRanks_wire d truth rs [] (payload truth 0)
  rw [hr, List.append_nil] at ht
  rw [ht]
  simp only
  have foldEq : rs.foldl (newest truth) (payload truth 0) = payload truth
      (best d (rankAnswers truth)) := by
    have h := foldl_best d (rankAnswers truth) (payload truth)
    have h' : (List.finRange (d+1)).foldl (newest truth) (payload truth 0) =
        rs.foldl (newest truth) (payload truth 0) := by
      simp [List.finRange_succ, newest, rs]
    rw [← h']
    exact h
  rw [foldEq]
  simp [payload, recover]

private theorem assembled_spec (s : Word) (truth : Word → Bool) :
    assembled (readRequest s).width.succ ((questions s).map truth) =
      assemble s ((questions s).map truth) := by
  let d := (readRequest s).width.succ
  let flags (q : Query d) := truth (questionWord s q)
  have hz : (questions s).map truth = (batch d).map flags := by simp [questions, d, flags, Function.comp_def]
  rw [hz]
  have lookup : readAnswer (List.map (fun q => (q, flags q)) (batch d)) = flags :=
    funext (fun q => readAnswer_map _ _ _ (mem_batch q))
  have zipped (qs : List (Query d)) :
      qs.zip (qs.map flags) = qs.map (fun q => (q, flags q)) := by
    induction qs <;> simp [*]
  rw [assembled_table]
  change matrixWord (recover flags) = matrixWord (recoverBatch ((batch d).zip ((batch d).map flags)))
  rw [zipped, recoverBatch, lookup]

def computeDimension : Code :=
  .write 9 (.copy 0) ⨟ FieldCode.takeReverse 9 10 ⨟ FieldCode.takeReverse 9 10 ⨟
    set 2 true ⨟ normalize 10 2 11

theorem computeDimension_run (s : State) :
    ∃ u t, Run emptyLanguage computeDimension s u t 0 ∧ t ≤ 30*(s.reg 0).length+30 ∧
      u.reg 2 = ones (readRequest (s.reg 0)).width.succ ∧ u.queries = s.queries ∧
      ∀ r, r ≠ 2 → r ≠ 9 → r ≠ 10 → r ≠ 11 → u.reg r = s.reg r := by
  let a := s.write 9 (s.reg 0)
  have save : Run emptyLanguage (.write 9 (.copy 0)) s a 1 0 := .write
  obtain ⟨b,t₁,run₁,c₁,tail₁,_,q₁,o₁⟩ := FieldCode.takeReverse_run a (src := 9) (dst := 10) (by decide)
  obtain ⟨c,t₂,run₂,c₂,_,width,q₂,o₂⟩ := FieldCode.takeReverse_run b (src := 9) (dst := 10) (by decide)
  let start := c.write 2 [true]
  obtain ⟨u,t₃,run₃,c₃,dim,q₃,o₃⟩ := normalize_run (src := 10) (dst := 2) (flag := 11)
    (by decide) (by decide) (by decide) start
  refine ⟨u, _, .seq save (.seq run₁ (.seq run₂ (.seq (runSet c 2 true) run₃))),
    ?_, ?_, q₃.trans (q₂.trans (q₁.trans rfl)), ?_⟩
  · have lim₁ := QueryEncoding.take_lengths (s.reg 0)
    have lim₂ := QueryEncoding.take_data_le ((take (s.reg 0)).2)
    simp [a] at c₁ tail₁
    rw [tail₁] at c₂ width
    simp [start,width] at c₃
    omega
  · have e : (readRequest (s.reg 0)).width = (take ((take (s.reg 0)).2)).1.length := by
      unfold readRequest
      cases take (s.reg 0)
      rfl
    rw [e]
    simp only [a, write_same] at tail₁
    rw [tail₁] at width
    simp only [start, write_ne _ _ (show (10:Nat) ≠ 2 by decide), write_same,
      width, List.length_reverse] at dim
    have app (n : Nat) : ones n ++ [true] = ones n.succ := by
      change ones n ++ ones 1 = ones (n + 1)
      exact List.replicate_append_replicate
    rwa [app] at dim
  · intro r h2 h9 h10 h11
    rw [o₃ r h10 h2 h11, write_ne _ _ h2, o₂ r h9 h10, o₁ r h9 h10, write_ne _ _ h9]

/-- Decode the selected matrix from a single sequence of answers. Rank zero
is the fallback and each later feasible rank replaces the saved matrix. -/
def assembler : Code :=
  computeDimension ⨟ readBlock ⨟ .write 7 (.copy 3) ⨟ .write 8 (.copy 2) ⨟
    forUnary 8 stepRank ⨟ FieldCode.reverse 7 0 11

theorem assembler_local : assembler.allowed false false false := by
  repeat' constructor

theorem assembler_run (s : Word) (answer : Word → Bool) :
    ∃ out t, Run emptyLanguage assembler (State.input s ((questions s).map answer)) out t 0 ∧
      t ≤ 200 * (s.length + 1)^3 ∧ out.output = assemble s ((questions s).map answer) := by
  let replies := (questions s).map answer
  let initial := State.input s replies
  let d := (readRequest s).width.succ
  obtain ⟨a,t₁,run₁,c₁,dim,_,frame⟩ := computeDimension_run initial
  change a.reg 2 = ones d at dim
  have h₁ : a.reg 1 = replies := frame 1 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨b,t₂,run₂,c₂,blk,_,_,other⟩ := readBlock_run a d dim
  let selected := b.write 7 (b.reg 3)
  let begin := selected.write 8 (ones d)
  have save : Run emptyLanguage (.write 7 (.copy 3)) b selected 1 0 := .write
  have bd : b.reg 2 = ones d := (other 2 (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans dim
  have start : Run emptyLanguage (.write 8 (.copy 2)) selected begin 1 0 := by
    simpa [selected, begin, bd, Expr.eval] using stepWrite selected 8 (.copy 2)
  obtain ⟨c,t₃,run₃,c₃,rest⟩ := consumeRanks_run begin d d
    (by simp [begin, selected, bd]) (by simp [begin])
  obtain ⟨out,run₄,_,result,_,_⟩ := FieldCode.reverse_run c (src := 7) (dst := 0) (flag := 11)
    (by decide) (by decide) (by decide)
  have hval : (c.reg 7).reverse = assemble s replies := by
    change (c.reg 7).reverse = _
    have h₃ := congrArg Prod.snd rest
    have h₁' := congrArg Prod.fst blk
    have h₃' := congrArg Prod.snd blk
    simp only at h₃ h₁' h₃'
    rw [h₁] at h₁' h₃'
    rw [h₃]
    simpa [begin, selected, h₁', h₃', assembled, replies, d] using assembled_spec s answer
  have t₄ : (c.reg 7).length = 2*(d*d)+d := by
    rw [← List.length_reverse (as := c.reg 7), hval]
    exact QueryEncoding.matrixWord_length _
  refine ⟨out, _, .seq run₁ (.seq run₂ (.seq save (.seq start (.seq run₃ run₄)))),
    ?_, result.trans hval⟩
  change t₁ ≤ 30*s.length+30 at c₁
  let N := s.length + 1
  have hD : d ≤ N := Nat.succ_le_succ (width_le s)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have twoSquares : d*d ≤ N*N := Nat.mul_le_mul hD hD
  have sqCube : N*N ≤ N*N*N :=
    calc
      N*N = (N*N)*1 := (Nat.mul_one _).symm
      _ ≤ N*N*N := Nat.mul_le_mul_left _ hN
  have singleSquare : N ≤ N*N :=
    calc
      N = N*1 := (Nat.mul_one _).symm
      _ ≤ N*N := Nat.mul_le_mul_left _ hN
  have hd2 := Nat.le_trans twoSquares sqCube
  have hd1 := Nat.le_trans hD (Nat.le_trans singleSquare sqCube)
  have h3 : d*d*d ≤ N*N*N := Nat.mul_le_mul twoSquares hD
  have n3 := Nat.le_trans singleSquare sqCube
  have const := Nat.le_trans hN n3
  rw [t₄]
  change _ ≤ 200*N^3
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
    Nat.mul_one] at c₂ c₃ ⊢
  simp only [Nat.mul_assoc] at sqCube h3 hd2 hd1 n3 const
  have c₁' : t₁ ≤ 30*N := by dsimp [N]; omega
  omega

end HullBatchPrograms
