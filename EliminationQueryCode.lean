module

public import EliminationCode
public import HullBatchMachine

/-! The arithmetic end of a hull-query verifier. The query header, packed
matrix and checker flag use the same registers as the certificate loader. -/

@[expose] public section

namespace EliminationQueryCode

open ComplexityModel HullRecovery HullDecoder
open WordCode (Preserves preserves_write)
open HullBatchMachine (ones ones_succ forUnary)

private theorem wr (s : State) (r : Nat) (e : Expr) :
    Run emptyLanguage (.write r e) s (s.write r (e.eval s)) 1 0 := .write

private theorem yes {s t : State} {test : Test} {a b : Code} {k : Nat}
    (h : test.eval s = true) (run : Run emptyLanguage a s t k 0) :
    Run emptyLanguage (.branch test a b) s t (k + 1) 0 := .branch h run

private theorem no {s t : State} {test : Test} {a b : Code} {k : Nat}
    (h : test.eval s = false) (run : Run emptyLanguage b s t k 0) :
    Run emptyLanguage (.branch test a b) s t (k + 1) 0 := .branch h run

private def iter (f : Word → Word) : Nat → Word → Word
  | 0, w => w
  | k + 1, w => iter f k (f w)

private theorem iter_tail (n : Nat) (w : Word) :
    iter List.tail n w = w.drop n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [iter, ih]
    cases w <;> simp [List.drop_succ_cons]

private theorem iter_zeroes (n : Nat) (w : Word) :
    iter (false :: ·) n w = List.replicate n false ++ w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [iter, ih]
    have e : List.replicate (n + 1) false = List.replicate n false ++ [false] :=
      (List.replicate_append_replicate (n := n) (m := 1) (a := false)).symm
    rw [e, List.append_assoc]
    rfl

private theorem repeat_run {ctr dst : Nat} (h : dst ≠ ctr)
    (op : Expr) (f : Word → Word) (operation : ∀ s, op.eval s = f (s.reg dst))
    (k : Nat) (s : State) (clock : s.reg ctr = ones k) :
    ∃ out, Run emptyLanguage (forUnary ctr (.write dst op)) s out (4 * k + 1) 0 ∧
      out.reg dst = iter f k (s.reg dst) ∧ Preserves s out [ctr, dst] := by
  induction k generalizing s with
  | zero =>
    exact ⟨s, .loopFalse (by simp [Test.eval, clock]), rfl, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    let v := s.write dst (f (s.reg dst))
    let next := v.write ctr (ones k)
    have write : Run emptyLanguage (.write dst op) s v 1 0 := by
      simpa only [v, operation] using wr s dst op
    have debit : Run emptyLanguage (.write ctr (.tail ctr)) v next 1 0 := by
      simpa [v, next, State.write, Expr.eval, Ne.symm h, clock, ones_succ] using wr v ctr (.tail ctr)
    obtain ⟨out, later, result, frame⟩ := ih next (by simp [next, State.write])
    refine ⟨out, ?_, ?_, ?_⟩
    · have t : 4 * (k + 1) + 1 = 1 + 1 + 1 + (4 * k + 1) + 1 := by omega
      rw [t]
      exact .loopTrue (by simp [Test.eval, clock, ones_succ]) (.seq write debit) later
    · simpa [next, v, State.write, h, iter] using result
    · have a : Preserves s v [ctr, dst] := (preserves_write ..).mono (by simp)
      have b : Preserves v next [ctr, dst] := (preserves_write ..).mono (by simp)
      exact a.trans (b.trans frame)

def drop (ctr dst : Nat) : Code := forUnary ctr (.write dst (.tail dst))

theorem drop_run (s : State) {ctr dst n : Nat} (h : dst ≠ ctr) (clock : s.reg ctr = ones n) :
    ∃ out, Run emptyLanguage (drop ctr dst) s out (4 * n + 1) 0 ∧
      out.reg dst = (s.reg dst).drop n ∧ Preserves s out [ctr, dst] := by
  simpa only [drop, iter_tail] using repeat_run h (.tail dst) List.tail (fun _ => rfl) n s clock

private def zeroes (ctr dst : Nat) : Code := forUnary ctr (.write dst (.cons false dst))

private theorem zeroes_run (s : State) {ctr dst n : Nat} (h : dst ≠ ctr) (clock : s.reg ctr = ones n) :
    ∃ out, Run emptyLanguage (zeroes ctr dst) s out (4 * n + 1) 0 ∧
      out.reg dst = List.replicate n false ++ s.reg dst ∧ Preserves s out [ctr, dst] := by
  simpa only [zeroes, iter_zeroes] using repeat_run h (.cons false dst) (false :: ·)
    (fun _ => rfl) n s clock

private theorem word_zero (n : Nat) : word (zero n) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have eq : zero (n + 1) = cons false (zero n) := by funext i; cases i using Fin.cases <;> rfl
    rw [eq, word_cons, ih, List.replicate_succ]

private theorem word_unit (i : Fin n) :
    word (unit i) = List.replicate i.val false ++ true :: List.replicate (n - i.val - 1) false := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rw [unit_zero, word_cons, word_zero]; simp
    | succ i =>
      have h : n + 1 - i.succ.val - 1 = n - i.val - 1 := by simp
      rw [unit_succ, word_cons, ih, h]
      simp [List.replicate_succ]

private def prepareBit : Code :=
  .write 64 (.copy 42) ⨟ .write 65 (.copy 6) ⨟ drop 65 64 ⨟ .write 64 (.tail 64) ⨟
    .write 41 .empty ⨟ zeroes 64 41 ⨟ .write 41 (.cons true 41) ⨟
      .write 65 (.copy 6) ⨟ zeroes 65 41

private def initSlots : List Nat := [41, 64, 65]

private theorem prepareBit_run (s : State) (i : Fin n)
    (width : s.reg 42 = ones n) (column : s.reg 6 = ones i.val) :
    ∃ out t, Run emptyLanguage prepareBit s out t 0 ∧ t ≤ 8 * n + 17 ∧
      out.reg 41 = word (unit i) ∧ Preserves s out initSlots := by
  let a := s.write 64 (ones n)
  let b := a.write 65 (ones i.val)
  have ar : Run emptyLanguage (.write 64 (.copy 42)) s a 1 0 := by
    simpa [a, Expr.eval, width] using wr s 64 (.copy 42)
  have br : Run emptyLanguage (.write 65 (.copy 6)) a b 1 0 := by
    simpa [b, a, State.write, Expr.eval, column] using wr a 65 (.copy 6)
  obtain ⟨c, cr, rest, cframe⟩ :=
    drop_run b (ctr := 65) (dst := 64) (n := i.val) (by decide) (by simp [b, State.write])
  have restLen : c.reg 64 = ones (n - i.val) := by
    simpa [a, b, State.write, ones, List.drop_replicate] using rest
  let d := c.write 64 (ones (n - i.val - 1))
  have trim : Run emptyLanguage (.write 64 (.tail 64)) c d 1 0 := by
    have h : n - i.val = (n - i.val - 1) + 1 := by have := i.isLt; omega
    have restLen' : c.reg 64 = true :: ones (n - i.val - 1) :=
      restLen.trans ((congrArg ones h).trans (ones_succ _))
    simpa only [d, Expr.eval, restLen', List.tail_cons] using wr c 64 (.tail 64)
  let e := d.write 41 []
  have clear : Run emptyLanguage (.write 41 .empty) d e 1 0 := .write
  obtain ⟨f, fr, zero, fframe⟩ := zeroes_run e (ctr := 64) (dst := 41) (n := n - i.val - 1)
    (by decide) (by simp [e, d, State.write])
  let g := f.write 41 (true :: f.reg 41)
  have bit : Run emptyLanguage (.write 41 (.cons true 41)) f g 1 0 := .write
  let h := g.write 65 (ones i.val)
  have colAgain : g.reg 6 = ones i.val := by
    rw [show g.reg 6 = f.reg 6 from rfl, fframe.2 6 (by decide)]
    simp [e, d, State.write, cframe.2 6 (by decide), b, a, column]
  have reset : Run emptyLanguage (.write 65 (.copy 6)) g h 1 0 := by
    simpa [h, Expr.eval, colAgain] using wr g 65 (.copy 6)
  obtain ⟨out, final, vector, outframe⟩ :=
    zeroes_run h (ctr := 65) (dst := 41) (n := i.val) (by decide) (by simp [h, State.write])
  refine ⟨out, _, .seq ar (.seq br (.seq cr (.seq trim (.seq clear (.seq fr (.seq bit (.seq reset final))))))),
    by have := i.isLt; omega, ?_, ?_⟩
  · simp [word_unit, vector, h, g, e, State.write, zero]
  · have fa : Preserves s a initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fb : Preserves a b initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fc := cframe.mono (more := initSlots) (by simp [initSlots, List.cons_subset])
    have fd : Preserves c d initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fe : Preserves d e initSlots := (preserves_write ..).mono (by simp [initSlots])
    have ff := fframe.mono (more := initSlots) (by simp [initSlots, List.cons_subset])
    have fg : Preserves f g initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fh : Preserves g h initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fout := outframe.mono (more := initSlots) (by simp [initSlots, List.cons_subset])
    exact fa.trans (fb.trans (fc.trans (fd.trans (fe.trans (ff.trans (fg.trans (fh.trans fout)))))))

private def prepareZero : Code := .write 64 (.copy 42) ⨟ .write 41 .empty ⨟ zeroes 64 41

private theorem prepareZero_run (s : State) (width : s.reg 42 = ones n) :
    ∃ out, Run emptyLanguage prepareZero s out (4 * n + 5) 0 ∧
      out.reg 41 = word (zero n) ∧ Preserves s out initSlots := by
  let a := s.write 64 (ones n)
  let b := a.write 41 []
  have ar : Run emptyLanguage (.write 64 (.copy 42)) s a 1 0 := by
    simpa [a, Expr.eval, width] using wr s 64 (.copy 42)
  have br : Run emptyLanguage (.write 41 .empty) a b 1 0 := .write
  obtain ⟨out, run, vector, frame⟩ := zeroes_run b (ctr := 64) (dst := 41) (n := n)
    (by decide) (by simp [a, b, State.write])
  have t : 4 * n + 5 = 1 + (1 + (4 * n + 1) + 1) + 1 := by omega
  refine ⟨out, by rw [t]; exact .seq ar (.seq br run), ?_, ?_⟩
  · simpa [word_zero, b, State.write] using vector
  · have fa : Preserves s a initSlots := (preserves_write ..).mono (by simp [initSlots])
    have fb : Preserves a b initSlots := (preserves_write ..).mono (by simp [initSlots])
    exact fa.trans (fb.trans (frame.mono (by simp [initSlots, List.cons_subset])))


private def prepare : Code :=
  .write 42 (.cons true 4) ⨟ .branch (.head 8) prepareBit prepareZero

private def vectorSlots : List Nat := [41, 42, 64, 65]

private theorem prepare_run (s : State) (i : Fin (m + 1)) (isBit : Bool)
    (width : s.reg 4 = ones m) (col : isBit = true → s.reg 6 = ones i.val)
    (mode : (Test.head 8).eval s = isBit) :
    ∃ out t, Run emptyLanguage prepare s out t 0 ∧ t ≤ 8 * (m + 1) + 20 ∧
      out.reg 41 = word (if isBit then unit i else zero (m + 1)) ∧
      out.reg 42 = ones (m + 1) ∧ Preserves s out vectorSlots := by
  let a := s.write 42 (ones (m + 1))
  have base : Run emptyLanguage (.write 42 (.cons true 4)) s a 1 0 := by
    simpa [a, Expr.eval, width, ones_succ] using wr s 42 (.cons true 4)
  have h : a.reg 42 = ones (m + 1) := by simp [a, State.write]
  have bm : (Test.head 8).eval a = isBit := by simpa [a, Test.eval, State.write] using mode
  have fr : Preserves s a vectorSlots := (preserves_write ..).mono (by simp [vectorSlots])
  cases isBit
  · obtain ⟨out, run, vector, frame⟩ := prepareZero_run a h
    exact ⟨out, _, .seq base (no bm run), by omega, vector,
      (frame.2 42 (by decide)).trans h, fr.trans (frame.mono (by simp [vectorSlots, initSlots, List.cons_subset]))⟩
  · have ci : a.reg 6 = ones i.val := by simpa [a, State.write] using col rfl
    obtain ⟨out, t, run, time, vector, frame⟩ := prepareBit_run a i h ci
    exact ⟨out, _, .seq base (yes bm run), by omega, vector,
      (frame.2 42 (by decide)).trans h, fr.trans (frame.mono (by simp [vectorSlots, initSlots, List.cons_subset]))⟩

private def readBit : Code :=
  .write 65 (.copy 7) ⨟ drop 65 44 ⨟ .write 0 .empty ⨟ WordCode.prependHead 44 0

private theorem readBit_run (s : State) (j : Fin n) (x : Bits n)
    (row : s.reg 7 = ones j.val) (vector : s.reg 44 = word x) :
    ∃ out, Run emptyLanguage readBit s out (4 * j.val + 8) 0 ∧ out.output = [x j] := by
  let a := s.write 65 (ones j.val)
  have copy : Run emptyLanguage (.write 65 (.copy 7)) s a 1 0 := by
    simpa [a, Expr.eval, row] using wr s 65 (.copy 7)
  obtain ⟨b, cut, data, _⟩ := drop_run a (ctr := 65) (dst := 44) (n := j.val)
    (by decide) (by simp [a, State.write])
  let c := b.write 0 []
  have clear : Run emptyLanguage (.write 0 .empty) b c 1 0 := .write
  let out := c.write 0 ((c.reg 44).headD false :: c.reg 0)
  have finish : Run emptyLanguage (WordCode.prependHead 44 0) c out 2 0 :=
    WordCode.prependHead_run emptyLanguage c 44 0
  have t : 4 * j.val + 8 = 1 + (4 * j.val + 1 + (1 + 2 + 1) + 1) + 1 := by omega
  have d : c.reg 44 = (word x).drop j.val := by simpa [c, a, State.write, vector] using data
  have bit : ((word x).drop j.val).headD false = x j := by
    have h : j.val < (word x).length := by simp
    rw [List.drop_eq_getElem_cons h]
    simp [word]
  refine ⟨out, by rw [t]; exact .seq copy (.seq cut (.seq clear finish)), ?_⟩
  change (c.reg 44).headD false :: c.reg 0 = [x j]
  rw [d, bit]
  rfl

private def project : Code := .branch (.head 8) readBit (WordCode.setBit 0 true)

private theorem project_run (s : State) (j : Fin n) (isBit : Bool) (x : Bits n)
    (mode : (Test.head 8).eval s = isBit) (row : isBit = true → s.reg 7 = ones j.val)
    (hx : s.reg 44 = word x) :
    ∃ out t, Run emptyLanguage project s out t 0 ∧ t ≤ 4 * n + 9 ∧
      out.output = [if isBit then x j else true] := by
  cases isBit
  · exact ⟨s.write 0 [true], 4, no mode (WordCode.setBit_run ..), by omega,
      by simp [State.output, State.write]⟩
  · obtain ⟨out, r, v⟩ := readBit_run s j x (row rfl) hx
    exact ⟨out, _, yes mode r, by have := j.isLt; omega, v⟩

private def checkResult : Code :=
  .write 64 (.copy 43) ⨟ .write 65 (.copy 5) ⨟ drop 64 65 ⨟
    .branch (.empty 65) project (WordCode.setBit 0 false)

private theorem checkResult_run (s : State) {r rank : Nat} (j : Fin n) (isBit : Bool) (x : Bits n)
    (rBound : rank ≤ r) (rankBound : rank ≤ n)
    (requested : s.reg 5 = ones r) (computed : s.reg 43 = ones rank)
    (row : isBit = true → s.reg 7 = ones j.val) (mode : (Test.head 8).eval s = isBit)
    (vector : s.reg 44 = word x) :
    ∃ out t, Run emptyLanguage checkResult s out t 0 ∧ t ≤ 8 * n + 16 ∧
      out.output = [(rank == r) && (if isBit then x j else true)] := by
  let a := s.write 64 (ones rank)
  let b := a.write 65 (ones r)
  have ra : Run emptyLanguage (.write 64 (.copy 43)) s a 1 0 := by
    simpa [a, Expr.eval, computed] using wr s 64 (.copy 43)
  have rb : Run emptyLanguage (.write 65 (.copy 5)) a b 1 0 := by
    simpa [a, b, Expr.eval, State.write, requested] using wr a 65 (.copy 5)
  obtain ⟨c, cut, data, frame⟩ := drop_run b (ctr := 64) (dst := 65) (n := rank)
    (by decide) (by simp [b, a, State.write])
  have d : c.reg 65 = ones (r - rank) := by
    simpa [b, State.write, ones, List.drop_replicate] using data
  have test : (Test.empty 65).eval c = (rank == r) := by
    have eq : r - rank = 0 ↔ rank = r := by omega
    simp [Test.eval, d, ones, eq, Bool.beq_eq_decide_eq]
  by_cases eq : rank = r
  · have cm : (Test.head 8).eval c = isBit := by
      simpa [Test.eval, frame.2 8 (by decide), a, b, State.write] using mode
    have cr : isBit = true → c.reg 7 = ones j.val := by
      intro hb
      simp [frame.2 7 (by decide), a, b, State.write, row hb]
    have cv : c.reg 44 = word x := by
      simp [frame.2 44 (by decide), a, b, State.write, vector]
    obtain ⟨out, t, answer, time, value⟩ := project_run c j isBit x cm cr cv
    refine ⟨out, _, .seq ra (.seq rb (.seq cut (yes ?_ answer))), by omega, ?_⟩
    · simpa [eq] using test
    · simpa [eq] using value
  · refine ⟨c.write 0 [false], _, .seq ra (.seq rb (.seq cut (no ?_ (WordCode.setBit_run ..)))),
      by omega, by simp [State.output, State.write, eq]⟩
    simpa [eq, Bool.beq_eq_decide_eq] using test

/-- Arithmetic verifier on packed lifted rows. A failed earlier certificate
check bypasses elimination entirely. -/
def finish : Code :=
  .branch (.head 33) (prepare ⨟ EliminationCode.eliminate ⨟ checkResult) (WordCode.setBit 0 false)

theorem finish_pure : finish.pure := by
  simp [finish, prepare, prepareBit, prepareZero, EliminationCode.eliminate_pure, checkResult,
    project, readBit, zeroes, drop, forUnary, WordCode.setBit, WordCode.prependHead, Code.allowed]

private theorem total_bound (m rows : Nat) :
    EliminationCode.columnTime (m + 1) rows * (m + 1) + 22 * (m + 1) + 57 ≤
      300 * (m + rows + 1) ^ 4 := by
  let q := m + rows + 1
  have positive : 1 ≤ q := by omega
  have a : m + 1 ≤ q := by omega
  have b : rows ≤ q := by omega
  have q2 : q ≤ q ^ 2 := by
    simpa [Nat.pow_succ] using Nat.mul_le_mul_left q positive
  have q3 : q ^ 2 ≤ q ^ 3 := by
    simpa only [Nat.pow_succ q 2, Nat.mul_one] using Nat.mul_le_mul_left (q ^ 2) positive
  have q4 : q ^ 3 ≤ q ^ 4 := by
    simpa only [Nat.pow_succ q 3, Nat.mul_one] using Nat.mul_le_mul_left (q ^ 3) positive
  have pack : (2 * (m + 1) + 1) * rows ≤ 3 * q ^ 2 := by
    have bound := Nat.mul_le_mul (show 2 * (m + 1) + 1 ≤ 3*q by omega) b
    simpa only [Nat.mul_assoc, Nat.pow_succ q 1, Nat.pow_one] using bound
  have side : 14 * ((2 * (m + 1) + 1) * rows) + 29 * (m + 1) + 71 ≤ 142 * q ^ 2 := by omega
  have bands : (14 * ((2 * (m + 1) + 1) * rows) + 29 * (m + 1) + 71) * rows ≤ 142 * q ^ 3 := by
    simpa only [Nat.mul_assoc, Nat.pow_succ q 2] using Nat.mul_le_mul side b
  have step : EliminationCode.columnTime (m+1) rows ≤ 210 * q ^ 3 := by
    unfold EliminationCode.columnTime
    omega
  have full : EliminationCode.columnTime (m+1) rows * (m+1) ≤ 210 * q ^ 4 := by
    simpa only [Nat.mul_assoc, Nat.pow_succ q 3] using Nat.mul_le_mul step a
  change _ ≤ 300 * q ^ 4
  omega

/-- The result of rank verification and the requested projection bit with a
polynomial bound in the unary dimension and the supplied row count. -/
theorem finish_run (s : State) (xs : List (Bits (m + 1))) (r : Nat) (col row : Fin (m + 1))
    (isBit accepted : Bool) (width : s.reg 4 = ones m) (rankIn : s.reg 5 = ones r)
    (colIn : isBit = true → s.reg 6 = ones col.val)
    (rowIn : isBit = true → s.reg 7 = ones row.val)
    (mode : (Test.head 8).eval s = isBit) (certificate : (Test.head 33).eval s = accepted)
    (matrix : accepted = true → s.reg 40 = EliminationCode.packRows xs)
    (rankBound : rank xs ≤ r) :
    ∃ out time, Run emptyLanguage finish s out time 0 ∧ time ≤ 300 * (m + xs.length + 1) ^ 4 ∧
      out.output = [accepted && (rank xs == r) &&
        (if isBit then normal xs (unit col) row else true)] := by
  cases accepted
  · refine ⟨s.write 0 [false], 4, no certificate (WordCode.setBit_run ..), ?_,
      by simp [State.output, State.write]⟩
    have := total_bound m xs.length
    omega
  · obtain ⟨a, setupTime, setup, setupBound, vec, clock, prepFrame⟩ :=
      prepare_run s col isBit width colIn mode
    let x := if isBit then unit col else zero (m + 1)
    obtain ⟨b, elimTime, gauss, elimBound, ranked, normalized, gaussFrame⟩ :=
      EliminationCode.eliminate_run a xs x ((prepFrame.2 40 (by decide)).trans (matrix rfl)) vec clock
    have rankIn' : b.reg 5 = ones r := by rw [gaussFrame.2 5 (by decide), prepFrame.2 5 (by decide), rankIn]
    have rowIn' : isBit = true → b.reg 7 = ones row.val := by
      intro hb
      rw [gaussFrame.2 7 (by decide), prepFrame.2 7 (by decide), rowIn hb]
    have mode' : (Test.head 8).eval b = isBit := by
      simpa only [Test.eval, gaussFrame.2 8 (by decide), prepFrame.2 8 (by decide)] using mode
    obtain ⟨out, checkTime, readout, checkBound, value⟩ :=
      checkResult_run b row isBit (normal xs x) rankBound (rank_bounds xs).1 rankIn' ranked rowIn' mode' normalized
    refine ⟨out, _, yes certificate (.seq setup (.seq gauss readout)), ?_, ?_⟩
    · have p := total_bound m xs.length
      omega
    · cases isBit <;> simpa [x] using value

end EliminationQueryCode
