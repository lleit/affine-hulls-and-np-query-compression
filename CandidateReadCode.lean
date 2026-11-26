module

public import EliminationQueryCode
public import WidthCode
public import ComplexityModel.ReplayFrameCode

/-! Decode the diagonal of a projected hull matrix into an affine base and
a triangular pivot schedule. Spurious matrices still give shaped schedules.
For a genuine projection, the trace of the canonical normal form makes a
separate Gaussian elimination pass unnecessary. -/

@[expose] public section

namespace CandidateReadCode

open ComplexityModel HullDecoder
open HullRecovery hiding pack
open AffineSearch (Candidate Shaped linearPoints translate translate_self_left Genuine)
open QueryEncoding (put take pack matrixWord)
open HullBatchMachine (ones ones_succ forUnary forUnary_run stepWrite runTrue runFalse)
open WordCode (Preserves preserves_write)

private def slot (w : Word) : Option Word :=
  if w.headD false then none else some w.tail

/-- Read the next `count` columns, dropping `offset` bits from the first
column before reading its diagonal. Missing bits are filled by zeroes. -/
def schedule : Nat → Nat → Word → List (Option Word)
  | 0, _, _ => []
  | k + 1, offset, w =>
    let f := take w
    slot (WidthCode.resize (k + 1) (f.1.drop offset)) :: schedule k (offset + 1) f.2

def base (k : Nat) (w : Word) : Word := (WidthCode.resize (k+1) (take w).1).tail

def present (k : Nat) (w : Word) : Bool := !(WidthCode.resize (k+1) (take w).1).headD false

def pivots (k : Nat) (w : Word) : List (Option Word) := schedule k 1 (take w).2

def decode (k : Nat) (w : Word) : Option Candidate :=
  if present k w then some ⟨base k w, pivots k w⟩ else none

def pivotWord : Option Word → Word
  | none => []
  | some p => true :: p

def packedPivots (ps : List (Option Word)) : Word := pack (ps.reverse.map pivotWord)

theorem base_width (k : Nat) (w : Word) : (base k w).length = k := by
  simp [base, WidthCode.resize, WidthCode.resize_length]

theorem schedule_shape (n i : Nat) (w : Word) : Shaped n (schedule n i w) := by
  induction n generalizing i w with
  | zero => exact .nil
  | succ n ih =>
    unfold schedule slot
    dsimp only
    split
    · exact .free (ih _ _)
    · exact .pivot (by simp [WidthCode.resize, WidthCode.resize_length]) (ih _ _)

theorem decode_shape {k : Nat} {w : Word} {a : Candidate} (h : decode k w = some a) :
    Shaped k a.pivots ∧ a.base.length = k := by
  unfold decode at h
  split at h
  · simp only [Option.some.injEq] at h
    subst a
    exact ⟨schedule_shape _ _ _, base_width _ _⟩
  · contradiction

@[simp] private theorem word_tail (v : Bits (n + 1)) : (word v).tail = word (tail v) := by
  conv => lhs; rw [← cons_head_tail v, word_cons]
  rfl

@[simp] private theorem word_head (v : Bits (n + 1)) : (word v).headD false = head v := by
  conv => lhs; rw [← cons_head_tail v, word_cons]
  rfl

private def minor (M : Matrix (n + 1)) : Matrix n := fun i => tail (M i.succ)

private def diagonal : (n : Nat) → Matrix n → List (Option Word)
  | 0, _ => []
  | k + 1, M => slot (word (M 0)) :: diagonal k (minor M)

private theorem offset_pack (n i : Nat) (data : List Word) :
    schedule n (i+1) (pack data) = schedule n i (pack (data.map List.tail)) := by
  induction n generalizing i data with
  | zero => rfl
  | succ n ih =>
    cases data with
    | nil =>
      have e : take [] = ([], []) := rfl
      simp only [pack, List.map_nil, schedule, e, List.drop_nil]
      have fixed : schedule n (i+1+1) [] = schedule n (i+1) [] := ih (i+1) []
      rw [fixed]
    | cons v rest =>
      simp only [pack, List.map_cons, schedule, QueryEncoding.take_put]
      have e : v.drop (i+1) = v.tail.drop i := by cases v <;> simp [List.drop_succ_cons]
      rw [e, ih (i+1) rest]

private theorem matrix_schedule (M : Matrix n) : schedule n 0 (matrixWord M) = diagonal n M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold matrixWord
    rw [List.ofFn_succ]
    simp only [schedule, pack, QueryEncoding.take_put, List.drop_zero, WidthCode.resize_eq_word,
      bits_word, diagonal]
    rw [offset_pack n 0]
    have e : pack ((List.ofFn fun i : Fin n => word (M i.succ)).map List.tail) =
        matrixWord (minor M) := by
      apply congrArg pack
      apply List.ext_getElem (by simp [matrixWord])
      intro j hj₁ hj₂
      simp only [matrixWord, List.getElem_map, List.getElem_ofFn, word_tail, minor]
    rw [e, ih]

private theorem minor_encode (xs : List (Bits (n + 1))) :
    minor (encode xs) = encode (subproblem xs) := by
  funext i
  change tail (normal xs (unit i.succ)) = normal (subproblem xs) (unit i)
  rw [unit_succ]
  cases hn : splitPivot xs with
  | none => simp [normal_none hn, subproblem, hn]
  | some p =>
    obtain ⟨p, rest⟩ := p
    simp [normal_some hn, subproblem, hn, lower]

private theorem slot_none {xs : List (Bits (n + 1))} (h : splitPivot xs = none) :
    slot (word (encode xs 0)) = none := by
  change slot (word (normal xs (unit 0))) = none
  rw [unit_zero, normal_none h, word_cons]
  rfl

private theorem first_generator {xs : List (Bits (n + 1))} {p rest} (h : splitPivot xs = some (p, rest)) :
    ∃ v : Bits n, slot (word (encode xs 0)) = some (word v) ∧
      ListSpan xs (cons true v) := by
  let v := normal (subproblem xs) (tail p)
  have lowerUnit : lower p (unit (0 : Fin (n+1))) = tail p := by simp [unit_zero, lower]
  have col : encode xs 0 = cons false v := by
    change normal xs (unit 0) = cons false v
    rw [normal_some h, lowerUnit]
    simp [v, subproblem, h]
  have a : add (unit (0 : Fin (n+1))) (encode xs 0) = cons true v := by
    rw [unit_zero, col]
    apply eq_of_head_tail <;> simp
  have member : add (unit (0 : Fin (n+1))) (encode xs 0) ∈ columns (encode xs) :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  exact ⟨v, by rw [col, word_cons]; rfl, a ▸ (projected_sameSpan xs _).mp (.gen member)⟩

private theorem translate_mem {ps : List (Option Word)} (shape : Shaped n ps)
    (v x : Bits n) :
    word x ∈ (linearPoints ps).map (translate (word v)) ↔ word (add v x) ∈ linearPoints ps := by
  rw [word_add]
  constructor
  · intro hm
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
    rw [← hyx, translate_self_left (by rw [word_length, shape.points_width hy])]
    exact hy
  · intro hm
    exact List.mem_map.mpr ⟨_, hm, translate_self_left (by simp)⟩

private theorem diagonal_shape (M : Matrix n) : Shaped n (diagonal n M) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    unfold diagonal slot
    split
    · exact .free (ih _)
    · exact .pivot (by simp) (ih _)

private theorem diagonal_spec (xs : List (Bits n)) (x : Bits n) :
    word x ∈ linearPoints (diagonal n (encode xs)) ↔ ListSpan xs x := by
  induction n with
  | zero =>
    have e : x = zero 0 := funext (fun i => Fin.elim0 i)
    subst x
    exact ⟨fun _ => .zero, fun _ => by simp [diagonal, word, linearPoints]⟩
  | succ n ih =>
    let rest := subproblem xs
    let ps := diagonal n (encode rest)
    have low (y : Bits n) :
        word y ∈ linearPoints ps ↔ ListSpan xs (cons false y) :=
      (ih _ _).trans (subproblem_span _ _)
    have e : word x = head x :: word (tail x) := by
      conv => lhs; rw [← cons_head_tail x, word_cons]
    rw [diagonal, minor_encode, e]
    change (head x :: word (tail x)) ∈ linearPoints (slot (word (encode xs 0)) :: ps) ↔ _
    cases h : splitPivot xs with
    | none =>
      rw [slot_none h]
      cases hx : head x with
      | false =>
        simp only [linearPoints, List.mem_map, List.cons.injEq, true_and, exists_eq_right]
        have same : cons false (tail x) = x := by rw [← hx, cons_head_tail]
        exact (low _).trans (by rw [same])
      | true =>
        simp only [linearPoints, List.mem_map, List.cons.injEq, Bool.false_eq_true,
          false_and, and_false, exists_const, false_iff]
        intro has
        have no := span_head_false (splitPivot_none h) has
        rw [hx] at no
        contradiction
    | some pair =>
      obtain ⟨p, rs⟩ := pair
      obtain ⟨v, slotV, inSpan⟩ := first_generator h
      rw [slotV]
      have lp := span_without_head (x := x) inSpan (by simp)
      cases hx : head x with
      | false =>
        simp only [linearPoints, List.mem_append, List.mem_map, List.cons.injEq,
          true_and, Bool.true_eq_false, false_and, and_false, exists_const, or_false, exists_eq_right]
        exact (low _).trans (by simpa [lower, hx] using lp.symm)
      | true =>
        simp only [linearPoints, List.mem_append, List.mem_map, List.cons.injEq,
          Bool.false_eq_true, false_and, and_false, exists_const, false_or, true_and]
        have tr := translate_mem (diagonal_shape (encode rest)) v (tail x)
        rw [List.mem_map] at tr
        apply tr.trans
        rw [add_comm]
        exact (low _).trans (by simpa [lower, hx] using lp.symm)

private def slice : List (Option Word) → Option Candidate
  | some b :: rest => some ⟨b, rest⟩
  | _ => none

private theorem decode_slice (k : Nat) (w : Word) : decode k w = slice (schedule (k+1) 0 w) := by
  simp only [decode, schedule, List.drop_zero, base, pivots, present, slot]
  have e : (0 : Nat) + 1 = 1 := rfl
  rw [e]
  cases (WidthCode.resize (k+1) (take w).1).headD false <;> simp [slice]

private theorem slice_spec (s : List (Option Word)) (x : Bits n) :
    (∃ a, slice s = some a ∧ word x ∈ a.points) ↔ word (lift x) ∈ linearPoints s := by
  rw [show word (lift x) = true :: word x from word_cons true x]
  cases s with
  | nil =>
    simp [slice, linearPoints]
  | cons hd rest =>
    cases hd
    · simp [slice, linearPoints, List.mem_map]
    · simp [slice, linearPoints, List.mem_map, AffineSearch.Candidate.points]

/-- On a genuine normal-form matrix, the decoded affine candidate has exactly
the slice of the row span in the homogenizing coordinate. -/
theorem decode_projection (xs : List (Bits (n+1))) (x : Bits n) :
    (∃ a, decode n (matrixWord (encode xs)) = some a ∧ word x ∈ a.points) ↔
      ListSpan xs (lift x) := by
  rw [decode_slice, matrix_schedule, slice_spec, diagonal_spec]

theorem true_candidate {S : Word → Prop} (width : ∀ w, S w → w.length = n)
    (sat : ∃ w, S w) (xs : List (Bits (n+1)))
    (rep : ∀ v, ListSpan xs v ↔ Span (Lifted (fun v : Bits n => S (word v))) v) :
    ∃ A, decode n (matrixWord (encode xs)) = some A ∧ Genuine S A := by
  let w := matrixWord (encode xs)
  have holds (x : Bits n) :
      (∃ A, decode n w = some A ∧ word x ∈ A.points) ↔
        AffineHull (fun v : Bits n => S (word v)) x :=
    (decode_projection _ _).trans ((rep _).trans (affineHull_iff_lifted_span _ _).symm)
  have incl (v : Word) (hv : S v) : ∃ A, decode n w = some A ∧ v ∈ A.points := by
    have back := word_bits (width v hv)
    have h := (holds (bits v n)).mpr (affineHull_gen (by simpa only [back] using hv))
    simpa only [back] using h
  obtain ⟨v, hv⟩ := sat
  obtain ⟨A, ha, _⟩ := incl v hv
  refine ⟨A, ha, ?_, ?_⟩
  · intro u hu
    obtain ⟨B, hb, hm⟩ := incl u hu
    rw [ha] at hb
    cases hb
    exact hm
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
    have shape := decode_shape ha
    have len := shape.1.points_width hz
    have len' : (translate A.base z).length = n := by
      simp [AffineSearch.translate_length, len, shape.2]
    have back := word_bits len'
    have aff := (holds (bits (translate A.base z) n)).mp ⟨A, ha, by rw [back]; exact hu⟩
    simpa only [back] using parity_hull aff


open ReplayFrameCode (shift embed shift_run)

private def shiftedResize : Code := shift 65 WidthCode.resizeCode

private theorem shiftedResize_run (s : State) (n : Nat) (width : s.reg 86 = ones n) :
    ∃ out t, Run emptyLanguage shiftedResize s out t 0 ∧ t ≤ 13 * n + 14 ∧
      out.reg 87 = WidthCode.resize n (s.reg 87) ∧ Preserves s out [86, 87, 88, 89] := by
  let inner : State := ⟨fun r => s.reg (65 + r), s.queries⟩
  have eq : embed 65 s inner = s := by
    refine State.ext ?_ rfl
    funext r
    by_cases h : r < 65
    · simp [embed, h]
    · simp [embed, h, inner, show 65 + (r - 65) = r by omega]
  obtain ⟨innerOut, t, run, time, value, frame⟩ := WidthCode.resize_run inner n width
  let out := embed 65 s innerOut
  have shifted : Run emptyLanguage shiftedResize s out t 0 := by
    simpa only [shiftedResize, eq] using (shift_run 65 s run)
  refine ⟨out, t, shifted, time, ?_, ?_⟩
  · exact (ReplayFrameCode.embed_high 65 s innerOut 22).trans value
  · refine ⟨frame.1, fun r hr => ?_⟩
    by_cases h : r < 65
    · exact ReplayFrameCode.embed_low s innerOut h
    · have j : r - 65 ∉ [21, 22, 23, 24] := by
        simp at hr ⊢
        omega
      have arith : 65 + (r - 65) = r := by omega
      simp [out, embed, h, frame.2 _ j, inner, arith]

private def getEntry : Code :=
  FieldCode.takeField 80 87 90 91 ⨟
    .write 93 (.copy 92) ⨟ EliminationQueryCode.drop 93 87 ⨟ .write 86 (.copy 94) ⨟ shiftedResize

private def entrySlots : List Nat := [80, 86, 87, 88, 89, 90, 91, 93]

private theorem getEntry_run (s : State) (n i : Nat)
    (width : s.reg 94 = ones n) (offset : s.reg 92 = ones i) :
    ∃ out t, Run emptyLanguage getEntry s out t 0 ∧
      t ≤ 14 * (s.reg 80).length + 4 * i + 13 * n + 38 ∧
      out.reg 80 = (take (s.reg 80)).2 ∧
      out.reg 87 = WidthCode.resize n ((take (s.reg 80)).1.drop i) ∧
      Preserves s out entrySlots := by
  obtain ⟨a, t₁, takeRun, cost₁, rest, value, queue, preserve⟩ :=
    FieldCode.takeField_run s (src := 80) (dst := 87) (scratch := 90) (flag := 91)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let b := a.write 93 (ones i)
  have copyI : Run emptyLanguage (.write 93 (.copy 92)) a b 1 0 := by
    simpa [b, Expr.eval, preserve 92 (by decide) (by decide) (by decide) (by decide), offset]
      using stepWrite a 93 (.copy 92)
  obtain ⟨c, cut, trimmed, cutFrame⟩ :=
    EliminationQueryCode.drop_run b (ctr := 93) (dst := 87) (n := i) (by decide) (by simp [b, State.write])
  let d := c.write 86 (ones n)
  have copyN : Run emptyLanguage (.write 86 (.copy 94)) c d 1 0 := by
    simpa [d, Expr.eval, cutFrame.2 94 (by decide), b, State.write,
      preserve 94 (by decide) (by decide) (by decide) (by decide), width] using stepWrite c 86 (.copy 94)
  obtain ⟨out, t₂, resize, cost₂, normalized, frame⟩ := shiftedResize_run d n (by simp [d, State.write])
  refine ⟨out, _, .seq takeRun (.seq copyI (.seq cut (.seq copyN resize))), by omega, ?_, ?_, ?_⟩
  · rw [frame.2 80 (by decide)]
    simpa [d, State.write, cutFrame.2 80 (by decide), b] using rest
  · rw [normalized]
    simp [d, State.write, trimmed, b, value]
  · have first : Preserves s a entrySlots := ⟨queue, fun r hr => by
      simp [entrySlots] at hr
      exact preserve r (by omega) (by omega) (by omega) (by omega)⟩
    have second : Preserves a b entrySlots := (preserves_write ..).mono (by simp [entrySlots])
    have third := cutFrame.mono (more := entrySlots) (by simp [entrySlots, List.cons_subset])
    have fourth : Preserves c d entrySlots := (preserves_write ..).mono (by simp [entrySlots])
    have last := frame.mono (more := entrySlots) (by simp [entrySlots, List.cons_subset])
    exact first.trans (second.trans (third.trans (fourth.trans last)))

private def tag : Code := .branch (.head 87) (.write 87 .empty)
  (.write 87 (.tail 87) ⨟ .write 87 (.cons true 87))

private theorem tag_run (s : State) :
    ∃ out t, Run emptyLanguage tag s out t 0 ∧ t ≤ 4 ∧
      out.reg 87 = pivotWord (slot (s.reg 87)) ∧ Preserves s out [87] := by
  cases e : (s.reg 87).headD false
  · let a := s.write 87 (s.reg 87).tail
    let b := a.write 87 (true :: (s.reg 87).tail)
    have run₁ : Run emptyLanguage (.write 87 (.tail 87)) s a 1 0 := .write
    have run₂ : Run emptyLanguage (.write 87 (.cons true 87)) a b 1 0 := by
      simpa [a, b, Expr.eval, State.write] using stepWrite a 87 (.cons true 87)
    exact ⟨b, 4, runFalse (by simpa [Test.eval] using e) (.seq run₁ run₂), by decide,
      by rw [show slot (s.reg 87) = some (s.reg 87).tail by simp only [slot, e, Bool.false_eq_true, ↓reduceIte]]; rfl,
      (preserves_write ..).trans (preserves_write ..)⟩
  · exact ⟨s.write 87 [], 2, runTrue (by simpa [Test.eval] using e) .write, by decide,
      by rw [show slot (s.reg 87) = none by simp only [slot, e, ↓reduceIte]]; rfl, preserves_write ..⟩

private def readPivot : Code :=
  getEntry ⨟ tag ⨟ WordCode.putField 87 83 95 96 97 ⨟ .write 92 (.cons true 92)

private def iterationSlots : List Nat :=
  [80, 83, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]

private theorem readPivot_run (s : State) (n i : Nat)
    (width : s.reg 94 = ones (n+1)) (offset : s.reg 92 = ones i) :
    let data := take (s.reg 80)
    let maybe := slot (WidthCode.resize (n+1) (data.1.drop i))
    ∃ out t, Run emptyLanguage readPivot s out t 0 ∧
      t ≤ 14 * (s.reg 80).length + 4 * i + 27 * (n+1) + 69 ∧
      out.reg 80 = data.2 ∧ out.reg 83 = put (pivotWord maybe) (s.reg 83) ∧
      out.reg 92 = ones (i+1) ∧ out.reg 94 = ones (n+1) ∧ Preserves s out iterationSlots := by
  dsimp only
  obtain ⟨a, t₁, extraction, cost₁, residual, value, first⟩ := getEntry_run s (n+1) i width offset
  obtain ⟨b, t₂, label, cost₂, encoded, second⟩ := tag_run a
  obtain ⟨c, append, output, third⟩ :=
    WordCode.putField_run b (src := 87) (dst := 83) (tmp := 95) (rev := 96) (flag := 97)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let out := c.write 92 (ones (i+1))
  have advance : Run emptyLanguage (.write 92 (.cons true 92)) c out 1 0 := by
    simpa [out, Expr.eval, third.2 92 (by decide), second.2 92 (by decide),
      first.2 92 (by decide), offset, ones_succ] using stepWrite c 92 (.cons true 92)
  have f₁ := first.mono (more := iterationSlots) (by simp [entrySlots, iterationSlots, List.cons_subset])
  have f₂ := second.mono (more := iterationSlots) (by simp [iterationSlots])
  have f₃ := third.mono (more := iterationSlots) (by simp [iterationSlots, List.cons_subset])
  have f₄ : Preserves c out iterationSlots := (preserves_write ..).mono (by simp [iterationSlots])
  refine ⟨out, _, .seq extraction (.seq label (.seq append advance)), ?_, ?_, ?_, ?_, ?_,
    f₁.trans (f₂.trans (f₃.trans f₄))⟩
  · have size : (b.reg 87).length ≤ n+1 := by
      rw [encoded]
      unfold slot
      split
      · simp [pivotWord]
      · simp [pivotWord, value, WidthCode.resize, WidthCode.resize_length]
    omega
  · simp [out, State.write, third.2 80 (by decide), second.2 80 (by decide), residual]
  · simp [out, State.write, output, encoded, value, second.2 83 (by decide), first.2 83 (by decide)]
  · simp [out, State.write]
  · simp [out, State.write, third.2 94 (by decide), second.2 94 (by decide), first.2 94 (by decide), width]


private def writePivots : List (Option Word) → Word → Word
  | [], suffix => suffix
  | row :: ps, suffix => put (pivotWord row) (writePivots ps suffix)

private theorem writePivots_append (xs ys : List (Option Word)) (suffix : Word) :
    writePivots (xs ++ ys) suffix = writePivots xs (writePivots ys suffix) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [writePivots, ih]

private theorem writePivots_packed (xs : List (Option Word)) :
    writePivots xs [] = pack (xs.map pivotWord) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [writePivots, pack, ih]

private theorem takeRestLength (w : Word) : (take w).2.length ≤ w.length := by
  have h := QueryEncoding.take_lengths w
  omega

private def readPivots : Code := forUnary 94 readPivot

private theorem readPivots_run (s : State) (n i limit budget : Nat)
    (width : s.reg 94 = ones n) (offset : s.reg 92 = ones i)
    (size : (s.reg 80).length ≤ budget) (totalWidth : i + n ≤ limit) :
    ∃ out t, Run emptyLanguage readPivots s out t 0 ∧
      t ≤ (14 * budget + 31 * limit + 72) * n + 1 ∧
      out.reg 83 = writePivots (schedule n i (s.reg 80)).reverse (s.reg 83) ∧
      Preserves s out iterationSlots := by
  induction n generalizing s i with
  | zero =>
    have stop : Run emptyLanguage readPivots s s 1 0 :=
      .loopFalse (by simp [Test.eval, width])
    exact ⟨s, 1, stop, by simp, rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨a, one, part, cost, left, stored, off, ctr, first⟩ := readPivot_run s n i width offset
    let b := a.write 94 (ones n)
    have count : b.reg 94 = ones n := by simp [b, State.write]
    have debit : Run emptyLanguage (.write 94 (.tail 94)) a b 1 0 := by
      simpa [b, Expr.eval, ctr, ones_succ] using stepWrite a 94 (.tail 94)
    have size' : (b.reg 80).length ≤ budget := by
      simp only [b, HullBatchMachine.write_ne _ _ (by decide : 80 ≠ 94), left]
      exact Nat.le_trans (takeRestLength _) size
    have offset' : b.reg 92 = ones (i+1) := by simpa [b, State.write] using off
    obtain ⟨out, later, loop, bound, value, frame⟩ := ih b (i+1) count offset' size' (by omega)
    have hasMore : (Test.head 94).eval s = true := by simp [Test.eval, width, ones_succ]
    have all : Run emptyLanguage readPivots s out (one + 1 + 1 + later + 1) 0 :=
      .loopTrue hasMore (.seq part debit) loop
    refine ⟨out, _, all, ?_, ?_, ?_⟩
    · rw [Nat.mul_succ]
      omega
    · have residual : b.reg 80 = (take (s.reg 80)).2 := by
        simp [b, State.write, left]
      have prev : b.reg 83 = a.reg 83 := rfl
      rw [value, residual, prev, stored]
      simp [schedule, List.reverse_cons, writePivots_append, writePivots]
    · have f : Preserves a b iterationSlots := (preserves_write ..).mono (by simp [iterationSlots])
      exact first.trans (f.trans frame)

private def recordFlag : Code :=
  .branch (.head 87) (WordCode.setBit 84 false) (WordCode.setBit 84 true)

private theorem recordFlag_run (s : State) :
    Run emptyLanguage recordFlag s (s.write 84 [!(s.reg 87).headD false]) 4 0 := by
  cases h : (s.reg 87).headD false
  · exact runFalse (by exact h) (WordCode.setBit_run ..)
  · exact runTrue (by exact h) (WordCode.setBit_run ..)

private def readBase : Code :=
  .write 94 (.cons true 81) ⨟ .write 92 .empty ⨟ getEntry ⨟
    .write 82 (.tail 87) ⨟ recordFlag ⨟ .write 83 .empty ⨟ .write 94 (.tail 94) ⨟
      WordCode.setBit 92 true

def footprint : List Nat := [82, 84] ++ iterationSlots

private theorem readBase_run (s : State) (k : Nat) (width : s.reg 81 = ones k) :
    ∃ out t, Run emptyLanguage readBase s out t 0 ∧
      t ≤ 14 * (s.reg 80).length + 13 * (k+1) + 57 ∧
      out.reg 80 = (take (s.reg 80)).2 ∧ out.reg 82 = base k (s.reg 80) ∧
      out.reg 83 = [] ∧ out.reg 84 = [present k (s.reg 80)] ∧
      out.reg 92 = ones 1 ∧ out.reg 94 = ones k ∧ Preserves s out footprint := by
  let a := s.write 94 (ones (k+1))
  let b := a.write 92 []
  have wa : Run emptyLanguage (.write 94 (.cons true 81)) s a 1 0 := by
    simpa [a, Expr.eval, width, ones_succ] using stepWrite s 94 (.cons true 81)
  have wb : Run emptyLanguage (.write 92 .empty) a b 1 0 := .write
  obtain ⟨c, scanTime, scan, cost, rem, word, frame⟩ :=
    getEntry_run b (k+1) 0 (by simp [a, b, State.write]) (by simp [b, State.write])
  let d := c.write 82 (c.reg 87).tail
  have wd : Run emptyLanguage (.write 82 (.tail 87)) c d 1 0 := .write
  let e := d.write 84 [!(d.reg 87).headD false]
  have we : Run emptyLanguage recordFlag d e 4 0 := recordFlag_run d
  let f := e.write 83 []
  have wf : Run emptyLanguage (.write 83 .empty) e f 1 0 := .write
  let g := f.write 94 (ones k)
  have ct : f.reg 94 = ones (k+1) := by
    simp [f, e, d, State.write, frame.2 94 (by decide), b, a]
  have wg : Run emptyLanguage (.write 94 (.tail 94)) f g 1 0 := by
    simpa [g, Expr.eval, ct, ones_succ] using stepWrite f 94 (.tail 94)
  let out := g.write 92 [true]
  have done : Run emptyLanguage (WordCode.setBit 92 true) g out 3 0 := WordCode.setBit_run ..
  have hword : c.reg 87 = WidthCode.resize (k+1) (take (s.reg 80)).1 := by
    simpa [b, a, State.write] using word
  have hval : b.reg 80 = s.reg 80 := rfl
  rw [hval] at cost rem
  refine ⟨out, _, .seq wa (.seq wb (.seq scan (.seq wd (.seq we (.seq wf (.seq wg done)))))),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [out, g, f, e, d, State.write, rem]
  · simp [out, g, f, e, d, State.write, base, hword]
  · simp [out, g, f, State.write]
  · simp [out, g, f, e, d, State.write, present, hword]
  · rfl
  · simp [out, g, State.write]
  · have fa : Preserves s a footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have fb : Preserves a b footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have fc := frame.mono (more := footprint) (by simp [entrySlots, footprint, iterationSlots, List.cons_subset])
    have fd : Preserves c d footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have fe : Preserves d e footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have ff : Preserves e f footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have fg : Preserves f g footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    have fo : Preserves g out footprint :=
      (preserves_write ..).mono (by simp [footprint, iterationSlots])
    exact fa.trans (fb.trans (fc.trans (fd.trans (fe.trans (ff.trans (fg.trans fo))))))

/-- Read the matrix in register 80 at the unary affine width in register 81.
Registers 82, 83 and 84 receive the base, packed reverse pivot schedule, and
candidate-present bit, respectively. -/
def readCandidate : Code := readBase ⨟ readPivots

theorem readCandidate_pure : readCandidate.pure := by
  simp [readCandidate, readBase, getEntry, shiftedResize, readPivots, readPivot, tag, recordFlag,
    forUnary, EliminationQueryCode.drop, WordCode.setBit, Code.allowed, FieldCode.takeField_allowed,
    WidthCode.resize_allowed, ReplayFrameCode.shift_allowed, WordCode.putField_allowed]

private theorem cost_quadratic (n L : Nat) :
    (14 * L + 31 * (n+1) + 72) * n + 14 * L + 13 * (n+1) + 59 ≤ 220 * (n + L + 1) ^ 2 := by
  let q := n + L + 1
  have hm : 14 * L + 31 * (n+1) + 72 ≤ 117 * q := by omega
  have ht : (14 * L + 31 * (n+1) + 72) * n ≤ 117 * q ^ 2 := by
    simpa only [Nat.pow_two, Nat.mul_assoc] using Nat.mul_le_mul hm (show n ≤ q by omega)
  have hp : q ≤ q ^ 2 := by
    simpa only [Nat.pow_two, Nat.mul_one] using Nat.mul_le_mul_left q (show 1 ≤ q by omega)
  change _ ≤ 220 * q ^ 2
  omega

theorem readCandidate_run (s : State) (k : Nat) (width : s.reg 81 = ones k) :
    ∃ out time, Run emptyLanguage readCandidate s out time 0 ∧
      time ≤ 220 * (k + (s.reg 80).length + 1) ^ 2 ∧
      out.reg 82 = base k (s.reg 80) ∧ out.reg 83 = packedPivots (pivots k (s.reg 80)) ∧
      out.reg 84 = [present k (s.reg 80)] ∧ Preserves s out footprint := by
  obtain ⟨a, t, first, startTime, residual, input, empty, enabled, offset, clock, firstFrame⟩ :=
    readBase_run s k width
  have sz : (a.reg 80).length ≤ (s.reg 80).length := by
    rw [residual]
    exact takeRestLength _
  obtain ⟨out, more, loop, loopTime, packed, restFrame⟩ :=
    readPivots_run a k 1 (k+1) (s.reg 80).length clock offset sz (by omega)
  refine ⟨out, t + more + 1, .seq first loop, ?_, ?_, ?_, ?_, ?_⟩
  · have := cost_quadratic k (s.reg 80).length
    omega
  · exact (restFrame.2 82 (by decide)).trans input
  · simpa only [residual, empty, pivots, packedPivots, writePivots_packed] using packed
  · exact (restFrame.2 84 (by decide)).trans enabled
  · exact firstFrame.trans (restFrame.mono (fun _ h => List.mem_append_right _ h))


/-- Decode a list of candidate output words. The genuine output survives the
filter on every satisfiable restricted instance. -/
def decodeList (k : Nat) (words : List Word) : List Candidate := words.filterMap (decode k)

theorem decodeList_shape {k : Nat} {words : List Word} {a : Candidate}
    (member : a ∈ decodeList k words) : Shaped k a.pivots ∧ a.base.length = k := by
  obtain ⟨w, _, eq⟩ := List.mem_filterMap.mp member
  exact decode_shape eq

theorem decodeList_genuine (check : Word → Word → Bool) (words : List Word)
    (x : Word) (k : Nat) (hs : List Word)
    (contains : QueryEncoding.hullWord check (QueryEncoding.requestWord x k hs) ∈ words)
    (sat : ∃ w, AffineSearch.Models (check x) k hs w) :
    ∃ a ∈ decodeList k words, Genuine (AffineSearch.Models (check x) k hs) a := by
  let r : QueryEncoding.Request := ⟨x,k,hs⟩
  let answers := QueryEncoding.oracle check r
  obtain ⟨cert, _, hspan, hmatrix⟩ := recover_basis (QueryEncoding.oracle_spec check r)
  have hS (v : Bits k) : QueryEncoding.S check r v ↔ AffineSearch.Models (check x) k hs (word v) := by
    simp [QueryEncoding.S, r, AffineSearch.Models, AffineSearch.valid]
  have ident : QueryEncoding.S check r =
      (fun v : Bits k => AffineSearch.Models (check x) k hs (word v)) :=
    funext (fun v => propext (hS v))
  change ∀ v, ListSpan (cert.val.map lift) v ↔ Span (Lifted (QueryEncoding.S check r)) v at hspan
  rw [ident] at hspan
  obtain ⟨a, found, good⟩ := true_candidate (n := k) (S := AffineSearch.Models (check x) k hs)
    (fun w hw => (by simpa [AffineSearch.Models, AffineSearch.valid] using hw : w.length=k ∧ _).1)
    sat _ hspan
  refine ⟨a, List.mem_filterMap.mpr ⟨_, contains, ?_⟩, good⟩
  unfold QueryEncoding.hullWord
  rw [QueryEncoding.read_requestWord]
  change decode k (matrixWord (recover answers)) = some a
  rw [hmatrix]
  exact found


/-- Serialize one candidate as the escaped base followed by the reversed
schedule. The list collector escapes this packet as one outer field. -/
def candidateWord (a : Candidate) : Word := put a.base (packedPivots a.pivots)

private theorem pivotWord_bound {k : Nat} {ps : List (Option Word)}
    (shape : Shaped k ps) : ∀ p ∈ ps, (pivotWord p).length ≤ k+1 := by
  induction shape with
  | nil => simp
  | free _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | later
    · simp [pivotWord]
    · exact Nat.le_succ_of_le (ih _ later)
  | pivot hr _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | later
    · simp [pivotWord, hr]
    · exact Nat.le_succ_of_le (ih _ later)

private theorem mapSum_le {α : Type} (f : α → Nat) (ls : List α) (limit : Nat)
    (h : ∀ x ∈ ls, f x ≤ limit) : (ls.map f).sum ≤ limit * ls.length := by
  induction ls with
  | nil => simp
  | cons a tail ih =>
    have first := h a List.mem_cons_self
    have rest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem candidateWord_length {k : Nat} {a : Candidate} (shape : Shaped k a.pivots)
    (baseLength : a.base.length = k) : (candidateWord a).length ≤ 5*(k+1)^2 := by
  unfold candidateWord packedPivots
  rw [QueryEncoding.put_length, QueryEncoding.pack_length, baseLength,
    List.length_map, List.length_reverse, shape.length, List.map_map]
  have budget := mapSum_le (fun p => (pivotWord p).length) a.pivots.reverse (k+1)
    (fun p hp => pivotWord_bound shape p (List.mem_reverse.mp hp))
  rw [List.length_reverse, shape.length] at budget
  change ((a.pivots.reverse.map (fun p => (pivotWord p).length)).sum) ≤ (k+1)*k at budget
  have either : (k+1)*k ≤ (k+1)^2 := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left _ (by omega)
  have small : k + 1 ≤ (k+1)^2 := by
    rw [Nat.pow_two]
    simpa using Nat.mul_le_mul_left (k+1) (show 1 ≤ k+1 by omega)
  simp only [Function.comp_def]
  omega

private def writeCandidates : List Candidate → Word → Word
  | [], suffix => suffix
  | a :: rest, suffix => put (candidateWord a) (writeCandidates rest suffix)

private theorem writeCandidates_append (xs ys : List Candidate) (suffix : Word) :
    writeCandidates (xs ++ ys) suffix = writeCandidates xs (writeCandidates ys suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeCandidates, ih]

private theorem writeCandidates_packed (xs : List Candidate) :
    writeCandidates xs [] = pack (xs.map candidateWord) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeCandidates, pack, ih]

private def saveCandidate : Code :=
  .branch (.head 84)
    (WordCode.putField 82 83 104 105 107 ⨟ WordCode.putField 83 100 104 105 107 ⨟
      .write 101 (.cons true 101))
    .skip

private def saveSlots : List Nat := [83, 100, 101, 104, 105, 107]

private theorem saveCandidate_run (s : State) (k : Nat) (w : Word)
    (first : s.reg 82 = base k w) (piv : s.reg 83 = packedPivots (pivots k w))
    (flag : s.reg 84 = [present k w]) :
    ∃ out time, Run emptyLanguage saveCandidate s out time 0 ∧ time ≤ 14*k+70*(k+1)^2+50 ∧
      out.reg 100 = writeCandidates (decode k w).toList (s.reg 100) ∧
      out.reg 101 = ones (decode k w).toList.length ++ s.reg 101 ∧
      Preserves s out saveSlots := by
  cases h : present k w with
  | false =>
    have skip : Run emptyLanguage saveCandidate s s 2 0 :=
      runFalse (by simp [Test.eval, flag, h]) .skip
    exact ⟨s, 2, skip, by omega, by simp [decode, h, writeCandidates],
      by simp [decode, h], rfl, fun _ _ => rfl⟩
  | true =>
    let candidate : Candidate := ⟨base k w, pivots k w⟩
    have some : decode k w = Option.some candidate := by simp [decode, h, candidate]
    obtain ⟨a, putFirst, assembled, f₁⟩ := WordCode.putField_run s
      (src := 82) (dst := 83) (tmp := 104) (rev := 105) (flag := 107)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨b, putPacket, encoded, f₂⟩ := WordCode.putField_run a
      (src := 83) (dst := 100) (tmp := 104) (rev := 105) (flag := 107)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    let out := b.write 101 (true :: b.reg 101)
    have inc : Run emptyLanguage (.write 101 (.cons true 101)) b out 1 0 := .write
    have yes : (Test.head 84).eval s = true := by simp [Test.eval, flag, h]
    have encodedOne : a.reg 83 = candidateWord candidate := by
      simpa [first, piv, candidate, candidateWord] using assembled
    have packetLen := candidateWord_length (decode_shape some).1 (decode_shape some).2
    have baseLen := base_width k w
    refine ⟨out, _, runTrue yes (.seq putFirst (.seq putPacket inc)), ?_, ?_, ?_, ?_⟩
    · rw [first, encodedOne]
      omega
    · simp [out, State.write, encoded, encodedOne, f₁.2 100 (by decide), some, writeCandidates]
    · simp [out, State.write, f₂.2 101 (by decide), f₁.2 101 (by decide), some, ones_succ]
    · have aFrame := f₁.mono (more := saveSlots) (by simp [saveSlots, List.cons_subset])
      have bFrame := f₂.mono (more := saveSlots) (by simp [saveSlots, List.cons_subset])
      have z : Preserves b out saveSlots := by
        exact (preserves_write ..).mono (by simp [saveSlots])
      exact aFrame.trans (bFrame.trans z)


private def listIteration : Code := FieldCode.takeField 99 80 102 103 ⨟ readCandidate ⨟ saveCandidate
private def listLoop : Code := .loop (.head 106) (.branch (.empty 99) (.write 106 .empty) listIteration)

def listFootprint : List Nat := [99,100,101,102,103,104,105,106,107] ++ footprint

private theorem listLoop_run (s : State) (k budget : Nat) (words : List Word)
    (width : s.reg 81 = ones k) (input : s.reg 99 = pack words)
    (size : (pack words).length ≤ budget) (active : s.reg 106 = [true]) :
    ∃ out time, Run emptyLanguage listLoop s out time 0 ∧
      time ≤ 500 * (k + budget + 1)^2 * words.length + 4 ∧
      out.reg 100 = writeCandidates (decodeList k words).reverse (s.reg 100) ∧
      out.reg 101 = ones (decodeList k words).length ++ s.reg 101 ∧
      Preserves s out listFootprint := by
  induction words generalizing s with
  | nil =>
    let out := s.write 106 []
    have stop : Run emptyLanguage listLoop out out 1 0 :=
      .loopFalse (by simp [out, Test.eval, State.write])
    have arm : Run emptyLanguage (.branch (.empty 99) (.write 106 .empty) listIteration) s out 2 0 :=
      runTrue (by simp [Test.eval, input, pack]) .write
    refine ⟨out, 4, .loopTrue (by simp [Test.eval, active]) arm stop, by simp, ?_, ?_, ?_⟩
    · simp [out, State.write, decodeList, writeCandidates]
    · simp [out, State.write, decodeList, ones]
    · exact (preserves_write ..).mono (by simp [listFootprint])
  | cons w words ih =>
    have raw : s.reg 99 = put w (pack words) := input
    obtain ⟨a, t₁, scan, time₁, left, matrix, queue, frame₁⟩ :=
      FieldCode.takeField_run s (src := 99) (dst := 80) (scratch := 102) (flag := 103)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [raw, QueryEncoding.take_put] at left matrix
    have Lw : w.length ≤ budget := by
      have mn := QueryEncoding.put_length w (pack words)
      change (put w (pack words)).length ≤ budget at size
      omega
    have Lws : (pack words).length ≤ budget := by
      have mn := QueryEncoding.put_length w (pack words)
      change (put w (pack words)).length ≤ budget at size
      omega
    have widthA : a.reg 81 = ones k := by
      rw [frame₁ 81 (by decide) (by decide) (by decide) (by decide), width]
    obtain ⟨b, t₂, read, time₂, base, pivots, present, frame₂⟩ := readCandidate_run a k widthA
    change a.reg 80 = w at matrix
    rw [matrix] at time₂ base pivots present
    obtain ⟨c, t₃, save, time₃, oldValue, oldCount, frame₃⟩ :=
      saveCandidate_run b k w base pivots present
    have arm : Run emptyLanguage (.branch (.empty 99) (.write 106 .empty) listIteration)
        s c (t₁ + (t₂ + t₃ + 1) + 1 + 1) 0 := by
      have nonempty : (Test.empty 99).eval s = false := by rw [Test.eval, raw]; cases w <;> rfl
      exact runFalse nonempty (.seq scan (.seq read save))
    have enable : (Test.head 106).eval s = true := by simp [Test.eval, active]
    have cInputs : c.reg 99 = pack words := by
      rw [frame₃.2 99 (by decide), frame₂.2 99 (by decide)]
      exact left
    have cWidth : c.reg 81 = ones k := by
      rw [frame₃.2 81 (by decide), frame₂.2 81 (by decide)]
      exact widthA
    have cActive : c.reg 106 = [true] := by
      rw [frame₃.2 106 (by decide), frame₂.2 106 (by decide),
        frame₁ 106 (by decide) (by decide) (by decide) (by decide), active]
    obtain ⟨out, rest, later, restTime, values, count, kept⟩ := ih c cWidth cInputs Lws cActive
    have total : Run emptyLanguage listLoop s out
        (t₁ + (t₂ + t₃ + 1) + 1 + 1 + rest + 1) 0 := .loopTrue enable arm later
    refine ⟨out, _, total, ?_, ?_, ?_, ?_⟩
    · rw [input] at time₁
      have norm := Nat.pow_le_pow_left (show k + w.length + 1 ≤ k + budget + 1 by omega) 2
      have std := Nat.pow_le_pow_left (show k + 1 ≤ k + budget + 1 by omega) 2
      have q : k + budget + 1 ≤ (k + budget + 1)^2 := by
        rw [Nat.pow_two]
        simpa using Nat.mul_le_mul_left (k+budget+1) (show 1 ≤ k+budget+1 by omega)
      simp only [List.length_cons, Nat.mul_succ]
      omega
    · rw [values, oldValue, frame₂.2 100 (by decide),
        frame₁ 100 (by decide) (by decide) (by decide) (by decide)]
      cases h : decode k w <;> simp [decodeList, h, List.reverse_cons, writeCandidates_append, writeCandidates]
    · rw [count, oldCount, frame₂.2 101 (by decide),
        frame₁ 101 (by decide) (by decide) (by decide) (by decide)]
      cases h : decode k w <;> simp [decodeList, h, ones, List.replicate_succ', List.append_assoc]
    · have f₁ : Preserves s a listFootprint := ⟨queue, fun r hr => by
        simp [listFootprint, footprint, iterationSlots] at hr
        exact frame₁ r (by omega) (by omega) (by omega) (by omega)⟩
      have f₂ := frame₂.mono (more := listFootprint) (fun _ h => List.mem_append_right _ h)
      have f₃ := frame₃.mono (more := listFootprint)
        (by simp [saveSlots, listFootprint, footprint, iterationSlots, List.cons_subset])
      exact f₁.trans (f₂.trans (f₃.trans kept))

/-- Register 99 holds the packed list of raw matrix words. Decode each at
the unary width in register 81. Register 100 receives the reversed packed
list of valid candidates and register 101 the unary length of that list. -/
def readCandidateList : Code :=
  .write 100 .empty ⨟ .write 101 .empty ⨟ WordCode.setBit 106 true ⨟ listLoop

theorem readCandidateList_pure : readCandidateList.pure := by
  simp [readCandidateList, listLoop, listIteration, saveCandidate, WordCode.setBit, Code.allowed,
    FieldCode.takeField_allowed, readCandidate_pure, WordCode.putField_allowed]

theorem readCandidateList_run (s : State) (k : Nat) (words : List Word)
    (width : s.reg 81 = ones k) (input : s.reg 99 = pack words) :
    ∃ out time, Run emptyLanguage readCandidateList s out time 0 ∧
      time ≤ 600 * (k + (s.reg 99).length + 1)^3 ∧
      out.reg 100 = pack ((decodeList k words).reverse.map candidateWord) ∧
      out.reg 101 = ones (decodeList k words).length ∧ Preserves s out listFootprint := by
  let a := s.write 100 []
  let b := a.write 101 []
  let c := b.write 106 [true]
  have r₁ : Run emptyLanguage (.write 100 .empty) s a 1 0 := .write
  have r₂ : Run emptyLanguage (.write 101 .empty) a b 1 0 := .write
  have r₃ : Run emptyLanguage (WordCode.setBit 106 true) b c 3 0 := WordCode.setBit_run ..
  let L := (s.reg 99).length
  have LB : (pack words).length ≤ L := by
    change _ ≤ (s.reg 99).length
    rw [input]
    exact Nat.le_refl _
  obtain ⟨out, t, run, bound, data, len, frame⟩ :=
    listLoop_run c k L words (by simpa [c, b, a, State.write] using width)
      (by simpa [c, b, a, State.write] using input) LB (by simp [c, State.write])
  refine ⟨out, _, .seq r₁ (.seq r₂ (.seq r₃ run)), ?_, ?_, ?_, ?_⟩
  · let q := k + L + 1
    have size : words.length ≤ L := by
      rw [QueryEncoding.pack_length] at LB
      omega
    have h : 500 * q^2 * words.length ≤ 500 * q^3 := by
      calc
        500 * q^2 * words.length ≤ 500 * q^2 * q :=
          Nat.mul_le_mul_left _ (show words.length ≤ q by omega)
        _ = 500 * q^3 := by rw [Nat.pow_succ q 2, ← Nat.mul_assoc]
    have pos : 0 < q^3 := Nat.pow_pos (by omega)
    change t ≤ 500 * q^2 * words.length + 4 at bound
    change _ ≤ 600*q^3
    omega
  · simpa [c, b, a, State.write, writeCandidates_packed] using data
  · simpa [c, b, State.write] using len
  · have fa : Preserves s a listFootprint := (preserves_write ..).mono (by simp [listFootprint])
    have fb : Preserves a b listFootprint := (preserves_write ..).mono (by simp [listFootprint])
    have fc : Preserves b c listFootprint := (preserves_write ..).mono (by simp [listFootprint])
    exact fa.trans (fb.trans (fc.trans frame))


def readPivotWord (w : Word) : Option Word :=
  if w.isEmpty then none else some w.tail

@[simp] theorem read_pivotWord (p : Option Word) : readPivotWord (pivotWord p) = p := by
  cases p <;> rfl

/-- The machine result is independently readable by a base field followed
by the tagged pivot fields in reverse order. -/
def readCandidateWord (k : Nat) (w : Word) : Candidate :=
  let fields := take w
  ⟨fields.1, ((QueryEncoding.unpack k fields.2).map readPivotWord).reverse⟩

@[simp] theorem read_candidateWord (k : Nat) (a : Candidate) (shape : Shaped k a.pivots) :
    readCandidateWord k (candidateWord a) = a := by
  have len : (a.pivots.reverse.map pivotWord).length ≤ k := by simp [shape.length]
  simp only [readCandidateWord, candidateWord, QueryEncoding.take_put, packedPivots,
    QueryEncoding.unpack_pack _ _ len, List.map_map, Function.comp_def, read_pivotWord,
    List.map_id', List.reverse_reverse]

end CandidateReadCode
