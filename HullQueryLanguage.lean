module

public import QueryEncoding

@[expose] public section

namespace HullQueryLanguage

open AffineSearch HullRecovery HullDecoder
open QueryEncoding (put take readRequest Request matrixWord hullWord S)

private def indexWord (i : Nat) (rest : Word) : Word := put (List.replicate i true) rest

def takeIndex (s : Word) : Nat × Word :=
  let (digits, rest) := take s
  (digits.length, rest)

@[simp] private theorem takeIndex_indexWord (i : Nat) (rest : Word) :
    takeIndex (indexWord i rest) = (i, rest) := by
  simp [takeIndex, indexWord]

private def encodeQuery : Query d → Word
  | .rank r => false :: indexWord r []
  | .bit r i j => true :: indexWord r (indexWord i (indexWord j []))

def readQuery (d : Nat) : Word → Option (Query d)
  | false :: rest =>
    let (r, _) := takeIndex rest
    if hr : r < d + 1 then some (.rank ⟨r, hr⟩) else none
  | true :: rest =>
    let (r, rest) := takeIndex rest
    let (i, rest) := takeIndex rest
    let (j, _) := takeIndex rest
    if hr : r < d + 1 then
      if hi : i < d then
        if hj : j < d then some (.bit ⟨r, hr⟩ ⟨i, hi⟩ ⟨j, hj⟩)
        else none
      else none
    else none
  | [] => none

@[simp] private theorem read_encodeQuery (q : Query d) : readQuery d (encodeQuery q) = some q := by
  cases q <;> simp [readQuery, encodeQuery, Fin.isLt]

/-- The request is passed verbatim and the tag and indices identify one
coordinate of the batch. Unary indices keep the parsing bound immediate. -/
def questionWord (s : Word) (q : Query (readRequest s).width.succ) : Word := put s (encodeQuery q)

private theorem indexWord_length (i : Nat) (rest : Word) :
    (indexWord i rest).length = 2 * i + 1 + rest.length := by
  simp [indexWord, QueryEncoding.put_length]

theorem questionWord_length_le (s : Word) (q : Query (readRequest s).width.succ) :
    (questionWord s q).length ≤ 2 * s.length + 6 * (readRequest s).width.succ + 5 := by
  cases q with
  | rank r =>
    have hr := r.isLt
    simp only [questionWord, QueryEncoding.put_length, encodeQuery, List.length_cons,
      indexWord_length, List.length_nil, Nat.add_zero]
    omega
  | bit r i j =>
    have hr := r.isLt
    have hi := i.isLt
    have hj := j.isLt
    simp only [questionWord, QueryEncoding.put_length, encodeQuery, List.length_cons,
      indexWord_length, List.length_nil, Nat.add_zero]
    omega

/-- A list of satisfying assignments, written as length-delimited fields. -/
def certificateWord (w : Witness m r) : Word :=
  QueryEncoding.pack (w.val.map word)

/-- Read exactly the requested number of assignments. An exhausted field
stream supplies the all-zero word, just like a short assignment. -/
def certificateRows (m : Nat) : Nat → Word → List (Bits m)
  | 0, _ => []
  | n + 1, s => bits (take s).1 m :: certificateRows m n (take s).2

theorem certificateRows_length (m r : Nat) (s : Word) :
    (certificateRows m r s).length = r := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => simp [certificateRows, ih]

def readCertificate (m r : Nat) (s : Word) : Witness m r :=
  ⟨certificateRows m r s, certificateRows_length m r s⟩

@[simp] theorem read_certificateWord (w : Witness m r) :
    readCertificate m r (certificateWord w) = w := by
  have packed (xs : List (Bits m)) :
      certificateRows m xs.length (QueryEncoding.pack (xs.map word)) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [certificateRows, QueryEncoding.pack, bits_word, ih]
  apply Subtype.ext
  change certificateRows m r (QueryEncoding.pack (w.val.map word)) = w.val
  exact (congrArg (fun k => certificateRows m k (QueryEncoding.pack (w.val.map word)))
    w.property).symm.trans (packed w.val)

theorem certificateWord_length (w : Witness m r) :
    (certificateWord w).length = r * (2 * m + 1) := by
  have sumLength (xs : List (Bits m)) : ((xs.map word).map List.length).sum = xs.length * m := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, word_length, List.length_cons, Nat.add_mul,
        Nat.one_mul, ih]
      omega
  rw [certificateWord, QueryEncoding.pack_length, sumLength, List.length_map, w.property,
    Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

instance (check : Word → Word → Bool) (r : Request) : DecidablePred (S check r) :=
  fun v => inferInstanceAs (Decidable (check r.input (decode r.history (word v)) = true))

/-- The single Boolean verifier for encoded queries. All inputs decode to a
bounded-width request, and invalid query indices are rejected. -/
def verifyFields (check : Word → Word → Bool) (fields : Word × Word) (cert : Word) : Bool :=
  let r := readRequest fields.1
  match readQuery (r.width + 1) fields.2 with
  | none => false
  | some q => verify (S check r) q (readCertificate r.width q.level.val cert)

def verifyWord (check : Word → Word → Bool) (s cert : Word) : Bool :=
  verifyFields check (take s) cert

def language (check : Word → Word → Bool) : Word → Prop :=
  fun s => ∃ cert, verifyWord check s cert = true

theorem language_questionWord (check : Word → Word → Bool) (s : Word)
    (q : Query (readRequest s).width.succ) :
    language check (questionWord s q) ↔ Yes (S check (readRequest s)) q := by
  unfold language verifyWord questionWord
  rw [QueryEncoding.take_put]
  simp only [verifyFields, read_encodeQuery]
  constructor
  · rintro ⟨cert, h⟩
    exact ⟨_, (verify_correct _ _ _).mp h⟩
  · rintro ⟨w, h⟩
    exact ⟨certificateWord w, by simpa only [read_certificateWord] using (verify_correct _ _ _).mpr h⟩

theorem width_le (s : Word) : (readRequest s).width ≤ s.length := by
  change (take (take s).2).1.length ≤ s.length
  have h := QueryEncoding.take_lengths s
  have h' := QueryEncoding.take_lengths (take s).2
  omega

/-- Every yes-instance, including malformed words that happen to decode to
valid queries, has a certificate of quadratic bit length. -/
theorem language_bounded (check : Word → Word → Bool) (s : Word) :
    language check s ↔
      ∃ cert, cert.length ≤ (s.length + 1) * (2 * s.length + 1) ∧
        verifyWord check s cert = true := by
  constructor
  · rintro ⟨cert, h⟩
    let r := readRequest (take s).1
    change (match readQuery (r.width + 1) (take s).2 with
      | none => false
      | some q => verify (S check r) q (readCertificate r.width q.level.val cert)) = true at h
    cases he : readQuery (r.width + 1) (take s).2 with
    | none => simp [he] at h
    | some q =>
      simp only [he] at h
      let w := readCertificate r.width q.level.val cert
      have hw : r.width ≤ s.length :=
        Nat.le_trans (width_le _) (QueryEncoding.take_data_le s)
      have hq : q.level.val ≤ s.length + 1 := by
        have h := q.level.isLt
        omega
      refine ⟨certificateWord w, ?_, ?_⟩
      · rw [certificateWord_length]
        exact Nat.mul_le_mul hq (by omega)
      · change (match readQuery (r.width + 1) (take s).2 with
          | none => false
          | some p => verify (S check r) p
                        (readCertificate r.width p.level.val (certificateWord w))) = true
        simpa only [he, read_certificateWord] using h
  · rintro ⟨cert, _, h⟩
    exact ⟨cert, h⟩

def questions (s : Word) : List Word :=
  (batch (readRequest s).width.succ).map (questionWord s)

theorem questions_length (s : Word) :
    (questions s).length = ((readRequest s).width + 2) *
      (1 + ((readRequest s).width + 1) * ((readRequest s).width + 1)) := by
  simp [questions, batch_length]

theorem questions_count_bound (s : Word) : (questions s).length ≤ 4 * (s.length + 1) ^ 3 := by
  rw [questions_length]
  have width := width_le s
  have dimension : (readRequest s).width + 1 ≤ s.length + 1 := Nat.succ_le_succ width
  have square := Nat.mul_le_mul dimension dimension
  have product := Nat.mul_le_mul (show (readRequest s).width + 2 ≤ 2 * (s.length + 1) by omega)
    (show 1 + ((readRequest s).width + 1) * ((readRequest s).width + 1) ≤
        2 * ((s.length + 1) * (s.length + 1)) by
      have positive : 0 < (s.length + 1) * (s.length + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      omega)
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using product

theorem question_length_of_mem {s q : Word} (h : q ∈ questions s) :
    q.length ≤ 8 * s.length + 11 := by
  obtain ⟨query, _, rfl⟩ := List.mem_map.mp h
  have len := questionWord_length_le s query
  have width := width_le s
  omega

/-- A consumer of every answer in the predetermined order. -/
def assemble (s replies : Word) : Word :=
  matrixWord (recoverBatch ((batch (readRequest s).width.succ).zip replies))

theorem assemble_correct (check : Word → Word → Bool) (s : Word)
    (answer : Word → Bool)
    (h : ∀ q, q ∈ questions s → (answer q = true ↔ language check q)) :
    assemble s ((questions s).map answer) = hullWord check s := by
  let r := readRequest s
  let expected := QueryEncoding.oracle check r
  let actual (q : Query r.width.succ) := answer (questionWord s q)
  have sameAnswers : actual = expected := by
    funext q
    have ha := (h (questionWord s q) (List.mem_map_of_mem (mem_batch q))).trans
      (language_questionWord check s q)
    have he : expected q = true ↔ Yes (S check r) q := QueryEncoding.oracle_spec check r q
    change (actual q = true ↔ Yes (S check r) q) at ha
    have eq := ha.trans he.symm
    cases a : actual q <;> cases e : expected q <;> simp_all
  have lookup : readAnswer (List.map (fun q => (q, expected q)) (batch r.width.succ)) =
      expected := funext (fun q => readAnswer_map _ _ _ (mem_batch q))
  simp only [questions, List.map_map, Function.comp_def]
  change matrixWord (recoverBatch ((batch r.width.succ).zip
    ((batch r.width.succ).map actual))) = matrixWord (recover expected)
  have zipped (qs : List (Query r.width.succ)) :
      qs.zip (qs.map expected) = qs.map (fun q => (q, expected q)) := by
    induction qs <;> simp [*]
  rw [sameAnswers, zipped, recoverBatch, lookup]

end HullQueryLanguage
