module

public import HullDecoder

@[expose] public section

namespace QueryEncoding
open AffineSearch
open HullRecovery
open HullDecoder

/-- Escape each data bit by prefixing a 1. A single 0 terminates the field. -/
def put : Word → Word → Word
  | [], rest => false :: rest
  | b :: bs, rest => true :: b :: put bs rest

def take : Word → Word × Word
  | true :: b :: bs => let (w, rest) := take bs; (b :: w, rest)
  | false :: rest => ([], rest)
  | _ => ([], [])

@[simp] theorem take_put (w rest : Word) : take (put w rest) = (w, rest) := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [put, take, ih]

theorem take_lengths (s : Word) :
    2 * (take s).1.length + (take s).2.length ≤ s.length := by
  match s with
  | [] => simp [take]
  | false :: rest => simp [take]
  | [true] => simp [take]
  | true :: b :: bs =>
    have ih := take_lengths bs
    rw [take]
    cases h : take bs with
    | mk w rest =>
      simp only [h, List.length_cons] at ih ⊢
      omega

theorem take_data_le (s : Word) : (take s).1.length ≤ s.length := by
  have h := take_lengths s
  omega

theorem take_rest_lt {s : Word} (h : s ≠ []) : (take s).2.length < s.length := by
  match s with
  | [] => contradiction
  | false :: rest => simp [take]
  | [true] => decide
  | true :: b :: rest =>
    have length := take_lengths rest
    rw [take]
    cases e : take rest with
    | mk data remaining =>
      simp only [e, List.length_cons] at length ⊢
      omega

theorem put_length (w rest : Word) : (put w rest).length = 2*w.length + 1 + rest.length := by
  induction w with
  | nil => simp [put]; omega
  | cons b bs ih => simp only [put, List.length_cons, ih]; omega

def pack : List Word → Word
  | [] => []
  | x :: xs => put x (pack xs)

def unpack : Nat → Word → List Word
  | 0, _ => []
  | fuel+1, s =>
    if s.isEmpty then [] else
    let (w, rem) := take s
    w :: unpack fuel rem

private theorem put_nonempty (x s : Word) : (put x s).isEmpty = false := by
  cases x <;> rfl

theorem unpack_pack (ws : List Word) (fuel : Nat) (h : ws.length ≤ fuel) :
    unpack fuel (pack ws) = ws := by
  induction ws generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons w ws ih =>
    cases fuel with
    | zero => simp at h
    | succ f =>
      simp only [pack, unpack, put_nonempty, Bool.false_eq_true, ↓reduceIte, take_put,
        ih f (by simpa using h)]

theorem pack_length (ws : List Word) : (pack ws).length = 2*(ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [pack, put_length, List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

def matrixWord (M : Matrix d) := pack (List.ofFn fun i => word (M i))
def readMatrix (d : Nat) (s : Word) : Matrix d :=
  let cols := unpack d s
  fun i => bits (cols[i.val]?.getD []) d

@[simp] theorem read_matrixWord (M : Matrix d) : readMatrix d (matrixWord M) = M := by
  funext i
  simp [readMatrix, matrixWord, unpack_pack, List.getElem?_ofFn, i.isLt, bits_word]

theorem matrixWord_length (M : Matrix d) : (matrixWord M).length = 2*(d*d) + d := by
  rw [matrixWord, pack_length, List.length_ofFn]
  have general (xs : List Word) (h : ∀ x ∈ xs, x.length = d) :
      (xs.map List.length).sum = xs.length * d := by
    induction xs with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      rw [h w List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      omega
  rw [general _ (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; simp), List.length_ofFn]

structure Request where
  input : Word
  width : Nat
  history : List Word
  deriving Repr

/-- Unary width prevents exponentially large ranks on malformed instances. -/
def requestWord (x : Word) (k : Nat) (hs : List Word) : Word :=
  put x (put (List.replicate k true) (pack hs))

def readRequest (s : Word) : Request :=
  let (x, tail) := take s
  let (unary, rem) := take tail
  ⟨x, unary.length, unpack rem.length rem⟩

@[simp] theorem read_requestWord (x : Word) (k : Nat) (hs : List Word) :
    readRequest (requestWord x k hs) = ⟨x, k, hs⟩ := by
  have h : hs.length ≤ (pack hs).length := by rw [pack_length]; omega
  simp [readRequest, requestWord, unpack_pack hs _ h]

theorem request_size {n k hs} (h : History n k hs) (x : Word) :
    (requestWord x k hs).length ≤ 2*x.length + 2*n*n + 3*n + 2 := by
  simp only [requestWord, put_length, List.length_replicate, pack_length]
  have a := h.maskBits
  have b := h.rounds
  have c := Nat.mul_le_mul_right n (show hs.length ≤ n by omega)
  rw [Nat.mul_assoc]
  omega

def S (check : Word → Word → Bool) (r : Request) : Bits r.width → Prop :=
  fun v => check r.input (decode r.history (word v)) = true

/-- This total mathematical function is the target to implement by a
one-batch oracle machine. Classical choice here specifies the oracle's
truth values; it is never used by the executable SAT search. -/
noncomputable def oracle (check : Word → Word → Bool) (r : Request) :
    Query (r.width+1) → Bool := by
  classical
  exact fun q => decide (Yes (S check r) q)

theorem oracle_spec (check : Word → Word → Bool) (r : Request) :
    CorrectAnswers (S check r) (oracle check r) := by
  classical
  intro q
  simp [oracle]

noncomputable def hullWord (check : Word → Word → Bool) (s : Word) : Word :=
  let r := readRequest s
  matrixWord (recover (oracle check r))

/-- Candidate lists for a restricted problem are always decoded into
well-formed spaces, even on fictitious transcripts or malformed outputs. -/
def listFrom (out : Word → List Word) (x : Word) (k : Nat) (hs : List Word) :
    List AffineSearch.Candidate :=
  (out (requestWord x k hs)).filterMap (fun s => candidate (readMatrix (k+1) s))

theorem list_shape (out : Word → List Word) (x : Word) (k : Nat) (hs : List Word)
    (A : AffineSearch.Candidate) (ha : A ∈ listFrom out x k hs) :
    Shaped k A.pivots ∧ A.base.length = k := by
  obtain ⟨_, _, h⟩ := List.mem_filterMap.mp ha
  exact candidate_shape h

theorem list_genuine (check : Word → Word → Bool) (out : Word → List Word)
    (contains : ∀ s, hullWord check s ∈ out s)
    (x : Word) (k : Nat) (hs : List Word) (sat : ∃ w, Models (check x) k hs w) :
    ∃ A ∈ listFrom out x k hs, Genuine (Models (check x) k hs) A := by
  let r : Request := ⟨x,k,hs⟩
  let answers := oracle check r
  obtain ⟨cert, _, hspan, hmatrix⟩ := recover_basis (oracle_spec check r)
  have hS (v : Bits k) : S check r v ↔ Models (check x) k hs (word v) := by
    simp [S,r,Models,valid]
  have sr : (fun v : Bits k => S check r v) = (fun v => Models (check x) k hs (word v)) :=
    funext (fun v => propext (hS v))
  change ∀ v, ListSpan (cert.val.map lift) v ↔ Span (Lifted (S check r)) v at hspan
  rw [show S check r = _ from sr] at hspan
  obtain ⟨A, ca, good⟩ := true_candidate (n := k) (S := Models (check x) k hs)
    (fun w hw => (by simpa [Models, valid] using hw : w.length=k ∧ _).1)
    sat _ hspan
  refine ⟨A, List.mem_filterMap.mpr ⟨_, contains (requestWord x k hs), ?_⟩, good⟩
  unfold hullWord
  rw [read_requestWord]
  change candidate (readMatrix (k+1) (matrixWord (recover (oracle check r)))) = some A
  rw [read_matrixWord, hmatrix]
  exact ca

end QueryEncoding
