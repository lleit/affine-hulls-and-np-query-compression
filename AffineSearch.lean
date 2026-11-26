module

public import AffinePruning

/-! Deterministic SAT search using a list of candidate hulls. Work in the
current free coordinates and parameterize the retained hyperplane explicitly.
Each cut therefore removes one free variable even if the true dimension is
unknown. Store a history of masks to decode assignments at the original width. -/

@[expose] public section

namespace AffineSearch
abbrev Word := List Bool

def dot : Word → Word → Bool
  | a :: as, b :: bs => (a && b) ^^ dot as bs
  | _, _ => false

@[simp] theorem dot_zero_left (z x : Word) (h : true ∉ z) : dot z x = false := by
  induction z generalizing x with
  | nil => rfl
  | cons b bs ih =>
    have hb : b = false := by cases b <;> simp_all
    have ht : true ∉ bs := fun w => h (List.mem_cons_of_mem _ w)
    cases x <;> simp [hb, dot, ih _ ht]

/-- The first set bit is the pivot. Inserting the dot product of the
remaining coordinates solves the equation over the two-element field. -/
def inflate : Word → Word → Word
  | [], x => x
  | true :: z, x => dot z x :: x
  | false :: z, b :: x => b :: inflate z x
  | false :: _, [] => []

def dropPivot : Word → Word → Word
  | [], x => x
  | true :: _, _ :: x => x
  | false :: z, b :: x => b :: dropPivot z x
  | _ :: _, [] => []

theorem drop_length (z x : Word) (nz : true ∈ z) (h : x.length = z.length) :
    (dropPivot z x).length + 1 = x.length := by
  induction z generalizing x with
  | nil => simp at nz
  | cons a z ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases a <;> simp_all [dropPivot]

theorem inflate_drop (z x : Word) (width : x.length = z.length)
    (zero : dot z x = false) : inflate z (dropPivot z x) = x := by
  induction z generalizing x with
  | nil => rfl
  | cons a z ih =>
    cases x with
    | nil => simp at width
    | cons b x =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at width
      cases a with
      | false => simp [inflate, dropPivot, ih x width (by simpa [dot] using zero)]
      | true =>
        simp only [dot, Bool.true_and] at zero
        cases b <;> cases hv : dot z x <;> simp_all [inflate, dropPivot]

theorem inflate_spec (z x : Word) (nz : true ∈ z) (h : x.length+1 = z.length) :
    (inflate z x).length = z.length ∧ dot z (inflate z x) = false := by
  induction z generalizing x with
  | nil => simp at nz
  | cons a z ih =>
    cases a with
    | true => simp_all [inflate, dot]
    | false =>
      have ht : true ∈ z := by simpa using nz
      cases x with
      | nil =>
        simp only [List.length_nil, List.length_cons] at h
        have hz : z = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hz] at ht
      | cons b x =>
        have hr : x.length + 1 = z.length := by simpa using h
        obtain ⟨hw, hv⟩ := ih x ht hr
        simp [inflate, dot, hw, hv]

/-- Most recent (narrowest-domain) mask first. -/
def decode (history : List Word) (x : Word) : Word :=
  history.foldl (fun w z => inflate z w) x

@[simp] theorem decode_cons (z : Word) (zs : List Word) (x : Word) :
    decode (z :: zs) x = decode zs (inflate z x) := rfl

/-- Each history element is a nonzero mask on the preceding width. -/
inductive History : Nat → Nat → List Word → Prop where
  | start (n) : History n n []
  | cut {n k zs z} : History n (k+1) zs → z.length = k+1 → true ∈ z →
      History n k (z :: zs)

theorem History.width {n k zs} (h : History n k zs) {x : Word} (hw : x.length = k) :
    (decode zs x).length = n := by
  induction h generalizing x with
  | start => exact hw
  | cut prev len nz ih =>
    rw [decode_cons]
    apply ih
    exact ((inflate_spec _ _ nz (by omega)).1).trans len

theorem History.rounds {n k zs} (h : History n k zs) : zs.length + k = n := by
  induction h with
  | start => simp
  | cut prev len nz ih => simp only [List.length_cons]; omega

/-- Total mask bits in the stored description, independent of the size
of every candidate list returned during earlier rounds. -/
theorem History.maskBits {n k zs} (h : History n k zs) :
    (zs.map List.length).sum ≤ zs.length * n := by
  induction h with
  | start => simp
  | cut prev len nz ih =>
    have bound := prev.rounds
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- One optional pivot per coordinate. A pivot row starts with its pivot
and stores only its suffix. Rows deeper in the description have a leading zero. -/
def directions : List (Option Word) → List Word
  | [] => []
  | none :: ps => (directions ps).map (false :: ·)
  | some r :: ps => (true :: r) :: (directions ps).map (false :: ·)

structure Candidate where
  base : Word
  pivots : List (Option Word)
  deriving Repr

def Candidate.basis (a : Candidate) : List Word := directions a.pivots

def translate (a v : Word) := List.zipWith Bool.xor a v

def linearPoints : List (Option Word) → List Word
  | [] => [[]]
  | none :: ps => (linearPoints ps).map (false :: ·)
  | some r :: ps =>
    let tail := linearPoints ps
    tail.map (false :: ·) ++ tail.map (fun x => true :: translate r x)

def Candidate.points (a : Candidate) := (linearPoints a.pivots).map (translate a.base)

theorem linearPoints_length (ps : List (Option Word)) :
    (linearPoints ps).length = 2^(directions ps).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [linearPoints, directions, ih, Nat.pow_succ]; omega

theorem points_length (a : Candidate) : a.points.length = 2^a.basis.length := by
  simp [Candidate.points, Candidate.basis, linearPoints_length]

/-- Compare the number of coefficients with K directly. False candidates
are harmless. Only enumerate a candidate when it has at most K points.
For the other candidates 2^dimension > K already gives the strict union bound. -/
def small (K : Nat) (a : Candidate) : Bool := 2^a.basis.length ≤ K

def probes (K : Nat) (L : List Candidate) := (L.filter (small K)).flatMap Candidate.points

theorem probe_bound (K : Nat) (L : List Candidate) :
    (probes K L).length ≤ L.length * K := by
  induction L with
  | nil => simp [probes]
  | cons a L ih =>
    by_cases h : small K a = true
    · have hp : 2^a.basis.length ≤ K := by simpa [small] using h
      simp [probes, h, points_length, Nat.succ_mul] at *
      omega
    · simp [probes, h, Nat.succ_mul] at *
      omega

def valid (check : Word → Bool) (k : Nat) (hs : List Word) (w : Word) : Bool :=
  w.length == k && check (decode hs w)

def Models (check : Word → Bool) (k : Nat) (hs : List Word) (w : Word) : Prop :=
  valid check k hs w = true

/-- Specification of a genuine hull. Every model occurs and every listed
point satisfies every parity equation shared by the models. -/
def Genuine (S : Word → Prop) (A : Candidate) : Prop :=
  (∀ w, S w → w ∈ A.points) ∧
  (∀ w, w ∈ A.points → AffinePruning.hull dot S w)

def Splits (z : Word) (A : Candidate) : Prop :=
  ∀ b : Bool, ∃ w ∈ A.points, dot z w = b

abbrev Lister := Nat → List Word → List Candidate
abbrev Splitter := Nat → List Candidate → Word

/-- Keep only the masks when advancing to a new round. -/
def search (check : Word → Bool) (listHulls : Lister) (split : Splitter) :
    Nat → List Word → Option Word
  | 0, hs => if check (decode hs []) then some (decode hs []) else none
  | k+1, hs =>
    let L := listHulls (k+1) hs
    match (probes L.length L).find? (valid check (k+1) hs) with
    | some w => some (decode hs w)
    | none =>
      let big := L.filter (fun a => !small L.length a)
      let z := split (k+1) big
      if z.length == k+1 && z.contains true then
        search check listHulls split k (z :: hs)
      else none

theorem search_sound (check : Word → Bool) (listHulls : Lister) (split : Splitter)
    {n k hs} (hist : History n k hs) {x : Word}
    (ans : search check listHulls split k hs = some x) :
    x.length = n ∧ check x = true := by
  induction k generalizing hs with
  | zero =>
    simp only [search] at ans
    split at ans
    · rename_i h
      cases ans
      exact ⟨hist.width rfl, h⟩
    · contradiction
  | succ k ih =>
    rw [search] at ans
    dsimp only at ans
    split at ans
    · rename_i w he
      have hv := List.find?_some he
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at hv
      cases ans
      exact ⟨hist.width hv.1, hv.2⟩
    · split at ans
      · rename_i hz
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hz
        exact ih (.cut hist hz.1 hz.2) ans
      · contradiction

/-- These two contracts isolate the list theorem and splitter theorem.
Both are required only on genuine histories; the splitter contract is
needed only for large candidates in the actual list at that round. -/
theorem search_complete (check : Word → Bool) (listHulls : Lister) (split : Splitter)
    {n : Nat}
    (lists : ∀ k hs, History n k hs → (∃ w, Models check k hs w) →
      ∃ A ∈ listHulls k hs, Genuine (Models check k hs) A)
    (splits : ∀ k hs, History n k hs →
      let L := listHulls k hs
      let big := L.filter (fun a => !small L.length a)
      ∀ A ∈ big, (split k big).length = k ∧ Splits (split k big) A)
    {k hs} (hist : History n k hs) (sat : ∃ w, Models check k hs w) :
    ∃ x, search check listHulls split k hs = some x := by
  induction k generalizing hs with
  | zero =>
    obtain ⟨w, hw⟩ := sat
    simp only [Models, valid, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨hlen,hc⟩ := hw
    have : w = [] := List.length_eq_zero_iff.mp hlen
    subst w
    exact ⟨decode hs [], by simp [search, hc]⟩
  | succ k ih =>
    let L := listHulls (k+1) hs
    let big := L.filter (fun a => !small L.length a)
    let z := split (k+1) big
    obtain ⟨A, hA, cover, exactHull⟩ := lists _ _ hist sat
    change A ∈ L at hA
    rw [search]
    dsimp only
    generalize he : List.find? _ _ = ans
    cases ans with
    | some w => exact ⟨_, rfl⟩
    | none =>
      change (probes L.length L).find? (valid check (k+1) hs) = none at he
      have hlarge : small L.length A = false := by
        cases hh : small L.length A with
        | false => rfl
        | true =>
          obtain ⟨w, hw⟩ := sat
          have hm : w ∈ probes L.length L :=
            List.mem_flatMap.mpr ⟨A, List.mem_filter.mpr ⟨hA, hh⟩, cover w hw⟩
          exact False.elim ((List.find?_eq_none.mp he w hm) hw)
      have hbig : A ∈ big := List.mem_filter.mpr ⟨hA, by simp [hlarge]⟩
      obtain ⟨hlen, hsplit⟩ := splits _ _ hist A hbig
      change z.length = k + 1 at hlen
      obtain ⟨p, hp, h1⟩ := hsplit true
      have nz : true ∈ z := by
        apply Classical.byContradiction
        intro hem
        have hz := dot_zero_left z p hem
        change dot z p = true at h1
        simp [hz] at h1
      obtain ⟨q, hq, h0⟩ := hsplit false
      obtain ⟨w, hw, hz⟩ := AffinePruning.attained_on_witness dot (exactHull q hq) h0
      change dot z w = false at hz
      simp only [Models, valid, Bool.and_eq_true, beq_iff_eq] at hw
      have wh : w.length = z.length := hw.1.trans hlen.symm
      have dlen := drop_length z w nz wh
      have nextSat : Models check k (z :: hs) (dropPivot z w) := by
        simp only [Models, valid, Bool.and_eq_true, beq_iff_eq, decode_cons]
        exact ⟨by omega, by rw [inflate_drop z w wh hz]; exact hw.2⟩
      change ∃ x, (if (z.length == k+1 && z.contains true) then _ else _) = some x
      simp only [hlen, beq_self_eq_true, List.contains_iff_mem.mpr nz,
        Bool.and_self, if_true]
      exact ih (.cut hist hlen nz) ⟨_, nextSat⟩

end AffineSearch
