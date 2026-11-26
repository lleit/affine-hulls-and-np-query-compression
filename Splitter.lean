module

public import Std

/-! A deterministic common parity for explicit affine spaces over the two-element field. -/

@[expose] public section

namespace Splitter

abbrev Word := List Bool
abbrev Schedule := List (Option Word)

def dot : Word → Word → Bool
  | a :: as, b :: bs => (a && b) ^^ dot as bs
  | _, _ => false

def add (a b : Word) : Word := List.zipWith Bool.xor a b

@[simp] theorem dot_nil_left (z : Word) : dot [] z = false := by cases z <;> rfl
@[simp] theorem dot_nil_right (x : Word) : dot x [] = false := by cases x <;> rfl
@[simp] theorem add_cons (a b : Bool) (x y : Word) :
    add (a :: x) (b :: y) = (a ^^ b) :: add x y := rfl
@[simp] theorem length_add (x y : Word) :
    (add x y).length = min x.length y.length := List.length_zipWith

theorem dot_add {x y : Word} (z : Word) (h : x.length = y.length) :
    dot (add x y) z = (dot x z ^^ dot y z) := by
  induction x generalizing y z with
  | nil =>
    cases y with
    | nil => simp [add]
    | cons => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      cases z with
      | nil => simp
      | cons c z =>
        simp only [add_cons, dot, ih _ (by simpa using h)]
        cases a <;> cases b <;> cases c <;>
          cases dot x z <;> cases dot y z <;> decide

/-- A pivot contributes its trailing coefficients. Clear the current column
in all rows and recurse on the trailing columns. -/
def clear (pivot : Option Word) (row : Word) : Word :=
  match pivot with
  | none => row.tail
  | some r => if row.headD false then add r row.tail else row.tail

def echelon : Nat → List Word → Schedule
  | 0, _ => []
  | n + 1, rows =>
    let pivot := (rows.find? (·.headD false)).map List.tail
    pivot :: echelon n (rows.map (clear pivot))

def rank : Schedule → Nat
  | [] => 0
  | none :: rest => rank rest
  | some _ :: rest => rank rest + 1

@[simp] theorem rank_none (rest : Schedule) : rank (none :: rest) = rank rest := rfl
@[simp] theorem rank_some (r : Word) (rest : Schedule) :
    rank (some r :: rest) = rank rest + 1 := rfl

theorem rank_le_length (steps : Schedule) : rank steps ≤ steps.length := by
  induction steps with
  | nil => decide
  | cons p ps ih => cases p <;> simp only [rank_none, rank_some, List.length_cons] <;> omega

theorem rank_append (xs ys : Schedule) : rank (xs ++ ys) = rank xs + rank ys := by
  induction xs with
  | nil => simp [rank]
  | cons x xs ih => cases x <;> simp [ih, Nat.add_right_comm]

@[simp] theorem rank_reverse (xs : Schedule) : rank xs.reverse = rank xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, rank_append, ih]
    cases x <;> simp [rank]

@[simp] theorem length_echelon (n : Nat) (rows : List Word) :
    (echelon n rows).length = n := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih => simp [echelon, ih]

/-- Each occupied column solves its equation in terms of later coordinates. -/
def equation (p : Option Word) (b : Bool) (suffix : Word) : Prop :=
  match p with
  | none => True
  | some r => b = dot r suffix

def satisfies : Schedule → Word → Prop
  | [], _ => True
  | _ :: _, [] => False
  | p :: ps, b :: suffix => equation p b suffix ∧ satisfies ps suffix

def orthogonal (rows : List Word) (z : Word) : Prop :=
  ∀ row ∈ rows, dot row z = false

private theorem clear_length {n : Nat} {p : Option Word} {r : Word}
    (hr : r.length = n + 1) (hp : ∀ t, p = some t → t.length = n) :
    (clear p r).length = n := by
  cases r with
  | nil => simp at hr
  | cons b r =>
    have hl : r.length = n := by simpa using hr
    cases p with
    | none => exact hl
    | some t => cases b <;> simp [clear, hl, hp t rfl]

private theorem clear_dot {n : Nat} {p : Option Word} {r : Word}
    (hr : r.length = n + 1) (hp : ∀ t, p = some t → t.length = n)
    (b : Bool) (z : Word) (he : equation p b z)
    (hn : p = none → r.headD false = false) :
    dot (clear p r) z = dot r (b :: z) := by
  cases r with
  | nil => simp at hr
  | cons a r =>
    have hl : r.length = n := by simpa using hr
    cases p with
    | none =>
      have ha : a = false := hn rfl
      simp [ha, clear, dot]
    | some t =>
      change b = dot t z at he
      cases a with
      | false => simp [clear, dot]
      | true =>
        simp [clear, dot, dot_add z ((hp t rfl).trans hl.symm), he]

theorem echelon_spec {n : Nat} {rows : List Word} {z : Word}
    (hz : z.length = n) (hw : ∀ row ∈ rows, row.length = n) :
    satisfies (echelon n rows) z ↔ orthogonal rows z := by
  induction n generalizing rows z with
  | zero =>
    have hz' : z = [] := List.length_eq_zero_iff.mp hz
    simp [hz', satisfies, echelon, orthogonal]
  | succ n ih =>
    cases z with
    | nil => simp at hz
    | cons b z =>
      let source := rows.find? (·.headD false)
      let pivot := source.map List.tail
      have hp : ∀ t, pivot = some t → t.length = n := by
        intro t ht
        cases h : source with
        | none => simp [pivot, h] at ht
        | some r =>
          have hr := hw r (List.mem_of_find?_eq_some h)
          cases r with
          | nil => simp at hr
          | cons a r => simpa [pivot, h, ← (show r = t by simpa [pivot, h] using ht)] using hr
      have hn : ∀ r ∈ rows, pivot = none → r.headD false = false := by
        intro r hm hz'
        have hs : source = none := by
          cases h : source <;> simp_all [pivot]
        simpa using List.find?_eq_none.mp hs r hm
      have he : orthogonal rows (b :: z) → equation pivot b z := by
        intro h
        cases hs : source with
        | none => simp [pivot, hs, equation]
        | some r =>
          have ha := List.find?_some hs
          have hd := h r (List.mem_of_find?_eq_some hs)
          cases r with
          | nil => simp [List.headD] at ha
          | cons a r =>
            have ht : a = true := ha
            subst a
            simp only [dot, Bool.true_and] at hd
            have hd' : b = dot r z := by
              cases b <;> cases hv : dot r z <;> simp_all
            simpa [pivot, hs, equation] using hd'
      change (equation pivot b z ∧ satisfies (echelon n (rows.map (clear pivot))) z) ↔ _
      rw [ih (by simpa using hz)]
      · constructor
        · rintro ⟨hb, ht⟩ r hm
          rw [← clear_dot (hw r hm) hp b z hb (hn r hm)]
          exact ht _ (List.mem_map.mpr ⟨r, hm, rfl⟩)
        · intro h
          refine ⟨he h, ?_⟩
          intro t ht
          obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ht
          rw [clear_dot (hw r hm) hp b z (he h) (hn r hm)]
          exact h _ hm
      · intro t ht
        obtain ⟨r, hm, rfl⟩ := List.mem_map.mp ht
        exact clear_length (hw r hm) hp

structure Candidate where
  /-- Columns to consider, from last to first. -/
  steps : Schedule
  weight : Nat

def advance (b : Bool) (suffix : Word) (c : Candidate) : Candidate :=
  match c.steps with
  | [] => c
  | none :: ps => ⟨ps, c.weight⟩
  | some row :: ps => ⟨ps, if b == dot row suffix then c.weight + c.weight else 0⟩

def score (cs : List Candidate) : Nat := (cs.map Candidate.weight).sum

def branch (b : Bool) (suffix : Word) (cs : List Candidate) : List Candidate :=
  cs.map (advance b suffix)

def choose (suffix : Word) (cs : List Candidate) : Bool × List Candidate :=
  let left := branch false suffix cs
  let right := branch true suffix cs
  if score left ≤ score right then (false, left) else (true, right)

/-- Fill the mask from right to left. The second result is used to state the
invariant about the remaining candidate weights. -/
def search : Nat → Word → List Candidate → Word × List Candidate
  | 0, suffix, cs => (suffix, cs)
  | n + 1, suffix, cs =>
    let (b, next) := choose suffix cs
    search n (b :: suffix) next

private theorem advance_weights (suffix : Word) (c : Candidate) :
    (advance false suffix c).weight + (advance true suffix c).weight =
      c.weight + c.weight := by
  cases c with
  | mk ps w =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases p with
      | none => rfl
      | some row => cases h : dot row suffix <;> simp [advance, h]

theorem score_branches (suffix : Word) (cs : List Candidate) :
    score (branch false suffix cs) + score (branch true suffix cs) =
      2 * score cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ((advance false suffix c).weight + score (branch false suffix cs)) +
        ((advance true suffix c).weight + score (branch true suffix cs)) =
      2 * (c.weight + score cs)
    have h := advance_weights suffix c
    omega

private theorem choose_spec (suffix : Word) (cs : List Candidate) :
    ∃ b, choose suffix cs = (b, branch b suffix cs) ∧
      score (branch b suffix cs) ≤ score cs := by
  have h := score_branches suffix cs
  dsimp only [choose]
  split
  · exact ⟨false, rfl, by omega⟩
  · exact ⟨true, rfl, by omega⟩

private theorem weight_le_score {c : Candidate} {cs : List Candidate} (h : c ∈ cs) :
    c.weight ≤ score cs := by
  induction cs with
  | nil => simp at h
  | cons d cs ih =>
    change c.weight ≤ d.weight + score cs
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have := ih hm
      omega

private theorem satisfies_append {ps : Schedule} {pre : Word}
    (h : ps.length = pre.length) (qs : Schedule) (zs : Word) :
    satisfies (ps ++ qs) (pre ++ zs) ↔
      satisfies ps (pre ++ zs) ∧ satisfies qs zs := by
  induction ps generalizing pre with
  | nil =>
    have hp : pre = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    simp [hp, satisfies]
  | cons p ps ih =>
    cases pre with
    | nil => simp at h
    | cons b pre =>
      simp only [List.cons_append, satisfies, ih (by simpa using h), and_assoc]

private theorem advance_keeps {p : Option Word} {ps : Schedule} {b : Bool}
    {suffix : Word} {w : Nat} (h : equation p b suffix) :
    w * 2 ^ rank (p :: ps) =
      (advance b suffix ⟨p :: ps, w⟩).weight * 2 ^ rank ps := by
  cases p with
  | none => rfl
  | some r =>
    change b = dot r suffix at h
    simp [advance, h, Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_two]

theorem search_spec (n : Nat) (suffix : Word) (cs : List Candidate)
    (width : ∀ c ∈ cs, c.steps.length = n) :
    let out := search n suffix cs
    (∃ pre : Word, pre.length = n ∧ out.1 = pre ++ suffix) ∧
      score out.2 ≤ score cs ∧
      ∀ c ∈ cs, satisfies c.steps.reverse out.1 →
        c.weight * 2 ^ rank c.steps ≤ score out.2 := by
  induction n generalizing suffix cs with
  | zero =>
    refine ⟨⟨[], rfl, rfl⟩, Nat.le_refl _, ?_⟩
    intro c hm _
    have hc : c.steps = [] := List.length_eq_zero_iff.mp (width c hm)
    simpa [search, hc, rank] using weight_le_score hm
  | succ n ih =>
    obtain ⟨b, hb, hscore⟩ := choose_spec suffix cs
    have hwidth : ∀ c ∈ branch b suffix cs, c.steps.length = n := by
      intro c hm
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      have h := width d hd
      cases d with
      | mk ps w =>
        cases ps with
        | nil => simp at h
        | cons p ps => cases p <;> simpa [advance] using h
    obtain ⟨⟨pre, hpre, hz⟩, hs, hall⟩ := ih (b :: suffix) (branch b suffix cs) hwidth
    dsimp only
    rw [search, hb]
    refine ⟨⟨pre ++ [b], by simp [hpre], by simpa [List.append_assoc] using hz⟩,
      Nat.le_trans hs hscore, ?_⟩
    intro c hc hsat
    have h := width c hc
    cases c with
    | mk ps w =>
      cases ps with
      | nil => simp at h
      | cons p ps =>
        have len : ps.reverse.length = pre.length := by simp_all
        have hsat' : satisfies ps.reverse (pre ++ b :: suffix) ∧ equation p b suffix := by
          simpa [hz, List.reverse_cons, satisfies_append len [p] (b :: suffix), satisfies]
            using hsat
        have hm : advance b suffix ⟨p :: ps, w⟩ ∈ branch b suffix cs :=
          List.mem_map.mpr ⟨_, hc, rfl⟩
        have htail : (advance b suffix ⟨p :: ps, w⟩).steps = ps := by
          cases p <;> rfl
        have hp := hall _ hm (by simpa [hz, htail] using hsat'.1)
        rw [htail] at hp
        change w * 2 ^ rank (p :: ps) ≤ _
        rw [advance_keeps hsat'.2]
        exact hp

/-- The affine points obtained by adding any subset of the direction rows to
the offset. -/
inductive AffinePoint : List Word → Word → Word → Prop where
  | base (a : Word) : AffinePoint [] a a
  | skip {r rs a x} : AffinePoint rs a x → AffinePoint (r :: rs) a x
  | take {r rs a x} : AffinePoint rs a x → AffinePoint (r :: rs) a (add r x)

structure Space where
  offset : Word
  directions : List Word

def Space.WellFormed (s : Space) (n : Nat) : Prop :=
  s.offset.length = n ∧ ∀ row ∈ s.directions, row.length = n

def Space.contains (s : Space) (x : Word) : Prop :=
  AffinePoint s.directions s.offset x

def Space.splitBy (s : Space) (z : Word) : Prop :=
  ∀ b : Bool, ∃ x, s.contains x ∧ dot x z = b

theorem AffinePoint.offset (rows : List Word) (a : Word) : AffinePoint rows a a := by
  induction rows with
  | nil => exact .base a
  | cons _ _ ih => exact .skip ih

theorem AffinePoint.direction {r : Word} {rows : List Word} (a : Word) (h : r ∈ rows) :
    AffinePoint rows a (add r a) := by
  induction rows with
  | nil => simp at h
  | cons s rs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact .take (AffinePoint.offset rs a)
    · exact .skip (ih h)

private theorem affine_orthogonal {rows : List Word} {a x z : Word}
    (p : AffinePoint rows a x) (hw : ∀ r ∈ rows, r.length = a.length)
    (h : orthogonal rows z) : x.length = a.length ∧ dot x z = dot a z := by
  induction p with
  | base => simp
  | skip _ ih =>
    exact ih (fun r hr => hw r (List.mem_cons_of_mem _ hr))
      (fun r hr => h r (List.mem_cons_of_mem _ hr))
  | @take r rs a x _ ih =>
    obtain ⟨hlen, hdot⟩ := ih (fun r hr => hw r (List.mem_cons_of_mem _ hr))
      (fun r hr => h r (List.mem_cons_of_mem _ hr))
    have hr := hw r List.mem_cons_self
    rw [length_add, dot_add z (hr.trans hlen.symm), h r List.mem_cons_self, hdot, hr, hlen]
    simp

private theorem orthogonal_or_direction (rows : List Word) (z : Word) :
    orthogonal rows z ∨ ∃ r ∈ rows, dot r z = true := by
  induction rows with
  | nil => exact Or.inl (by simp [orthogonal])
  | cons r rs ih =>
    cases h : dot r z with
    | true => exact Or.inr ⟨r, List.mem_cons_self, h⟩
    | false =>
      rcases ih with good | ⟨s, hs, hv⟩
      · exact Or.inl (fun s hs => (List.mem_cons.mp hs).elim (· ▸ h) (good s))
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hv⟩

theorem Space.split_iff {s : Space} {n : Nat} {z : Word} (h : s.WellFormed n) :
    s.splitBy z ↔ ¬ orthogonal s.directions z := by
  constructor
  · intro both good
    obtain ⟨x, hx, hdot⟩ := both (!dot s.offset z)
    have he := (affine_orthogonal hx (fun r hr => (h.2 r hr).trans h.1.symm) good).2
    cases hv : dot s.offset z <;> simp_all
  · intro bad b
    obtain good | ⟨r, hr, hv⟩ := orthogonal_or_direction s.directions z
    · exact False.elim (bad good)
    have hd := dot_add z ((h.2 r hr).trans h.1.symm)
    rw [hv] at hd
    by_cases hb : dot s.offset z = b
    · exact ⟨s.offset, AffinePoint.offset _ _, hb⟩
    · refine ⟨add r s.offset, AffinePoint.direction _ hr, ?_⟩
      rw [hd]
      cases b <;> cases hval : dot s.offset z <;> simp_all

def Space.dimension (n : Nat) (s : Space) : Nat :=
  rank (echelon n s.directions)

def prepare (n : Nat) (s : Space) : Candidate :=
  let steps := echelon n s.directions
  ⟨steps.reverse, 1 <<< (n - rank steps)⟩

/-- Compute a common splitting mask by minimizing the sum of the conditional
failure probabilities, scaled by (2^n). -/
def split (n : Nat) (spaces : List Space) : Word :=
  (search n [] (spaces.map (prepare n))).1

theorem score_prepare (n d : Nat) (spaces : List Space)
    (high : ∀ s ∈ spaces, d ≤ s.dimension n) :
    score (spaces.map (prepare n)) ≤ spaces.length * 2 ^ (n - d) := by
  induction spaces with
  | nil => simp [score]
  | cons s ss ih =>
    have h := high s List.mem_cons_self
    have ht := ih (fun a ha => high a (List.mem_cons_of_mem _ ha))
    have hp : 2 ^ (n - s.dimension n) ≤ 2 ^ (n - d) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left h n)
    change (1 <<< (n - s.dimension n)) + score (ss.map (prepare n)) ≤
      (ss.length + 1) * 2 ^ (n - d)
    rw [Nat.one_shiftLeft, Nat.add_mul, Nat.one_mul]
    omega

theorem split_spec_of_score (n : Nat) (spaces : List Space)
    (wellFormed : ∀ s ∈ spaces, s.WellFormed n)
    (budget : score (spaces.map (prepare n)) < 2 ^ n) :
    (split n spaces).length = n ∧ ∀ s ∈ spaces, s.splitBy (split n spaces) := by
  have hwidth : ∀ c ∈ spaces.map (prepare n), c.steps.length = n := by
    intro c hc
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
    simp [prepare]
  obtain ⟨⟨pre, hpre, hz⟩, hscore, hall⟩ := search_spec n [] _ hwidth
  have hlen : (split n spaces).length = n := by
    simpa [split, hz] using hpre
  refine ⟨hlen, ?_⟩
  intro s hs
  apply (Space.split_iff (wellFormed s hs)).mpr
  intro good
  have hsat : satisfies (prepare n s).steps.reverse (split n spaces) := by
    simpa [prepare] using (echelon_spec hlen (wellFormed s hs).2).mpr good
  have hh := hall _ (List.mem_map.mpr ⟨s, hs, rfl⟩) hsat
  have hdim : s.dimension n ≤ n := by simpa [Space.dimension] using rank_le_length (echelon n s.directions)
  have hweight : (prepare n s).weight * 2 ^ rank (prepare n s).steps = 2 ^ n := by
    simp only [prepare, rank_reverse, Nat.one_shiftLeft, ← Nat.pow_add]
    congr 1
    change n - s.dimension n + s.dimension n = n
    omega
  rw [hweight] at hh
  omega

/-- A list of fewer than (2^d) spaces of dimension at least (d) has a
common splitting parity. The result is the mask computed by `split`. -/
theorem split_spec (n d : Nat) (spaces : List Space)
    (wellFormed : ∀ s ∈ spaces, s.WellFormed n)
    (high : ∀ s ∈ spaces, d ≤ s.dimension n)
    (few : spaces.length < 2 ^ d) :
    (split n spaces).length = n ∧ ∀ s ∈ spaces, s.splitBy (split n spaces) := by
  apply split_spec_of_score n spaces wellFormed
  cases spaces with
  | nil => simpa [score] using Nat.two_pow_pos n
  | cons s ss =>
    have hdim : s.dimension n ≤ n := by simpa [Space.dimension] using rank_le_length (echelon n s.directions)
    have hdn : d ≤ n := Nat.le_trans (high s List.mem_cons_self) hdim
    have hpow : 2 ^ d * 2 ^ (n - d) = 2 ^ n := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hdn]
    apply Nat.lt_of_le_of_lt (score_prepare n d _ high)
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_right few (Nat.two_pow_pos _)

/-- A reference enumeration of the homogeneous system's kernel. This
enumeration is used in the rank certificate and is absent from `split`. -/
def kernel : Schedule → List Word
  | [] => [[]]
  | none :: ps =>
    let tail := kernel ps
    tail.map (false :: ·) ++ tail.map (true :: ·)
  | some r :: ps => (kernel ps).map (fun z => dot r z :: z)

theorem mem_kernel {ps : Schedule} {z : Word} :
    z ∈ kernel ps ↔ z.length = ps.length ∧ satisfies ps z := by
  induction ps generalizing z with
  | nil => simp [kernel, satisfies]
  | cons p ps ih =>
    cases z with
    | nil => cases p <;> simp [kernel]
    | cons b z =>
      cases p with
      | none =>
        cases b <;> simp [kernel, satisfies, equation, ih]
      | some r =>
        simp only [kernel, List.mem_map, List.cons.injEq, List.length_cons,
          Nat.add_right_cancel_iff, satisfies, equation]
        constructor
        · rintro ⟨_, hm, hb, rfl⟩
          exact ⟨(ih.mp hm).1, hb.symm, (ih.mp hm).2⟩
        · rintro ⟨hlen, hb, hs⟩
          exact ⟨z, ih.mpr ⟨hlen, hs⟩, hb.symm, rfl⟩

theorem length_kernel (ps : Schedule) :
    (kernel ps).length = 2 ^ (ps.length - rank ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | none =>
      simp only [kernel, List.length_append, List.length_map, ih, List.length_cons, rank_none]
      rw [show ps.length + 1 - rank ps = (ps.length - rank ps) + 1 by
        have := rank_le_length ps
        omega, Nat.pow_succ, Nat.mul_two]
    | some r => simp [kernel, ih]

private theorem nodup_prepend {head : Word → Bool} {zs : List Word}
    (h : zs.Nodup) : (zs.map (fun z => head z :: z)).Nodup := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    rcases List.nodup_cons.mp h with ⟨hn, hzs⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hzs⟩
    rintro hm
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    exact hn ((List.cons.inj he).2 ▸ hw)

private theorem nodup_prepend_both {zs : List Word} (h : zs.Nodup) :
    (zs.map (false :: ·) ++ zs.map (true :: ·)).Nodup := by
  have aux {xs ys : List Word} (hx : xs.Nodup) (hy : ys.Nodup)
      (hd : ∀ x ∈ xs, x ∉ ys) : (xs ++ ys).Nodup := by
    induction xs with
    | nil => exact hy
    | cons x xs ih =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hx
      exact List.nodup_cons.mpr ⟨fun hm => (List.mem_append.mp hm).elim hn (hd x List.mem_cons_self),
        ih ht (fun y hy => hd y (List.mem_cons_of_mem _ hy))⟩
  apply aux (nodup_prepend h) (nodup_prepend h)
  intro x hx hy
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨_, _, he⟩ := List.mem_map.mp hy
  cases he

theorem nodup_kernel (ps : Schedule) : (kernel ps).Nodup := by
  induction ps with
  | nil => simp [kernel]
  | cons p ps ih =>
    cases p with
    | none => exact nodup_prepend_both ih
    | some r => exact nodup_prepend ih

/-- The dimension is certified by the exact cardinality of the annihilator,
expressed as a duplicate-free enumeration of its width-`n` masks. -/
theorem Space.annihilator_size (s : Space) (n : Nat) (hw : s.WellFormed n) :
    ∃ zs : List Word, zs.Nodup ∧ zs.length = 2 ^ (n - s.dimension n) ∧
      ∀ z, z ∈ zs ↔ z.length = n ∧ orthogonal s.directions z := by
  refine ⟨kernel (echelon n s.directions), nodup_kernel _, ?_, ?_⟩
  · simpa [Space.dimension] using length_kernel (echelon n s.directions)
  · intro z
    rw [mem_kernel, length_echelon]
    exact and_congr_right (fun hz => echelon_spec hz hw.2)

/-! ## Work bounds

The work measure counts coordinate visits, list element visits, and natural
number operations at unit cost. Each term budgets the passes in the
corresponding executable definition. A separate bound limits the size of the
natural numbers that carry the conditional weights. -/

def rowBits (rows : List Word) : Nat := (rows.map List.length).sum

/-- At every column, budget one pivot scan, one clear pass, and at most one
coordinate visit per row bit for the XORs. -/
def echelonWork : Nat → List Word → Nat
  | 0, _ => 1
  | n + 1, rows =>
    let pivot := (rows.find? (·.headD false)).map List.tail
    1 + 2 * rows.length + rowBits rows + echelonWork n (rows.map (clear pivot))

private theorem rowBits_bound (rows : List Word) (width : Nat)
    (h : ∀ r ∈ rows, r.length ≤ width) : rowBits rows ≤ width * rows.length := by
  induction rows with
  | nil => simp [rowBits]
  | cons r rs ih =>
    have hf := h r List.mem_cons_self
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    change r.length + rowBits rs ≤ width * (rs.length + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem clear_le_length (p : Option Word) (r : Word) :
    (clear p r).length ≤ r.length := by
  have h : r.tail.length ≤ r.length := by simp
  cases p with
  | none => exact h
  | some t =>
    cases r with
    | nil => simp [clear]
    | cons b rs =>
      cases b with
      | false => exact h
      | true =>
        change (add t rs).length ≤ rs.length + 1
        rw [length_add]
        exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_succ _)

theorem echelonWork_bound (fuel : Nat) (rows : List Word) (width : Nat)
    (h : ∀ r ∈ rows, r.length ≤ width) :
    echelonWork fuel rows ≤ 1 + fuel * (1 + (width + 2) * rows.length) := by
  induction fuel generalizing rows with
  | zero => simp [echelonWork]
  | succ n ih =>
    let pivot := (rows.find? (·.headD false)).map List.tail
    have htail := ih (rows.map (clear pivot)) (by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact Nat.le_trans (clear_le_length pivot s) (h s hs))
    have hbits := rowBits_bound rows width h
    change 1 + 2 * rows.length + rowBits rows + echelonWork n (rows.map (clear pivot)) ≤ _
    rw [List.length_map] at htail
    rw [Nat.succ_mul n (1 + (width + 2) * rows.length), Nat.add_mul width 2]
    rw [Nat.add_mul width 2] at htail
    omega

/-- Each bit costs two branch passes, two weight maps and two sums. Each
branch evaluates at most one dot product per space against the current suffix. -/
def choiceWork (suffix : Word) (cs : List Candidate) : Nat :=
  1 + (6 + 2 * suffix.length) * cs.length

def searchWork : Nat → Word → List Candidate → Nat
  | 0, _, _ => 1
  | n + 1, suffix, cs =>
    let (b, next) := choose suffix cs
    choiceWork suffix cs + searchWork n (b :: suffix) next

theorem searchWork_bound (n : Nat) (suffix : Word) (cs : List Candidate) (width : Nat)
    (hw : suffix.length + n ≤ width) :
    searchWork n suffix cs ≤ 1 + n * (1 + (6 + 2 * width) * cs.length) := by
  induction n generalizing suffix cs with
  | zero => simp [searchWork]
  | succ n ih =>
    obtain ⟨b, hb, _⟩ := choose_spec suffix cs
    have htail := ih (b :: suffix) (branch b suffix cs) (by simp only [List.length_cons]; omega)
    have hchoice : choiceWork suffix cs ≤ 1 + (6 + 2 * width) * cs.length := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_right
      omega
    rw [searchWork, hb, Nat.succ_mul n (1 + (6 + 2 * width) * cs.length)]
    have hlen : (branch b suffix cs).length = cs.length := List.length_map _
    dsimp only
    rw [hlen] at htail
    omega

/-- Include the length-`n` rank and reverse passes and the binary weight
initialization in the preparation budget. -/
def prepareWork (n : Nat) (s : Space) : Nat := echelonWork n s.directions + 3 * (n + 1)

def totalRows (spaces : List Space) : Nat := (spaces.map (fun s => s.directions.length)).sum

def totalWork (n : Nat) (spaces : List Space) : Nat :=
  (spaces.map (fun s => 1 + prepareWork n s)).sum + searchWork n [] (spaces.map (prepare n))

theorem split_work_bound (n : Nat) (spaces : List Space)
    (hw : ∀ s ∈ spaces, s.WellFormed n) :
    totalWork n spaces ≤
      spaces.length * (4 * n + 5) + (n * (n + 2)) * totalRows spaces +
        (1 + n * (1 + (6 + 2 * n) * spaces.length)) := by
  have he : (spaces.map (fun s => 1 + prepareWork n s)).sum ≤
      spaces.length * (4 * n + 5) + (n * (n + 2)) * totalRows spaces := by
    induction spaces with
    | nil => simp [totalRows]
    | cons s ss ih =>
      have h := echelonWork_bound n s.directions n
        (fun r hr => Nat.le_of_eq ((hw s List.mem_cons_self).2 r hr))
      have ht := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
      change 1 + (echelonWork n s.directions + 3 * (n + 1)) +
          (ss.map (fun s => 1 + prepareWork n s)).sum ≤
        (ss.length + 1) * (4 * n + 5) +
          (n * (n + 2)) * (s.directions.length + totalRows ss)
      rw [Nat.add_mul ss.length 1, Nat.one_mul,
        Nat.mul_add (n * (n + 2)) s.directions.length (totalRows ss)]
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at h
      omega
  have hs := searchWork_bound n [] (spaces.map (prepare n)) n (by simp)
  rw [List.length_map] at hs
  exact Nat.add_le_add he hs

/-- Bound both branch scores at every recursive call reached by the search.
Each weight added to a score and each partial sum is bounded by that score. -/
def SearchWithin (cap : Nat) : Nat → Word → List Candidate → Prop
  | 0, _, cs => score cs ≤ cap
  | k + 1, suffix, cs =>
    score cs ≤ cap ∧ score (branch false suffix cs) ≤ 2 * cap ∧
      score (branch true suffix cs) ≤ 2 * cap ∧
      (let (b, next) := choose suffix cs
       SearchWithin cap k (b :: suffix) next)

theorem search_within (cap fuel : Nat) (suffix : Word) (cs : List Candidate)
    (h : score cs ≤ cap) : SearchWithin cap fuel suffix cs := by
  induction fuel generalizing suffix cs with
  | zero => exact h
  | succ n ih =>
    obtain ⟨b, hb, hbest⟩ := choose_spec suffix cs
    have he := score_branches suffix cs
    refine ⟨h, by omega, by omega, ?_⟩
    rw [hb]
    exact ih _ _ (Nat.le_trans hbest h)

theorem split_counter_bound (n : Nat) (spaces : List Space) :
    let cap := spaces.length * 2 ^ n
    SearchWithin cap n [] (spaces.map (prepare n)) ∧
      2 * cap < 2 ^ (n + spaces.length.log2 + 2) := by
  have h := score_prepare n 0 spaces (fun _ _ => Nat.zero_le _)
  rw [Nat.sub_zero] at h
  refine ⟨search_within _ _ _ _ h, ?_⟩
  calc
    2 * (spaces.length * 2 ^ n) = spaces.length * (2 ^ n * 2) := by
      ac_rfl
    _ < 2 ^ (spaces.length.log2 + 1) * (2 ^ n * 2) :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.mul_pos (Nat.two_pow_pos _) (by decide))
    _ = 2 ^ (n + spaces.length.log2 + 2) := by
      rw [← Nat.pow_succ, ← Nat.pow_add]
      congr 1
      omega

end Splitter
