module

public import AffineSearch

@[expose] public section

namespace AffineSearch

inductive Shaped : Nat → List (Option Word) → Prop where
  | nil : Shaped 0 []
  | free : Shaped k ps → Shaped (k+1) (none :: ps)
  | pivot : r.length = k → Shaped k ps → Shaped (k+1) (some r :: ps)

theorem Shaped.length {n ps} (h : Shaped n ps) : ps.length = n := by
  induction h <;> simp_all

@[simp] theorem translate_length (a x : Word) :
    (translate a x).length = min a.length x.length := List.length_zipWith

theorem translate_zero (v : Word) :
    translate v (List.replicate v.length false) = v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change _ :: _ = a :: v
    cases a <;> simpa [translate] using ih

theorem translate_self_left {x y : Word} (h : x.length = y.length) :
    translate x (translate x y) = y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [translate]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have ht := ih (y := y) (by simpa using h)
      change (a ^^ (a ^^ b)) :: translate x (translate x y) = b :: y
      cases a <;> cases b <;> simp [ht]

theorem dot_translate (z a x : Word) (h : a.length = x.length) :
    dot z (translate a x) = (dot z a ^^ dot z x) := by
  induction a generalizing x z with
  | nil => cases x <;> cases z <;> simp_all [dot, translate]
  | cons a as ih =>
    cases x with
    | nil => simp at h
    | cons b bs =>
      cases z with
      | nil => rfl
      | cons c cs =>
        change ((c && (a ^^ b)) ^^ dot cs (translate as bs)) = _
        rw [ih cs bs (by simpa using h)]
        simp only [dot]
        cases a <;> cases b <;> cases c <;> cases dot cs as <;> cases dot cs bs <;> rfl

theorem Shaped.points_width {n ps} (h : Shaped n ps) {x : Word}
    (mem : x ∈ linearPoints ps) : x.length = n := by
  induction h generalizing x with
  | nil => simpa [linearPoints] using congrArg List.length (show x = [] by simpa [linearPoints] using mem)
  | free h ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp mem
    simp [ih hw]
  | pivot hr h ih =>
    rcases List.mem_append.mp mem with lo | hi
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp lo
      simp [ih hw]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      simp [ih hw, hr]

theorem Shaped.zero_mem {n ps} (h : Shaped n ps) :
    List.replicate n false ∈ linearPoints ps := by
  induction h with
  | nil => simp [linearPoints]
  | free h ih =>
    exact List.mem_map_of_mem ih
  | pivot hr h ih => exact List.mem_append_left _ (List.mem_map_of_mem ih)

theorem Shaped.directions_mem {n ps} (h : Shaped n ps) {v : Word}
    (mem : v ∈ directions ps) : v ∈ linearPoints ps := by
  induction h generalizing v with
  | nil => simp [directions] at mem
  | free h ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp mem
    exact List.mem_map_of_mem (ih hw)
  | pivot hr h ih =>
    rcases List.mem_cons.mp mem with rfl | later
    · apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨_, h.zero_mem, by rw [← hr, translate_zero]⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp later
      exact List.mem_append_left _ (List.mem_map_of_mem (ih hw))

theorem candidate_splits {k : Nat} {A : Candidate} {z v : Word}
    (width : Shaped k A.pivots) (anchor : A.base.length = k)
    (mem : v ∈ A.basis) (hv : dot z v = true) : Splits z A := by
  have vmem := width.directions_mem mem
  have vlen := width.points_width vmem
  have ha : A.base ∈ A.points := List.mem_map.mpr
    ⟨_, width.zero_mem, by rw [← anchor, translate_zero]⟩
  have hb : translate A.base v ∈ A.points := List.mem_map_of_mem vmem
  have flip := dot_translate z A.base v (anchor.trans vlen.symm)
  rw [hv] at flip
  intro b
  cases he : dot z A.base <;> cases b
  · exact ⟨_, ha, he⟩
  · exact ⟨_, hb, by simpa [he] using flip⟩
  · exact ⟨_, hb, by simpa [he] using flip⟩
  · exact ⟨_, ha, he⟩

end AffineSearch
