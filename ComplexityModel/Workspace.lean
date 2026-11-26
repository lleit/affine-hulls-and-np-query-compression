module

public import ComplexityModelTranscripts

@[expose] public section

namespace ComplexityModel

/-- Bounds both the size of each word and the number of queued words. -/
def State.Bounded (s : State) (n : Nat) : Prop :=
  s.Fits n ∧ s.queries.length ≤ n

theorem State.Bounded.mono {s : State} (h : s.Bounded m) (hle : m ≤ n) : s.Bounded n :=
  ⟨h.1.mono hle, Nat.le_trans h.2 hle⟩

theorem State.Bounded.write {s : State} (h : s.Bounded n) (hw : w.length ≤ n) :
    (s.write d w).Bounded n :=
  ⟨s.write_fits h.1 hw, h.2⟩

theorem State.Bounded.drop {s : State} (h : s.Bounded n) : s.drop.Bounded n := by
  refine ⟨State.drop_fits h.1, ?_⟩
  simp only [State.drop, List.length_tail]
  have := h.2
  omega

theorem State.Bounded.push {s : State} (h : s.Bounded n) : (s.push r).Bounded (n + 1) :=
  ⟨(State.push_fits h.1).mono (Nat.le_succ _), Nat.succ_le_succ h.2⟩

theorem State.input_bounded {x w : Word} (hx : x.length ≤ n) (hw : w.length ≤ n) :
    (State.input x w).Bounded n :=
  ⟨State.input_fits hx hw, Nat.zero_le _⟩

theorem Source.advance_bounded (src : Source) {s : State} (h : s.Bounded n) :
    (src.advance s).Bounded n := by
  cases src
  · exact h
  · exact h.drop

def Frame.Bounded (n : Nat) : Frame → Prop
  | .next _ => True
  | .callResult s _ => s.Bounded n

theorem Frame.Bounded.mono {f : Frame} (h : f.Bounded m) (hle : m ≤ n) : f.Bounded n := by
  cases f
  · trivial
  · exact State.Bounded.mono h hle

def Config.Bounded (c : Config) (n : Nat) : Prop :=
  match c with
  | .exec _ s frames | .resume s frames =>
    s.Bounded n ∧ (∀ frame ∈ frames, frame.Bounded n) ∧ frames.length ≤ n

def Event.Bounded (e : Event) (n : Nat) : Prop :=
  match e with
  | .halt s => s.Bounded n
  | .next d => d.Bounded n
  | .question w no yes => w.length ≤ n ∧ no.Bounded n ∧ yes.Bounded n

theorem Config.input_bounded (c : Code) (x : Word) :
    (Config.exec c (State.input x) []).Bounded x.length :=
  ⟨State.input_bounded (Nat.le_refl _) (Nat.zero_le _), by simp, Nat.zero_le _⟩

/-- Ordinary instructions and either answer to an oracle query increase the
uniform workspace bound by at most one. Each frame contains only a code
pointer or a suspended caller. -/
theorem Config.step_bounded {c : Config} (h : c.Bounded n) : c.step.Bounded (n + 1) := by
  have le : n ≤ n + 1 := Nat.le_succ _
  have singleton (b : Bool) : ([b] : Word).length ≤ n + 1 := by simp
  cases c with
  | exec code s frames =>
    obtain ⟨hs, hf, hl⟩ := h
    have hs' := hs.mono le
    have hf' : ∀ frame ∈ frames, frame.Bounded (n + 1) :=
      fun frame mem => (hf frame mem).mono le
    have hl' := Nat.le_trans hl le
    cases code with
    | skip => exact ⟨hs', hf', hl'⟩
    | write d e => exact ⟨hs'.write (e.eval_fits hs.1), hf', hl'⟩
    | push r => exact ⟨hs.push, hf', hl'⟩
    | pop d => exact ⟨hs'.drop.write (State.head_fits hs'.1), hf', hl'⟩
    | seq a b =>
      refine ⟨hs', ?_, Nat.succ_le_succ hl⟩
      intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · trivial
      · exact hf' f hm
    | branch test yes no => exact ⟨hs', hf', hl'⟩
    | loop test body =>
      simp only [Config.step]
      split
      · refine ⟨hs', ?_, Nat.succ_le_succ hl⟩
        intro f hm
        rcases List.mem_cons.mp hm with rfl | hm
        · trivial
        · exact hf' f hm
      · exact ⟨hs', hf', hl'⟩
    | ask src d =>
      have successor (b : Bool) :
          (Config.resume ((src.advance s).write d [b]) frames).Bounded (n + 1) :=
        ⟨(src.advance_bounded hs').write (singleton b), hf', hl'⟩
      simp only [Config.step]
      split
      · exact successor _
      · rename_i w hw
        exact ⟨Source.read_fits hs'.1 hw, successor _, successor _⟩
    | callBit src d body =>
      have advanced := src.advance_bounded hs'
      simp only [Config.step]
      split
      · exact ⟨advanced.write (singleton _), hf', hl'⟩
      · rename_i w hw
        refine ⟨State.input_bounded (Source.read_fits hs'.1 hw) (Nat.zero_le _), ?_,
          Nat.succ_le_succ hl⟩
        intro f hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact advanced
        · exact hf' f hm
  | resume s frames =>
    obtain ⟨hs, hf, hl⟩ := h
    cases frames with
    | nil => exact hs.mono le
    | cons frame frames =>
      have hf' : ∀ f ∈ frames, f.Bounded (n + 1) := fun f hm =>
        (hf f (List.mem_cons_of_mem _ hm)).mono le
      have hl' : frames.length ≤ n + 1 := by
        simp only [List.length_cons] at hl
        omega
      cases frame with
      | next => exact ⟨hs.mono le, hf', hl'⟩
      | callResult caller d =>
        have bound : caller.Bounded n := hf _ (List.mem_cons_self ..)
        exact ⟨(bound.mono le).write (singleton _), hf', hl'⟩

/-- Even the output words on incorrect transcripts have polynomial length. -/
theorem Config.candidate_word_length {c : Config} {w : Word} (hf : c.Bounded n)
    (hm : w ∈ c.candidates t q) : w.length ≤ n + t + 1 := by
  induction t generalizing c q n with
  | zero =>
    have hstep := c.step_bounded hf
    rw [Config.candidates] at hm
    cases he : c.step with
    | halt s =>
      rw [he] at hm hstep
      have hw := List.mem_singleton.mp hm
      subst w
      exact (show s.Bounded (n + 1) from hstep).1.1 0
    | next | question => simp [he] at hm
  | succ k ih =>
    have hstep := c.step_bounded hf
    rw [Config.candidates] at hm
    cases he : c.step with
    | halt s =>
      rw [he] at hm hstep
      have hw := List.mem_singleton.mp hm
      subst w
      exact Nat.le_trans ((show s.Bounded (n + 1) from hstep).1.1 0) (by omega)
    | next d =>
      rw [he] at hm hstep
      have bound := ih (show d.Bounded (n + 1) from hstep) hm
      omega
    | question a no yes =>
      rw [he] at hm hstep
      cases q with
      | zero => simp at hm
      | succ l =>
        obtain ⟨_, hno, hyes⟩ :
            a.length ≤ n + 1 ∧ no.Bounded (n + 1) ∧ yes.Bounded (n + 1) := hstep
        rcases List.mem_append.mp hm with h | h
        · have bound := ih hno h
          omega
        · have bound := ih hyes h
          omega

end ComplexityModel
