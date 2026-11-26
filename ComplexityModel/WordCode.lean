module

public import ComplexityModel.FieldCode

@[expose] public section

namespace ComplexityModel

@[ext] theorem State.ext {s t : State} (registers : s.reg = t.reg) (queue : s.queries = t.queries) :
    s = t := by
  cases s
  cases t
  cases registers
  cases queue
  rfl

namespace WordCode

/-- Run a register-only operation with a specified register frame. -/
def Preserves (s u : State) (changed : List Nat) : Prop :=
  u.queries = s.queries ∧ ∀ r, r ∉ changed → u.reg r = s.reg r

theorem Preserves.trans {s t u : State} {changed : List Nat}
    (first : Preserves s t changed) (second : Preserves t u changed) : Preserves s u changed :=
  ⟨second.1.trans first.1, fun r hr => (second.2 r hr).trans (first.2 r hr)⟩

theorem Preserves.mono {s u : State} {changed more : List Nat}
    (h : Preserves s u changed) (sub : ∀ r ∈ changed, r ∈ more) : Preserves s u more :=
  ⟨h.1, fun r hr => h.2 r fun hbad => hr (sub r hbad)⟩

theorem preserves_write (s : State) (r : Nat) (w : Word) :
    Preserves s (s.write r w) [r] :=
  ⟨rfl, fun i ni => by simp_all [State.write]⟩

def prependHead (src dst : Nat) : Code :=
  .branch (.head src) (.write dst (.cons true dst)) (.write dst (.cons false dst))

theorem prependHead_run (A : Language) (s : State) (src dst : Nat) :
    Run A (prependHead src dst) s (s.write dst ((s.reg src).headD false :: s.reg dst)) 2 0 := by
  unfold prependHead
  apply Run.branch (bit := (s.reg src).headD false) rfl
  cases h : (s.reg src).headD false <;> simp only [h, Bool.false_eq_true, ↓reduceIte] <;>
    exact Run.write

def setBit (r : Nat) (b : Bool) : Code := .seq (.write r .empty) (.write r (.cons b r))

theorem setBit_run (A : Language) (s : State) (r : Nat) (b : Bool) :
    Run A (setBit r b) s (s.write r [b]) 3 0 := by
  have clear : Run A (.write r .empty) s (s.write r []) 1 0 := .write
  have write : Run A (.write r (.cons b r)) (s.write r []) ((s.write r []).write r [b]) 1 0 := by
    simpa [Expr.eval, State.write] using
      (Run.write (A := A) (s := s.write r []) (d := r) (e := .cons b r))
  have collapse : (s.write r []).write r [b] = s.write r [b] := by
    refine State.ext ?_ rfl
    funext i
    by_cases hi : i = r <;> simp [State.write, hi]
  rw [← collapse]
  exact .seq clear write

private def escapeLoop (src dst flag : Nat) : Code :=
  .loop (.head flag) (.branch (.empty src) (.write flag .empty)
    (.seq (prependHead src dst) (.seq (.write dst (.cons true dst)) (.write src (.tail src)))))

private theorem escapeLoop_run (s : State) {src dst flag : Nat}
    (hd : dst ≠ src) (hf : flag ≠ src) (hfd : flag ≠ dst) (rev : Word)
    (h : s.reg src = rev) (active : s.reg flag = [true]) :
    ∃ u, Run emptyLanguage (escapeLoop src dst flag) s u (8 * rev.length + 4) 0 ∧
      u.reg dst = rev.foldl (fun rest b => true :: b :: rest) (s.reg dst) ∧
      Preserves s u [src, dst, flag] := by
  induction rev generalizing s with
  | nil =>
    let out := s.write flag []
    have step : Run emptyLanguage
        (.branch (.empty src) (.write flag .empty)
          (.seq (prependHead src dst) (.seq (.write dst (.cons true dst)) (.write src (.tail src)))))
        s out 2 0 := .branch (bit := true) (by simp [Test.eval, h]) .write
    have stop : Run emptyLanguage (escapeLoop src dst flag) out out 1 0 :=
      .loopFalse (by simp [out, State.write, Test.eval])
    refine ⟨out, .loopTrue (by simp [Test.eval, active]) step stop,
      by simp [out, State.write, Ne.symm hfd], ?_⟩
    exact (preserves_write ..).mono (by simp)
  | cons bit rest ih =>
    let a := s.write dst (bit :: s.reg dst)
    let b := a.write dst (true :: bit :: s.reg dst)
    let next := b.write src rest
    have data : Run emptyLanguage (prependHead src dst) s a 2 0 := by
      simpa [a, h] using prependHead_run emptyLanguage s src dst
    have tag : Run emptyLanguage (.write dst (.cons true dst)) a b 1 0 := by
      simpa [b, a, Expr.eval, State.write] using
        (Run.write (A := emptyLanguage) (s := a) (d := dst) (e := .cons true dst))
    have drop : Run emptyLanguage (.write src (.tail src)) b next 1 0 := by
      simpa [next, b, a, Expr.eval, State.write, Ne.symm hd, h] using
        (Run.write (A := emptyLanguage) (s := b) (d := src) (e := .tail src))
    have step : Run emptyLanguage
        (.branch (.empty src) (.write flag .empty)
          (.seq (prependHead src dst) (.seq (.write dst (.cons true dst)) (.write src (.tail src)))))
        s next 7 0 :=
      .branch (bit := false) (by simp [Test.eval, h]) (.seq data (.seq tag drop))
    obtain ⟨out, loop, data', frame⟩ := ih next
      (by simp [next, State.write]) (by simp [next, b, a, State.write, hf, hfd, active])
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [show 8 * (bit :: rest).length + 4 = 7 + (8 * rest.length + 4) + 1 by
        simp only [List.length_cons]; omega]
      exact .loopTrue (by simp [Test.eval, active]) step loop
    · simpa [next, b, State.write, hd] using data'
    · apply Preserves.trans (t := next) _ frame
      exact ((preserves_write s dst _).mono (by simp)).trans
        (((preserves_write a dst _).mono (by simp)).trans ((preserves_write b src _).mono (by simp)))

private theorem escape_fold (word rest : Word) :
    word.reverse.foldl (fun acc bit => true :: bit :: acc) (false :: rest) =
      QueryEncoding.put word rest := by
  induction word with
  | nil => rfl
  | cons bit restWord ih =>
    simp [List.foldl_append, ih, QueryEncoding.put]

/-- Prepend one escaped field from register `src` to register `dst`.
The three scratch registers must be distinct from each other and from
`dst`. The source is copied before any scratch registers are modified. -/
def putField (src dst tmp rev flag : Nat) : Code :=
  .seq (.write tmp (.copy src))
    (.seq (FieldCode.reverse tmp rev flag)
      (.seq (.write dst (.cons false dst)) (.seq (setBit flag true) (escapeLoop rev dst flag))))

theorem putField_allowed (src dst tmp rev flag : Nat) (push direct queued : Bool) :
    (putField src dst tmp rev flag).allowed push direct queued := by
  simp [putField, FieldCode.reverse_allowed, setBit, escapeLoop, prependHead, Code.allowed]

theorem putField_run (s : State) {src dst tmp rev flag : Nat}
    (hdt : dst ≠ tmp) (hdr : dst ≠ rev) (hdf : dst ≠ flag)
    (hrt : rev ≠ tmp) (hft : flag ≠ tmp) (hfr : flag ≠ rev) :
    ∃ u, Run emptyLanguage (putField src dst tmp rev flag) s u (14 * (s.reg src).length + 23) 0 ∧
      u.reg dst = QueryEncoding.put (s.reg src) (s.reg dst) ∧ Preserves s u [dst, tmp, rev, flag] := by
  let w := s.reg src
  let copied := s.write tmp w
  have copy : Run emptyLanguage (.write tmp (.copy src)) s copied 1 0 := .write
  obtain ⟨reversed, revRun, _, data, queue, others⟩ := FieldCode.reverse_run copied hrt hft hfr
  have reversedData : reversed.reg rev = w.reverse := by simpa [copied, State.write] using data
  let term := reversed.write dst (false :: reversed.reg dst)
  let start := term.write flag [true]
  have addTerm : Run emptyLanguage (.write dst (.cons false dst)) reversed term 1 0 := .write
  have startData : start.reg rev = w.reverse := by
    simp [start, term, State.write, Ne.symm hdr, Ne.symm hfr, reversedData]
  obtain ⟨out, loop, result, frame⟩ :=
    escapeLoop_run start hdr hfr (Ne.symm hdf) w.reverse startData (by simp [start, State.write])
  refine ⟨out, ?_, ?_, ?_⟩
  · have hlen : (copied.reg tmp).length = w.length := by simp [copied, State.write]
    have arm : Run emptyLanguage (setBit flag true) term start 3 0 := setBit_run ..
    have all := Run.seq copy (Run.seq revRun (Run.seq addTerm (Run.seq arm loop)))
    change Run emptyLanguage (putField src dst tmp rev flag) s out _ 0 at all
    have total : 1 + (6 * (copied.reg tmp).length + 10 +
        (1 + (3 + (8 * w.reverse.length + 4) + 1) + 1) + 1) + 1 = 14 * w.length + 23 := by
      simp only [hlen, List.length_reverse]
      omega
    simpa only [total] using all
  · have dstEq : start.reg dst = false :: s.reg dst := by
      simp [start, term, copied, State.write, hdf, hdt, others dst hdt hdr hdf]
    rw [result, dstEq, escape_fold]
  · have revFrame : Preserves copied reversed [dst, tmp, rev, flag] := by
      exact ⟨queue, fun r hr => by simp at hr; exact others r hr.2.1 hr.2.2.1 hr.2.2.2⟩
    have copyFrame : Preserves s copied [dst, tmp, rev, flag] := (preserves_write ..).mono (by simp)
    have termFrame : Preserves reversed term [dst, tmp, rev, flag] := (preserves_write ..).mono (by simp)
    have startFrame : Preserves term start [dst, tmp, rev, flag] := (preserves_write ..).mono (by simp)
    exact copyFrame.trans (revFrame.trans (termFrame.trans (startFrame.trans (frame.mono (by
      intro r hr; simp at hr ⊢; rcases hr with h | h | h <;> simp [h])))))

end WordCode
end ComplexityModel
