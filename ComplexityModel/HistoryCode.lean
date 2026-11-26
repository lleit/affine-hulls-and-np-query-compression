module

public import ComplexityModel.RestrictionCode

@[expose] public section

namespace ComplexityModel.HistoryCode

open QueryEncoding (take unpack)
open WordCode (Preserves setBit setBit_run preserves_write)

private def step : Code :=
  .branch (.empty 17) (.write 20 .empty)
    (.seq (FieldCode.takeField 17 10 18 19) RestrictionCode.inflate)

private def loop : Code := .loop (.head 20) step

private theorem loop_run (s : State) (gas cap : Nat)
    (hLen : (s.reg 17).length ≤ gas) (hCap : gas ≤ cap) (active : s.reg 20 = [true]) :
    ∃ u t, Run emptyLanguage loop s u t 0 ∧ t ≤ (120 * (cap+1)) * gas + 4 ∧
      u.reg 11 = AffineSearch.decode (unpack gas (s.reg 17)) (s.reg 11) ∧
      Preserves s u [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  have live : (Test.head 20).eval s = true := by simp [Test.eval, active]
  cases empty : s.reg 17 with
  | nil =>
    let out := s.write 20 []
    have body : Run emptyLanguage step s out 2 0 :=
      .branch (bit := true) (by simp [Test.eval, empty]) .write
    have done : Run emptyLanguage loop out out 1 0 :=
      .loopFalse (by simp [Test.eval, out, State.write])
    refine ⟨out, 4, .loopTrue live body done, by omega, ?_,
      (preserves_write ..).mono (by simp)⟩
    cases gas <;> simp [out, State.write, empty, unpack, AffineSearch.decode]
  | cons bit rest =>
    cases gas with
    | zero => simp [empty] at hLen
    | succ fuel =>
      let history := s.reg 17
      have nonempty : history ≠ [] := by simp [history, empty]
      obtain ⟨parsed, t₁, parse, bound₁, suffix, mask, queue, preserved⟩ :=
        FieldCode.takeField_run s (src := 17) (dst := 10) (scratch := 18) (flag := 19)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨rebuilt, t₂, inflate, bound₂, x, preserved'⟩ := RestrictionCode.inflate_run parsed
      have history' : rebuilt.reg 17 = (take history).2 :=
        (preserved'.2 17 (by decide)).trans suffix
      have x' : rebuilt.reg 11 = AffineSearch.inflate (take history).1 (s.reg 11) := by
        rw [x, mask, preserved 11 (by decide) (by decide) (by decide) (by decide)]
      have active' : rebuilt.reg 20 = [true] := by
        rw [preserved'.2 20 (by decide), preserved 20 (by decide) (by decide) (by decide) (by decide), active]
      have remaining := QueryEncoding.take_rest_lt nonempty
      have remainingCount : (rebuilt.reg 17).length ≤ fuel := by
        rw [history']
        change history.length ≤ fuel + 1 at hLen
        omega
      obtain ⟨u, t, run, bound, decoded, frame⟩ :=
        loop_run rebuilt fuel cap remainingCount (by omega) active'
      have body : Run emptyLanguage step s rebuilt (t₁ + t₂ + 2) 0 :=
        .branch (bit := false) (by simp [Test.eval, empty]) (.seq parse inflate)
      refine ⟨u, _, .loopTrue live body run, ?_, ?_, ?_⟩
      · have short := QueryEncoding.take_data_le history
        change history.length ≤ fuel + 1 at hLen
        rw [mask] at bound₂
        change t₂ ≤ 29 * (take history).1.length + 43 at bound₂
        change t₁ ≤ 14 * history.length + 17 at bound₁
        rw [Nat.mul_succ (120 * (cap + 1)) fuel]
        omega
      · rw [decoded, history', x']
        rw [← empty]
        change _ = AffineSearch.decode (unpack (fuel+1) history) (s.reg 11)
        have ne : history.isEmpty = false := by simp [history, empty]
        rw [unpack, if_neg (by simp [ne])]
        cases take history
        rfl
      · have frame₁ : Preserves s parsed [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
          refine ⟨queue, fun r hr => ?_⟩
          simp at hr
          exact preserved r (by omega) (by omega) (by omega) (by omega)
        have frame₂ := preserved'.mono (more := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20])
          (by intro r hr; simp at hr ⊢; omega)
        exact frame₁.trans (frame₂.trans frame)
termination_by gas

/-- Decode a stack of restrictions in register 17 and restore the witness
in register 11. Registers 10 through 20 are reserved for the operation. -/
def decode : Code := .seq (setBit 20 true) loop

theorem decode_allowed (push direct queued : Bool) : decode.allowed push direct queued := by
  simp [decode, setBit, loop, step, Code.allowed, FieldCode.takeField_allowed,
    RestrictionCode.inflate_allowed]

theorem decode_run (s : State) :
    ∃ u t, Run emptyLanguage decode s u t 0 ∧
      t ≤ 120 * ((s.reg 17).length + 1) * (s.reg 17).length + 8 ∧
      u.reg 11 = AffineSearch.decode (unpack (s.reg 17).length (s.reg 17)) (s.reg 11) ∧
      Preserves s u [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  let start := s.write 20 [true]
  let n := (s.reg 17).length
  have startRun : Run emptyLanguage (setBit 20 true) s start 3 0 := setBit_run ..
  obtain ⟨u, t, run, bound, spec, frame⟩ := loop_run start n n
    (by simp [start, n, State.write]) (Nat.le_refl _) (by simp [start, State.write])
  change t ≤ 120 * ((s.reg 17).length + 1) * (s.reg 17).length + 4 at bound
  refine ⟨u, _, .seq startRun run, by omega, ?_, ?_⟩
  · simpa [start, n, State.write] using spec
  · exact ((preserves_write s 20 _).mono (by simp)).trans frame

end ComplexityModel.HistoryCode
