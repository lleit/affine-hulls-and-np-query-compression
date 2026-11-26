module

public import ReplayParameters

@[expose] public section

namespace CandidateCutoffCode

open ComplexityModel
open HullBatchMachine (normalize normalize_run ones stepWrite)
open WordCode (Preserves preserves_write setBit setBit_run)

local infixr:60 " ▷ " => Code.seq

/-- Save the active width, count the packed bytes plus two, and compute
the unary logarithm used to decide which candidates can be enumerated. -/
def cutoff : Code :=
  .write 152 (.copy 1) ▷ .write 153 (.copy 150) ▷ setBit 21 true ▷
  .write 21 (.cons true 21) ▷ normalize 153 21 154 ▷ .write 1 .empty ▷
  ReplayParameters.logCap 1 ▷ .write 151 (.copy 1) ▷ .write 1 (.copy 152)

theorem cutoff_pure : cutoff.pure := by
  simp [cutoff, normalize, HullBatchMachine.set, HullBatchMachine.scanCore,
    setBit, Code.allowed, ReplayParameters.logCap_pure]

def cutoffTime : Poly := ⟨390, 2⟩

private theorem cost_bound (n : Nat) :
    37 * (n + 3) * (n + 2) + 5 * n + 36 ≤ cutoffTime.at n := by
  have pos : 0 < n + 1 := by omega
  let m := n + 1
  have mpos : 0 < m := pos
  have square : m ≤ m * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left m mpos
  have prod : (n + 3) * (n + 2) ≤ 6 * (m * m) := by
    have hn₁ : n + 3 ≤ 3*m := by dsimp [m]; omega
    have hn₂ : n + 2 ≤ 2*m := by dsimp [m]; omega
    have h := Nat.mul_le_mul hn₁ hn₂
    simpa only [Nat.mul_mul_mul_comm 3 m 2 m, show 3*2=6 by decide] using h
  rw [cutoffTime, Poly.at, Nat.pow_two, Nat.mul_assoc]
  change 37 * ((n + 3) * (n + 2)) + 5*n + 36 ≤ 390 * (m*m)
  dsimp [m] at *
  omega

theorem cutoff_run (s : State) :
    ∃ u t, Run emptyLanguage cutoff s u t 0 ∧
      t ≤ cutoffTime.at (s.reg 150).length ∧
      u.reg 151 = ones ((s.reg 150).length + 2).log2 ∧
      Preserves s u [21,22,23,24,25,151,152,153,154] := by
  let n := (s.reg 150).length
  let a := s.write 152 (s.reg 1)
  let b := a.write 153 (s.reg 150)
  let c := b.write 21 [true]
  let d := c.write 21 (ones 2)
  have save : Run emptyLanguage (.write 152 (.copy 1)) s a 1 0 := .write
  have input : Run emptyLanguage (.write 153 (.copy 150)) a b 1 0 := by
    simpa [a, b, Expr.eval] using stepWrite a 153 (.copy 150)
  have seed : Run emptyLanguage (setBit 21 true) b c 3 0 := setBit_run ..
  have inc : Run emptyLanguage (.write 21 (.cons true 21)) c d 1 0 := by
    simpa [c, d, Expr.eval] using stepWrite c 21 (.cons true 21)
  obtain ⟨e, t, count, countTime, tally, countQueue, countFrame⟩ :=
    normalize_run (src := 153) (dst := 21) (flag := 154) (by decide) (by decide) (by decide) d
  have inputSize : (d.reg 153).length = n := by simp [d,c,b,n]
  rw [inputSize] at countTime tally
  have tally' : e.reg 21 = ones (n+2) := by
    simpa [d, ones, List.replicate_succ', List.append_assoc] using tally
  let f := e.write 1 []
  have zero : Run emptyLanguage (.write 1 .empty) e f 1 0 := .write
  obtain ⟨g, t', lg, lgTime, lgOut, lgFrame⟩ :=
    ReplayParameters.logCap_run 1 (n+2) f (by simpa [f] using tally')
  let cutoffWord := ones (n+2).log2
  have lgOut' : g.reg 1 = cutoffWord := by simpa [f, cutoffWord] using lgOut
  let h := g.write 151 cutoffWord
  let u := h.write 1 (s.reg 1)
  have store : Run emptyLanguage (.write 151 (.copy 1)) g h 1 0 := by
    simpa [h, Expr.eval, lgOut'] using stepWrite g 151 (.copy 1)
  have saved : h.reg 152 = s.reg 1 := by
    simp [h, lgFrame.2 152 (by decide), f, countFrame 152 (by decide) (by decide) (by decide),
      d, c, b, a]
  have restore : Run emptyLanguage (.write 1 (.copy 152)) h u 1 0 := by
    simpa [u, Expr.eval, saved] using stepWrite h 1 (.copy 152)
  refine ⟨u, _, .seq save (.seq input (.seq seed (.seq inc (.seq count
    (.seq zero (.seq lg (.seq store restore))))))), ?_, by simp [u,h,cutoffWord,n], ?_⟩
  · have bnd := cost_bound n
    change t ≤ 5*n + 8 at countTime
    change t' ≤ 37 * (n + 3) * (n + 2) + 11 at lgTime
    change _ ≤ cutoffTime.at n
    omega
  · refine ⟨lgFrame.1.trans countQueue, ?_⟩
    intro r hr
    by_cases req : r = 1
    · subst r
      simp [u]
    · have nonmem ⦃i : Nat⦄ (hi : i ∈ [21,22,23,24,25,151,152,153,154]) : r ≠ i := by
        intro eq
        subst i
        exact hr hi
      have logFrame : r ∉ [1,21,22,23,24,25] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨req, nonmem (by decide), nonmem (by decide), nonmem (by decide),
          nonmem (by decide), nonmem (by decide)⟩
      rw [show u.reg r = g.reg r by
        simp [u, h, req, nonmem (i := 151) (by decide)],
        lgFrame.2 r logFrame, show f.reg r = e.reg r by simp [f, req],
        countFrame r (nonmem (by decide)) (nonmem (by decide)) (nonmem (by decide))]
      simp [d, c, b, a, nonmem (i := 21) (by decide), nonmem (i := 153) (by decide),
        nonmem (i := 152) (by decide)]

theorem pack_count_le (words : List Word) : words.length ≤ (QueryEncoding.pack words).length := by
  rw [QueryEncoding.pack_length]
  omega

theorem rank_small_iff (rank bytes : Nat) :
    rank ≤ (bytes+2).log2 ↔ 2^rank ≤ bytes+2 :=
  Nat.le_log2 (by omega)

end CandidateCutoffCode
