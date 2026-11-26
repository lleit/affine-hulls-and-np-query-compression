module

public import QueryEncoding
public import SearchSplitter
public import MachineEnumeration

@[expose] public section

namespace WitnessSearch

open ComplexityModel

/-- Search a restricted instance using a fixed adaptive program. Replaying
the program on each possible answer tape needs no oracle. -/
def solveRestricted (c : Code) (p : Poly) (a b : Nat)
    (check : Word → Word → Bool) (x : Word) (n : Nat) (history : List Word) : Option Word :=
  let outputs (s : Word) :=
    MachineEnumeration.compiledCandidates c s (p.at s.length) ((s.length + 2).log2 * a + b)
  AffineSearch.search (check x) (QueryEncoding.listFrom outputs x) AffineSearch.mask n history

def solve (c : Code) (p : Poly) (a b : Nat)
    (check : Word → Word → Bool) (x : Word) (n : Nat) : Option Word :=
  solveRestricted c p a b check x n []

/-- The logarithmic-query hypothesis is used only to obtain a program with
a genuine output among its replays. The resulting deterministic algorithm
returns a witness exactly on the yes-instances of the verifier. -/
theorem of_log_hull (check : Word → Word → Bool)
    (h : FPLogNP (QueryEncoding.hullWord check)) :
    ∃ c : Code, ∃ p : Poly, ∃ a b : Nat, ∀ x n,
      (∀ w, solve c p a b check x n = some w → w.length = n ∧ check x w = true) ∧
      ((∃ w, solve c p a b check x n = some w) ↔ ∃ w, w.length = n ∧ check x w = true) := by
  obtain ⟨c, p, a, b, hr⟩ := FPLogNP.compiled_candidate_bound h
  refine ⟨c, p, a, b, fun x n => ?_⟩
  let outputs (s : Word) :=
    MachineEnumeration.compiledCandidates c s (p.at s.length) ((s.length + 2).log2 * a + b)
  have contains (s : Word) : QueryEncoding.hullWord check s ∈ outputs s := (hr s).1
  let list := QueryEncoding.listFrom outputs x
  refine ⟨?_, ?_⟩
  · intro w hw
    exact AffineSearch.search_sound _ _ _ (.start n) hw
  · exact AffineSearch.solve_iff (check x) n list
      (fun k hs _ A ha => QueryEncoding.list_shape outputs x k hs A ha)
      (fun k hs _ => QueryEncoding.list_genuine check outputs contains x k hs)

/-- A common bound for the number of simulated tapes at any round, using
the initial width and input length. -/
def tapeBound (a b inputLength width : Nat) : Nat :=
  (2 * inputLength + 2 * width * width + 3 * width + 4) ^ a * 2 ^ b

theorem replay_count_bound (a b : Nat) (x : Word) {n k hs}
    (history : AffineSearch.History n k hs) :
    2 ^ (((QueryEncoding.requestWord x k hs).length + 2).log2 * a + b) ≤
      tapeBound a b x.length n := by
  apply Nat.le_trans (pow_log_cap ..)
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_left
  have size := QueryEncoding.request_size history x
  omega

theorem candidates_and_probes_bound (c : Code) (p : Poly) (a b : Nat) (x : Word) {n k hs}
    (history : AffineSearch.History n k hs) :
    let outputs (s : Word) :=
      MachineEnumeration.compiledCandidates c s (p.at s.length) ((s.length + 2).log2 * a + b)
    let candidates := QueryEncoding.listFrom outputs x k hs
    let bound := tapeBound a b x.length n
    candidates.length ≤ bound ∧
      (AffineSearch.probes candidates.length candidates).length ≤ bound * bound := by
  dsimp only
  let s := QueryEncoding.requestWord x k hs
  let outputs (q : Word) :=
    MachineEnumeration.compiledCandidates c q (p.at q.length) ((q.length + 2).log2 * a + b)
  let L := QueryEncoding.listFrom outputs x k hs
  have count : L.length ≤ tapeBound a b x.length n := by
    apply Nat.le_trans (List.length_filterMap_le _ _)
    exact Nat.le_trans (MachineEnumeration.compiledCandidates_length ..)
      (replay_count_bound a b x history)
  exact ⟨count, Nat.le_trans (AffineSearch.probe_bound _ _) (Nat.mul_le_mul count count)⟩

/-- Sum the verified machine transition counts of all replays in a round.
Use the size of the original input and its original witness width so the
same polynomial bounds every restriction. -/
theorem replay_work_bound (c : Code) (p : Poly) (a b : Nat) (x : Word) {n k hs}
    (history : AffineSearch.History n k hs) :
    let s := QueryEncoding.requestWord x k hs
    let budget := p.at s.length
    let clock := MachineEnumeration.loweringCost (MachineEnumeration.frameWidth c) budget * budget
    let cap := (s.length + 2).log2 * a + b
    let maxBudget := p.at (2*x.length + 2*n*n + 3*n + 2)
    let maxClock :=
      MachineEnumeration.loweringCost (MachineEnumeration.frameWidth c) maxBudget * maxBudget
    ∃ work : List (Word × Nat),
      work.map Prod.fst = MachineEnumeration.tapes cap ∧
      (∀ entry ∈ work, ∃ out, Run emptyLanguage (MachineEnumeration.replayProgram c)
        (State.input s (MachineEnumeration.clockWord clock ++ entry.1)) out entry.2 0) ∧
      (work.map Prod.snd).sum ≤ (24 * maxClock + 36) * tapeBound a b x.length n := by
  dsimp only
  let s := QueryEncoding.requestWord x k hs
  let budget := p.at s.length
  let maxBudget := p.at (2*x.length + 2*n*n + 3*n + 2)
  let cap := (s.length + 2).log2 * a + b
  let width := MachineEnumeration.frameWidth c
  have hb : budget ≤ maxBudget := p.mono (QueryEncoding.request_size history x)
  have hLower : MachineEnumeration.loweringCost width budget ≤
      MachineEnumeration.loweringCost width maxBudget := by
    unfold MachineEnumeration.loweringCost
    omega
  have clock := Nat.mul_le_mul hLower hb
  obtain ⟨work, tapes, runs, bound⟩ := MachineEnumeration.compiledCandidates_work c s budget cap
  refine ⟨work, tapes, runs, Nat.le_trans bound ?_⟩
  apply Nat.mul_le_mul _ (replay_count_bound a b x history)
  change 24 * (MachineEnumeration.loweringCost width budget * budget) + 36 ≤
    24 * (MachineEnumeration.loweringCost width maxBudget * maxBudget) + 36
  omega

end WitnessSearch
