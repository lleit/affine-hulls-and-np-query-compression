module

public import QueryHeaderCode
public import CertificateCode
public import RestrictedVerifier
public import EliminationQueryCode

@[expose] public section

namespace HullVerifierCode

open ComplexityModel
open HullRecovery (Bits Query Witness lift rank normal unit ListSpan SameSpan Span)
open HullQueryLanguage (verifyWord verifyFields)
open QueryEncoding (take readRequest)
open HullBatchMachine (ones)

private def isBit : Query d → Bool
  | .rank _ => false
  | .bit .. => true

private def col : Query (m+1) → Fin (m+1)
  | .rank _ => 0
  | .bit _ i _ => i

private def row : Query (m+1) → Fin (m+1)
  | .rank _ => 0
  | .bit _ _ j => j

private theorem reverseSpan (xs : List (Bits n)) : SameSpan xs.reverse xs := by
  intro x
  exact ⟨Span.mono (fun _ h => .gen (by simpa using h)),
    Span.mono (fun _ h => .gen (by simpa using h))⟩

private theorem verify_reverse (check : Word → Word → Bool) (req : Word)
    (q : Query ((readRequest req).width + 1))
    (w : Witness (readRequest req).width q.level.val) :
    let xs := w.val.reverse.map lift
    let accepted := w.val.all (fun v => RestrictedVerifier.check check req (HullDecoder.word v))
    HullRecovery.verify (QueryEncoding.S check (readRequest req)) q w =
      (accepted && (rank xs == q.level.val) &&
        (if isBit q then normal xs (unit (col q)) (row q) else true)) := by
  let r := readRequest req
  let xs := w.val.reverse.map lift
  let all := w.val.all (fun v => RestrictedVerifier.check check req (HullDecoder.word v))
  have dec (v : Bits r.width) :
      decide (QueryEncoding.S check r v) = RestrictedVerifier.check check req (HullDecoder.word v) := by
    cases h : RestrictedVerifier.check check req (HullDecoder.word v) <;>
      simp_all [RestrictedVerifier.check, QueryEncoding.S, r]
  have equalPred := funext dec
  have span : SameSpan xs (w.val.map lift) := by
    simpa only [xs, List.map_reverse] using reverseSpan (w.val.map lift)
  have ranked := HullRecovery.rank_congr span
  have normalized := HullRecovery.normal_congr span
  change HullRecovery.verify (QueryEncoding.S check r) q w =
    (all && (rank xs == q.level.val) &&
      (if isBit q then normal xs (unit (col q)) (row q) else true))
  unfold HullRecovery.verify
  rw [equalPred, ranked, normalized]
  cases q <;> simp [all, r, rank, normal, isBit, col, row, Bool.and_assoc]

/-- Compile a two-input checker into a verifier for the hull query language. -/
def compile (c : Code) : Code :=
  .seq QueryHeaderCode.parse
    (.branch (.head 9)
      (.seq (CertificateCode.checkRows (RestrictedVerifier.compile c)) EliminationQueryCode.finish)
      (WordCode.setBit 0 false))

theorem compile_pure {c : Code} (hc : c.pure) : (compile c).pure := by
  simp [compile, Code.allowed, QueryHeaderCode.parse_pure, CertificateCode.checkRows_pure
    (RestrictedVerifier.compile_pure hc), EliminationQueryCode.finish_pure, WordCode.setBit]

private def restrictedTime (time : Poly) : Poly := (time.plus ⟨43, 1⟩).plus ⟨300, 2⟩

private def certificateTime (time : Poly) : Poly :=
  (((restrictedTime time).plus ⟨43, 1⟩).plus ⟨200, 1⟩).times ⟨1, 1⟩

def compileTime (time : Poly) : Poly := (certificateTime time).plus ⟨6000, 4⟩

theorem compile_run {c : Code} {time : Poly} {check : Word → Word → Bool}
    (program : CertificateCode.Implements c time check) (s cert : Word) :
    ∃ out t, Run emptyLanguage (compile c) (State.input s cert) out t 0 ∧
      t ≤ (compileTime time).at (s.length + cert.length) ∧
      out.output = [verifyWord check s cert] := by
  let n := s.length + cert.length
  let metadata := QueryHeaderCode.header s
  let req := (take s).1
  let r := readRequest req
  let m := r.width
  let encodedQuery := (take s).2
  let restricted := RestrictedVerifier.compile c
  let checkRestricted := RestrictedVerifier.check check
  have spec : CertificateCode.Implements restricted (restrictedTime time) checkRestricted := by
    intro x w
    obtain ⟨out, t, run, bound, output⟩ := RestrictedVerifier.compile_run program x w
    exact ⟨out, t, run, bound, by simp [output, checkRestricted]⟩
  obtain ⟨parsed, tHeader, parse, headerCost, hcert, hreq, hwidth, hrank, hcol, hrow, mode, status, _⟩ :=
    QueryHeaderCode.parse_run s cert
  change parsed.reg 9 = [metadata.valid] at status
  change parsed.reg 8 = [metadata.isBit] at mode
  have reqEq : parsed.reg 2 = req := hreq
  have widthEq : parsed.reg 4 = ones m := hwidth
  have fieldSize := QueryEncoding.take_lengths s
  have widthBound : m ≤ req.length := HullQueryLanguage.width_le req
  have pairSize : req.length + m ≤ n := by
    change 2 * req.length + encodedQuery.length ≤ s.length at fieldSize
    dsimp [n]
    omega
  have parseSize : tHeader ≤ 200 * (n + 1) := by dsimp [n]; omega
  have zpos : 1 ≤ n + 1 := by omega
  have linear_le : n + 1 ≤ (n + 1)^4 := by
    have power := Nat.pow_le_pow_right zpos (show 1 ≤ 4 by decide)
    simpa only [Nat.pow_one] using power
  have sum := Poly.plus_bound (certificateTime time) ⟨6000, 4⟩ n
  have large : (Poly.mk 6000 4).at n = 6000 * (n + 1)^4 := rfl
  rw [large] at sum
  cases read : HullQueryLanguage.readQuery (m+1) encodedQuery with
  | none =>
    have failed : metadata.valid = false := by
      cases h : metadata.valid with
      | false => rfl
      | true =>
        obtain ⟨q, has⟩ := (QueryHeaderCode.valid_iff_query s).mp h
        change HullQueryLanguage.readQuery (m+1) encodedQuery = some q at has
        rw [read] at has
        contradiction
    have halt : (Test.head 9).eval parsed = false := by simp [Test.eval, status, failed]
    let out := parsed.write 0 [false]
    have failRun : Run emptyLanguage
        (.branch (.head 9) (.seq (CertificateCode.checkRows restricted) EliminationQueryCode.finish)
          (WordCode.setBit 0 false)) parsed out 4 0 :=
      HullBatchMachine.runFalse halt (WordCode.setBit_run emptyLanguage parsed 0 false)
    have result : verifyWord check s cert = false := by
      unfold verifyWord verifyFields
      dsimp only
      rw [read]
    refine ⟨out, _, .seq parse failRun, ?_, by simp [out, State.output, result]⟩
    change tHeader + 4 + 1 ≤ (compileTime time).at n
    unfold compileTime
    omega
  | some q =>
    have valid : metadata.valid = true :=
      (QueryHeaderCode.valid_iff_query s).mpr ⟨q, read⟩
    have running : (Test.head 9).eval parsed = true := by simp [Test.eval, status, valid]
    have props := QueryHeaderCode.query_matches s q read
    have rankValue : metadata.rank = q.level.val := props.1
    have tag : metadata.isBit = isBit q := by
      cases q with
      | rank i => exact props.2
      | bit i j k => exact props.2.1
    have coordinates : isBit q = true →
        metadata.col = (col q).val ∧ metadata.row = (row q).val := by
      intro eq
      cases q with
      | rank i => simp [isBit] at eq
      | bit i j k => exact props.2.2
    have certRank : parsed.reg 5 = ones q.level.val := hrank.trans (congrArg ones rankValue)
    obtain ⟨scanned, tPoints, points, pointsBound, packed, accepted, frame⟩ :=
      CertificateCode.checkRows_run spec parsed m q.level.val widthEq certRank
    let certWitness := HullQueryLanguage.readCertificate m q.level.val cert
    let rows := certWitness.val
    let xs := rows.reverse.map lift
    let ok := rows.all (fun v => checkRestricted req (HullDecoder.word v))
    have rowsLen : xs.length = q.level.val := by simp [xs, rows, certWitness,
      HullQueryLanguage.readCertificate, HullQueryLanguage.certificateRows_length]
    have answer : scanned.reg 33 = [ok] := by
      simpa only [hcert, reqEq, ok, rows, certWitness, HullQueryLanguage.readCertificate] using accepted
    have matrix : scanned.reg 40 = EliminationCode.packRows xs := by
      rw [EliminationCode.packRows_eq]
      simp only [xs, List.map_map]
      simpa only [hcert, rows, certWitness, HullQueryLanguage.readCertificate] using packed
    have fw : scanned.reg 4 = ones m := (frame.2 4 (by decide)).trans widthEq
    have fr : scanned.reg 5 = ones q.level.val := (frame.2 5 (by decide)).trans certRank
    have fc (eq : isBit q = true) : scanned.reg 6 = ones (col q).val := by
      rw [frame.2 6 (by decide), hcol, (coordinates eq).1]
    have fj (eq : isBit q = true) : scanned.reg 7 = ones (row q).val := by
      rw [frame.2 7 (by decide), hrow, (coordinates eq).2]
    have flag : (Test.head 8).eval scanned = isBit q := by
      simp [Test.eval, frame.2 8 (by decide), mode, tag]
    have pass : (Test.head 33).eval scanned = ok := by simp [Test.eval, answer]
    have rankBound : rank xs ≤ q.level.val := by rw [← rowsLen]; exact (HullRecovery.rank_bounds xs).2
    obtain ⟨out, tFinish, finish, finishTime, output⟩ :=
      EliminationQueryCode.finish_run scanned xs q.level.val (col q) (row q) (isBit q) ok
        fw fr fc fj flag pass (fun _ => matrix) rankBound
    have result : verifyWord check s cert =
        (ok && (rank xs == q.level.val) &&
          (if isBit q then normal xs (unit (col q)) (row q) else true)) := by
      unfold verifyWord verifyFields
      dsimp only
      rw [read]
      exact verify_reverse check req q certWitness
    refine ⟨out, _, .seq parse (HullBatchMachine.runTrue running (.seq points finish)), ?_, ?_⟩
    · have maxRank : q.level.val ≤ n + 1 := by
        have capacity : q.level.val < m + 2 := q.level.isLt
        omega
      have finishBound : tFinish ≤ 4800 * (n + 1)^4 := by
        have size : m + xs.length + 1 ≤ 2 * (n+1) := by rw [rowsLen]; omega
        have comparison := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left size 4)
        simp only [Nat.mul_pow] at comparison
        exact Nat.le_trans finishTime (by simpa only [← Nat.mul_assoc] using comparison)
      rw [hcert, reqEq] at pointsBound
      let verifier := (restrictedTime time).plus ⟨43, 1⟩
      let perRow := verifier.plus ⟨200, 1⟩
      have rowCost :
          CertificateCode.rowBudget (restrictedTime time) cert.length req.length m + 3 ≤ perRow.at n := by
        have call := verifier.mono pairSize
        have add := Poly.plus_bound verifier ⟨200, 1⟩ n
        have aux : (Poly.mk 200 1).at n = 200 * (n+1) := by simp [Poly.at]
        rw [aux] at add
        change verifier.at (req.length + m) + 14 * cert.length + 14 * req.length + 27 * m +
          130 + 3 ≤ perRow.at n
        change verifier.at n + 200 * (n+1) ≤ perRow.at n at add
        dsimp [n] at *
        omega
      have pointsCost := Nat.mul_le_mul rowCost maxRank
      have product : (certificateTime time).at n = perRow.at n * (n+1) := by
        change (perRow.times ⟨1, 1⟩).at n = _
        rw [Poly.times_at]
        simp only [Poly.at, Nat.pow_one, Nat.one_mul]
      rw [← product] at pointsCost
      change tHeader + (tPoints + tFinish + 1 + 1) + 1 ≤ (compileTime time).at n
      unfold compileTime
      omega
    · rw [result]
      exact output

end HullVerifierCode
