# Affine Hull Verification

Lean checks that the polynomial-time functions computed using one parallel
batch of NP queries equal those computed using logarithmically many adaptive
NP queries exactly when P = NP. The entry point is
`ComplexityImplication.classEquality_iff_pEqualsNP`. The forward implication
requires only inclusion of the parallel class in the adaptive class.

## Build

Run `lake build` with Lean 4.35.0, pinned in `lean-toolchain`. The build
uses Lean's standard library and needs no external Lean packages.
Run the separate finite checks with `python3 check_affine.py`.

For Palomar verification, run `lake comparator` from a clean checkout
on Linux with Bubblewrap. [Challenge.lean](Challenge.lean) states the two
results using only Lean core. [Solution.lean](Solution.lean) exposes the
proved declarations selected by [comparator.json](comparator.json). The
two proof placeholders in the Challenge mark the statements Comparator
checks against the Solution. [formalization.yaml](formalization.yaml)
records the scope, provenance, attribution, and review history.

## What Lean checks

- `HullQueryLanguage.lean` proves that a single batch of Boolean answers
  determines the correct affine hull. `HullBatchProducer.lean` and
  `HullBatchPrograms.lean` implement the batch and assembly with proved
  machine-time bounds. `ComplexityModel/BatchCode.lean` collects the
  replies in order.
- `HullVerifierCode.lean` implements the full query verifier for any
  polynomial-time input checker. Lean verifies the runtime and the
  output for every encoded query and certificate. The proof includes
  witness reconstruction and Gaussian elimination.
- `ReplayParameters.lean`, `ReplayListCode.lean`, and `CandidatePipeline.lean`
  verify a deterministic polynomial-time machine that computes the replay
  clock, enumerates hypothetical answer tapes, and decodes the resulting
  hull candidates. The genuine hull appears when the restriction has a
  solution.
- `CandidateClassifyCode.lean` tests all points of the low-rank candidates
  and prepares the remaining candidates for `GreedySplitterCode.lean`.
  `RoundSemantics.lean` proves that a cut preserves the existence of a
  witness and that a zero mask after failed probes certifies emptiness.
- `SearchRoundProgram.lean` combines those components into a complete
  deterministic machine. `SearchInitCode.lean` and `SearchLoopCode.lean`
  verify initialization, the full sequence of rounds, and its polynomial
  time bound. `ComplexityImplication.lean` connects the resulting decider to
  every NP verifier and checks the reverse direction.

## Correspondence with the standard oracle classes

The statement uses the finite register program model in
[ComplexityModel/Machine.lean](ComplexityModel/Machine.lean). A program
has finitely many fixed register addresses. Each register holds a binary
word, and the instructions read a head bit, remove or prepend a bit,
copy a word, and manipulate a stack of query words. An oracle step receives
one bit from a fixed language. `FPParallelNP` fixes the stack using an
oracle-free producer, then runs a consumer that can query or discard
entries already on the stack. `FPLogNP` allows adaptive queries and
bounds their number by a fixed multiple of the binary logarithm of the
input length plus a constant, using `n + 2` to cover short inputs.
Both definitions also impose a polynomial time bound for all inputs.
This is the one-batch versus logarithmic-adaptive comparison in
Definition 2 of [Naik and Selman](https://cse.buffalo.edu/documents/selman/note.pdf#page=5).

A tape machine can store all registers, the query stack, and the active
call frames as delimited binary strings. In a run of at most `T` steps,
words have length at most the total input and witness length plus `T`, and
the stack grows by at most one entry per step. Call depth is bounded by the
fixed syntax.
Even copying entire words and scanning this storage at every simulated
step therefore costs polynomial time. For an adaptive run, each successful
query instruction needs exactly one tape-machine oracle call. For a
one-batch run, the tape machine obtains answers for the entire producer
stack together, then runs the consumer using those stored bits.

In the other direction, each tape can be represented by two registers
containing fixed-width symbol codes. One stores the symbols to the left
of the head, and the other starts with the current symbol and continues
to the right. A head move transfers a symbol between registers and treats
an empty register as a blank. Reading or adding a fixed-width symbol takes
a fixed number of register instructions. Finite control is implemented with
tests inside a loop. Input, output, and witness encodings can be converted
by scans. For an adaptive oracle machine, copy the query into a register
and invoke one query instruction. For a batch machine, the producer
stores its query words on the stack, and the consumer retrieves their
answers before running the original deterministic postprocessing. A stack
reversal or an equivalent reordering of the answers costs polynomial
time. The same simulations, without queries, preserve the polynomial
time bounds for P and for NP verifiers.

These simulations justify the conventional notation in the research note.
The simulations between the register and tape models are a mathematical
argument outside the Lean development.

## Research background

The [written verification note](output/pdf/affine-hull-verification.pdf)
gives the argument and the prior-art assessment. Naik and Selman asked
whether Hypothesis B implies P = NP. Buhrman, Fortnow, and Torenvliet
used adaptive transcript enumeration and studied the class equality.
Arvind and Torán connected the equality to sparse reductions and
logarithmic approximability. The distinguishing step here uses a
polynomial-size list of possible affine hulls to find a witness or cut one
coordinate while preserving satisfiability. Publication priority remains
unverified. [Naik and Selman](https://cse.buffalo.edu/documents/selman/note.pdf#page=2) ·
[Buhrman, Fortnow, and Torenvliet](https://ir.cwi.nl/pub/1902) ·
[Arvind and Torán](https://eccc.weizmann.ac.il/report/1998/027/)

The note illustrates the batch on Boolean circuits using a padded
row-echelon matrix. The Lean construction applies to any fixed NP verifier.
It recovers the canonical linear normal form whose kernel is the span of
the lifted witnesses. The maximal feasible rank determines the bits of
that form. The decider checks low-rank candidates directly and uses a
greedy parity mask for the remaining ones. A nonzero mask removes one
free coordinate and keeps the existence of a witness unchanged.

Ludwig Leitmeir supplied the exploratory discussion and directed
verification and packaging. ChatGPT contributed the
exploratory argument, and Codex produced and checked the Lean
development. The current review record covers machine checks and finite
tests. Independent expert assessment remains open.

The code and research note are covered by the [MIT license](LICENSE).
