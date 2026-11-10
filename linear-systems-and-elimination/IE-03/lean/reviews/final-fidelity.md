# IE-03 independent final review of fidelity and scope

**Phase:** Final proof review, fidelity and scope  
**Reviewer:** Codex sub-agent `ie03_statement_a` (AI agent and nonauthor)  
**Date:** 2026-11-09  
**Verdict:** APPROVE at `89987eb5059ce5a497c18ce50c9b86f8cf394b86`.

I reviewed the concrete source imported by `Solution.lean`, including
`Proof.lean`, the five phase checks and their decoded data, `Certificate/Sound.lean`,
`Certificate/Checkpoint.lean`, `Walsh.lean`, `Lift.lean`, `Path.lean`, and
`Definitions.lean`. The Git tree for the entire `NLA/` closure at this revision
is `dd2514f14b12093b1824857f074b5aa1622e5db8`. I checked the working files
against that revision. The proof module SHA-256 is
`d801f8e2cd600fcbbdbb516679e4c2be763148310da972bfcbc0783235edcb37`.
The frozen statement hashes still pass and the canonical README and ID
registry match published source `3017ea813328900a812c0c105ca16ad6f694857e`.
The field, path and growth correspondence established in statement review A
continues to apply to the unchanged definitions and Challenge.

## Proof-to-target correspondence

- **Real input.** In `Walsh.lean`, `walsh_hadamard` starts from the order-one
  matrix and proves the sign and row Gram conditions after each doubling.
  For each pair of columns the parity factors cancel when the two row
  parities differ. When they agree, the pair contributes twice the
  corresponding product in the preceding matrix. This proves the exact
  Gram identity at order `2 ^ 12 = 4096` for the same real matrix used in
  `Proof.lean`. The seed check links the initial certificate square to
  `walsh 4`, and the lifting theorem carries that origin to `walsh 12`.
- **Certified local steps.** `stepOK` checks both pivot indices, positivity
  of the common denominators, a nonzero pivot numerator, and the pivot bound
  throughout the old active square. It checks the cleared-denominator
  Schur identity at every survivor entry. `step_sound` transfers those
  integer facts to the real pivot predicate and an entrywise equality on
  the entire new active square. The slot decoder returns an unbounded
  signed integer before each check. Rational `peak` is converted to the
  real maximum via the exact cast and absolute-value identities in
  `trace_sound`.
- **Legal lifted steps.** `Lift.lean` proves the two doubled pivots at
  active indices `(2r,2c)` before and after the first deletion, with values
  `p` and `-2p`. The proof bounds every entry after the first pivot by
  `2|p|`, using the original whole-square bound and the nonzero pivot.
  `schur_double_twice` identifies the exact remaining Schur square.
  `PivotPrefix.double` applies these facts to each prefix step and proves
  that the peak doubles. Two such lifts multiply a prefix's order, count
  and peak by four.
- **One full path.** `Trace` includes an actual `PivotPrefix` and an
  entrywise match on the active square at its endpoint. `Trace.append`
  transports the next prefix across precisely that match, preserving
  the selected pivot positions and Schur updates. At each phase bridge,
  `lift_sound` proves the entrywise match between the doubled endpoint
  and the next phase seed. The combined peak is the maximum of the lifted
  earlier peak and the new phase peak. The final prefix has endpoint order
  zero, and `Trace.complete` yields the corresponding `CompletePath`.
- **Exact conclusion.** `counterexample` pairs the real Hadamard proof and
  the complete trace for `walsh 12` with exact peak 4608. Its sign entries
  make the original normalization equal to one. The proof of `cryer_false`
  instantiates the alleged universal equality with this witness and
  derives the contradiction `4608 = 4096`. The certificate generator
  supplies data only. The exported conclusion requires neither an
  externally supplied growth bound nor a hypothesis that a path exists.

I independently decoded all packed checkpoint rows and reconstructed every
local step from the pinned published pivot lists using Python's exact
`Fraction` arithmetic, without importing the certificate generator. I checked
that each decoded table matched the rational recurrence and that the checks
and trace lists used the corresponding coordinates and successor tables.
The five phases checked 10, 16, 22, 28, and 48 local steps on active squares
starting at orders 16, 24, 32, 40, and 48. Their reconstructed total prefix
counts were 10, 56, 246, 1012, and 4096, with peaks 4, 16, 64, 256, and 4608.
The reconstructed first overshoot was the signed pivot +4608 at step 4089.
This arithmetic replay is corroboration. The Lean phase proof bodies use
`decide +kernel` and the symbolic lift and trace theorems.

I inspected `verification/local-build-and-axioms.log` and separately ran
`lake env lean Audit.lean` on the local macOS build. It exited zero and
reported exactly `propext`, `Classical.choice`, and `Quot.sound` for both
exports. This review covers the full original conjecture through one
real counterexample. The exported statements leave the paper's exact
overshoot index, the binary matrix file, the larger-order family, and the
asymptotic conjecture outside their scope. Isolated Linux Comparator and
kernel replay are separate mechanical gates. I did not run them in this review.
