# Status and exact remaining target

**NM-01 is not fully resolved by this package.** This is a second-round partial-results submission for review.

The original target is a uniform algorithm, polynomial in total binary input length, for the exact minimum-volume threshold decision on every input satisfying the repository's weak SSC promise. The hidden factors are not supplied. The algorithm must have polynomial runtime on all inputs, while correctness is required only on promised inputs.

The new factor-recovery theorem assumes stronger SSC and an exact decision/value oracle. It does not construct that oracle. The weak-SSC example shows that the proposed projective probes can leave the entire promise. The SOS theorems rule out fixed degrees and polynomial-size standard dense levels for the stated input-preordering approach; they do not prove that every polynomial-time method fails.

No theorem here provides the missing polynomial-time value oracle, avoids facet enumeration on all promised instances, or supplies a promise-preserving general complexity-hardness reduction. Checking SSC itself is a separate task and is not a substitute.

The proofs are self-checked and supported by exact rational computations. There is no independent mathematical audit, external peer review, or Lean/formal proof-assistant verification. Twenty-three new full-suite test methods and sixteen original regression methods passed; this count is not an asymptotic proof or an independent review. Exact full-monomial cross-checks supplement the quotient-basis SOS verification.

The canonical repository entry was read directly through the web. Its exact assumptions are retained in the report. No repository edits were made, and no `Solved` or `Lean verified` claim is warranted.
