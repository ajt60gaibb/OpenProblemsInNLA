# MF-12 independent complete mathematical source review

**Approve the complete mathematical source route for all 28 frozen exports;
withhold mechanical and publication acceptance.** No blocking mathematical,
model or scope defect was found in the exact reviewed snapshot. In particular
the final source theorem retains every nonnegative real exponent, a fixed
positive dimension, exactly two distinct real matrices, fixed positive ordered
constants, every positive word length and the actual nth-root limit one.
MF-12 is not yet fully Lean verified: the latest real build still failed in
four earlier modules, and the new final assembly has not been built.

Reviewer: OpenAI Codex agent `/root/next_elimination`, independent of proof
implementation author `/root/next_matrix_functions`. I read Lifted,
Realization and Solution in full, completing the earlier source reviews of
the other fifteen proof modules. This directory retains the entire nineteen-file
project import closure: seventeen proof modules, Definitions and Solution,
2482 source lines. `CHECKS.json` records every source hash, the frozen boundary,
exact canonical source provenance and all prior review hashes. Each of the 28
exported signatures occurs once and matches the independent Challenge after
whitespace normalization. Solution contains exactly the 28 corresponding
LeanCert kernel assertions and axiom-print commands. It imports no Challenge.

The canonical problem and complete authored manuscript were read from actual
Git-bound sources at `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. The previous
statement, fourteen-export prefix, six-module prefix and Jordan/lower-bound
reports explain the complete matrix construction, actual word maxima, genuine
Euclidean operator norms, arbitrary-gap budget, every-word upper bound,
every-length lower word, Jordan growth and real root limit. Their precise
hashes are part of this review chain. All earlier source dependencies matched
those reviewed snapshots when this complete snapshot was taken; later
compiler repairs require explicit byte-bound reconciliation.

## Actual lifted family and distinct generators

Lifted preserves the frozen Kronecker definition and canonical finite-product
coordinate equivalence. If a right tensor factor has an entry equal to one,
reading that coordinate recovers every entry of the left factor. The resulting
injectivity lemma proves the two lifted matrices differ because the actual
Jordan factor has unit diagonal and the actual fractional generators differ.
It works also for m=0. Distinctness is proved from coordinates, not asserted as
a hypothesis or inferred from a potentially noninjective family encoding.

For every fixed alpha in (0,1), m>=0 and n>=1, the exact word identity tensors
the original six-dimensional word with J_m^n. The lower proof uses the already
proved prescribed base word of exact length n. Both factors' lower bounds are
nonnegative before multiplication, and the tensor norm comparison divides
only by the positive dimension product 6*(m+1). This gives exactly the frozen
constant `fractionalLower * jordanLower / (6*(m+1))`.

The upper proof quantifies over every binary word of length n, combines its
actual base norm bound with the Jordan norm bound, and applies the tensor
upper comparison. The constant is exactly the frozen
`(6*(m+1))*fractionalUpper*(m+1)`. All inequalities refer to the genuine induced
Euclidean operator norm and the finite-family maximum. There is no appeal to
an unproved exact tensor spectral-norm formula, although the deliberately
coarse comparison suffices. Positive n justifies the real-power identity
`n^(alpha+m)=n^alpha*n^m`.

The lifted constants and matrices depend only on alpha and m, not n. Positivity
of the lower constant is proved directly. Their ordering c<=C follows from
the already established pair of actual growth inequalities at n=1. That step
is not circular: both inequalities and the finite maximum semantics precede
the comparison. Positive lower bound and c<=C give positive upper bound when
needed for the root-limit theorem.

## Every nonnegative real exponent, including zero

Realization uses the natural floor m of gamma. The gamma>=0 premise gives
m<=gamma. If gamma=m, the chosen family is the actual pair {J_m,0} in dimension
m+1. J_m has a unit diagonal and is nonzero, so the finite set has exactly two
members and is nonempty. Its maximal growth is exactly the norm of J_m^n,
including all words with zero generators, as established by the previous
family-growth theorem. The integer power is converted to the specified real
power, and the positive constants are ordered using the n=1 bounds. The case
gamma=0 gives m=0, dimension one, and the genuinely distinct pair {1,0}.

If gamma differs from m, alpha=gamma-m satisfies 0<alpha<1 by the exact floor
bounds. The lifted pair then has positive dimension 6*(m+1), exactly two
members by the coordinate distinctness proof, and the required every-length
bounds after substituting alpha+m=gamma. Both branches exhibit their matrices
and constants before quantifying over n. There is no dimension or generator
that changes with the requested word length.

In both cases the actual growth sequence, with its true finite maximum
semantics, is passed to the general squeeze theorem. The resulting limit is
`familyGrowth(M,n)^(1/(n:R)) -> 1`, exactly the canonical joint-spectral-radius
condition. The finite-length lower bound keeps the real roots nonnegative
where monotonicity is used; n=0 is irrelevant to the limit. Neither a default
value of a supremum nor a default-valued limit is used to force the result.

Thus the complete source route meets the original all-real-exponent target.
It also proves exactly two matrices, while the original question only asks
for a nonempty finite family. It does not claim the source's additional
rational-entry or irrational-example corollaries, optimal constants/dimensions,
or convergence after dividing growth by n^gamma. These omissions do not
remove any part of the original canonical question.

## Actual build status is separate

I inspected the authentic downloaded module log for Linux run35031607095,
commit `4bd2d76ec6e37696ff0c2d5feacf21e342371f27`, and retained its exact hash
and full contents. Words, Parameters, Norms, Tensor, MatrixAlgebra, Budgets and
HolderBound completed successfully; their fourteen exported declarations show
only the standard foundational axioms. The four previous repair changes are
therefore genuinely accepted in that run, rather than merely proposed.

The same log reports failures in RootLimit, PowerBounds, Gaps and JordanEntries.
They concern real-power continuity imports/field elaboration, lambda-bearing
identifier parsing, natural scalar normalization of a list length, and the
finite-index diagonal branch simplification. Their resulting placeholder
axioms are explicitly rejected by LeanCert. The source-level mathematical
identities were checked independently and remain sound, but failed code is
not accepted proof. Isolated standard-axiom lines in a failed module do not
make that whole module pass. The newer downstream and final assembly modules
were not accepted by this run, and no complete-MF-12 success is claimed.

The author's subsequent repairs are outside this immutable reviewed snapshot
until a recorded addendum checks their exact changes. Full publication still
requires a successful source-bound build of all 28 exports, actual transitive
axiom and LeanCert acceptance, default-kernel replay, Comparator with complete
definition matching, rejection controls and two independent final referees.
The manifest's whole-problem-verified status must remain false until those
gates pass. No local Lean/Lake/build command was run by this reviewer.

## Quality, reuse and attribution

The entire mathematical route uses exact identities, symbolic induction,
finite attained extrema, elementary real inequalities, finite Holder and
standard continuity/limits. Coarse fixed constants eliminate expensive
rectangular singular-value calculations, square-root evaluation and large
interval computations. Natural logarithm bounds use exact integer arithmetic.
No finite sample is substituted for an all-word, all-length or all-exponent
proof. The pinned Mathlib API statements used in each source review are
identified in the associated receipts.

All inspected project sources contain ordinary definitions and proofs. The
closure check found no new axiom, proof hole, native proof, unsafe replacement,
custom implementation binding or Challenge import. This lexical check is
only a source safeguard; it is not a transitive kernel audit. The use of
Mathlib and LeanCert diagnostics does not imply the checker software itself
was formally certified by this review.

Original mathematics remains attributed to Matthew J. Colbrook, University
of Cambridge DAMTP. George Stepaniants is credited for the formalization with
the Department of Computing and Mathematical Sciences, California Institute
of Technology, Pasadena, California, USA. The files disclose AI assistance,
retain their license and publish no George email. This is scoped Tau Ceti-style
agent review of correctness, fidelity, generality, reuse, computation, API and
documentation, not official certification or external human peer review.
