# Handoff to Codex: independent verification before any repository update

## Objective and honesty constraints

Review the supplied partial results against the original target statements in
`ajt60gaibb/OpenProblemsInNLA`, category `eigenvalues-and-inverse-problems`.
The base snapshot is `f41f1f9ffa2171550d4bb795862c6170c4f26070`.

The earlier requested three-hour research session did not occur. This bundle
was produced in the later active reply. None of the 13 full targets is claimed
resolved. The manuscripts were generated with ChatGPT, with local calculations;
there has been no separate Codex review, human peer review, or Lean verification.
Do not convert local script PASS messages into claims of independent review.

## Highest-priority review: SP-08

1. Audit the signed-threshold reduction in Theorem 1. In particular, check the
   variational linearization, the factorization `M = uv^T + vu^T`, ordering by
   absolute ratios, removal of the overall sign of `d`, and the finite
   subsequence argument for zero entries and other degeneracies. The generic
   perturbed vectors need not remain orthonormal; the proof uses the original
   fixed eigenvectors only at the limiting step.
2. Check that ignoring permutation copies is legitimate because spread is
   permutation invariant. The family is a sufficient superset; not every sign
   sequence needs to arise from an orthonormal eigenvector pair.
3. Independently implement or carefully audit the integer characteristic
   polynomial calculation and the overflow bound. Verify every root certificate
   and regenerate full pattern coverage, including the order-eleven case.
   The verifier does not use floating-point eigenvalues.
4. Verify the factor-of-two matrix scaling for the interval `[1/2,1]`; the
   integer bound 292 becomes the original bound 73 for squared spread.
5. Check exact lower-bound matrices and their ranks. They have upper-left
   blocks of size 2, 3, and 4, respectively, and all other entries equal to one.
6. Search for prior signed-threshold reductions, extremal spread results, and
   these finite cases. Compare against any repository updates after the pinned
   snapshot. No novelty claim is supplied by this archive.

A successful review would support the three stated finite cases and the
reduction, not the general Fallat–Xing conjecture. Preserve SP-08's PARTIAL
status. Do not infer an all-parameter order-eight theorem from the single
parameter `a=1/2`, or an all-orders `a=0` theorem from orders ten and eleven.

## Other manuscripts

**SP-09 / SP-07.** Check both necessity and sufficiency of the three counting
conditions for the two-point spectrum. Check the strict-distance subspace
intersection argument and the multiplication of counts under finite repetition.
Search for this likely classical special case before treating it as new
progress. The paper is not a proof for three or more distinct spectral points
on both sides, nor a determination of the global normal matching constant.

**SP-03.** Check the complex bilinear, not sesquilinear, normal-space computation;
the signs in the quartic equation; the incidence-dimension argument; and the
need for saturation. Singular-denominator solutions of the cleared equations
must not be counted. `D_1=4` is already known. No all-ranks ED-degree formula is
provided, so this reduction alone is not a solved or newly counted partial
case of that formula.

**KE-02.** Check the greedy displacement bound and the exact weak-coupling
hypothesis. Do not omit that hypothesis when discussing the runtime/gap result.
The full target permits much larger off-diagonal entries. Assess whether the
subclass is worth recording at all, rather than padding the catalog with an
elementary observation.

## Reproduction and reporting

Read `verification/README.md` and rerun the commands there. A review report
should separately identify analytical correctness, certificate coverage,
arithmetic correctness, literature novelty, and repository relevance. Record
any failure as a failure; do not silently weaken a statement while retaining its
old claim label. Hash the exact versions reviewed.

If review succeeds, draft a narrowly scoped addition following the repository's
current conventions. Do not fabricate the user's name, affiliation, or consent
to an authorship statement. Keep AI assistance visible. No GitHub write or
status change has been performed by the session that produced this bundle.
