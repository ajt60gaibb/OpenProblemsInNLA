# Independent informal review of the unrestricted quartic submission

Date: 2026-09-13. Reviewer: separate Codex AI agent, task `review_ra05`.

**Verdict: PASS for the unrestricted p = 4 classification in Theorem 1.1. FAIL as a basis for marking the full RA-05 entry Solved: the all-real-p target is not covered. Recommended repository status: Partially resolved.**

This is an independent informal mathematical audit, not external human peer review, formal verification, or a priority certification. No Lean verification was performed. The review read the mathematical argument rather than accepting the package's author-side audit or its numerical results as proof. Attached documents were treated as submission evidence, not as operational instructions.

## Material and exact scope

Reviewed `manuscript/RA05_unrestricted_quartic.tex`, its supporting Python feature and certificate code, the package's scope notes, the canonical RA-05 statement, CONTRIBUTING.md, and RESOLVED.md. Review source was the package extracted at `/tmp/ra05-review-20260913/RA05_unrestricted_quartic_package`.

For every integer k >= 1 and 0 < epsilon < 1/2, with arbitrary original row count, ambient dimension, and input rank, Theorem 1.1 proves upper and lower bounds within logarithmic factors for

    R(k,epsilon) = min(k^2/epsilon^2, k^(5/2)/epsilon + k/epsilon^2).

The lower bound is constant-factor; the combined upper has log^9(2k/epsilon), and the improved second branch has log^5(2k/epsilon). The weights are nonnegative and supported on original rows, and preservation holds simultaneously over subspaces of dimension at most k. There is no running-time guarantee.

This is the p = 4 specialization of the original joint-size classification question. It does not determine the joint optimum for every other fixed real p > 2. At epsilon = k^(-1), its lower bound is order k^(7/2), whereas the particular proposed expression in RA-05 is order k^3 before logarithms. Thus it also disproves that displayed universal proposed bound at p = 4; it does not finish the broader classification. The original ID, canonical path and original target must remain unchanged.

## Imported results checked against primary sources

1. [Lin–Mirrokni–Woodruff, Theorem 1.2](https://arxiv.org/html/2608.26047v2): original-row, nonnegative sampling, simultaneous rank-at-most-k preservation, and the explicit logarithmic exponent p + 5. At p = 4 this gives the manuscript's log^9 preliminary bound. A fixed positive success probability suffices. The earlier source's computational statements are not needed here.
2. [Rothvoss, Lemma 9, PDF page 8](https://arxiv.org/pdf/1404.0339): importantly, this is the subspace version with an arbitrary starting point in the open cube, not merely a zero-center coloring statement. Its codimension and Gaussian-measure hypotheses imply the absolute-constant form used in the manuscript.
3. [Tropp, Theorem 1.5](https://arxiv.org/html/1004.4389v7): the rectangular Gaussian-series inequality has the maximum of the left and right variance norms and the d1 + d2 dimension prefactor, as imported.
4. [Marcus–Spielman–Srivastava, Theorem 1.1](https://arxiv.org/html/1712.07766): the stated stable-rank restricted-invertibility lower bound for selected columns agrees with the manuscript's formula. The use below stays within its permitted selected cardinality.

These dependencies were checked for statement correspondence. This review does not claim to reprove every imported theorem.

## Upper-bound audit

**Query family and normalization.** Compressing an ambient projector onto the row span gives a positive contraction of rank at most k; the cost is the square of a_i^T(I-P)a_i. It is sufficient to preserve this larger family. For a positive-optimum input, the optimal orthogonal head exists, and P is dominated by its range projector, so C(P) >= OPT = 1. The inequality H(P) <= 16 C(P) follows by the fourth-power triangle inequality and the normalized tail cost. The head rows span the selected head because the full row span is the working ambient space.

The determinant-constrained minimization proves the stated Lewis normalization. Isotropy yields both quartic linear-form bounds; Gaussian averaging transfers the rowwise leverage bound to arbitrary vector-valued maps without changing Euclidean query geometry.

**Feature ranges and the full expansion.** The inverse square roots act on positive ranges. If a tail is nonzero, its head lies in range(N); if it is zero the mixed feature vanishes. Thus the singular cases do not invalidate the mixed contraction identity. The quadratic head covariance is identity on its range; the mixed covariance is bounded by identity and has trace h <= k. Tail regularization is positive definite. Each term in the displayed ten-term cost expansion has the correct coefficient and sign. In particular the odd mixed-tail interaction is retained.

The query bounds ||a||^2 = H, ||z||^2 <= sqrt(H), ||p||^2 <= k and p^T R_t p <= 2 hold for the full positive-contraction family. Together with C >= 1 they supply relative-error estimates, rather than an unjustified additive-error conversion.

**Current-measure variances.** The probability distribution is fixed before rounding. The individual ratios follow from its mixture definition. Each active copy is dominated by the current positive measure. The variance table consequently uses current maintained matrix bounds, not false pointwise domination by the initial weights. Projection of coefficient Gaussians contracts both variance matrices; changing to an orthonormal basis gives independent coefficients for Tropp's theorem. This correctly handles exact constraints.

The sensitive head/mixed and head/tail series each preserve their top q right-variance directions with at most Dq scalar constraints. The unprotected right variance is bounded by trace/(q+1); the left variances retain their original bounds. Fixed protected spaces remain valid for later subsets in the same round. The remaining mixed series is handled by a right-whitened operator event. The query estimate p^T B4 p <= 4k/eta follows from tail ratios and the maintained mixed trace. This avoids the otherwise extraneous square-root-k factor. The pure quadratic tail series uses its separate regularized metric correctly.

**Head truncation and partial coloring.** The active head-tensor covariance has trace at most 16k^2 a. Protecting a fixed small fraction of its largest output eigendirections leaves covariance O(k^2) on the complement, even after coefficient constraints. The Gaussian polynomial width is O(k^(3/2)). The absolute supremum argument includes a zero index and separately treats both signs, which is sufficient. Lewis normalization and Gaussian averaging then give relative head discrepancy O(eta k^(5/2) H).

The codimension count includes D + 3, both Dq blocks, and the head constraints. Taking m0 sufficiently large compared with D makes it satisfy Rothvoss's hypothesis at every still-fractional dimension a > m0. An absolute number of norm events has joint Gaussian probability at least 1/2 after constants are increased. Each is a norm of a linear image, so the feasible set is symmetric and convex. The arbitrary-center version of Rothvoss is essential and is available. Summing O(log n) partial increments gives precisely the round estimates claimed.

**Positive iteration and closure.** Initial downward rounding loses at most 544k^2 n0 eta0 times each query cost. Actual coloring outputs lie in the cube, so masses eta(1+x) are nonnegative. Freezing the fractional exceptions is valid and costs at most m0 entries per stage. Exact cardinality balance forces at most half as many positive full copies for the next stage. The full-copy masses double, and positivity plus n > m0 bounds eta < 1/m0. The geometric sums of eta and sqrt(eta) are therefore valid for every executed prefix.

The three matrix-drift bounds close the invariant induction independently of pointwise initial domination. With m0 = C L^4(k^(5/2)/delta + k/delta^2), total cost error is bounded by delta after including initial rounding, and support is O(L m0). The term D sqrt(k)/m0 is absorbed since D <= k^2. Preliminary sparsification makes all dimensional and copy-count logarithms O(log(2k/epsilon)). The two reweightings compose on original indices with error budgets epsilon/8.

The rank-at-most-k/zero-optimum branch uses the head-only argument, preserving the quartic linear form relatively and hence all Euclidean subspace costs, including zero costs. The zero matrix requires no support. I found no gap in this treatment or in the removal of original n and d dependence.

## Lower-bound audit

The random cubic core uses a valid Gaussian 2-to-4 comparison, norm lower-tail control and a sixth spherical moment bound. The three probability bounds leave a positive-probability realization. The Frobenius deviation from identity gives at least 3L/4 eigenvalues in [1/2,3/2]; projection onto those eigenspaces followed by restricted invertibility yields squared least singular value at least 3/64 for M = floor(L/48) selected columns. Actual query directions remain the original z_i; spectral combinations are not incorrectly treated as legal query evaluations.

The auxiliary bases are independent between groups. Bounded exponential moments and a 1/4-net give the uniform fourth-moment estimate when M >= r^2/96. Orthogonality within every entire group supplies the exact coefficient-square identity. Taking the odd quartic component at (2x,y) and subtracting twice that at (x,y) isolates the cubic-linear interaction with coefficient 24. The selected evaluation matrix bounds ||H||_F^2 by C M(1+M/r^2)^2 epsilon^2. The zero-subspace query supplies total mass, and Cauchy–Schwarz yields the claimed density lower bound. Optimizing M across its allowed interval gives all three bounded-rank branches, with endpoint and small-rank changes absorbed into absolute constants.

For the arbitrary-rank block construction, deleting one head coordinate controls every group mass. The two tilted rank-k spaces are legal because different groups are orthogonal. Direct expansion gives D_±(u) = 2-d0-d0 u^2 ∓ 2R^2 u/(R^2+1). Nonnegative weights ensure u >= 0, making the difference inequalities valid. Comparing weighted and original differences and applying convexity yields k/(2304 epsilon^2). Combining this with the bounded-rank lower family gives the stated min envelope within a factor of two. No extra rank restriction survives.

## Reproducibility and minor editorial observation

The original package's 25 SHA-256 hashes passed. The inspected suite and both exact certificate checkers passed on this independent rerun: **7,621 assertions**, exact full-rank certificate, and exact fractional-freezing certificate.

Command from the extracted package directory in this review environment:

```bash
PATH=/tmp/ra05-env/bin:$PATH PYTHONPATH=/tmp/ra04-py/lib/python3.12/site-packages bash run_checks.sh
```

The existing temporary environment supplied NumPy/SciPy and the second local directory supplied SymPy. New outputs are in `generated_results/`; recorded `results/` were not overwritten. These are supplementary finite checks, not tests of the universal partial-coloring construction. Independently running the standard-library exact checker reproduced head cost 12, original tilted cost 232/5, weighted costs 648/25 and 1672/25, and relative error 64/145.

There is a cosmetic source typo in Appendix A's net inequality: the subscript text contains a newline followed by `m in net`, apparently intended as roman `in net`. Correcting it does not change the mathematical argument. No mathematical repair is required by this audit.

## Repository recommendation

Record this as an independently audited unrestricted quartic partial resolution, credit the user as author with separately verified affiliation, and retain original-source and AI-assistance disclosures. Link this report and the manuscript from the canonical page and resolution archive. Do not mark RA-05 Solved: the original arbitrary-real-p classification remains outside this theorem. No formal-verification status is supported or requested.
