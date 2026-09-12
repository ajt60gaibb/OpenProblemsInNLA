# PR #181 — independent spectral partial-results review

Reviewer: Codex AI agent `/root/audit_tensors_complexity`. Date: 12 September 2026. This is an independent informal AI mathematical/evidence audit, not external human peer review or formal verification.

**Verdict: PASS at the stated scopes for all five entries.** KE-02 may become Partially resolved; SP-08 and SP-09 appropriately retain Partially resolved; SP-03 and SP-07 appropriately remain Open. None of the five original universal targets is fully resolved.

Reviewed head: `fed3f4bcfd11de1d6509522849e8ffa773007979`, clean read-only worktree `/private/tmp/nla-audit-181`. Published comparison base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`. No repository, git, or remote mutation was performed. Packaged AI reviews and numerical claims were not treated as authority.

## Target fidelity and statuses

All five permanent canonical paths and IDs are retained under `eigenvalues-and-inverse-problems`. Original mathematical-target prose and its following retained material compare byte-for-byte with the published base from the relevant original statement/context boundary. Difficulty, importance, rating rationale, and the 217-entry registry are unchanged. The new material records narrower results after the unchanged original targets; it does not substitute an easier question.

| Entry | Independently supported contribution | Correct status boundary |
| --- | --- | --- |
| KE-02 | Deterministic weak-coupling perturbation; constant diagonal with equal off-diagonal magnitudes, allowing complex phases; arbitrary order two | Partially resolved. General varying, strongly coupled tridiagonal inputs remain. |
| SP-03 | Generic regular-locus skew-multiplier reduction with saturation; rederivation of the known value `D_1=4` | Open. No new generic degree at higher rank or all-ranks formula is proved. |
| SP-07 | Sharp constant one on the subclass with at most two eigenvalues on one side | Open. The optimal constant for all normal pairs is not determined. |
| SP-08 | Signed-threshold reduction and exact finite cases `(n,a)=(8,1/2),(10,0),(11,0)` | Partially resolved. These do not establish every dimension and interval parameter. |
| SP-09 | Amplification invariance when at least one normal spectrum has at most two distinct points | Partially resolved. The general class with at least three values on both sides is not covered. |

## Independent mathematical review

I read the complete final KE-02, SP-03, SP-08, and SP-09 proofs and SP-07 result, as well as the retained prior weak-coupling argument and the result-classification documents. Findings follow.

### KE-02

For Theorem A, sorting the original diagonal and applying the monotone ramp from `-delta` to `delta` yields diagonal spacings at least `2 delta/(n-1)`. The row-sum bound gives `||R||_2 <= eta`, so Hermitian eigenvalue perturbation leaves gaps at least `delta/(n-1)` under the displayed weak-coupling hypothesis. Sorting costs `O(n log n)`; returning the diagonal perturbation in original index order preserves tridiagonal structure. Comparisons and complex magnitudes respect the problem's exact arithmetic and square-root model.

For Theorem B, complex off-diagonal phases can be removed by a diagonal unitary. In the large-coupling branch the eigenvalues are `tau + 2r cos(k pi/(n+1))`. Their adjacent gaps are at least `12r/(n+1)^2`. The branch threshold `r > delta/(4n)` therefore yields the claimed lower bound, using `(n+1)^2 <= 3n^2` for `n>=2`; since `delta<1`, it also implies the fixed polynomial gap required by the original target. The trigonometric expression is only used in the proof; the algorithm need not evaluate it. The small-coupling branch is covered by the ramp theorem. Zero coupling, the threshold boundary, and arbitrary complex phases are covered. The order-two formula directly gives a gap at least `2 delta` after perturbing the smaller and larger diagonal entries in opposite directions.

These are substantive classes of the original problem, including its suggested Toeplitz starting case; they justify the partial status without asserting a result for arbitrary tridiagonal matrices.

### SP-03

The proof consistently uses the complex **bilinear** Frobenius pairing and transpose, not the Hermitian norm or conjugate transpose. The differential of `X^T J X=J` is surjective onto skew matrices, and its annihilator yields the unique skew multiplier in `U=X+JXK`. With `Q=I+K^2`, the identity `U-JUK=XQ` gives the rational reconstruction on `det(Q) != 0`.

I independently checked the signs in the quartic system: with `G=U^T U` and `R=U^T J U`, its skew equation is `R+GK+KG-KRK-QJQ=0`. There are exactly `m(2m-1)` skew variables and equations. The normal-bundle parameterization and the proper hypersurface `det(I+K^2)=0` give a bad-image dimension at most `N^2-1`, so generic actual critical points avoid that denominator. The argument does not count the unsaturated quartic system indiscriminately: saturation by the determinant, or an inverse-variable equation, is required and explicitly retained.

For `m=1`, the displayed generic quartic and a concrete point with nonzero discriminant and no denominator roots establish the known degree four. This does not yield the conjectured all-rank degree formula. The retained Open label is accurate.

### SP-09 and its SP-07 consequence

For a normal matrix with two distinct values `a,b` and multiplicities `p,n-p`, a candidate orbit distance `t` necessarily satisfies three threshold conditions: every eigenvalue of the other matrix is within `t` of at least one anchor, at least `p` are within `t` of `a`, and at least `n-p` are within `t` of `b`. The latter two follow by dimension intersection with the spectral subspace having distance strictly greater than `t`; normality is essential and present.

These conditions are also sufficient: allocate the eigenvalues forced to a single anchor, then fill remaining capacities with the values eligible for either. This proves equality with bottleneck spectral matching, including repeated eigenvalues and closed distance thresholds. Scalar limits and reversal of the two matrices are handled. Repetition multiplies all relevant counts and capacities by the same integer, leaving the feasible thresholds unchanged. Thus unrestricted finite unitary amplification preserves the distance on the stated subclass. The other normal spectrum may be genuinely noncollinear in the complex plane; the result is not restricted to self-adjoint pairs.

For SP-07, taking the identity unitary then gives the subclass matching inequality with constant one, and the simple shifted diagonal example makes that constant sharp on the subclass. It does not determine the universal normal-matrix constant. Both status boundaries are correct.

### SP-08

The extremal spread can be exposed by the linear functional `xx^T-yy^T`. Writing this as `uv^T+vu^T`, a generic approximation with nonzero coordinates and distinct ratio magnitudes orders its signs into the displayed signed-threshold family. Permutation and simultaneous sign switching give `2^(2n-1)` representatives. A finite subsequence argument handles zero coefficients and ties in the original exposing functional. It establishes the existence of a threshold-pattern maximizer for the continuous symmetric entry box, not a claim that every maximizer is rank two.

The exact polynomial certificates correctly bound both extreme eigenvalues: nonnegative coefficients of a translated monic polynomial exclude positive translated roots. Applying the same check to the reflected polynomial bounds the negative extreme; nonnegative endpoint sums and the exact squared-width comparison produce the desired spread bound. The rank-two branch uses its characteristic quadratic. The explicit block attainers have exactly rank two because the compressed determinant is proportional to `(a-1) k(n-k) < 0`; their squared spreads are 73, 133, and 161 in the three asserted cases.

I checked the coverage implementation's exact Newton identities and integer-overflow bound, not just its printed PASS result. For every tested dimension and entry bound, the stated dominating integer `n 2^n (nb)^n` is below signed 64-bit range and controls the matrix-power, coefficient, and partial-sum quantities actually computed. Root-certificate arithmetic uses Python integers. All characteristic-polynomial classes are checked against the full regenerated family; the verifier does not infer coverage from a hash or sampled patterns. Floating-point eigenvalues are used to propose certificates, not to accept them.

The parent reviewer separately reread the SP-08 proof and checkers and reported agreement with this assessment. This corroboration is another informal AI review, not an additional formal certificate of the analytic reduction.

## Primary references and attribution

Checked primary sources include [the workshop report, Problem 3.2](https://arxiv.org/html/2602.05394v3) for KE-02; [Baaijens–Draisma, §5](https://arxiv.org/html/1405.0422) for SP-03's known small degrees and original degree question; [Calkin and collaborators, Theorem 9 and surrounding computational discussion](https://arxiv.org/html/2510.15919v1) for SP-08's prior cases; [Marcoux–Sarkowicz–Zhang, §3.5](https://arxiv.org/html/2508.13834v1) for the known self-adjoint amplification result; and [Parusiński–Rainer, Proposition 3.4](https://arxiv.org/html/2603.23056) for the existing universal-constant bounds relevant to SP-07. The submission retains the older credited results and distinguishes new recorded subclasses from a claim of historical novelty. No exhaustive priority search is asserted.

The supplied author affiliation is consistent with the official [Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/). The wrapper identifies AI assistance, historical self-reviews, the new informal audits, and the absence of Lean or external human verification.

## Independent executions and evidence limits

I inspected all invoked code before copying the reference material to `/private/tmp/nla-181-independent-7m_74lan/spectral`. Certificate decompression and generated logs were confined to that scratch copy. The invoked paths perform local mathematical computation and file reads/writes; no dependency installation or remote action was run. The finite algebra checks used Python 3.12.14 and SymPy 1.14.0; SP-08 coverage used the bundled Python/NumPy runtime.

Fresh logs under `independent-reruns/` record:

| Check | Result |
| --- | --- |
| KE-02 | PASS: 378 ramp cases, 1,134 branch/gap checks, 30,240 exact complex-rational gauge identities, and rejection of two invalid-class inputs |
| SP-03 | PASS: 12 rational reconstruction/quartic-identity cases across `m=1,2,3`, plus the quartic discriminant and exceptional-root checks |
| SP-09 | PASS: 15,024 exact assignment/threshold comparisons and 30,048 multiplicity-amplification checks |
| SP-08 `(8,1/2)` | PASS: all 32,768 patterns, 5,648 distinct polynomials; integer-scaled squared bound 292, hence 73 for the original matrix |
| SP-08 `(10,0)` | PASS: all 524,288 patterns, 65,077 distinct polynomials; squared bound 133 |
| SP-08 `(11,0)` | PASS: all 2,097,152 patterns, 222,013 distinct polynomials; squared bound 161 |

The smaller finite tests are diagnostics, not substitutes for the universal analytic arguments. For SP-08 the exhaustive exact finite certificate verification, combined with the independently read reduction and explicit attainers, supports precisely the three computer-assisted subcase proofs. It says nothing about unenumerated dimensions or parameters.

## Source preservation and visual review

Of the 49 original hash entries, 41 match the retained bytes directly or after lossless certificate decompression. Eight final Markdown files differ as disclosed: KE-02/proof.md; SP-03/proof.md and result.md; SP-07/result.md; SP-08/proof.md and result.md; SP-09/proof.md and result.md. The original eight pre-attribution Markdown files were unavailable to this reviewer and the parent reviewer. **Their exact semantic preservation relative to those unavailable originals cannot be independently established from the old hashes.** The final mathematical contents of all eight were independently audited, and the disclosed differences do not create a mathematical blocker. This report does not claim a stronger archival comparison than was possible.

Using the PDF skill's render-and-inspect procedure, I visually inspected both pages of each canonical PDF for KE-02, SP-03, SP-07, SP-08, and SP-09: ten pages total. All are readable and consistent with the reviewed status boundaries. No clipping, overflow, missing mathematical glyph, or orphaned heading was found. The ordinary SP-08 paragraph continuation at a page boundary does not lose content. Renders are retained as `{ID}-{1,2}.png` in `/private/tmp/nla-177-181-pdf-review`.

**Acceptance boundary:** publish the five contributions with their stated partial/supporting classifications, preserving all original universal targets. No full-solution, Lean-verification, external-human-review, or priority claim is supported by this audit.
