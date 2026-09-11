# Independent audit of PR40 and PR54 — 11 September 2026

**Verdict: no blocking mathematical or target-preservation error found at the frozen heads. Both PRs are reasonable to accept with exactly their stated scopes.** This is a fresh analytic and exact-computation review, not reliance on the contributor's PASS labels, external human peer review, a proof-assistant formalization, or a claim of historical priority.

Reviewed heads:

- PR40: `06ec182448d1acd802ec416f413ff9b3d5161cc2`
- PR54: `27f1498ba2a9f269c7ef9a5fe38ccf59c246d005`

The seven factorization manuscript bodies, three frame manuscript bodies, conference certificate exposition, all twelve changed canonical mathematical statements, and the code used below were read. Each final manuscript's complete body matches its reviewed/submitted TeX source, with its declared SHA-256 checked. All twelve original canonical statement bodies match `origin/main` after removing only the delimited submission addendum and dated status metadata; no original target has been substituted, no ID reassigned, and no canonical path moved.

## Recommended status by entry

| Entry | Result supported by this audit | Correct status |
|---|---|---|
| NM-03 | Exact rational-input nonnegative rank-two approximation decision is NP-hard; positive SPD and simple-spectrum strengthenings valid | Solved |
| NM-04 | Exact rectangular Rowland–Wu coefficient identity, including vanishing minors and dimension-one cases | Solved |
| NR-03 | Nonnegative rank exactly eight only for the fixed three-bit matrix | Partially resolved |
| NR-04 | Nine-point squared-distance matrix has nonnegative rank exactly seven | Solved |
| PF-01 | Real PSD rank four at n=5,6; stated general upper bound and monotonic lower bound valid | Partially resolved |
| PF-02 | Minimal real congruence quotient can be disconnected, including positive examples in all k>=3 | Solved |
| PF-05 | Straight-line infinitesimal rigidity iff uniqueness for the exact rank-three, PSD-size-two definition | Solved |
| FR-02 | Sharp full/nearly-full sparsity leading constant in the complex cyclic Fourier model | Partially resolved |
| FR-04 | Sharp weighted planar inequality and general polynomial auxiliary bound; exponential target untouched | Open |
| FR-09 | Four exact certificate-backed dimensions, 166,209,256,1505 | Partially resolved |
| FR-10 | Sharp fixed Walsh sparsities 2,3,4 and full/nearly-full leading constants | Partially resolved |
| FR-11 | Twelve unrestricted symmetric measurements suffice in real dimension seven, plus stated stability and exact decoder | Partially resolved |

## PR40 proof audit

The paths in this section are under `pr-40/references/colbrook-factorization-2026-09-11/reviewed-sources/`.

### NM-03 — `NM-03_rank_two_approximation_hardness.tex`

The reduction starts from positive one-in-three SAT with distinct variables in each clause. The source's NP-complete starting problem is supported by [Hasan–Mondal–Rahman](https://arxiv.org/html/2108.12500), including its stronger positive planar version. No assumption about rational certificates for arbitrary real feasible factors is needed.

The two anchors in the homogeneous equation force either a one-in-three assignment, its complement, or one of the two constant Boolean vectors. Deleting unused variables is necessary and is done. The rational vector with original coordinates 1/3 and anchors 1,0 proves that the nonconstant kernel subspace is nonempty even for unsatisfiable instances.

The projector construction is exact rational linear algebra with polynomial bit complexity. Its three spectral subspaces give the claimed rational threshold. The row-space orthogonal decomposition, including its equality conditions, correctly forces every rank-at-most-two matrix at that threshold to be `lambda uu^T+vv^T`. This argument does not silently assume symmetric approximants. Strict positivity of the input follows from the projector entry bound.

The critical endpoint-rounding lemma (lines 114–146) is valid: nonnegativity gives `Nab<=1+delta`, the variance identity bounds the sum of endpoint products, and `L^2>=4/N` converts row residuals to at most `3N delta=1/4`. Integrality then forces exact zero clause residual. Both extrema survive rounding, so the Boolean vector is nonconstant. Completeness is explicit: the two-row-type positive matrix admits nonnegative factors of inner dimension two.

The gap argument (Theorem 5) correctly bounds both the lost top direction and leakage into the penalized subspace. The normalized projected vector is well defined; the Frobenius estimate gives `d<=1/(12N^2)`, hence residual at most 1/2 after rounding. The simple-spectrum perturbation uses a nonzero discriminant polynomial, a polynomial-size candidate set, and a Lipschitz estimate for distance to the feasible set. The final threshold has a strict margin, so infimum attainment is not needed. No NP-membership or constant-relative-error conclusion is licensed.

Fresh checks enumerated all fifteen nonempty clause subsets on four available variables, removing unused variables, verified the Boolean equivalence, projector identities, positive inputs, thresholds, and all generated Boolean witnesses.

### NM-04 — `NM-04_sinkhorn_identity.tex`

The four cofactor/column/row/border identities are polynomial identities, so singular minors cause no gap. The empty-minor case is separately included. Substituting the balanced Schur complement gives the master identity with upward coefficient n and downward coefficient -m. The vector `(n/m)^k` exactly reconciles these coefficients with the original H convention. The minor covariance under diagonal scaling then transfers singularity to the arbitrary positive input.

The identity being proved matches the actual four cases and coefficient normalization of [Rowland–Wu, Conjecture 2](https://arxiv.org/html/2409.02789v2). The principal-minor expansion of a sum with a diagonal matrix proves the claimed coefficient sum, not merely a degree bound.

The arbitrary-margin extension uses deleted-row/deleted-column weights, as required by direct determinant differentiation. The additive compound formula has consistent signs and weights, including zeroth exterior power. Its characteristic polynomial, normalized coefficient sum, and square-unit-margin inverse/complement relation follow as stated. The degenerate-input degree argument divides out a common perturbation power and uses positivity plus cross-ratio continuity; it does not assert that the unperturbed displayed determinant is always a nonzero polynomial.

Fresh computations checked all four derivative identities symbolically for every minor of a 3x3 indeterminate matrix. Independently assembled weighted null vectors, additive compounds and characteristic polynomials pass at dimensions (1,1), (1,3), (3,1), (2,3), (3,2), (3,3), (4,3).

### NR-03 — `NR-03_n3_exact_rank.tex`

The rank-seven minor and parity null vector are correct. Both factor families inherit parity balance only under a hypothetical seven-term factorization, since both factors then have full rank. The nine distinguished entries cannot share a parity-balanced positive rectangle: different indices are excluded by zeros, and the same-index remaining alternatives force one side onto even subsets alone. Seven terms cannot cover nine entries; the identity factorization supplies eight.

The fresh exhaustive support calculation found exactly 89 rectangles whose row and column sets both contain both parities, each covering at most one distinguished entry. The conclusion is rank eight, not rank nine: imposing parity balance on a wider factorization would be invalid, and the manuscript explicitly avoids that mistake. The family n>=4 remains open.

### NR-04 — `NR-04_nine_point_distance.tex`

The polygon contact lemma is sound. Half-open vertex normal cones assign each supporting edge normal once; two distinct contact normals assigned to the same vertex would force a relative-interior contact point onto two different outer edges. Normalization of a low-rank factor places its column polytope in the simplex. The rank-three product columns have two-dimensional affine span, and each diagonal zero supplies an interior contact on a distinct edge because all other coordinates are strictly positive.

A three-dimensional polytope with at most six vertices has at most eight facets; its planar section therefore cannot supply nine contacts. This applies to either factor. Thus a six-term factorization would require both factor ranks at least five, contradicting Sylvester's bound `rank(WH)>=5+5-6=4`. The argument includes nonsymmetric matrices with the stated zero pattern. The integer seven-term reflection factorization was independently reconstructed and multiplied exactly. It matches all 81 entries, and the leading 3x3 minor is eight.

### PF-01 — `PF-01_subset_intersection.tex`

The dimension argument correctly forces one factor span to have dimension five in a hypothetical size-three factorization. It yields independent symmetric matrices Xi with factors Xi+Xj. Nonzero factors and zero diagonal imply orthogonal ranges, hence singular primal factors. Their sum is positive definite; otherwise the factor span would have dimension at most three.

Adjugates at rank two give the positive common outside gradient, while rank one gives zero gradient. The cubic coefficient argument leaves exactly `lambda e3+q sum ai xi`. Independently generated linear constraints have rank 29 on the 35 cubic monomials, confirming the six-dimensional space. The unspecialized Hessian determinant is the printed factorization. Positivity excludes one of the three possible pair sums and the elementary two-value classification leaves exactly the eight listed cases. All eight obstruction values were recomputed exactly. Global singular-point Hessian rank at most four, and rank-one Hessian rank at most three, provide the claimed contradictions.

The graph factors are PSD by construction, with trace equal to squared Frobenius distance. All 400 products in the combined n=5/n=6 two-layer factors were independently verified with exact radicals. The general odd/even construction and submatrix monotonicity use the correct subset cardinalities. The integer minimum over `ab>=d` is indeed `ceil(2 sqrt(d))`. No lower bound five for n=7 or 8 follows, and none is claimed. This remains one family entry.

### PF-02 — `PF-02_disconnected_orbits.tex`

The explicit positive Gram matrix has determinant 8192. Reflection of exactly one off-diagonal coordinate preserves the Gram entries and positive definiteness of the listed factors while reversing their six-dimensional coordinate orientation. Full ordinary rank makes the orientation nonzero in every size-three factorization. The congruence action determinant `(det S)^4` is positive, so the sign descends continuously to the quotient and separates it into two nonempty clopen sets. This proves disconnectedness, not only failure of path connectedness.

The all-size block construction forces a three-dimensional support from zero pairings and block ranks. Its symmetric-matrix orientation is independent of a basis of that support. The positive perturbation argument is also valid: normalization `sum A_i=I` bounds all primal and dual factors, giving a compact fiber. The eigenvalue gap and nonzero restricted Gram determinant persist uniformly over that fiber. Orthogonal equivalence of normalized representatives ensures that the resulting orientation still descends to the original congruence quotient. The nonquantitative small rational perturbation is an existence result, as advertised. Integer Gram/reflection/full-rank and cross-block-zero checks passed independently for k=3 through 7.

### PF-05 — `PF-05_rigidity_with_zeros.tex`

The operator representation uses the full three-dimensional factor spans correctly. The integration lemma is valid specifically for size two: at a rank-one dual factor, either the null-direction coefficient is positive, or straight-line feasibility forces the off-diagonal coefficient to vanish and the direction to be an exact scalar eigenvector. Thus the inverse-adjoint curve stays PSD. A straight segment of congruence operators preserves every rank-one ray, which forces its direction to be scalar.

Removing zero rows/columns preserves both properties and forces their directions to be zero. The normalized nonzero zero-pair yields the displayed three-parameter alternative operator; its shear and reflection adjustments preserve the distinguished primal/dual pair. The constructed rank-one-image direction is nonscalar. The exact identity `s q=g+(sigma u+alpha/2)^2` proves feasibility of all dual factors, including the flat q=0 case. The primal determinant identity proves the corresponding primal feasibility. Both adjoint and determinant identities were independently expanded.

For the remaining positive-entry case, [Dawson–Hoşten–Kubjas–Metsälampi v2, Theorem 5.2](https://arxiv.org/html/2410.18891v2) has precisely the required rank/size assumptions and does not impose distinct rank-one factors. Definition 1, Remark 1 and Theorem 2.2 match the canonical straight-line convention. The external theorem is therefore applicable rather than a merely related citation.

## PR54 proof audit

The manuscript paths are under `pr-54/references/colbrook-frames-2026-09-11/manuscripts/`.

### FR-02 and FR-10 — `sampling_thresholds.tex`

The low-sparsity result is specific to real Walsh rows with replacement and distortion 1/2. For two columns, distinct nonzero binary characters give independent sign sequences; the binomial union and second-moment thresholds agree. For three columns, the Gaussian/cosh argument proves the stated uniform positive-deviation MGF bound. The negative tail uses a valid one-sided bounded-variable Bernstein estimate, not the false assertion that `|1-X|<=1`. A polynomial-size sphere net and N^2 translated Gram types give the upper constant.

The matching lower proof's balanced type restriction is essential and valid. Disjoint character subspaces give independent events; line-intersecting subspaces have joint probability p^2/s after conditioning on the common bit sequence, and only O(N) partners per event are positively correlated. The two second-moment terms go to zero under the displayed strict inequalities. The exact integer comparisons `I>2J` at q=7/16 and 3/8 were checked. The rank-three affine supports at sparsity four have a Bernstein threshold strictly below the affine-plane threshold, so they do not change the constant. The stated constants are 5.298802786555886, 16.70018044183633, 36.38716620781762 (decimal displays only).

The full-space proof diagonalizes the sampling counts and uses the correct upper-tail entropy h+. Lower-tail entropy is strictly larger. The occupancy lower bound and pairwise negative correlations imply overload with high probability. The treatment of small m by rank, and uniform estimates for the remaining m, justify minima without assuming success is monotone in m. For nearly-full sparsity, truncating a conjugated flat row gives the necessary count bound; the convergent distortion perturbation preserves the leading constant. The real/complex field conventions and both canonical success probabilities are respected. No uniform intermediate-sparsity or cyclic low-sparsity claim is proved or asserted.

### FR-04 — `planar_projection_bound.tex`

The consecutive projective angle argument uses the determinant inequality for each pair. The log/arccos concavity and q/arccos convexity have the printed signs, including limiting q=1 cases. Jensen's inequalities give the claimed weighted sharp constant; equally spaced equal-length lines attain it. Determinant weighting of n-2 rows gives `(n-1)e_(n-1)/e_(n-2)`, and Newton's inequalities bound it by `2E/n`. Projection to the residual plane then gives the general formula, including rank-deficient inputs and n=2. Exact derivative and weighted-energy checks passed.

The resulting order is polynomial n^(-3/2). It cannot establish a uniform exponential decay. Keeping FR-04 Open is correct, and the manuscript explicitly disclaims novelty of the already-known polynomial order.

### FR-09 — `conference-proof.md` and rational certificates

The exact Cayley phase parametrization preserves every conjugacy and unit-modulus constraint. There are exactly d-1 real correlation equations; conjugate shifts and the even half-shift are handled correctly. Each real Hessian has total entrywise absolute sum at most 32d, including repeated dependence on the same coordinate. Thus the remainder and derivative bounds yield the stated self-map and contraction inequalities. Since `||I-MJ||<1`, M is invertible, so the Banach fixed point is a zero of F rather than merely MF.

The circulant block construction is Hermitian, has zero diagonal and unimodular off-diagonal entries, and squares to `(2d-1)I`. Trace zero fixes both eigenvalue multiplicities. Its shifted/rescaled Gram matrix gives exactly the canonical unit-norm tight equiangular frame, including two-circulant synthesis without assuming an invertible off-diagonal block.

I read the complete integer verifier, its input checks, signs, outward rounding, derivative construction, coarse-Jacobian error estimate and overflow proof before running it. All four supplied certificates pass a fresh run. The largest certificate, d=1505, has self-map bound approximately `1.003736e-10 < 1e-8` and contraction bound approximately `0.01145135 < 1`. These decimal figures are displays of exact rational comparisons. A second run for d=166 used only unbounded Python integer interval products, independent of the int64 multiplication path, and also passed. The separate direct-polynomial small-model checker confirms all value/derivative enclosures in dimensions 3 through 8. Its source was read, and its imported verifier was confirmed byte-identical to the version read above.

Only d=166,209,256,1505 have the necessary input certificates here. The other 88 report-only dimensions are correctly not accepted as certified. No all-dimension assertion is supported.

### FR-11 — `twelve_measurements.tex`

The coefficient map is a real-linear isomorphism onto the seven-dimensional hyperplane, and the real quotient has precisely the two-dimensional kernel `z(z-b)(t z^4+conjugate(t))`. The nonsingular symmetric bilinear argument proves all-signal recovery, including zero, without positivity or rank-one assumptions on the measurements.

All ten unordered root partitions are covered: four with fixed roots together, four split adjacent rotating pairs, and two split opposite pairs. The coefficient identities and three uniform imaginary-part bounds are correct; their weakest bound is 385/144. The rational bounds were independently recomputed. Complex leading-coefficient phases are retained through `alpha beta=t`, so hyperplane membership creates the intended contradiction.

The conservative stability proof keeps monic normalization separate from coefficient norms. The Mahler estimate is valid for degrees below three as well. Under the hypothetical small quotient norm, the lower bound on |t|, disjoint root disks, Rouché comparison, coefficient perturbation estimates, and final `385/144 > 12/5` contradiction all hold. The real coordinate norm estimate yields the announced bilinear constant 1e-6. Consequently both noise bounds and the openness-under-perturbation conclusion follow.

The exact decoder's quartic leading coefficient is nonzero; all nongeneric branches, conjugate tests, unused data equations, and the zero case are accounted for. Independent expansion generated twelve integral symmetric matrices with maximum absolute entry 144, and confirmed the quartic leading coefficient. After reading the floating-point decoder, a fresh seed-213 run passed 173 finite examples across all five branches, including scales 10^(-150) through 10^(150). Maximum relative signal error was approximately 2.58e-15. This numerical diagnostic does not turn the exact decoder proof into a uniform floating-point stability theorem; the manuscript makes that distinction already.

## Reproduction and document QA

Run the independent scripts using Python with SymPy 1.14.0:

```sh
PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps /Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 independent_checks.py
PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps /Users/ajt253/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 independent_nm04_pf01.py
```

Run from this report's directory. The results are **369/369** and **439/439**, respectively. Fresh certificate, model and decoder outputs are `conference-rerun.json`, `conference-pure-python-rerun.json`, `conference-model-rerun.json`, and `decoder-rerun.json`. Source-body integrity is recorded in `source-integrity.json`. Fourteen PR54 record-manifest hashes use pre-Git CRLF bytes, exactly as the manifest's stated convention permits; restoring CRLF explains every such mismatch, with no unexplained changes.

Read-only PDF QA used the PDF skill. All **22 changed final PDFs / 78 pages** were rendered and visually inspected on nine contact sheets, including every canonical page and every manuscript page. No clipped text, missing pages, overlap, broken glyphs, or incorrect displayed scope was found. Automated extraction found zero replacement glyphs and zero out-of-page character boxes. Section progression, the PF01 certificate table, theorem formulas, and final-page scopes agree with the source bodies reviewed. Extracted texts, contact sheets and structured diagnostics are in `pdf-qa/`; `pdf_qa.py` reproduces them. No submitted PDF or source file was modified.

Shared root indexes, merge conflicts, numbering-validator execution on the final combined tree, and external GitHub actions are the integrating agent's responsibility. This audit does not approve changes to the frozen mathematical targets or broader statuses than the table above.
