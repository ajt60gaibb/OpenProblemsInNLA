# RA-05 independent review — PASS

Reviewer: independent Codex AI review agent `/root/review_ra05` (not the submission author or integrating agent). Date: 2026-09-14 UTC. Signed: Codex independent review agent.

**Verdict: PASS for the complete informal mathematical argument in Parts I and II.** No unresolved mathematical blocker was found. This is an informal AI-agent audit, not external human peer review, formal verification, or a novelty certificate. No Lean verification was requested or performed. Attached statements about status and workflow were treated as submission data, not instructions.

## Exact accepted scope and repository policy

For each fixed real p>2, all integer k>=1, every 0<epsilon<1/2, arbitrary finite real input matrices, unrestricted input rank and ambient dimension, the two parts establish the worst-case minimum support of nonnegative original-row strong coresets preserving every subspace of dimension at most k. With Lambda=log(2k/epsilon), the rate is

- non-even p: R=k^(p/2)/epsilon^2, lower R/Lambda^(5p/2+3), upper R Lambda^(p+5);
- even p: R=min(k^(p/2)/epsilon^2, k^((p+1)/2)/epsilon+k^(p/2-1)/epsilon^2), lower R without logarithmic loss, upper R Lambda^(p+5).

Constants depend only on the fixed exponent. This is an existence/size classification, without an efficient-construction claim. It matches the complete retained canonical target. It also disproves its subsidiary displayed additive upper-bound proposal for each fixed p>2. The previously published quartic and high-accuracy results alone were not used to certify the new claims: the entire included Part II proof was read and checked.

`CONTRIBUTING.md` Reporting a resolution and Lean verification, and `RESOLVED.md` Recording a new resolution, permit Solved for a complete argument passing an independent informal AI-agent audit. This report supports that level, conditional on integration retaining the original target, permanent ID/path, prior credit, precise classification and review disclosure. No full solution is present in the reviewed canonical page; its earlier contributions are partial. Global duplicate checks and publication actions belong to the integrating agent.

## Part I: analytic checks

1. **Core existence:** Recomputed the Gaussian increment comparison: for indices (x,y), with ||x||2=1 and ||y||p'<=1, the comparison variance difference is 2(1-x.x')(1-y.y')>=0. It gives E||G||2->p <= sqrt(r)+(L gamma_p)^(1/p). Markov, the explicit chi-square lower tail and a union bound give bounded p-moment cost for normalized rows with positive probability. For L=floor(r^(p/2)), E||K-I||F^2<=gamma_(2p), so Markov at L/16 leaves the claimed eigenvalue bulk. This proves a simultaneous all-direction moment estimate; it is not an unsupported finite-net or concentration assertion. Restricted invertibility on the bulk projection gives the stated least singular value for actual original columns, without assuming a positive-semidefinite non-even kernel.
2. **Walsh coefficient:** The Taylor remainder is integrable at both endpoints and has fixed nonzero sign by twice integrating R_q''=-R_(q-1). Polynomial annihilation is valid because the middle character degree exceeds p. The characteristic-function product gives the displayed Fourier integral. For h divisible by four both trigonometric powers are even; restricting to the explicit interval near pi/4 gives the stated eigenvalue lower bound. There is no cancellation or even-exponent interpolation. Restricted invertibility selects original cube columns with squared singular value at least beta_p 2^h/h^(2p+2).
3. **Multiplicative support:** Independently checked E=G Delta F^T, the cost bound C0 N, and the two-sided singular-value argument. Omitted rows contribute one each to ||Delta||F^2. This bounds all weights jointly (even signed weights in this regime), rather than adding unrelated groupwise bad queries. All product tests are legal hyperplane normals. Padding preserves them at rank k.
4. **All parameters:** Maximal admissible h in steps of four gives 2^h >= c_p epsilon^-2 h^-(2p+2); selecting N loses one more h, and the core pays h^-p/2. These are exactly the stated logarithmic losses. The explicit orthogonal-block construction supplies k/epsilon^2 at small k; its two tilted rank-k subspaces, residual formula, positive group masses, Cauchy--Schwarz and convexity all check. The constant-accuracy fallback follows from individual weight bounds and the zero-subspace mass query. Thus there is no missing small-rank or very-small-accuracy regime.

## Part II: new all-accuracy strengthening

1. **Structured Gaussian lemma:** The proposed estimate follows from two genuinely separate hypotheses: left variance bounds E||L_V Z||F^2 by sigma^2||L_V||F^2; full vectorized covariance bounds the top covariance eigenvalue by v^2||L_V||op^2. The Gaussian norm tail is derived by its moment-generating function. On the adapted norm |||V|||=(sum omega_i ||VB_i||^(2l))^(1/(2l)), ||L_V||F=|||V|||^l. Spanning makes this a norm on dimension k^2. Polarization gives a deterministic constant-mesh polynomial norming set of cardinality exp(O_l(k^2)). A union bound therefore yields sigma+O_l(vk), uniformly, with no condition-number or output-column loss. The Gram-matrix/isometry reduction covers arbitrary output dimensions. This is a derived uniform scale, not a sampled norming assertion.
2. **Features and all monomials:** Checked the optimal-head normalization, elementary Lewis isotropy construction, zero rows/ranges, probability densities, sensitivity, and mixed-feature covariance domination. The operator-valued mixed factorization has the correct tensor degrees and common scalar/vector output. Frobenius query-map bounds give k^(c/2)H^((l+j)/(2s)). In particular l+j+c<=2s-1 and j+c<=s-1 in the protected family. Balanced cross factors, one-cross anisotropic terms, and recombined pure-tail terms are covered separately; a vector output is never incorrectly counted as rank one.
3. **Protection and partial coloring:** Full matrix-Hilbert covariance has trace <=C_s k^(l+j)/eta. Protecting its top q=floor(theta_s A) eigenvectors costs q real scalar equations. Coefficient restriction contracts left variance and vectorized covariance and forces output orthogonal to those q directions. Hence v^2<=C_s k^(l+j)/(eta A); it does not require paying D_l q equations. Combining with the structured lemma yields relative error sqrt(eta)[k^((s-1)/2)+k^(s+1/2)/sqrt(A)]. Radial output truncation is separately allocated within the codimension budget. Its Gaussian width and Gaussian averaging give eta k^(s+1/2). All Gaussian events are symmetric convex increment constraints with fixed positive joint probability; Rothvoss's arbitrary-center subspace lemma applies at each fractional point. Recomputed protection spaces need not persist because their errors are summed.
4. **Invariant induction and support:** Active copies are dominated by the pre-round full positive measure; the argument does not assume the evolving weights are dominated by their original values. Frozen fractional entries remain in the invariants. Exact mass conservation halves full-copy counts. At executed stages eta<1/m0, so sum eta<=2/m0 and sum sqrt(eta)<=4/sqrt(m0). These close cumulative feature-matrix deviations and yield relative error O_s(L^(3/2)[k^(s+1/2)/m0+sqrt(k^(s-1)/m0)]). The specified m0 and O(L) frozen batches give the fifth logarithmic power. Preliminary row reduction removes original n,d dependence; positive composition preserves original indices. The zero-optimum head-only argument and Gaussian averaging cover zero-cost queries.
5. **Lower bounds:** Checked the smoothed stable core, legal fixed-rank auxiliary subspaces, exact polynomial derivative extraction, Frobenius mean-error bound and support conversion for unbounded auxiliary size. The separate variable-density construction proves its core and Haar-basis net event explicitly; its interpolation and entire-group orthogonality give the stated finite density inequality. Optimizing that inequality and combining with the uncapped high-accuracy bound gives the exact even rate throughout all regimes, including their junctions.

## Primary-source dependencies checked

The following original statements were opened and read on 2026-09-14; the argument is conditional on the imported published theorems in the ordinary mathematical sense, not on author-side numerical checks.

- [Lin--Mirrokni--Woodruff, Theorem 1.2](https://arxiv.org/html/2608.26047v2): original-row upper size with logarithmic exponent p+5, all input matrices, fixed failure probability; the source confirms rank-at-most-k preservation.
- [Marcus--Spielman--Srivastava, Theorem 1.1](https://arxiv.org/html/1712.07766): the stated Spielman--Srivastava stable-rank selected-column inequality, without unit-column hypothesis.
- [Rothvoss, Lemma 9, page 8](https://arxiv.org/pdf/1404.0339): a symmetric convex set of sufficient Gaussian measure in a coefficient subspace, arbitrary starting center in the open cube, and constant-fraction saturation. Taking the number of fractional coordinates sufficiently large ensures 1/2>=exp(-c0 A); this is absorbable in the manuscript's C_s threshold.
- [Tropp, Theorem 1.5](https://arxiv.org/html/1004.4389v7): rectangular Gaussian-series tail with both variance matrices and dimension prefactor. Projected coefficient Gaussians are first expressed in an orthonormal basis, so the independence hypothesis is respected.

The Li--Wang--Woodruff attribution is historical background, not an unproved premise of the self-contained Part I lower-bound derivation. No first-discovery priority was assessed.

## Reproduction and limitations

Inspected and ran `code/check_certificate.py` with Python integers/Fractions: **17,575 assertions passed**, saved as `RA-05-exact.json`. The useful universal finite conclusion is m>=204-548592 epsilon^2 for its explicit cubic tensor input. Of the assertion total, 17,136 are repeated sampled factorization checks and 408 are direct residual checks; none certifies an asymptotic theorem by counting examples.

The optional `verify_non_even.py` numerical suite was inspected. Its rerun initially failed because available Python environments lacked mpmath or NumPy/SciPy. This is an environment limitation, not a failing mathematical assertion. The exact certificate and the complete analytic audit above do not depend on this numerical suite. The saved author-side numerical results are not represented as independently rerun evidence here.

No mathematical revision is required by this audit. Typesetting/attribution-only changes should retain the analytic bodies bound below. A later substantive change would require renewed review. Source PDF layout, authorship and current affiliation verification, package-wide archival checks and the final catalog/PR integration are separate integration responsibilities.

## Reviewed source hashes (SHA-256)

- `manuscript/part_i_non_even.tex`: `55757c05cb7e39aeac5340daece08ea3d80186faddd3dfa8e4d884f43f816e88`
- `manuscript/part_ii_even.tex`: `cbda2397a24674371dcdc471802ef312789d856635650ab57ebd7dc72f5e42f2`
- `RA05_full_resolution.pdf`: `1461b8c10732625df88e7ef5d6c6ab09a64cac5d692f0007f69394c04d8bc81c`
- `code/check_certificate.py`: `d844c70ddd9d0f2d30ae6db754b7678617b13a505c9c437c3dd7be50c5005ce5`
- `code/verify_non_even.py`: `3bef858336888d3eba963cff02fd4887b9f016cfb7e16b712677c75f348575eb`
- `results/cubic_tensor_certificate.json`: `fea14b120f7af446a4f80be6236859ae27eb545d04ecd6a87e7a26d8cd1eeb83`

Input ZIP: `da7a8b2e07ab48885d4bb954d77c863398986fc3628c507f26b7a72e0e35f0a4`

## Final publication integrity — PASS (2026-09-14 UTC)

Compared both final TeX sources with their reviewed originals: changes are confined to the added dated submission cover, explicit Sidney Holden byline/affiliation, PDF author metadata, URL wrapping and emergency line stretch. Both mathematical bodies, theorem statements, proofs and references remain unchanged. The canonical RA-05 notice has the exact accepted even/non-even formula, correct quantifiers and Solved status, credited imported upper bound/Fourier antecedent, and informal-review disclosure. The RESOLVED notice agrees. Historical partial/open statements are expressly superseded, while the original target and permanent path/ID remain retained.

Rendered and visually inspected both new submission covers and both original manuscript title pages (four pages total): author lines, equations, disposition, review qualification and historical-scope boxes are legible, with no clipping or overlap. Verified the combined manuscript PDF is the exact page-content-stream and extracted-text concatenation of the two final part PDFs (17 + 27 = 44 pages). Affiliation verification itself remains the integrating agent's responsibility.

Final publication SHA-256:

- `part-1.tex`: `6cc00d4e27c20529eb95a406313bb19fbaee5049bda2febca3d88ec5e3673712`
- `part-2.tex`: `911fe25ca20da6f3f3b05686d5d646f7aa0604a4488e3b368cdefeff73ef1175`
- `manuscript.pdf`: `d3d26a9e295f6eb80a57a8399469fb161a3bf4b86efb4741c464743bb09929ed`
