# MD-06 independent deterministic and full-manuscript review

Review date: 2026-09-11. Independent reviewer assignment: the full manuscript, with particular scrutiny of the variational correction, nonlinear cycle/tree construction, Hessian, explicit constants, and supplementary finite constructions. The canonical target and random-graph primary inputs were also checked independently. A separate reviewer specializes in the random-graph inputs; this report's mathematical verdict concerns the entire proof, not just the finite examples.

## Verdict and exact scope

**Mathematical verdict: PASS — full negative resolution of canonical MD-06.** For the uniform labelled simple cubic graph on even `n`, the proof establishes that the probability that every local minimum is synchronized tends to **zero**, rather than the conjectured one. It also proves the stronger existence, with probability tending to one, of a nonsynchronized critical point with a positive absolute lower bound on every edge cosine and a positive absolute Hessian bound on the mean-zero subspace. Recommend **Solved (disproved)** for the canonical conjecture, subject to the project's review and integration process.

**Reproduction-description defect in the submitted source:** Section 5.2 says an `analytic_gadget.py` and accompanying tests are supplied, but the inspected archive contains only `MD-06/code/verify_certificate.py`; no gadget program or tests were found anywhere in the extracted package. Thus that packaging assertion does not pass. The symbolic construction itself is mathematically valid and is not a premise of the asymptotic proof. The original should be retained; a reviewed copy should describe the absent program accurately before presenting the whole manuscript as fully checked. This issue was reported to the integration agent immediately.

No mathematical gap or unresolved asymptotic case was found. The integration agent will preserve the original source and add an explicit front-matter correction explaining the absent gadget program/tests and the separate provenance of reviewer code. Such a visible correction addresses the reproduction-description defect without changing the mathematical body. This review does not assert publication priority or proof-assistant verification.

## Reviewed source identity and canonical match

Original input: `.cache/colbrook-package-five/nla_submission_package/MD-06/manuscript/md06_counterexample.tex`.

- Full UTF-8/LF SHA-256: `fac30c17d890f6d0f767321ea13e7ff147a867073fef265f00a2ccf88ac66f75`.
- Normalized byte count: **22,850**.
- Hash procedure: decode the complete original as UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash. No trimming, omission of headers, or removal of terminal newlines.
- The manuscript is standalone and contains its preamble; no separate `common.tex` or unreviewed mathematical macros are used.
- This reviewer did not edit the submitted manuscript or canonical entry.

The complete `matrix-discrepancy-and-optimization/MD-06/README.md` was compared, as marked Open with last-check date 2026-09-10 at review start. The submitted graph distribution is uniform over labelled **simple** 3-regular graphs on `[n]`, for even `n`. The energy sums `1-cos` once per undirected edge. The domain is the full phase torus, synchronization is equality modulo `2*pi`, and local minima need not be strict because of rotation symmetry. All match the canonical problem. Existence of a nonsynchronized local minimum negates its every-local-minimum event; no dynamical basin-of-attraction or random-initialization claim is needed.

## Detailed deterministic proof audit

### Section 2, Lemma 2 (`lem:certificate`), lines 96–157

**PASS.** Differentiating the once-per-edge energy gives the stated sine gradient and weighted-Laplacian Hessian without a missing factor of two. Antisymmetry of sine implies zero total gradient, and the Hessian annihilates the constant vector.

Let `rho=c/(2*sqrt(2))` and restrict perturbations to the closed radius-`rho` ball in `1^perp`. The estimate `|h_u-h_v|<=sqrt(2)||h||_2` is the exact Cauchy–Schwarz bound for `e_u-e_v`. Cosine is globally 1-Lipschitz, including for arbitrarily large real lifts. Consequently every edge weight remains at least `c/2` throughout the whole ball. The unweighted spectral gap then gives Hessian lower bound `mu=c*gamma/2` on the slice, uniformly on every radial segment used in the proof.

Compactness gives a minimizer on the ball. At any boundary point, integrating the Hessian on the radial segment gives radial derivative at least `-rho*||g||+mu*rho^2`, which is strictly positive because `mu*rho=c^2*gamma/(4*sqrt(2))`. Therefore moving a sufficiently small distance inward decreases energy. A minimizer lies in the relative interior, and its gradient is orthogonal to the mean-zero subspace. The same gradient has zero sum, so it is exactly zero. This is an existence proof, not an assertion that an approximate point is stationary or that Newton iteration converges.

The Hessian at the corrected point retains the positive lower bound on `1^perp`. Taylor's theorem gives strict local minimality on that slice. Splitting any small real-lift perturbation into its mean-zero part and a constant rotation transfers this to local minimality on the torus. Rotation symmetry is handled correctly; a strictly positive Hessian on the entire space is neither asserted nor required.

### Section 3.1, Lemma 3 (`lem:profile`), lines 161–206

**PASS.** The continuous strictly increasing `F_R` vanishes at zero and exceeds `2*pi` at one for every `R>=4`. The displayed evaluation `F_4(1)=11*pi/6+2*asin(1/4)+2*asin(1/8)` is correct. Using `asin(x)>x` for positive `x` and `pi<4` proves the strict upper-end inequality. A unique root lies in `(0,1)`.

Increasing `R` adds the strictly positive term `2*asin(t/2^R)` for positive `t`, so the roots decrease. Convexity of arcsine places it below its endpoint chord `pi*x/2`; using the exact value `asin(1/2)=pi/6` proves `F_R(1/2)<=pi<2*pi`. Thus every root exceeds `1/2`.

All `delta_j` lie in `(0,pi/2)`, and `a_R=0` is compatible with the finite sum definition. Expanding `2*a_0+delta_0` gives exactly `F_R(t_R)=2*pi`. Therefore `sin(2*a_0)=-t_R` and `cos(2*a_0)=sqrt(1-t_R^2)>0`; the positive sign of the square root is justified by `delta_0` being in the principal arcsine range. Since `t_R<=t_4<1`, the common lower bound `c_0=sqrt(1-t_4^2)` is positive and independent of `R` and the cycle length.

### Remark 4 (`rem:constants`), lines 208–226

**PASS.** For `t_*=sqrt(255)/16`, the identity `asin(t_*)=pi/2-asin(1/16)` and the bound `asin(1/16)<1/sqrt(255)<1/15` give the first contribution `3*pi/2-1/5`. The inequality `asin(x)>=x+x^3/6` follows by integrating `(1-x^2)^(-1/2)>=1+x^2/2`. The sum over `x=t_*/2,t_*/4,t_*/8` gives linear coefficient `7/4` and cubic coefficient `73/1536`, which is greater than the manuscript's weaker `1/24`.

The lower estimates `t_*>99/100` and `t_*^3>97/100` are valid by squaring positive quantities. Exact rational arithmetic gives

`-1/5+(7/4)(99/100)+(1/24)(97/100)=151/96>11/7>pi/2`.

The last comparison uses the standard `pi<22/7`. Thus `F_4(t_*)>2*pi`, yielding `t_4<t_*` and `c_0>1/16`. The final conservative cosine bound `1/32` and the Hessian bound `1/320` for `gamma=1/10` are correct. The ratio `32/((1/16)^4(1/10)^2)` is exactly `209,715,200<2^28`. Hence `R=29+ceil(log_2 ell)` satisfies the strict radius inequality. All these rational constants were independently checked by the reviewer script.

### Definition 5 and Proposition 6 (`prop:localized`), lines 228–281

**PASS.** A clean induced radius-`R` neighborhood is connected and unicyclic, with the specified cycle its only cycle. In a simple cubic graph, a cycle vertex must have exactly one outward child. Each vertex at depth `1,...,R-1` has its parent and exactly two distinct children; any collision, same-level edge, or extra inward connection would create another cycle in the induced neighborhood. Thus the trees are disjoint and depth `j` has exactly `ell*2^(j-1)` vertices. The neighborhood has `ell*2^R` vertices. The clean hypothesis supplies all local graph structure used by the calculation.

For `ell` divisible by four, the repeated signs `+,+,-,-` close consistently around the cycle, including the last-to-first edge. Each root has one neighbor of each sign. Giving its tree the phase `epsilon*a_j` cancels the opposite-root sine force against the single child force at each root. At an interior depth-`j` vertex, the parent force is `-epsilon*t_R/2^(j-1)` and the two child forces each equal `epsilon*t_R/2^j`; cancellation is exact, including at depth `R-1` where the children have phase zero.

Each depth-`R` vertex has one nonzero parent and two zero-phase neighbors. Cleanliness in fact puts those neighbors outside the induced neighborhood; arbitrary further identifications and cycles outside do not matter, because their endpoints have phase zero. Every vertex beyond depth `R` is adjacent only to zero-phase vertices. Thus the only residual coordinates are the boundary ones, each of magnitude `t_R/2^(R-1)`, giving exactly `ell*t_R^2*2^(1-R)` for the squared gradient norm. There is no hidden assumption about the exterior graph being a tree or its boundary connections being independent.

The edge types are exhausted: same-sign cycle edges, opposite-sign cycle edges, tree edges, and zero-to-zero edges. Their cosines are respectively `1`, `sqrt(1-t_R^2)`, `cos(delta_j)>=cos(delta_0)`, and `1`, so all satisfy the uniform margin. An opposite-sign cycle difference is `±(2*pi-delta_0)`, whose distance from `2*pi*Z` is `delta_0>pi/6`. The gap statement uses distance modulo rotations correctly rather than the magnitude of an arbitrary lift.

### Theorem 7 (`thm:deterministic`), lines 283–306

**PASS.** Squaring the strict certificate threshold gives `c_0^4*gamma^2/32`. The radius inequality and `t_R<1` make the exact residual strictly smaller, so Lemma 2 applies. The correction changes each edge difference by strictly less than `c_0/2<=1/2`, whereas the distinguished cross-sign edge is initially more than `pi/6>1/2` from any multiple of `2*pi`. Distance to that closed set is 1-Lipschitz, so its corrected difference cannot vanish modulo `2*pi`. This excludes synchronization of the exact corrected minimum. The uniform cosine and Hessian conclusions are exactly those of the certificate.

There is no need to assume the correction stays supported on the local trees. It may involve every vertex; its global Euclidean norm is what controls all edge changes. The theorem is conditional on the full graph's spectral gap, which is verified probabilistically in the next section.

## Full asymptotic proof audit

### Random-graph inputs, Section 4, lines 308–329

**PASS.** Bordenave defines the uniform model on simple graphs with vertex set `[n]` on printed page 2. Theorem 1 bounds `mu_2` as well as the magnitude of the most negative adjacency eigenvalue, along sequences with `nd` even. For `d=3`, choose a fixed positive epsilon smaller than `3-2*sqrt(2)-1/10`; then `lambda_2(L)=3-mu_2>=1/10` with probability tending to one. This event entails connectivity. No conditioning on connectivity, configuration-model conversion, or omitted exceptional bipartite case is necessary. [Bordenave, Theorem 1 and model definition, printed p. 2](https://arxiv.org/pdf/1502.04482).

Johnson's Section 2 explicitly uses uniform simple regular graphs and requires even `n` for odd degree. Theorem 11 gives total-variation Poisson approximation to fixed-length cycle counts with mean `(d-1)^ell/(2*ell)`. Taking fixed `d=3` and fixed `ell` proves the required zero-count limit `exp(-2^ell/(2*ell))`. [Johnson, Section 2, printed p. 3; Theorem 11, printed p. 12](https://arxiv.org/pdf/1112.0704v5).

### Lemma 8 (`lem:clean-random`), lines 331–354

**PASS.** A radius neighborhood has at most `M=ell*2^R` vertices even when collisions reduce the count. A dirty connected neighborhood containing the given cycle has cyclomatic number at least two, hence `e-v>=1`. Removing leaves preserves `e-v`; because cycles are present, the process leaves a nonempty core of minimum degree at least two. It is a simple graph of maximum degree at most three and bounded size. This covers chorded cycles, colliding outward trees, and additional cycles connected through paths.

There are finitely many possible cores for fixed `ell,R`. For each specified labelled embedding, Johnson's Proposition 1(a) bounds its occurrence by `c_1*2^e*n^(-e)`. Its conditions `d<=n^(1/3)` and `e<=2*n^(1/10)` hold for all sufficiently large `n` because the degree and core are fixed. At most `n^v` embeddings of each core give `O(n^(v-e))=O(n^-1)`; summing over the finite types preserves this order. This is a bound on the existence of any dirty `ell`-cycle, not merely the neighborhood of a cycle chosen in advance. [Johnson, Proposition 1(a), printed p. 3](https://arxiv.org/pdf/1112.0704v5).

### Theorem 1 and stronger claim, lines 356–390

**PASS.** For fixed `ell` divisible by four, choose the corresponding fixed radius and apply the deterministic theorem on the intersection of three events: spectral gap, existence of an `ell`-cycle, and absence of dirty `ell`-cycles. A union bound gives the displayed upper bound for the global-synchronization event. These events need not be independent.

Taking the limit superior in even `n` with `ell,R` fixed yields at most `exp(-2^ell/(2*ell))`. Since this holds for every fixed multiple of four, that multiple may tend to infinity **after** the limit superior; the bound then tends to zero. Equivalently, for each positive error tolerance choose one sufficiently large fixed `ell`, then its fixed radius, then sufficiently large even `n`. No growing-radius estimate or uniformity in `ell` is assumed. Although a single fixed length would only give a positive-probability obstruction, the ordered limits close the entire canonical probability-one question.

The same argument applies to absence of a minimum with edge margin `c_0/2` and Hessian lower bound `c_0/20`; these constants do not depend on `ell`. The explicit weaker constants `1/32` and `1/320` therefore apply with high probability. The proof does not provide an effective useful finite-size threshold or a statement about the probability that random phase initialization converges to the new minimum. Neither is required by the canonical target.

## Supplementary finite assertions and code

### Section 5.1, rational certificates, lines 394–452

**PASS for the analytic certificate and verifier logic.** The identity `n||z||^2=sum_{u<v}(z_u-z_v)^2` holds on the mean-zero subspace. Bounding each pair difference along one shortest path by `D` times the full graph Dirichlet energy proves `lambda_2>=2/((n-1)D)>1/(nD)`. The inequality is deliberately crude but valid.

The sine polynomial through degree `2N+1` is also the Taylor polynomial through degree `2N+2`, because the next coefficient is zero; the cosine polynomial through degree `2N` likewise extends through degree `2N+1`. Lagrange remainders with the next derivatives bounded by one give the exact displayed enclosures for every real argument. No alternating-series term-size assumption, numerical argument reduction, or floating-point decision is necessary.

The complete supplied `code/verify_certificate.py` was read. It checks input phases and rational bounds, validates simple cubic connectivity, computes diameter by exhaustive BFS, accumulates signed sine intervals, bounds each gradient coordinate by the larger interval endpoint magnitude, and sums their squares. Acceptance compares `g2_upper<c^4*gamma^2/32` in `fractions.Fraction`. The nonzero edge witness `1<=abs(delta)<=5` remains of absolute value strictly between zero and `2*pi` after a change below `1/2`, using `2*pi>6`. All acceptance comparisons precede the descriptive float conversion. The routine proves a nearby exact nonsynchronized minimum, not exact stationarity of its rational input.

The table thresholds were independently recomputed as `1/81,920,000` and `1/4,718,592,000,000`. The integration agent freshly reran the two submitted data files, and this reviewer inspected the regenerated `verification/cubic20.json` and `verification/cubic500.json`: both report exact rational acceptance, diameters 5 and 12, the stated cosine and gap margins, and conservative squared-gradient bounds below `10^-22` and `10^-21`. Those finite runs are supplementary to the analytic random-graph theorem.

### Section 5.2, symbolic finite realization, lines 454–480

**Mathematical construction: PASS. Claimed supplied program/tests: FAIL as an archive-content assertion.** Four trees through depth `R-1` contain `4*2^(R-1)` vertices. Pairing their prospective leaves across opposite-sign trees produces `2^R` zero-phase vertices, for total `3*2^R`. The two pairing groups have equal size and are disjoint, so a perfect matching between them gives each new vertex a third edge without loops or duplicate edges. Parent vertices remain cubic; the original cycle connects all roots, and all added vertices attach to them. The resulting graph is simple, connected, and cubic.

Each new zero-phase vertex has two parents with opposite phases, so its two sine forces cancel, while its matching edge has zero force. All earlier root and tree cancellations remain unchanged. Edge cosines are positive by the scalar-profile lemma. Connectivity makes the weighted Hessian positive definite on the mean-zero subspace. The cross-root gap makes the equilibrium nonsynchronized. At `R=4`, the counts are indeed 48 vertices and 72 edges; at `R=5` they are 96 and 144.

The claimed `analytic_gadget.py` and accompanying tests are absent from the inspected archive. To check the finite construction independently, this reviewer wrote `verification/independent_md06_symbolic_review.py`, explicitly labelled **reviewer-written, not submitted code**. It constructs the graph at `R=4,5,6` and checks graph counts, simplicity, cubic degrees, connectivity, all allowed symbolic edge types, and exact zero sine-flow coefficients using integers and Fractions. It also checks the explicit-constant arithmetic. All passed; outputs are recorded in `independent_md06_symbolic_review_results.json`. This corroborates the finite construction but does not retroactively make the absent code part of the author's archive.

## Original-source and literature scope

The original source's Definition 2.1 uses angular variables and its Conjecture 3 asks whether uniform random cubic graphs are globally synchronizing with high probability. The canonical torus formulation matches those angular variables; the isolated sphere notation in that definition is not imposed as a new constraint. [Bandeira, Kireeva, Maillard, and Rödder, Definition 2.1 and Conjecture 3](https://arxiv.org/html/2504.20539v1).

DeVille and Ermentrout already give finite stable nonsynchronized cubic patterns and numerical evidence that the fraction of graphs lacking patterns decreases towards zero; Section IV phrases the asymptotic behavior as suggested by data. The submitted distinction between that evidence and the present asymptotic proof is accurate. The HTML labels its subsections numerically (I.5, II.1, III.7), corresponding to the manuscript's alphabetic I.E, II.A, III.G locators. [DeVille and Ermentrout, especially Sections III.7 and IV](https://arxiv.org/html/1512.06140).

## Exact remaining issues

- **Canonical mathematical target remaining:** none; the proof establishes the opposite probability limit, with uniform positive stability margins.
- **Mathematical correction required:** none found.
- **Presentation correction required for a fully accurate reviewed manuscript:** remove or explicitly qualify the assertion that `analytic_gadget.py` and accompanying tests were supplied, preserving the original archive. The integration agent's planned front-matter correction is a suitable way to qualify it without altering the mathematical body. Any newly added reviewer code must retain separate provenance.
- **Scope excluded from this verdict:** proof-assistant verification, priority certification, useful quantitative finite-`n` bounds, and probabilities for convergence from random initial phases.
