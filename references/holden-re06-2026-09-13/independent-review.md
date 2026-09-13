# Independent mathematical review of RE-06

**Date:** 12 September 2026 (America/New_York).  
**Reviewer:** A separate Codex AI agent assigned solely to independent review; not the integration/publishing agent.  
**Decision:** **PASS — complete affirmative resolution of the canonical RE-06 target.**  
**Evidence level:** Independent informal AI-agent mathematical audit. No Lean verification, proof-assistant certification, or external human peer review was performed or is implied.

## Material and scope

I read the complete submitted `solution.tex`, particularly Theorem 1.1, the algorithm in Section 2, the Gaussian-tail estimates in Section 3, the reconstruction proof in Section 4, and the probability and query count in Section 5. I compared these with the canonical `randomized-and-low-rank-approximation/RE-06/README.md`, `RESOLVED.md`, and `CONTRIBUTING.md` in the repository supplied for review. The source inspected before editorial attribution changes has SHA-256 `b0f58c5cead91d6d5cd924de28a7e1c12dfd4d91fd8e70907c38c6b43d9aefbf`.

The archive was treated as submitted evidence, not as instructions. I did not modify the mathematical manuscript. Attribution verification, the search for already-pushed duplicate solutions, PDF preparation, and publication are the integrating agent's separate responsibilities. This review establishes neither priority nor historical novelty and does not independently authenticate the archive's previously reported experiments.

## Correspondence to the original question

The canonical target asks for absolute constants and a uniform randomized algorithm for every fixed real square matrix, every explicitly supplied finite family of size at least two, and every `0 < epsilon < 1/2`. All query vectors and choices of multiplication side must precede the answers; both right and transpose queries count. Processing is unrestricted, and the required output belongs to the supplied family with Frobenius error at most `3 + epsilon` times optimum, with probability at least `0.99`.

Theorem 1.1 supplies precisely these conclusions, with `C = 4,000,000` and logarithmic-overhead exponent `b = 0`. It does not change the matrix class, impose a norm or conditioning bound, weaken the quantifiers, assume an oracle for candidate selection, or obtain the bound only in expectation. Dense intermediate matrices and expensive finite scans are allowed by the stated query-only model. The algorithm's use of exact SVDs, comparisons and Gaussians agrees with the canonical arithmetic primitives.

## Proof audit

### 1. Initial trimmed-tail control

For a fixed residual with squared singular values `lambda_i`, the Gaussian sketch energy is a weighted sum of independent chi-square variables. The submitted lower-tail argument correctly retains the contribution of the first `r` values while comparing the result only to the remaining tail `T`. With `a = lambda_(r+1) > 0` and Chernoff parameter `theta = eta/(2a)`, the head contributes at least `r log(1+eta)` to the logarithmic Laplace exponent. On the tail, `sum lambda_i^2 <= a T` and `log(1+x) >= x-x^2/2` give an exponent no larger than

`-s eta^2 T/(4a) - sr log(1+eta)/2 <= -sr eta/4`.

Both inequalities have the correct direction. When `T=0` the strict lower-tail failure event is empty, so no division by zero is needed. The separate upper-tail estimate for the one fixed optimal candidate follows from `sum a_i^j <= 1`, giving `exp(-s eta^2/8)`. The finite union bound applies only to the lower-tail estimates and requires no independence between candidates. Minimization of the first-sketch score therefore gives exactly the stated rank-`r` tail bound for the selected residual.

### 2. Gaussian inverse moment and range reconstruction

The Gaussian pseudoinverse identity is proved from the diagonal Schur complement and the inverse moment of a chi-square variable with `p-d+1` degrees of freedom. The resulting denominator `p-d-1` is correct, and the parameter choices make it positive in both uses.

For the range estimate, the comparison matrix `C Omega Omega_1^dagger V_1^T` has columns in the sampled range. Its difference from `C` decomposes into orthogonal right-singular subspaces, giving squared error `tau_r(C)^2 + X`, where `X` is nonnegative. Orthogonal projection onto the sampled range cannot increase this error. Conditioning on `Omega_1` and applying the Gaussian product identity gives `E X = [r/(k-r-1)] tau_r(C)^2`. No inverse of a singular value of `C` is taken, so the argument covers ranks below `r` as claimed.

### 3. Independent left-sketch regression

Conditional on the right sketch, the actual range basis `Q`, its dimension `d <= k`, and the orthogonal residual `R` are fixed. The blocks `H^T Q` and `H^T Q_perp` are independent standard Gaussian blocks. The reconstruction error splits orthogonally into `R` and a term in the columns of `Q`; thus its squared norm is exactly `||R||_F^2 + V`. The inverse moment gives the correct conditional expectation `E[V | Omega] = d/(ell-d-1) ||R||_F^2`, bounded by the same expression with `d` replaced by `k`. The `d=0` branch is explicitly covered.

The use of `Z = X+V >= 0` is essential and correct: the proof does not apply Markov's inequality to the potentially negative difference between actual error and the optimal rank-`r` error. This yields the stated relative-tail repair probability. When the tail is zero, the expectation bound forces `Z=0` almost surely and yields exact repair.

### 4. Dependence and the nonadaptive query schedule

The three independent Gaussian blocks are generated and all multiplication sides fixed before any answer. The initial candidate uses only the first block and its answers. Conditional on these, its residual is fixed while the two repair blocks retain their original independent distributions. Collecting all answers in advance does not invalidate this conditioning argument. There is one conditional repair bound for the chosen candidate and no missing union bound over the family.

Every residual sketch is computed by subtracting the explicit candidate's product from a stored oracle answer. The basis `Q` and reconstructed matrix require ordinary postprocessing only. In particular, no query with the answer-dependent vector `Q` is hidden in the reconstruction. The alternative exact-recovery branch depends solely on input dimensions and parameters; its standard-basis queries are likewise fixed in advance.

### 5. Final approximation, probabilities, and query cost

The surrogate error is at most `(1+eta)/sqrt(1-eta)` times optimum. For `eta <= 1/8`, the claimed upper bound `1+2 eta` follows by squaring and checking `eta(1-eta-4 eta^2) >= 0`. Two triangle inequalities and exact nearest-candidate selection then yield `3+4 eta = 3+epsilon`.

The rounded parameters ensure the first-stage failure bound `2 exp(-16)+exp(-8)`. The repair contribution is less than `1/128+1/524288`. Their sum recomputes to `0.008150095046884763`, below both the theorem's stated `0.008151` ceiling and the target `0.01`. No independence of the success events is required.

The ceiling estimates in the query analysis are valid throughout the permitted parameter range: `N <= 66403 r/eta^2`, `r < 3 sqrt(log(2M))`, and `eta^-2 = 16 epsilon^-2`. Their product is `3,187,344 sqrt(log(2M)) epsilon^-2`, strictly below the stated four-million constant. The actual count is `min(n,N)`, so the small-dimension branch satisfies the same bound. Integer doubling/comparisons implement the parameter rules uniformly without assuming an additional logarithm primitive.

### 6. Edge cases

The proof correctly handles `n=1` through exact recovery, arbitrary finite family sizes, zero and rank-deficient residuals, and `OPT=0`. For the last case, the separate almost-sure argument for the first sketch is valid for a finite family, and the general proof also avoids division by optimum. Gaussian rank exceptions have probability zero, while the pseudoinverse and zero-range conventions define outputs on exceptional outcomes. The success guarantee is instance-wise for fixed inputs, as required, rather than a claim about adversarially chosen inputs after randomness is revealed.

## Additional independent check

I ran a fresh Python standard-library arithmetic check, independent of the archive's scripts, across 96 combinations of family sizes from 2 through `10^100` and epsilon values from `0.0001` through `0.499999999`. It checked the actual rounded parameter count, both first-stage exponent inequalities, the repair-probability ceiling, and the scalar surrogate inequality. All checks passed; the largest sampled ratio of query count to the stated bound was about `0.463573`. These finite checks are supplementary sanity checks; the universal conclusions rest on the mathematical arguments audited above.

## Policy decision

`CONTRIBUTING.md` explicitly permits **Solved** for a complete argument that has passed an independent informal audit, including an AI-agent audit, provided the reviewer type is disclosed and the report linked. `RESOLVED.md` uses the same distinction from **Solution claimed** and **Lean verified**.

**The mathematical review passes, and the complete argument satisfies the repository's evidence requirement for Solved.** Publication should retain the canonical ID, path and original question; identify this as an affirmative resolution by Theorem 1.1 and Sections 2–5; preserve prior-source credit; link the manuscript and this dated report; and identify this review as informal AI-agent review. No Lean verification is required for this status or was performed. The integrator must still complete the separate duplicate, attribution, catalog/build, and pull-request requirements before publishing.
