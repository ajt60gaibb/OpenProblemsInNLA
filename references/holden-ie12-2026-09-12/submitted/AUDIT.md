# Mathematical and model audit

This audit records the internal checks behind the accompanying argument. It is not an independent review or a formal proof-assistant certificate. The self-contained proof is in `IE12_solution.pdf`.

## Proof map

| Paper location | Claim used downstream |
| --- | --- |
| Lemma 2, Section 2 | One unbiased rounding has a small operator-norm error with high probability and deterministic weight at most `65 n^2 / epsilon` |
| Lemma 3, Section 3 | At most `4^k` bounded-weight patterns; their identifiers and suffix descriptors can be built in charged time |
| Lemma 4, Section 3 | Both matrix-product directions cost `O(n 4^k + W/k + n)` after `O(W + k 4^k)` preprocessing |
| Lemma 6, Section 4 | The rectangular augmented system admits a condition-independent fixed-time kernel filter |
| Lemma 7, Section 5 | Clamping converts the approximate kernel vector to the original A-only backward-error metric |
| Lemma 8, Section 6 | Uniform small- and large-dimension inequalities cancel the iteration logarithm |
| Theorem 1 proof, Section 6 | Union of the probability bounds, all-outcome safety, deterministic cost, and storage |

## Scope and error metric

The input norm is a promise, not the output of a hidden singular-value calculation. The algorithm normalizes only `b`, using a dot product and a square root. Its final guarantee is evaluated with the original `A` and `b`. The exact certificate is

\[
\Delta A=(b-Ax)x^\top/\|x\|_2^2.
\]

It satisfies `(A + Delta A)x = b` and has norm equal to the stated backward error under `||A||_2 = 1`. No perturbation of `b` is silently allowed. Neither a small relative residual nor closeness to `A^{-1}b` is substituted for the requested criterion.

The rounded matrix may be singular. The construction does not solve an inconsistent rounded system and then pretend it is consistent. It works with an `n` by `n+1` matrix, whose kernel is guaranteed to be nontrivial. Indeed the original matrix need not be nonsingular either.

## Rounding and random primitives

One rounded matrix is drawn once and then reused. There is no accumulation of independently rounded products and no missing union bound over the iteration count.

For an entry `t = A_ij/h`, the integer part is found through repeated unit increments or decrements and comparisons. The total cost is charged to `sum |A_ij| / h`, bounded by `64 n^2 / epsilon`. No unit-cost floor is used in the proof.

The exact uniform draw uses the first coordinate of a normalized three-dimensional Gaussian direction. This coordinate is uniform on `[-1,1]`. Three Gaussian draws, one square root, and scalar arithmetic suffice. The probability-zero all-zero triple has an explicit branch, so no rejection loop or undefined division is left in the algorithm.

Every rounding error is centered and supported in an interval of length at most `h`. Its distribution need not be identical across entries. The bilinear-form bound uses independence and `sum u_i^2 v_j^2 = 1`. The two sphere nets cost nothing to the algorithm because they are used only in the proof. The probability estimate is dimension-uniform and does not use a random-input assumption about `A`.

The coefficient-weight bound is deterministic for every rounding outcome. The floor loops and preprocessing are therefore bounded even on failure events. The later Gaussian starting vector is fresh and independent of the rounded matrix.

## Weighted products and hidden logarithms

A naive appeal to a fixed-alphabet fast-product theorem would be insufficient: the alphabet of `Z` can grow. The proof instead controls the sum of weights `1 + |Z_ij|`.

A light coefficient has weight at most `k`. Heavy entries are handled directly, and are never expanded in unary. Separators created by heavy entries are charged as well: the number of light runs is at most the number of heavy entries plus the number of rows. This yields `S <= 2W/k + n` total product terms. No extra row-reset term is lost.

Pattern identifiers are built by explicit base-four arithmetic on an injective signed-unary code followed by padding. Computing a bin's identifier may cost `O(k)`, and this is paid in preprocessing through `S k <= 2W + n k`. There is no hash-table or arbitrary real-number bit-extraction assumption.

The product table is indexed by both pattern and starting column. Every product recomputes the whole table in `O(n 4^k)` operations. The recurrence uses a previously computed tail value, so it does **not** spend `O(k)` per table entry. The tail identifiers themselves were computed in preprocessing.

The forward and transpose routines are both constructed and paid for; transposition preserves `W`. There is no dense transpose product hidden in the iteration. Scaling by `h`, multiplication by the last column `c`, dot products, output summation, and vector updates all cost `O(n)` and are included.

Indexed scalar-array operations, counted at unit cost, do not change the bounds. The routines can also be viewed as preprocessing-generated arithmetic circuits with fixed wiring. This is ordinary scalar storage, not a word-RAM bit-packing trick. The chosen identifier range and table sizes are explicitly bounded by the memory estimate.

The iteration does **not** check `Ax-b` by a dense original-matrix product every time. A final original-system certificate check costs `O(n^2)` and is allowed. The prototype's early exit checks the augmented residual using the selected product backend.

## Filter and probability

On rounding success, `||Q||_2 <= 1 + epsilon/8 < 17/16`, and the squared norm of `B = [Q, -c]` is at most `545/256 < 4`. Therefore `I - B^T B/4` is a positive semidefinite contraction fixing `ker(B)`.

The unit kernel vector in the proof is existential and is never computed. Conditional on any good rounded matrix, its Gaussian coordinate is still standard normal. The elementary small-ball bound and Markov bound give a start event of probability greater than `0.998`.

The spectral proof separates eigenvalues at `eta^2/2` and retains the factor `lambda` in `lambda exp(-T lambda/2)`. This is important: replacing it by a uniform constant too soon would create an unnecessary `log(1/epsilon)` factor. The resulting iteration count is `O(epsilon^-2 log(n+1))`, independent of conditioning or a positive singular-value gap.

The final probability is strictly greater than `0.997`: rounding failure is less than `0.001`, and conditional filter failure is less than `0.002`. Independence between these two success events is not assumed; the conditional estimate suffices. No empirical success rate is used to establish this probability.

## Conversion and exceptional outcomes

On a successful filter outcome, the first `n` coordinates `u` cannot vanish: that would give augmented relative residual exactly `1`. The bound `||z||/||u|| < 3` uses the norm of `Q` and the approximate-kernel inequality, not the condition number of `A`.

The last coordinate `alpha` may equal zero. The denominator is explicitly clamped to signed magnitude at least `eta ||u||`, with the positive sign chosen at zero. The denominator is therefore nonzero, and its alteration contributes at most `eta` to the final backward-error budget.

The four components of the bound are the rounding term `rho`, at most `3 eta` from the augmented residual divided by `||u||`, and the clamping term `eta`. Their total is `rho + 4 eta = 5 epsilon/8`.

Outside the favorable events the algorithm is still defined. It has a fixed loop cap, no matrix inverse, no division by a singular value, and no unbounded retry. If the final `u` is exactly zero it returns `||b|| e_1`. Otherwise the clamped denominator is nonzero. The nonzero-output and norm bounds therefore hold for all random outcomes, not merely almost surely.

## Uniform operation bound and small dimensions

For `k = max(1, floor(log_16 n))`, the proof separately handles `n < 16`. The inequalities `k <= n`, `k 4^k <= 4n`, and `ell <= 39k` hold uniformly. The resulting cap is at most `10000 k / epsilon^2`.

The parameters are formed by multiplication and comparison loops; logarithms in their mathematical description are not assumed to be primitives. The main iteration loop implements the required ceiling through its stopping comparison.

Preprocessing, scalar indexing, initialization of unused table slots, loop counters, both products, and all vector work are included. The total is a worst-case bound `O(n^2 / epsilon^3)`, not an expected bound or one conditional on successful random draws. At most `O(n^2)` real-scalar words are stored. Exact real word size and precision are not bounded.

## What was actually executed

The archive records nine passing exact test groups and a 15-case floating-point solver suite, five same-draw dense/compressed comparisons, six additional nontrivial product budgets, and 300 rounding diagnostics. The exact tests use integer/rational arithmetic for their claims. The numerical solver and its Gaussian samples use floating-point arithmetic; its diagnostics are not part of the theorem.

During development, an empty `numpy.bincount` result produced an integer-typed array before a floating-point accumulation. The prototype was corrected to cast that intermediate to floating point. The saved exact and numerical checks were then rerun successfully. This implementation correction does not change the mathematical algorithm or proof.

No finite sample proves the universal theorem. No automated theorem prover, independent reviewer, or external repository acceptance is claimed. Historical novelty was not established by an exhaustive literature review. Finite-precision stability and practical speed remain outside this result's scope.
