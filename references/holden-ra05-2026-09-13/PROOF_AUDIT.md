# Internal proof audit

This is an internal audit, not independent peer review or formal verification. Section and theorem numbers refer to the new manuscript, not the prior quartic PDF.

## 1. Statement correspondence

The row cost is the pth power of Euclidean residual length. The required weights are nonnegative and supported on original input rows. The support count counts nonzero row indices. There is no algorithmic restriction on how the weights are chosen. All subspaces of dimension at most k are covered by the assumed guarantee.

The lower bound uses only hyperplanes in dimension k+1. For a unit normal z, the residual is exactly `(a_i dot z) z`; homogeneity extends the comparison to unnormalized query normals. This is a necessary-condition reduction, not an assertion of equivalence with preservation of all lower-dimensional subspaces.

**Audit outcome:** the lower bound is inside the canonical model.

## 2. Core construction and Gaussian estimate

For L = floor(r^(p/2)), the normalized Gaussian core has uniformly bounded p-moment with positive probability. The Gaussian comparison proof in Appendix A has increment difference `2(1-a)(1-b)`, which is nonnegative because the dual exponent is below two and hence every dual-ball vector has Euclidean norm at most one.

The off-diagonal derivative kernel has squared entries `|z_i dot z_j|^(2p-2)`. Its expected total squared off-diagonal mass is at most `gamma_(2p-2) L^2/r^(p-1)`. Dividing the Markov threshold L/16 gives a failure bound at most `16 gamma_(2p-2) r^(1-p/2)`, tending to zero for each fixed p>2. There is no uniform-in-p lower dimension threshold.

**Invalid shortcut avoided:** small Frobenius error relative to L does not mean small operator-norm perturbation. The proof only counts eigenvalues outside [1/2, 3/2], then uses spectral truncation.

**Invalid shortcut avoided:** non-even derivative kernels are not assumed positive semidefinite. The code includes an actual non-PSD p=3 example.

## 3. Restricted invertibility and legal queries

For B = Pi K, where Pi keeps eigenvalues in [1/2, 3/2], the bounds are:

```text
||B||_op <= 3/2,
||B||_F^2 >= 3L/16,
stable_rank(B) >= L/12,
M = floor(L/48) <= stable_rank(B)/4.
```

The imported theorem therefore gives a selected column matrix with squared least singular value at least `(1/4)*(3/16) = 3/64`. The unprojected evaluation matrix E = K_S satisfies `||E h|| >= ||Pi E h||`, so the same lower singular-value bound holds for E.

The selected vectors u_j label input groups. Every candidate z_i remains a legal query direction. The proof does not claim that spectral projections of nonlinear costs are themselves individual legal queries; it first bounds actual evaluations and then applies a matrix inequality to their collection.

**Dependency:** Spielman–Srivastava restricted invertibility as stated in Marcus–Spielman–Srivastava, Theorem 1.1. It is not a result established by this package's finite tests.

## 4. Noise construction

The three required events are estimated under the same distribution of independent uniform unit vectors. Dependence among the three events is harmless because the proof uses a union bound, not multiplication of probabilities.

The Bernstein variance is at most `gamma_(2p) r^(-p)`. Its deviation is `gamma_p N r^(-p/2)`. The resulting exponent is at least `rho_p N/r^(p/2)`. A 1/4-net then yields the claimed moment bound after multiplying the seminorm by 4/3.

The small-subset singular-value statement quantifies over every coefficient vector and every subset of at most q0 columns. A 1/8-net is taken separately in each coefficient sphere; all subsets are union-bounded. Normalizing the Gaussian columns costs at most a factor two in the lower singular value, giving the conservative squared bound 1/64.

The floor in q0 is handled only after its unfloored value is at least two. This produces q0 >= c_p r/log(r). The input size N is polynomial in r, with exponent depending on fixed p.

## 5. Scaling and mass bounds

The product rows are `N^(-1/p)(u_j,v_t)`, so their p-cost is exactly `(1/N) sum |u_j dot x + v_t dot y|^p`. In particular, the original mass of each group is one, not N.

Integrating the core-only query over the sphere bounds the total group mass. Evaluating at a group's own unit core vector bounds that group's mass. Nonnegative weights are necessary for discarding other groups in the latter argument.

The noise-only query controls the weighted directional p-moment. This avoids replacing a remainder by an uncontrolled total variation of the coreset weights.

## 6. Noninteger derivative extraction

The global Taylor order is `q = ceil(p)-1`, so `q < p` even when p is an integer. The qth derivative of `|x|^p` is globally Hölder of order alpha = p-q. The integral remainder gives an explicit bound `2^(1-alpha)|b|^p <= 2|b|^p`, uniformly in the scalar base point, including zero and sign changes.

The derivative stencil is exact on degrees 0 through q. Its weights are `d_0 = -H_q` and `d_j = (-1)^(j+1) binom(q,j)/j`. The finite-difference error is bounded by `C_p t^(p-1)`, while observations have error `C_p epsilon/t`. Choosing `t = epsilon^(1/p)` gives derivative error `C_p epsilon^(1-1/p)`.

The nonnegative-weight hypothesis is used in `|alpha-1/N| <= alpha+1/N`, and the latter total directional moment is bounded by a genuine cost query. This proof is not claimed for arbitrary signed weights.

For even p, the loss is a polynomial of degree p. A different stencil of order p extracts the derivative exactly, at fixed step size, giving `C_p epsilon` instead. No polynomial exactness is claimed for non-even p.

## 7. From derivatives to group means

The derivative equals p times the derivative-evaluation matrix acting on group mean errors. Taking a supremum over the noise direction is exactly the Euclidean norm of a vector. Summing the squared row bounds gives a Frobenius bound on E H. The least singular value of E transfers it to H with factor 64/3. The number of queries L is at most 96 times the number of groups M.

The full mean contributes `2 M ||mu||^2 <= 16 M/N`, not an unscaled error or an error multiplied by N.

## 8. Support conversion

For a group with q_j <= q0 retained noise vectors, the small-subset bound gives `||b_j||^2 >= s_j^2/(64 q_j)`. For larger q_j, subtracting `s_j^2/q0` makes the right side nonpositive. Empty groups use the explicit convention `s_j^2/q_j = 0`, consistent with their zero mass.

Cauchy–Schwarz turns the squared total mass into a support count. The total mass is at least M/2 because epsilon<1/2, and the total squared group mass is O_p(M). The term 1/N is absorbed by 1/q0, using N>=q0.

**Limitation:** this step supplies no stronger q_j-dependent information beyond q0. The saturation in the theorem is not a proved optimal saturation of S_p.

## 9. Padding and all-exponent contradiction

For arbitrary k, r = floor((k+1)/2) leaves either zero or one padding coordinate. A padded normal defines a hyperplane of dimension exactly k and has exactly the old cost. Thus no unsupported monotonicity assertion in k is needed.

For the displayed-formula contradiction, take `a = min(p-2,1)/8`, `epsilon = k^(-a)`, and the universal weaker exponent beta=2-2/p. The exponent gaps are `a(p-2)/p` and `(p-2)/2 - 2a/p`, both strictly positive. Also a beta<1, so log(k)/k is negligible. This defeats every fixed logarithmic exponent and every fixed multiplicative constant.

## 10. Explicit quartic appendix

The finite-field forms are alternating in characteristic two. Their pairwise differences are nondegenerate because the field degree is odd, so the trace is the identity on the prime field. The character-sum calculation gives exactly the required cross-basis absolute inner products.

The fourth-moment identity follows from orthogonal decomposition of the traceless symmetric matrices. The cubic entrywise kernel is exactly `(1-1/r)I + UU^T/r` and is bounded below by `(1-1/r)I`.

The four-query identity isolates the cubic-linear coefficient without a remainder. Every omitted row contributes exactly 1/r^2 to the squared coefficient error. This proof indeed allows real signed weights. It does not rely on the new random-core construction.

## 11. Verification limits

All finite tests passed, but no numerical test proves the continuum or asymptotic claims. The small random cores in the results do not meet the conservative Frobenius condition from the existence proof. The code reports this rather than silently equating an illustrative example with a certified large-r construction.

The main proof is analytic and imports a stated structural theorem. The earlier quartic PDF is included only for provenance; no unproved claim from that file is used as a premise in the new proof. The upper-bound comparison is imported from the cited paper, and is not a new upper-bound proof.
