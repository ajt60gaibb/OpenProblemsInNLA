# Exact Gaussian quadratic core specification

Written before implementation, 2026-10-06. The coordinator independently
approved these exact statements before code, including all stated domains.
The target is a bounded core needed by centered Gaussian Frobenius concentration;
the orthogonal diagonalization/matrix bridge remains a separate proof task.

Let `gaussianVector d` be the actual finite product of `d` real standard normal
laws on `Fin d → ℝ`, and `weightedSquares w z = ∑ i, w i * (z i)^2`.

1. For every real `s < 1/2`, the function `z ↦ exp(s*z²)` is integrable under
   `gaussianReal 0 1`, with integral `(sqrt(1-2*s))⁻¹`. Negative s are allowed.
2. For every natural d, real coefficient vector w and real t satisfying
   `∀ i, t*w i < 1/2`, the exact quadratic exponential is integrable and
   `∫ exp(t*weightedSquares w z) dμ = ∏ i, (sqrt(1-2*t*w i))⁻¹`.
   There is no restriction on the signs of t or w beyond those products.
3. For real `L > 0`, coefficients `0 ≤ w i ≤ L`, and real `x > 0`,
   `μ{z | 2*(∑ i,w i) + 4*L*x < weightedSquares w z} ≤ ofReal(exp(-x))`.
   Dimension zero is allowed. The event uses strict exceedance. A later matrix
   bridge handles zero operator norm separately instead of dividing by zero.

Proof route: evaluate the scalar weighted Gaussian integral with Mathlib's
proved Gaussian integral, factor the actual finite product integral, and apply
Chernoff at `t = 1/(4L)`. For `0 ≤ u ≤ 1/2`, the exact inequality
`-log(1-u) ≤ 2u` bounds the product MGF by `exp((∑w)/(2L))`.
The resulting threshold and tail constants are exactly 2 and 4 and exp(-x).

The local RRF GaussianQuadraticLaplace/LinearGaussianDensity proofs were
inspected for strategy. They use a substantially larger transformed-density
and matrix-square-root dependency chain. No RRF source is copied or imported;
this module will be proved directly from the pinned Mathlib APIs. The
manuscript's concentration result is not assumed, and no numerical sampling,
uncertified oracle, native proof, or custom axiom is admitted.
