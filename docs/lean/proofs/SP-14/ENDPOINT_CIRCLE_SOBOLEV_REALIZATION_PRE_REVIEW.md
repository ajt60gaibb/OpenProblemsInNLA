# SP-14: endpoint two-sided coefficients as a circle Sobolev function

**Status:** source-locked mathematical and exact-rational numerical pre-implementation contract; independent review required before Lean source. **Author:** `/root/sp14_base_proof`, 10 October 2026.

The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical construction is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially notation at lines 32–65 and Lemma “The square-root extension of the analytic projection” at lines 851–900. The exact frozen real-interval `FourierCoefficient` is in `Statements/SP14.lean`; its sign is `exp(-i p t)` and its normalization is `1/(2π)`. The actual negative Fourier operator is `EndpointNegativeOperator.lean`, SHA-256 `16685a4f52b47911d79fc79b78cbdd9117e3efcb914e5102e0b068da118442b1`, independently audited and imported. The approved two-block coefficient module is `EndpointTwoSidedCoefficient.lean`, frozen SHA-256 `85173facb7957479a81fc4ea5ce706ebdb50e1a25338004dbd61b8a3a6ff9422`, pending separate final imported audit when this contract was frozen. Its `true` block is nonnegative and its `false` block is negative.

## Scope and exact series

Fix `1/2 < r < 1`, hence `0 < r`, and `y : SobolevCoeff r`. Put `T := endpointNegativeOperator r hr hr1`. Use the already frozen physical coefficient convention

\[
 a_k=(k+1)^{-r}y_k=\texttt{physicalCoeff r y k},\qquad
 b_t=(t+1)^{-r}(Ty)_t=\texttt{physicalCoeff r (T y) t}.
\]

Define the *actual circle function* by two absolutely convergent series

\[
 \mathcal E_r y(z)=\sum_{k\ge0}a_k z^k+
                 \sum_{t\ge0}b_t z^{-(t+1)},\qquad z\in\mathbb T.
\]

In Lean use `Circle → ℂ`, `∑' k : ℕ`, and the circle coercion `(z : ℂ)` with an integer power for the negative mode. The zero mode occurs once, in the positive series at `k=0`. The negative series starts at `-1` when `t=0`. This definition does not presuppose endpoint vanishing or an inverse `V`.

The intended public surface, with exact namespace/imports resolved at implementation, is:

```lean
noncomputable def endpointCircleRealization
    (r : ℝ) (hrHalf : (1/2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) : Circle → ℂ

theorem continuous_endpointCircleRealization ... :
    Continuous (endpointCircleRealization r hrHalf hr1 y)

theorem endpointCircleRealization_fourier_nonneg ... (k : ℕ) :
    FourierCoefficient (endpointCircleRealization r hrHalf hr1 y) (k : ℤ) =
      physicalCoeff r y k

theorem endpointCircleRealization_fourier_neg ... (t : ℕ) :
    FourierCoefficient (endpointCircleRealization r hrHalf hr1 y)
      (-((t + 1 : ℕ) : ℤ)) =
      physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t
```

The real-interval integral in these statements is exactly the frozen `FourierCoefficient`; neither an abstract Fourier transform nor a formal Laurent coefficient can replace it. Prove the Fourier equalities by summable/uniform termwise integration of the two circle series and the already reviewed all-integer circle-mode integral. Continuity follows from uniform absolute convergence, using `‖(z : ℂ)^p‖=1` on `Circle` for every integer `p`. For an arbitrary integer `p`, the two displayed branches are exhaustive: if `0≤p`, `p=(k:ℤ)`; otherwise uniquely `p=-((t+1:ℕ):ℤ)`.

## Literal Sobolev energy and norm comparisons

The two-block coefficient energy is exactly

\[
 \|\texttt{endpointTwoSidedCoeffOperator}(y)\|^2
 =\sum_{k\ge0}(k+1)^{2r}|a_k|^2
  +\sum_{t\ge0}(t+1)^{2r}|b_t|^2
 =\|y\|^2+\|Ty\|^2.
\]

This is the exact Hilbert model already proved in `EndpointTwoSidedCoefficient.lean`; the circle series must realize those very coefficients. For a conventional full-circle weight `w_r(p)=(1+|p|)^r`, the positive weights agree exactly, while for `p=-(t+1)` the conventional weight is `(t+2)^r`, not `(t+1)^r`. Therefore the conventional two-sided circle energy `H_r(\mathcal E_r y)^2 := ∑' p : ℤ, w_r(p)^2 * ‖FourierCoefficient (\mathcal E_r y) p‖^2` satisfies the explicit, correctly oriented comparison

\[
 \|\texttt{endpointTwoSidedCoeffOperator}(y)\|^2
 \le H_r(\mathcal E_r y)^2
 \le 2^{2r}\|\texttt{endpointTwoSidedCoeffOperator}(y)\|^2
 \le 2^{2r}(1+C_r^2)\|y\|^2,
 \qquad C_r=1+1/r+1/(1-r).
\]

It is acceptable to define the circle `H^r` space first as continuous functions with finite conventional weighted Fourier energy, then prove membership and these inequalities. The initial gate should expose exact Fourier identities and the weighted-energy comparison; it must not silently identify the asymmetric two-block norm with the conventional full-circle norm.

## Absolute convergence and exact numerical checks

Let `S_r = ∑' n : ℕ, (n+1)^(-2r)`. Since `2r>1`, it is finite and the elementary decreasing-function integral bound gives `S_r≤1+1/(2r-1)`. Cauchy–Schwarz yields

\[
 \sum_k|a_k|\le\sqrt{S_r}\,\|y\|,\qquad
 \sum_t|b_t|\le\sqrt{S_r}\,\|Ty\|,
\]

so both series are absolutely and uniformly convergent on `Circle`, and their combined absolute sum is at most `√(2S_r)‖endpointTwoSidedCoeffOperator(y)‖`. The empty input gives the zero function and zero Fourier coefficients. No branch collision occurs at `p=0`; `p=-1` is `t=0`, and `p=1` is `k=1`.

For source-used exponents `r=3/4` and `r=7/8`, exact rational arithmetic checks the constants:

| `r` | `C_r` | `S_r` upper bound | `2 S_r (1+C_r²)` upper bound |
|---|---:|---:|---:|
| `3/4` | `19/3` | `3` | `740/3` |
| `7/8` | `71/7` | `7/3` | `10180/21` |

Thus, for example, the uniform absolute sum at `r=3/4` is bounded by `√(740/3)‖y‖`. These are bounds, not asserted exact values of `S_r` or optimal operator constants. The endpoint `r=1/2` is excluded from the absolute-convergence argument because `S_r` diverges there. The manuscript's all-`0<r<1` `H^r` extension may instead be realized as an `L²` class for `r≤1/2`; that is a separate gate and is not claimed here.

This gate does **not** yet identify the realized function pointwise with `g₀V` for polynomial `y`, construct or bound the inverse `V`, prove `Π₊E y=y` in a separately defined function-space projection (although its exact nonnegative Fourier coefficients are established), prove vanishing at `-1`, or handle the perturbed background, nonlinear stage, jet-vector existence, both-sided nonextension, canonical gap, or the frozen Target. Those remain separate exact obligations. No Lean source for this gate before independent mathematical/numerical pre-review; any implementation must be frozen for a separate exact-source/imported LeanCert audit before aggregate import.
