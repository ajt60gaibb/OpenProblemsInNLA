# SP-14: infinite negative Fourier operator from the finite Schur bound

**Status:** revised source-locked mathematical and exact-numerical pre-implementation contract; independent re-review required before the row/operator Lean source. **Author:** `/root/sp14_base_proof`, 10 October 2026.

This revision supersedes the first contract SHA-256 `d9812ed8dbbee37467b342d4419d9c6688add126da9cb3b9485f2e51fee4ce75` and its initial independent pre-review `ENDPOINT_INFINITE_NEGATIVE_OPERATOR_INDEPENDENT_PRE_REVIEW.md` SHA-256 `74d8d05e12ad3c0b13892871a435dad12c8311bcefabd0ac666e30fe0719b81c` for the row-summability step. The already frozen truncation-density theorem does not use that insufficient step.

The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical construction is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, in the square-root extension lemma. The actual Fourier matrix and its all-cutoff finite complex Schur bound are frozen in `lean-statements/NLA/Proofs/SP14/EndpointFiniteMatrixSchur.lean`, SHA-256 `0b8c3b6c2647a2f955a638993b0560343cc101f10adb8df16ad4fd096800de3b`. The literal weighted coefficient space is `SobolevCoeff s` in `WeightedSobolevPhysical.lean`, SHA-256 `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109`; its truncation is `sobolevTruncation` in `WeightedSobolevOperators.lean`, SHA-256 `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1`.

Fix `0<r<1` and the **literal** `C_r = endpointSchurConstant r = 1+1/r+1/(1-r)`. For `t,k≥0`, retain the frozen actual Fourier integral

\[
F_{t,k}=\operatorname{FourierCoefficient}
 (z\mapsto\texttt{endpointBaseSymbol}(z)\,
                 \texttt{endpointInverseMonomial}(k,z))(-((t+1):\mathbb Z)),
\quad B^{(r)}_{t,k}=(t+1)^r(k+1)^{-r}F_{t,k}
 =\texttt{endpointFiniteFourierEntry}\;r\;t\;k.
\]

The input coordinate `y k` for `y : SobolevCoeff r` is the **weighted** coefficient `(k+1)^r a_k`; `physicalCoeff r y k` is the physical `a_k`. The output index `t` represents the negative Fourier mode `-(t+1)`. No mode zero enters this negative operator.

## Exact implementation surface

The next Lean gate should construct an unconditional complex continuous linear map

```lean
noncomputable def endpointNegativeOperator (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : SobolevCoeff r →L[ℂ] SobolevCoeff r
```

or an equivalent public map with the same literal domain, codomain, and matrix entries. It should prove all three conclusions:

```lean
theorem summable_endpointFiniteFourierEntry_mul
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
  Summable (fun k : ℕ => endpointFiniteFourierEntry r t k * y k)

theorem endpointNegativeOperator_apply
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
  endpointNegativeOperator r hr hr1 y t =
    ∑' k : ℕ, endpointFiniteFourierEntry r t k * y k

theorem endpointNegativeOperator_norm_le
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
  ‖endpointNegativeOperator r hr hr1‖ ≤ endpointSchurConstant r
```

The Lean parser may require explicit `lp` coordinate coercions, but any adjusted signature must preserve these quantified equalities and the exact frozen Fourier entry. An intermediate bounded map on finitely supported sequences is permitted; a final theorem conditional on an abstract extension or arbitrary matrix is **not** this gate.

## Mathematical proof obligation

For `y : SobolevCoeff r`, let `P_N y = sobolevTruncation r N y`. First prove `P_N y → y` in the `lp` norm, including `N=0`, directly from square summability of its coordinates. The finite theorem gives, for every `J,N`,

\[
\sum_{t<J}\left|\sum_{k<N} B^{(r)}_{t,k}y_k\right|^2
 \le C_r^2\sum_{k<N}|y_k|^2.
\]

For fixed `t`, put `S_N=∑_{k<N}|B^(r)_{t,k}|²`. Apply the finite theorem with `J=t+1` and the complex test vector `x_k=conj(B^(r)_{t,k})`. Its selected row is the nonnegative real number `S_N`; the other row squares are nonnegative. Hence `S_N²≤C_r² S_N`, and therefore `S_N≤C_r²`, including `S_N=0`. Bounded monotone partial sums prove `∑_k|B^(r)_{t,k}|²<∞`, so each actual Fourier row belongs to `ℓ²`. The pinned `lp.summable_mul` (Hölder exponents `2,2`) then proves `∑_k |B^(r)_{t,k} y_k|<∞` for every `y∈ℓ²`, and `Summable.of_norm` gives the displayed complex `tsum`. This **absolute** summability is essential: Cauchy convergence of ordered interval partial sums alone would not establish Mathlib's unconditional `Summable` predicate.

The same all-`J` estimate and passage to limits of these absolutely convergent row sums give

\[
\sum_{t<J}\left|\sum_{k\ge0}B^{(r)}_{t,k}y_k\right|^2
 \le C_r^2\|y\|_{\ell^2}^2
\]

for every `J`; monotone square sums put the output in `lp 2` and give `‖Ty‖≤C_r‖y‖`. Finite-sum linearity and coordinatewise convergence yield complex linearity; boundedness yields the continuous linear map and operator-norm inequality. Equivalently, define it first on finitely supported inputs, prove the same bound, extend by their proven density, and identify every output coordinate with the displayed `tsum`. This route must use the finite **actual-Fourier** theorem, not an assumed generic bound.

The algebraic cancellation of physical/weighted coordinates gives the additional source interpretation

\[
\texttt{physicalCoeff}\;r\;(Ty)\;t
 = \sum_{k\ge0} F_{t,k}\,\texttt{physicalCoeff}\;r\;y\;k,
\]

provided the right series is shown summable; it can be a separate follow-up theorem if the main three conclusions already retain `F` through `endpointFiniteFourierEntry`.

## Exact checks and scope

At `r=1/2`, `C_r=5` exactly. For the `1×1` truncation, the absolute Fourier entry is `1/2`; the full infinite operator bound remains `5`, with no numerical truncation limit asserted. At `N=0` the finite input sum is zero; at `J=0` the finite output sum is zero. The `t=0` row is the physical negative mode `-1`, and the first input is `k=0`. No denominator vanishes because every `k+1` and `t+1` is positive.

This gate proves only the negative-frequency part of the canonical square-root extension. The full two-sided extension needs the unchanged nonnegative projection and orthogonality; its bound is `sqrt(1+C_r²)`, **not** `C_r`. The actual background-dependent inverse estimates, Wiener smallness conclusion, nonlinear stage, jet-vector existence, both-sided nonextension, canonical gap, and frozen negative Target remain open. Do not write Lean source for this gate before independent mathematical/numerical review; freeze any implementation for a separate imported LeanCert signature/kernel audit before aggregate import.
