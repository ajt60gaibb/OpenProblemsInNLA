# SP-14 exterior base boundary square and zeros: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent review before Lean implementation. This is the boundary-branch semantic check promised in `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` (SHA-256 `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d`). The immutable original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`). The normalized exterior series `baseExteriorSymbol` is frozen in `BaseExteriorSeries.lean` (SHA-256 `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d`).

## Exact public claims

```lean
theorem baseExteriorSymbol_sq (z : Circle) :
    baseExteriorSymbol z ^ 2 = (z : ℂ) ^ 2 + 1

theorem baseExteriorSymbol_zero_of_sq_eq_neg_one (z : Circle)
    (hz : (z : ℂ) ^ 2 = -1) : baseExteriorSymbol z = 0
```

These hold at every circle point, including `z` with `z²=-1`. The second theorem is an immediate consequence of the first in the integral domain `ℂ`. It does not require choosing a square-root branch at those zeros.

## Exact proof route

For fixed `z:Circle`, let `q=(z:ℂ)^(-2)`. Since `‖z‖=1`, `‖q‖=1`, and `b_n=baseCoeff n · q^n` is absolutely summable by the independently certified `summable_norm_baseCoeff`. Integer exponent arithmetic gives

```text
baseExteriorSymbol z = (z:ℂ) · Σ' n, b_n.
```

Apply the norm-summable complex Cauchy product theorem `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` to `Σ' b_n`. Each finite antidiagonal term has factor `q^(p+r)`, so the coefficient convolution `baseCoeff_convolution n` yields a series with only terms `n=0` and `n=1`, equal to `1+q`. Therefore

```text
(baseExteriorSymbol z)^2 = z²(1+z⁻²)=z²+1.
```

No formal-power-series evaluation at the radius of convergence is assumed; the passage to boundary values is justified by actual norm summability and the Cauchy-product theorem. The finite convolution holds at `n=0` and `n=1` without omitted terms. The identity `z²·z⁻²=1` uses `Circle.coe_ne_zero` and is valid at the two boundary zeros. For `z²=-1`, the equation gives `baseExteriorSymbol z ^ 2=0`, hence `baseExteriorSymbol z=0`.

## Scope and branch

The square identity alone does not identify a branch. The already frozen series definition with `baseCoeff 0=1` fixes the normalized exterior branch; this theorem checks its boundary values. It does not itself prove an `OuterExtension` witness or an inner/outer nonextension statement. The base symbol has an outer extension and remains unsuitable as the final witness to the frozen negative `SP14.Target`. Its all-order Toeplitz identity is separately certified and under final independent audit; the packet counterexample remains open.
