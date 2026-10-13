# SP-14 exterior base series and Fourier interchange: pre-proof contract

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. This is the missing analytic bridge in the approved `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` (SHA-256 `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9`). The immutable source statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`); the mathematical reference is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`).

## Exact declarations and statements

Keep `baseCoeff n = Ring.choose (1/2:ℂ) n` unchanged. Prove the following without a summability hypothesis on callers:

```lean
theorem summable_norm_baseCoeff : Summable (fun n : ℕ => ‖baseCoeff n‖)

noncomputable def baseExteriorSymbol (z : Circle) : ℂ :=
  ∑' n : ℕ, baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ))

theorem baseExteriorSymbol_fourier_tsum (k : ℤ) :
    NLA.Statements.SP14.FourierCoefficient baseExteriorSymbol k =
      ∑' n : ℕ,
        baseCoeff n * (if 1 - 2 * (n : ℤ) = k then 1 else 0)

theorem baseExteriorSymbol_fourier_pattern :
    BaseFourierPattern baseExteriorSymbol

theorem baseExteriorSymbol_toeplitz_charpoly (m : ℕ) :
    (NLA.Statements.SP14.Toeplitz baseExteriorSymbol (2 * m + 1)).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m
```

The last theorem instantiates the independently audited conditional theorem `toeplitz_base_charpoly_of_fourier_pattern` (source SHA-256 to be recorded after its final frozen audit; current build source SHA-256 `1d3f3c01161ad3ba6aaadcd2603ee6b042978f43a48e88a4962292df3e96476c`). It is a base-symbol identity for all `m`, including `m=0`. The coefficient formula and parity pattern must use the frozen real-interval `FourierCoefficient` and all integer frequencies, with the negative sign in its exponential. The symbol is the explicitly normalized **exterior** series: its leading term is `z`, since `baseCoeff 0=1`; the choice of sign is fixed by this series, rather than inferred from the square equation alone.

## Exact summability proof route

Write `a_n=‖baseCoeff n‖ : ℝ`. Establish `a_0=1`, `a_1=1/2`, and, for each `n≥1`, the complex binomial recurrence

```text
(n+1)c_(n+1)=(1/2−n)c_n,
```

which gives the real nonnegative recurrence

```text
(n+1)a_(n+1)=(n−1/2)a_n.
```

Consequently `a_n=2n a_n−2(n+1)a_(n+1)` for `n≥1`. Summing from `1` through `N` telescopes:

```text
Σ_(n=1)^N a_n = 2a_1−2(N+1)a_(N+1) ≤ 1.
```

Thus every partial sum from `n=0` is at most `2`, including the empty sum. Since the terms are nonnegative, the bounded-partial-sums criterion gives `summable_norm_baseCoeff`. This proof needs no unproved asymptotic estimate or boundary value of the series. The recurrence has a separate `n=0` endpoint; applying the displayed norm recurrence at zero would be false.

## Exact termwise-integration route

For any `z:Circle` and integer `ℓ`, `‖(z:ℂ)^ℓ‖=1`. Therefore each series term has norm `‖baseCoeff n‖`, uniformly on the circle. Use `summable_norm_baseCoeff` to prove pointwise summability and continuity of `baseExteriorSymbol`; equivalently, use the uniform convergence theorem for a series of continuous functions dominated by these constant norms.

For fixed `k:ℤ`, the interval integrand of the `n`th term is

```text
F_n(t)=baseCoeff n · (Circle.exp t:ℂ)^(1−2n)
                     · exp(−(k:ℂ)i(t:ℂ)).
```

It is continuous in `t` and has norm exactly `‖baseCoeff n‖` on `[0,2π]`. Apply the interval version of dominated convergence or `intervalIntegral.hasSum_intervalIntegral_of_summable_norm`: the constant majorant is summable and its sum is interval integrable. This proves the interchange of `∫₀²π` and `∑' n` with the actual normalization factor `1/(2π)`. Then apply the kernel-checked `FourierCoefficient_circle_mode` (source SHA-256 `6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe`) to each term. The result is exactly `baseExteriorSymbol_fourier_tsum`, not merely a formal Fourier-coefficient assertion.

The frequencies `1−2n` are distinct. Elementary integer arithmetic reduces the tsum to zero at each even frequency and to `baseCoeff p.toNat` at `1−2p` when `p≥0`, zero when `p<0`. This establishes the exact existing `BaseFourierPattern` and hence the actual Toeplitz charpoly theorem above. In particular coefficients at `1`, `−1`, `−3` are `1`, `1/2`, `−1/8`; all even frequencies and all frequencies above `1` vanish.

## Boundary zero and branch semantics

The same absolutely convergent coefficient series and the already certified convolution `baseCoeff_convolution` should additionally prove, as a separate theorem, `(baseExteriorSymbol z)^2=(z:ℂ)^2+1` for every `z:Circle`. Therefore `baseExteriorSymbol z=0` whenever `(z:ℂ)^2=−1`, including the two points corresponding to `±i`. This boundary value must be obtained from the normalized series (or its certified Cauchy product), not used to justify convergence. The square identity alone does not define the branch; the series definition and `c_0=1` do. The exterior holomorphic realization `g₀(s)=Σ c_n s^(−n)` for `|s|>1`, its limit `1` at infinity, and its continuous boundary trace can be proved separately if needed for an explicit `OuterExtension` statement. These facts do not enter the Fourier coefficient or charpoly claims above.

This base symbol has an outer annular extension, so its charpoly identity is **not** a witness to the frozen negative `SP14.Target`. The final packet counterexample, nonextension on both sides, canonical average, selected-root multiplicities, and subsequence gap remain separate.
