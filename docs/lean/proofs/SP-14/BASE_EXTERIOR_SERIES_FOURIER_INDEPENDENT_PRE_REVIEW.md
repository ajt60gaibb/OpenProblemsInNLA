# SP-14 exterior series and Fourier bridge: independent pre-proof review

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the frozen `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` contract for implementation. The proposed theorems would identify the exact normalized exterior base series with the frozen integral-defined Fourier coefficients and prove its all-odd-order Toeplitz characteristic polynomial. They would not prove the frozen negative SP-14 `Target`.

The binomial recurrence is correct: for `n≥1`, `(n+1)c_(n+1)=(1/2−n)c_n`, hence `(n+1)a_(n+1)=(n−1/2)a_n` for `a_n=‖c_n‖`. The identity `a_n=2n a_n−2(n+1)a_(n+1)` telescopes to `Σ_(n=1)^N a_n=2a_1−2(N+1)a_(N+1)≤1`; adding `a_0=1` gives a bound of two on nonnegative partial sums. The `n=0` recurrence is intentionally treated separately. This is an exact summability proof and does not need an asymptotic estimate.

On the circle, integer powers have unit norm, so the `n`th summand has the constant norm `a_n`. The resulting uniform norm majorant supports convergence and a justified interchange with the actual real interval integral over `0..2π`; that analytic interchange is a required proof step. The previously audited integer-mode theorem then gives the coefficient at frequency `1−2n`, with the frozen negative exponential sign and `1/(2π)` normalization. The map `n↦1−2n` is injective. At even frequencies the coefficient is zero, while at `1−2p` it is `c_(p.toNat)` for `p≥0` and zero otherwise, exactly the existing `BaseFourierPattern`. The first coefficients `1,1/2,−1/8` and all-order Toeplitz conclusion are consistent with the reviewed finite blocks.

The series definition fixes the exterior branch through its leading term and coefficients; the square identity alone would leave a sign ambiguity. The optional boundary-square and outer-extension facts are correctly kept separate from the required Fourier and charpoly theorems. The base symbol has an outer extension and cannot serve as the final counterexample, which still needs packets, both nonextensions, selected-root multiplicities, a separated test, zero canonical average, and a positive empirical gap.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md`** | **`aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d`** |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` | `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9` |

Changed contract bytes reopen this pre-proof review.
