# IE-08 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the IE-08 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is an exact-statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/IE-08/README.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/ORIGINAL.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/NUMERICAL_TARGETS.md` | `31b774bae370d55c6575397db6c4b3dbad447a9205f3ab2549a96fd85b2bba08` |
| Supporting resolution: `eigenvalues-and-inverse-problems/IE-08/solution.md` | `650053dc10070ada37746a7fbb5a0d4735de967cc4452d5d03f771216a3e379d` |

The retained original and canonical README are byte identical. The permanent ID and path agree with `problem_ids.json`. The first three rows are the `check.py` specification review inputs; the solution is supporting evidence for the operational interpretation.

## Exact guarantee and numerical model

The specification preserves one uniform randomized floating-point algorithm and universal positive constants before every positive dimension, real `0<δ<1/2`, and complex matrix with spectral norm at most one. Its worst-case arithmetic count is `C n³ log(n/δ)^c` and precision is at most a universal multiple of `log(n/δ)` mantissa bits per real component. Using natural log and, if desired, a natural logarithmic exponent only changes universal witnesses on this domain. The constants do not depend on the matrix spectrum or conditioning.

Each run returns stored complex matrices `Q,T` with `T` **exactly upper triangular**. On one joint event of probability at least `99/100`, both `‖A−QTQᴴ‖₂≤δ` and `‖QᴴQ−I‖₂≤δ` hold; `Qᴴ` is conjugate transpose. The guarantee is against the original `A`, not just its rounded input. The spec adds no simplicity, separation, diagonalizability, or other spectral promise and correctly includes `n=1`.

The canonical statement explicitly requires a randomized **floating-point** algorithm in the usual relative-error model with sufficient exponent range. The resolution source confirms finite unbiased bits, capped sampling and loops, charged real arithmetic and classical matrix kernels, and no exact Gaussian/eigensolver oracle or hidden multiword precision. The spec appropriately requires an operational finite machine/transition meaning, real and complex rounding, worst-case caps on unsuccessful paths, and an explicit bridge if a finite dyadic accuracy request represents real `δ`. This prevents the mathematical proposition from degenerating into an arbitrary exact-real function with a cost label. Its discussion of conservative internal `R` and `u` parameters is evidence, not an added target. I found no changed residual, probability, cost, precision, quantifier, or floating-point condition.
