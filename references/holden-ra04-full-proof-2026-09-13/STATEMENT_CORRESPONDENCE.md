# Correspondence with the displayed RA-04 target

The canonical statement consulted was the RA-04 README at the URL and access date recorded in `sources.json`. The statement is reproduced mathematically in Section 1 of `report.pdf`. This comparison concerns that displayed algorithmic target, not all other conjectures in the source paper.

| RA-04 requirement | Manuscript correspondence |
|---|---|
| Real matrix `A` of arbitrary dimensions `n` by `d` | Theorem 1.1 and Section 1 use exactly this domain. Rectangular matrices are handled through `AA^T`. |
| Integers `1 <= b <= k`, `t = ceil(k/b)`, `k' = bt <= rank(A)` | The manuscript sets `m = k' = bt` with the same assumptions. |
| Positive relative `b`-step gap among the first `k'` squared singular values | Equation (1.1), with `lambda_i = sigma_i(A)^2`, is exactly that gap. No consecutive-gap assumption is added. |
| Empty minimum equal to one | Explicitly used when `t=1`. The square Gaussian starting-block argument handles this case directly. |
| Independent standard Gaussian entries in `G` | Unchanged. A fixed orthogonal eigenbasis preserves this distribution. No input perturbation, resampling, or modified sketch is introduced. |
| Exact Krylov space with powers from zero through `q-1` | Equation (1.2) and the exact simulated-start identity (7.5) use this convention. The simulated block is only an analytical construction. |
| Output `Z [Z^T A]_k` from SVD truncation | Theorem 1.1 and the imported convergence theorem refer to exactly this output. |
| An absolute constant for the displayed iteration order | Equation (1.3) is the same expression. Section 7 shows `C = 80 C0 + 4` suffices, where `C0 >= 1` is the absolute constant in the established good-start transfer theorem. A numerical value for `C0` is not assumed. |
| Both spectral and Frobenius `(1+epsilon)` approximation with probability at least `1-delta` | Equation (1.4), on a single probability event constructed in Section 7. |
| Ordered right-singular-vector energy guarantee | Equation (1.5); the imported result is checked against the right-vector convention in Problem 1.1 of Chen et al. It is not replaced by a left-vector assertion. |
| Every `0 < epsilon,delta < 1/2` | The new interpolation theorem holds for every `0 < eta < 1/2`; it is used with `eta=delta/2`. No cluster-width condition depends on the requested failure probability. |
| Exact zero-optimal-error case | When `lambda_{k+1}=0`, the rank and padding assumptions force `rank(A)=m=k`. Section 7 proves exact range recovery at depth `t+1` instead of taking a limit in a positive-tail estimate. |
| Unperturbed exact-arithmetic setting | The result makes no finite-precision claim. The word “perturbation” in the algebraic source title does not describe a change to the input; its average-case theorem is applied to the originally Gaussian `H`. |

The manuscript does not claim the source paper's distinct raw-matrix conditioning conjecture or a finite-precision extension. Neither is part of the RA-04 target inspected here. The raw monomial Krylov matrix may be badly conditioned even when the relevant interpolation and subspace quantities satisfy the new bound.

This correspondence is part of the author's self-audit, not an independently approved statement-equivalence certificate.
