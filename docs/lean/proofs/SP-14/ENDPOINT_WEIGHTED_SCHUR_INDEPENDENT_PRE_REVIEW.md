# SP-14 weighted Schur sums: independent pre-implementation review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact mathematical and indexing contract `ENDPOINT_WEIGHTED_SCHUR_PRE_REVIEW.md` at SHA-256 `0433186b4e5af5637f31ebc752e13b4f545a5639a0fa4e4a547e9ff8ce205c21` before Lean implementation.

I compared the contract with the canonical endpoint-extension lemma and its two displayed Schur sums (source lines 856–890), as well as the frozen negative SP-14 Target. The row index is `j≥1` and column index `k≥0`; the denominator is `j+k` and the `k+1` weight is preserved. Reindexing the second sum by `t=j−1` must retain `t+1+k`. The exact absolute Fourier kernel bound from the preceding approved gate gives the stated `M^(r)` entry and, after multiplying by `v_k` or `w_j`, exactly the two scalar row/column sums. Thus the finite Schur inequalities retain the actual Fourier kernel.

I independently checked both split estimates: for `n≤J`, `J+n−1≥J`; for `n>J`, `J+n−1≥n`. The first-term plus integral comparisons yield `1+J^(1−r)/(1−r)` and `J^(−r)/r` in the row, and `1+N^r/r` and `N^(r−1)/(1−r)` in the column. Multiplying by the outside powers gives the explicit common upper bound `C_r=1+1/r+1/(1−r)` for all `0<r<1`, including `j=1` and `k=0`. At `r=1/2`, `C_r=5`; the edge sums become exactly `∑_{n≥1}n^(−3/2)≤3`. No floating-point check is needed.

Approval covers summability, scalar bounds, and **finite** Schur inequalities. It does not imply an infinite-dimensional operator bound, inverse Hilbert–Schmidt estimate, density extension, endpoint vanishing, or the full SP-14 Target. Freeze any Lean implementation for an independent exact-signature/kernel audit before aggregate import.
