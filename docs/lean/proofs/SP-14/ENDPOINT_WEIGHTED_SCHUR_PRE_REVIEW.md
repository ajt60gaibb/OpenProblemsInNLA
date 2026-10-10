# SP-14: weighted Schur sums for the actual endpoint kernel

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source-locked mathematical/exact-check pre-implementation contract, awaiting independent review. Frozen negative Target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. This contract is the two displayed Schur sums in Lemma “The square-root extension of the analytic projection,” source lines about 856–890. The actual Fourier kernel is independently reviewed in `EndpointExtensionKernel.lean` SHA `2dd8c29d...`; its absolute entry/central-binomial bound is frozen in `EndpointAbsoluteKernel.lean` SHA-256 `da1aad945e27098c98daefddeacad99ad0246eb8a61890953317edfa05b2b673` (final independent audit pending when this contract was written).

For a **real** `r` with `0<r<1`, define the explicit finite constant

\[
 C_r=1+\frac1r+\frac1{1-r}>0.
\]

All real powers below are powers of positive bases. For every integer `j≥1` and `k≥0`, the two source sums, including their exact indexing, are

\[
 R_r(j)=j^r\sum_{k=0}^{\infty}
       \frac{(k+1)^{-r}}{j+k},\qquad
 S_r(k)=(k+1)^{1-r}\sum_{j=1}^{\infty}
       \frac{j^{r-1}}{j+k}.
\]

Prove both series summable and `R_r(j)≤C_r`, `S_r(k)≤C_r` for every allowed `r,j,k`, with `j=1` and `k=0` included. In Lean the second series may be indexed by `t:ℕ` with `j=t+1`; the denominator must then be `t+1+k`. No term at `j=0` is introduced.

The exact elementary proof splits at `n=j` in the row sum after substituting `n=k+1`. For `n≤j`, `j+n−1≥j`; for `n>j`, `j+n−1≥n`. The decreasing-function comparisons are

\[
 \sum_{n=1}^{J}n^{-r}\le1+\frac{J^{1-r}}{1-r},\qquad
 \sum_{n>J}n^{-r-1}\le\frac{J^{-r}}r
 \quad (J\ge1).
\]

They give `R_r(j)≤1+1/(1−r)+1/r`. For the column sum put `n=k+1` and split at `j=n`: the denominator `j+n−1` is at least `n` for `j≤n` and at least `j` for `j>n`. The exact comparisons

\[
 \sum_{j=1}^{N}j^{r-1}\le1+\frac{N^r}{r},\qquad
 \sum_{j>N}j^{r-2}\le\frac{N^{r-1}}{1-r}
 \quad (N\ge1)
\]

give `S_r(k)≤1+1/r+1/(1−r)`. At the exact check `r=1/2`, both constants equal `5`; at `j=1` in the row or `k=0` in the column, the underlying sum is exactly `∑_{n≥1} n^{-3/2}`, with no denominator shift. In these two edge cases the sharper bound `≤3` follows from the same first-term/integral comparison. These are exact analytic comparisons, not floating-point estimates.

The audited actual absolute Fourier kernel is

\[
 K_{j,k}=\frac{k+1/2}{j+k}A_kA_{j-1},
 \qquad A_n\le(n+1)^{-1/2}.
\]

Consequently the Sobolev-weighted entry

\[
 M^{(r)}_{j,k}=\frac{j^r}{(k+1)^r}K_{j,k}
 \le\frac{j^{r-1/2}(k+1)^{1/2-r}}{j+k}.
\]

With row weights `w_j=j^{-1/2}` and column weights `v_k=(k+1)^{-1/2}`, the **finite** Schur inequalities inherited from the two infinite sums are

\[
 \sum_{k=0}^{K}M^{(r)}_{j,k}v_k\le C_r w_j,
 \qquad
 \sum_{j=1}^{J}M^{(r)}_{j,k}w_j\le C_r v_k
\]

for every finite `K≥0`, `J≥1`; empty cutoff variants should also be harmless. A proposed public Lean surface may prove the two infinite scalar sums first and then the exact finite Schur inequalities for `endpointKernelAbs`; equivalent organization is acceptable. The entrywise bound is sourced from the actual `FourierCoefficient`, so no unrelated matrix can satisfy the gate by substitution.

This contract does **not** yet assert a bounded operator `E:H^r→H^r`, the infinite-dimensional Schur-test theorem, the Hilbert–Schmidt bound for `T(g₀)⁻¹`, density extension, endpoint vanishing, perturbed-background inverse estimates, or the full frozen negative Target. Those require separate explicit proofs and reviews. No Lean source for this gate before independent mathematical/exact-index review, and any implementation must be frozen for separate imported LeanCert audit before aggregate import.
