# SP-14: finite complex Schur bound for the actual endpoint extension matrix

**Status:** source-locked mathematical and exact-numerical pre-implementation contract; independent review required before Lean source. **Author:** `/root/sp14_base_proof`, 10 October 2026.

The frozen negative target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical construction is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Lemma “The square-root extension of the analytic projection,” around lines 851–897. The exact frozen Fourier mode is in `EndpointExtensionKernel.lean` SHA `2dd8c29d8d8ac936344e86ef37dcd794443113b3c4bf7c3f72268a8d8a59e83c`; the absolute coefficient is in `EndpointAbsoluteKernel.lean` SHA `da1aad945e27098c98daefddeacad99ad0246eb8a61890953317edfa05b2b673`. The scalar comparison modules are `EndpointWeightedSchur.lean` SHA `3f5e3bdcf912d1b38f2719ad9af1d647df69e987809d136c4865b892e0dbfccb`, `EndpointSchurSums.lean` SHA `2454551dd617c263ac24a997981da2b68da837187b7a0bbf7951cf1a037892ec`, and `EndpointSchurBounds.lean` SHA `cd466b5f516283210f0f58f70e1672abc009818fd89f609592b502d13d0e9db0`. The finite actual-kernel inequalities are frozen in `EndpointWeightedKernelSchur.lean` SHA `b7ba755ef50d356c00bd1c2b73529ddc053740b6537df974eec095d528c91849`, pending final independent source/kernel audit when this contract was written.

For real `0<r<1`, set the **literal** constant `C_r = 1 + 1/r + 1/(1-r)`. For natural row coordinate `t` and column coordinate `k`, the source's Fourier entry is

\[
 F_{t,k}=\operatorname{FourierCoefficient}
   (z\mapsto g_0(z)V_k(z))(-((t+1):\mathbb Z)),
 \quad g_0=\texttt{endpointBaseSymbol},\quad
 V_k=\texttt{endpointInverseMonomial}\;k.
\]

The physical negative-frequency index is **`j=t+1`**, never `t`. Define the complex Sobolev-weighted entry

\[
 B^{(r)}_{t,k}=(t+1)^r(k+1)^{-r}F_{t,k}.
\]

By norm multiplicativity and positivity of the real weights, `‖B^(r)_{t,k}‖ = endpointWeightedKernel r (t+1) k`; proving this exact identity in Lean is part of this gate. The frozen actual-kernel module proves the two finite Schur sums for every cutoff, using positive row/column weights `w_t=(t+1)^{-1/2}`, `v_k=(k+1)^{-1/2}`:

\[
 \sum_{k<N}|B_{t,k}|v_k\le C_r w_t,
 \qquad
 \sum_{t<J}|B_{t,k}|w_t\le C_r v_k.
\]

The next Lean theorem shall prove **finite complex matrix norm control** for *all* natural `N,J`, including `N=0` and/or `J=0`, and all vectors `x : Fin N → ℂ`:

\[
 \sum_{t:\mathrm{Fin}\,J}\left|\sum_{k:\mathrm{Fin}\,N}B^{(r)}_{t,k}x_k\right|^2
 \le C_r^2\sum_{k:\mathrm{Fin}\,N}|x_k|^2.
\]

An equivalent public Lean surface may define the finite complex linear map `Fin N → ℂ` to `Fin J → ℂ` with these exact entries, then prove its Euclidean operator norm is at most `C_r`. It must retain the frozen `FourierCoefficient` integral in the entry and the literal `Fin` index shift.

The elementary proof is the finite weighted Schur test. For each `t`, Cauchy–Schwarz gives

\[
 |\sum_k B_{t,k}x_k|^2
 \le (\sum_k |B_{t,k}|v_k)
       (\sum_k |B_{t,k}|\,|x_k|^2/v_k).
\]

The first factor is at most `C_r w_t`. Sum over `t`, interchange the *finite* sums, and use the column inequality to get `C_r² Σ_k |x_k|²`. Every `v_k` and `w_t` is strictly positive; the proof has no division by a zero endpoint, even when either finite index type is empty. Complex phases are handled by the triangle inequality before Cauchy–Schwarz. This gives the exact constant `C_r`, without a hidden factor from the complex norm.

Exact endpoint checks: with `N=0` or `J=0`, both sides reduce to zero (or the right side is nonnegative). With `N=J=1`, `F_{0,0}` has absolute value `1/2`, so the weighted one-by-one operator has norm `1/2≤C_r`; at `r=1/2`, `C_r=5`. The unweighted absolute `2×2` corner, rows `j=1,2` and columns `k=0,1`, is

\[
 \begin{pmatrix}1/2&3/8\\1/8&1/8\end{pmatrix},
\]

from the exact central coefficients `A_0=1`, `A_1=1/2`; the signed complex Fourier entries retain the sign from the frozen coefficient theorem. These checks are exact rationals, not floating-point evidence.

This finite theorem alone does **not** prove an infinite-dimensional bounded operator, the full `E:H^r→H^r` estimate, the separate Hilbert–Schmidt inverse bound, density, endpoint vanishing, a perturbed-background inverse, jet-vector existence, or the frozen negative Target. The subsequent extension must distinguish the negative-part norm bound `C_r` from the total two-sided norm bound `sqrt(1+C_r²)` when the positive projection is `y`. No Lean source for this gate before independent mathematical/source review; any Lean implementation must be frozen for a separate imported LeanCert audit before aggregate import.
