# SP-14: absolute endpoint-extension kernel and central-binomial decay

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source-locked mathematical/exact-rational pre-implementation contract, awaiting independent review. The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. This gate isolates the exact absolute matrix entry and the `A_l≤C(l+1)^(-1/2)` step of Lemma “The square-root extension of the analytic projection,” near source lines 856–890. The actual negative Fourier formula is kernel-reviewed in frozen `EndpointExtensionKernel.lean`, SHA-256 `2dd8c29d8d8ac936344e86ef37dcd794443113b3c4bf7c3f72268a8d8a59e83c`; the nonnegative projection is frozen in `EndpointExtensionPositive.lean`, SHA-256 `ea6326e1739412233b52c5c6a672acb7c925a5be693bd3097e2a7f915b5d8969` (final independent audit passed; aggregate import pending when this contract was written).

For every `n≥0`, define the nonnegative central-binomial quantity

\[
 A_n=(-1)^n b_n=\frac{\binom{2n}{n}}{4^n},\qquad
 b_n=\texttt{baseInverseCoeff n}=\binom{-1/2}{n}.
\]

Prove, with `n=0` included,

\[
 A_0=1,\quad A_n>0,\quad
 A_{n+1}=\frac{2n+1}{2n+2}A_n,\quad
 (n+1)A_n^2\le1,
 \quad A_n\le (n+1)^{-1/2}.
\]

The recurrence follows from the existing exact `baseInverseCoeff` recurrence. Its squared induction is sharp at `n=0`: if `(n+1)A_n²≤1`, then

\[
 (n+2)A_{n+1}^2
 \le \frac{(n+2)(2n+1)^2}{(n+1)(2n+2)^2}
 \le1,
\]

because the denominator minus numerator, before the common positive factor `(n+1)`, is

\[
 (2n+2)^2(n+1)-(2n+1)^2(n+2)=3n+2\ge0.
\]

For all `k≥0` and `j≥1`, use the **actual frozen Fourier integral**, not an abstract matrix surrogate, to define

\[
 K_{j,k}=
 \left|\widehat{\bigl(\texttt{endpointBaseSymbol}\cdot
       \texttt{endpointInverseMonomial}(k)\bigr)}(-j)\right|.
\]

The required public statement (with equivalent Lean coercions allowed) is the exact equality and bound

\[
 K_{j,k}=
 \frac{k+1/2}{k+j}A_kA_{j-1}
 \le \frac{k+1/2}{(k+j)\sqrt{(k+1)j}}.
\]

The equality uses the reviewed signed Fourier theorem plus `b_n=(-1)^nA_n`, positivity of `k+j`, and the complex norm of a real number. The last inequality uses the two square-root bounds. No `j=0` entry is asserted because the negative output mode is `-j` with `j≥1`.

The exact-rational checks are `A_0,…,A_4=(1,1/2,3/8,5/16,35/128)`. For rows `j=1,2,3` and columns `k=0,1,2`, the **absolute** kernel is

| `j \ k` | 0 | 1 | 2 |
|---|---:|---:|---:|
| 1 | `1/2` | `3/8` | `5/16` |
| 2 | `1/8` | `1/8` | `15/128` |
| 3 | `1/16` | `9/128` | `9/128` |

These entries are absolute values of the alternating signed table in `ENDPOINT_EXTENSION_KERNEL_PRE_REVIEW.md`; in particular `K_{1,0}=1/2` and `K_{2,0}=1/8`. This gate does **not** prove the infinite weighted Schur row and column sums, boundedness of `E:H^r→H^r`, Hilbert–Schmidt bounds for its inverse, density extension, endpoint vanishing, perturbed-background compatibility, or the full frozen negative Target. A later Schur contract will use the exact entry bound; no operator conclusion may be inferred from this finite entry gate alone.

No Lean source for this gate before independent mathematical/numerical review. Freeze any implementation for separate exact-signature/imported LeanCert audit before aggregate import.
