# SP-14: actual endpoint-extension Fourier kernel

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** mathematical and exact-rational pre-implementation contract, awaiting independent review. The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; the canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. This gate is the exact coefficient matrix in Lemma “The square-root extension of the analytic projection,” around source lines 856–890. Its scalar partial convolution is already proved in frozen `BaseEndpointPartialConvolution.lean`, SHA-256 `6e3ead11ba99fe781d8df49eaa4cdf7f920170488f72ebfece1f97b41c68f324` (independent final audit and aggregate integration pending when this contract was written).

This endpoint symbol is **different** from the previously proved odd-frequency `baseExteriorSymbol(z)=z\sqrt{1+z^{-2}}`. Here the exterior normalization is

\[
  g_0(s)=\sum_{n\ge0}a_n s^{-n}=\sqrt{1+s^{-1}},\qquad
  a_n=\binom{1/2}{n},\quad b_n=\binom{-1/2}{n},\quad
  A_n=(-1)^n b_n=\binom{2n}{n}/4^n.
\]

The boundary value is defined by the displayed absolutely summable series, including at its zero `s=-1`. For each `k≥0`, the triangular polynomial inverse of the analytic monomial `s^k` is

\[
 V_k(s)=\sum_{l=0}^{k}b_l s^{k-l},\qquad E_k(s)=g_0(s)V_k(s).
\]

Use the **frozen** `NLA.Statements.SP14.FourierCoefficient`, namely the totalized interval integral with `1/(2π)`, `Circle.exp`, and `exp(-i n t)`. All the functions in this contract are continuous, so interval-integral linearity is valid. The requested actual Fourier formulas, for every `k,p≥0` and `j≥1`, are

\[
 \widehat{E_k}(p)=\begin{cases}1&p=k,\\0&p\ne k,\end{cases}
 \qquad
 \widehat{E_k}(-j)
 =\sum_{d=0}^{k}a_{d+j}b_{k-d}
 =\frac{k+1/2}{k+j}b_kb_{j-1}
 =(-1)^{k+j-1}\frac{k+1/2}{k+j}A_kA_{j-1}.
\]

In Lean, the right sides of the Fourier equalities are coerced from real to complex. A proposed public surface is an explicit `endpointBaseSymbol : Circle → ℂ` series, `endpointInverseMonomial (k : ℕ) : Circle → ℂ` finite sum, and two theorems with conclusions equivalent to

```lean
FourierCoefficient (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
  (p : ℤ) = if p = k then 1 else 0

FourierCoefficient (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
  (-(j : ℤ)) =
  (((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
    baseInverseCoeff k * baseInverseCoeff (j - 1) : ℂ)
```

The negative-frequency theorem requires `1≤j`. The positive-frequency theorem covers `k=0`, `p=0`, and `p>k`, with no implicit finite frequency cutoff. To prove them, first show absolute summability of `a_n` from the already reviewed `summable_norm_baseCoeff` and the real-to-complex coefficient identity. Multiply by the finite `V_k`, interchange the resulting summable series with the actual interval integral, and apply the reviewed circle-mode integral formula. At `p≥0`, the coefficient of `s^p` is the full binomial convolution at order `k-p` when `p≤k`, and is zero when `p>k`; `(1+X)^{1/2}(1+X)^{-1/2}=1` yields the Kronecker result. At `-j`, the coefficient is exactly the frozen scalar theorem with `d=0,…,k`. No statement about an arbitrary pointwise square-root branch is substituted for this series definition.

The exact-rational signed kernel table for rows `j=1,2,3` and columns `k=0,1,2` is

| `j \ k` | 0 | 1 | 2 |
|---|---:|---:|---:|
| 1 | `1/2` | `-3/8` | `5/16` |
| 2 | `-1/8` | `1/8` | `-15/128` |
| 3 | `1/16` | `-9/128` | `9/128` |

For instance `k=0,j=1` is `a_1=1/2`; `k=0,j=2` is `a_2=-1/8`. The absolute-value matrix is the source's `K_{j,k}=((k+1/2)/(k+j))A_kA_{j-1}`. This gate does **not** prove its weighted Schur row/column sums, boundedness on `H^r`, Hilbert–Schmidt inverse, density extension, endpoint vanishing, any perturbed-background inverse estimate, or the full frozen negative Target. Each remains a separate obligation.

No Lean source for this gate is to be written before independent mathematical/numerical approval of this exact contract. Freeze the new Lean source for separate exact-signature/imported LeanCert audit before aggregate import.
