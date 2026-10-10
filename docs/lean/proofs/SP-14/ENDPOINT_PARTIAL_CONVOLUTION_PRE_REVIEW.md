# SP-14: endpoint projection partial convolution

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source-locked mathematical/numerical pre-implementation contract; no Lean source for this gate before independent review. The frozen negative target `lean-statements/NLA/Statements/SP14.lean` has SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` has SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. This contract takes the exact identity displayed in the proof of Lemma “Coefficient and geometry bounds from the base preconditioner” near source lines 735–745, which is then used in Lemma “The square-root extension of the analytic projection” near lines 856–890. The existing kernel-reviewed definitions are `baseCoeffReal n = Ring.choose (1/2 : ℝ) n` and `baseInverseCoeff n = Ring.choose (-1/2 : ℝ) n` in `BaseJetTriangular.lean` and `BaseJetBinomialInverse.lean`.

## Exact all-index claim

For every `k : ℕ` and `j : ℕ` with `1 ≤ j`, put `a_n = baseCoeffReal n`, `b_n = baseInverseCoeff n`. The finite sum is

\[
\sum_{d=0}^{k} a_{d+j}b_{k-d}
 =\frac{k+1/2}{k+j}\,b_k b_{j-1}.
\]

The denominator `k+j` is strictly positive because `j≥1`. The index `k−d` is natural subtraction only within `d≤k`. A proposed public Lean signature, with equivalent elaborated casts allowed, is:

```lean
theorem baseEndpoint_partialConvolution (k j : ℕ) (hj : 1 ≤ j) :
    (∑ d ∈ Finset.range (k + 1),
      baseCoeffReal (d + j) * baseInverseCoeff (k - d)) =
      ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
        baseInverseCoeff k * baseInverseCoeff (j - 1)
```

No `j=0` extension is asserted: its displayed denominator can vanish at `(k,j)=(0,0)`, and the endpoint projection uses only strictly negative output frequencies `−j`, `j≥1`. The `k=0` endpoint is included and gives `a_j = (1/(2j))b_{j−1}`. The `(k,j)=(0,1)` value is `1/2` on both sides.

## Finite proof and exact checks

Let `B_k(z)=∑_{l=0}^{k}b_lz^l` and `S_k(z)=(1+z)^{1/2}B_k(z)` as formal series. The binomial recurrence `(l+1)b_{l+1}=(-1/2-l)b_l` cancels each coefficient below degree `k` in `B_k/2+(1+z)B'_k`, while the degree-`k` coefficient is `(k+1/2)b_k`. Thus the exact formal identity is

\[
S'_k(z)=(k+1/2)b_k z^k(1+z)^{-1/2}.
\]

The coefficient of `z^(k+j−1)` on the left is `(k+j)∑_{d=0}^{k}a_{d+j}b_{k-d}`; on the right it is `(k+1/2)b_kb_{j−1}`. Division by the positive integer `k+j` gives the claim. This route can use the existing `PowerSeries.binomialSeries_add` convolution and formal derivative API, or an equivalent finite recurrence in `j` and `k`; neither route needs analytic convergence or branch choices.

Exact rational arithmetic with `Ring.choose` gives the following left/right values for `k=0,1,2,3`:

| `j` | `k=0` | `k=1` | `k=2` | `k=3` |
|---:|---:|---:|---:|---:|
| 1 | `1/2` | `−3/8` | `5/16` | `−35/128` |
| 2 | `−1/8` | `1/8` | `−15/128` | `7/64` |
| 3 | `1/16` | `−9/128` | `9/128` | `−35/512` |
| 4 | `−5/128` | `3/64` | `−25/512` | `25/512` |

These checks fix the sign, shift `j−1`, numerator `k+1/2`, and denominator `k+j` without floating-point rounding. They include `k=0`; `j=1` is the first allowed output row.

## Relation to the actual endpoint extension

The identity is an exact input to the source's negative-frequency matrix for `Ey=g₀T(g₀)⁻¹y`. Combining it with the existing explicit finite inverse is expected to identify, **up to the source's modulation signs**, the absolute matrix entry `K_{j,k}=(k+1/2)A_kA_{j−1}/(k+j)`, where `A_n=|b_n|`. This scalar gate alone does not assert that matrix identity, Schur row/column estimates, boundedness of `E:H^r→H^r`, endpoint vanishing, or the actual compatible inverse for `\mathcal A_g`. The latter still requires projection, conformal, Jacobian, and perturbation estimates. The two-mode finite background and the canonical negative `Target` remain distinct from this analytic gate.

After independent pre-review, implement the scalar identity in a separate unimported Lean module; freeze its source and obtain separate imported LeanCert kernel/source review before aggregation. Do not edit the frozen target or shared metadata, and do not run Lake cleanup.
