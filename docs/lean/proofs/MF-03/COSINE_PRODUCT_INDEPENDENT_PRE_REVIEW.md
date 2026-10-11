# MF-03 cosine product: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `COSINE_PRODUCT_PRE_REVIEW.md` as an exact mathematical contract and viable proof route for the proposed product module. This is prior to Lean implementation and does not certify the still-needed Padé existence, Schur coefficient bounds, or full MF-03 `Target`.

The proposed `waveSeries z=Σ'_{j≥0}z^j/(2j)!` is the same entire coefficient series used in the frozen normalized Padé equations. `cosinePartialProduct N z` starts with `k=0`, hence `ν=1` and factor `1+4z/π²`; `N=0` gives the empty product one, and there is no `ν=0` term. The factors use the **plus** sign `1+z/[π²(ν−1/2)²]`, matching the manuscript's cosine/hyperbolic-cosine product. The proposed multipliability, finite-product convergence, and `tprod` equality are separate public theorems, so the identity cannot rely on `tprod`'s fallback value when convergence is absent. The zero and three evaluation theorems preserve the exact normalization and the already-proved real value bound.

The even/odd splitting is indexed correctly. If `S_N(w)=∏_{n=1}^N(1−w²/n²)` and `C_N(w)=∏_{k=0}^{N−1}(1−4w²/(2k+1)²)`, then exactly `S_(2N)(2w)=S_N(w)C_N(w)`: even factors `n=2j` produce `S_N(w)`, odd factors `n=2k+1` produce `C_N(w)`. Pinned `Complex.tendsto_euler_sin_prod` converges in the form `πw S_N(w)→sin(πw)`. At `w∉ℤ`, the latter limit is nonzero, so taking the ratio of the `2w` and `w` formulas and using the sine double-angle identity gives `C_N(w)→cos(πw)`. At integer `w`, that quotient is `0/0`, including at zero; it must not be used. The contract correctly calls for locally uniform convergence of the odd product on compact sets from the summable `O((2k+1)⁻²)` factor perturbations, so its limit is continuous and equality extends from the dense noninteger set. The direct `w=0` value is one. Pointwise Euler-sine convergence alone would not justify the exceptional-set extension.

For arbitrary complex `z`, a complex `w` with `(πw)²=−z` exists because `π≠0`. Then

```text
1−4w²/(2k+1)² = 1+z/[π²(k+1/2)²]
```

term by term. The complex cosine series has coefficients `(-1)^j(πw)^(2j)/(2j)!`; substituting `(πw)²=−z` gives `z^j/(2j)!`, with no branch choice or sign reversal. The identity holds at every `z`, including values mapping to integer `w`. At `z=3`, equality of the complex series with the cast of the real `waveAtThree` requires a justified interchange of real-to-complex coercion and `tsum`, which the contract explicitly retains as a proof obligation.

The proposed product equality is an analytic function identity. It does not by itself prove that coefficients of finite products converge to `1/(2j)!`; that coefficient-extraction step, the determinant/dual Jacobi–Trudi and tableau estimates, normalized Padé existence, and universal closed-disk bound remain separate. The manuscript's eventual Padé denominator coefficients alternate in sign and are not identified with the positive elementary symmetric coefficients of this source product. The contract states those limits accurately.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/MF-03/COSINE_PRODUCT_PRE_REVIEW.md`** | **`b78f8d9255dee8ffd2a6c4add6637ce95dbeaad6c61b3e87148bb101d3091b9a`** |
| Canonical `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Source manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Reviewed `NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| Reviewed `NLA/Proofs/MF03/WaveAtThree.lean` | `824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a` |
| Pinned Mathlib `EulerSineProd.lean` | `0988322f130952835b0da8d43d24b44c281af10bf149bb869ac750160ec1d5ac` |
| Pinned Mathlib trigonometric `Series.lean` | `307b22a20bcee20728e6bfda013c6f08fb126a25a2fe5e7d6cedb031bcd6a079` |

Changed contract or mathematical source bytes reopen this pre-proof review.
